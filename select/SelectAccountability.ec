(**********************************************************************)
(***     This file contains the accountability proof for sElect     ***)
(**********************************************************************)

(*----------------------------------------*)
(* Require and import necessary theories  *)
(*----------------------------------------*)
require import AllCore SmtMap List FSet Finite. 
require (*  *) SelectDefinition. 

clone include SelectDefinition. 

module G = {
  var e : bool
  var f : bool
  var c : bool
}. 

section. 

(*----------------------------------------*)
(*   Abstract modules used in the proof   *)
(*----------------------------------------*)
declare module VSD <: VSD { -GlobVar, -G }. 
declare module A   <: Acc_Adv { -GlobVar, -VSD, -G }.  

(*-------------------------------------------*)
(* Original experiment with global variables *)
(*-------------------------------------------*)
module Acc_glob = {
  
  module S = Select(VSD)
  module O = Acc_Oracle(S)
  module A = A(O)

  proc init(): unit ={

    GlobVar.vsd_blame   <- [];
    GlobVar.v_ballots   <- empty;

  }

  proc vsd_verify(): vsd_evidence list ={

    var i, st, v, b, s, id,  vsd_evidence;

    i <- 0;
    
    (* verify run by all voters that honestly voted *)
    while (i < card (fdom GlobVar.v_ballots)){
      
      (* get state and ballot for voter id *)
            id <- nth witness (elems (fdom GlobVar.v_ballots)) i;
      (st,v,b) <- oget GlobVar.v_ballots.[id];
      s        <- oget GlobVar.v_sign.[id];

      vsd_evidence <@ S.vsd_verify(GlobVar.pp, st, v, b, s, GlobVar.bb, GlobVar.rez);

      if (vsd_evidence <> None){
        GlobVar.vsd_blame <- GlobVar.vsd_blame ++ [oget vsd_evidence];
      }

        i <- i + 1;
    }

    (* return all blame evidence *)
    return GlobVar.vsd_blame;
    
  }

  (* main experiment *)

  proc main(): bool ={

    var dishonest_blamed, pl, pl', i, st, v, b,  s, id, r;

    init();

    GlobVar.pp <@ A.setup();
    (GlobVar.bb, GlobVar.rez, GlobVar.v_sign) <@ A.run();

   (* if A has not provided valid signatures it loses *)
    G.e <- true;
    i  <- 0;
      while (i < card (fdom GlobVar.v_ballots)){
       id <- nth witness (elems (fdom GlobVar.v_ballots)) i;
      (st,v,b) <- oget GlobVar.v_ballots.[id];
       s        <- oget GlobVar.v_sign.[id];
      r <@ S.valid_sig(GlobVar.pp, b, s);
      if (!r) {
        G.e <- false;
      }
      i <- i + 1;
   }

    (* GlobVar.vsd_blame gets updated *)            
    vsd_verify();

    (* adv adds blame fom dishonest *)                
    dishonest_blamed <@ A.dishonest_blamed(GlobVar.vsd_blame);

    (* use this order as (+) keeps last map if x \in m2 then m2.[x] else m1.[x] *)
    GlobVar.vsd_blame <- GlobVar.vsd_blame ++ dishonest_blamed;

    (* universal verification *)
    pl <@ S.judge(GlobVar.pp, GlobVar.bb, GlobVar.rez, 
                             GlobVar.vsd_blame);
    pl'<@ S.bad(GlobVar.pp, GlobVar.bb, GlobVar.rez, GlobVar.v_ballots, 
                GlobVar.vsd_blame);
    
    (* G.f is true if judge has blamed an innocent party *)
    G.f <-  (exists x, Some x = pl /\ !(x \in pl'));
            
    (* G.c is set to true if *)
    G.c <-   (* no one is blamed
             and (more ballots or votes were introduced or honest votes were dropped) *)
                 (pl = None
                 /\ (   (* limit on number of ballots *)
                         n_v < (size GlobVar.bb) 
                      \/ (* more votes than ballots *)
                         size GlobVar.bb  < size GlobVar.rez.`1 
                      \/ (* honest votes were dropped *)
                         !((oflist (lex (map (fun x=> (oget GlobVar.v_ballots.[x]).`2) 
                             (to_seq (dom GlobVar.v_ballots))))) \subset (oflist GlobVar.rez.`1))
                    )
                  );

    return (G.e /\ G.f) \/ (G.e /\ G.c);

  }

}.

(*---------------------------------------------*)
(* Prove that acc with glob vars is equivalent *)
(* to the original security experiment         *)
(*---------------------------------------------*)
lemma acc_glob_equiv : equiv[Acc(Select(VSD),A).main ~ Acc_glob.main : ={glob A,glob VSD} ==> ={res}]. 
proof. 
proc. 
wp. progress.
conseq (: _ ==> ={pl, pl', GlobVar.bb, GlobVar.rez, GlobVar.v_ballots} /\ es{1} = G.e{2})=> [//#|].
sim.
qed. 

lemma acc_glob_equiv_pr &m : 
  Pr[Acc(Select(VSD),A).main() @ &m : res] 
  = Pr[Acc_glob.main() @ &m : res] 
  by byequiv acc_glob_equiv. 

(*----------------------------------------*)
(*          Fairness experiment           *)
(*----------------------------------------*)

module Fairness = {
  
  module O = Acc_Oracle(Select(VSD))
  module A = A(O)
  module S = Select(VSD)

  proc init(): unit ={

    GlobVar.vsd_blame   <- [];
    GlobVar.v_ballots   <- empty;

  }

 
  proc vsd_verify(): vsd_evidence list ={

    var i, st, v, b, s, id,  vsd_evidence;

    i <- 0;
    
    (* verify run by all voters that honestly voted *)
    while (i < card (fdom GlobVar.v_ballots)){
      
      (* get state and ballot for voter id *)
            id <- nth witness (elems (fdom GlobVar.v_ballots)) i;
      (st,v,b) <- oget GlobVar.v_ballots.[id];
      s        <- oget GlobVar.v_sign.[id];

      vsd_evidence <@ S.vsd_verify(GlobVar.pp, st, v, b, s, GlobVar.bb, GlobVar.rez);

      if (vsd_evidence <> None){
        GlobVar.vsd_blame <- GlobVar.vsd_blame ++ [oget vsd_evidence];
      }

        i <- i + 1;
    }

    (* return all blame evidence *)
    return GlobVar.vsd_blame;
    
  }



  (* main experiment *)

  proc main(): bool ={

    var dishonest_blamed, pl, pl', i, st, v, b,  s, id, r;

    init();

    GlobVar.pp <@ A.setup();
    (GlobVar.bb, GlobVar.rez, GlobVar.v_sign) <@ A.run();

   (* if A has not provided valid signatures it loses *)
    G.e <- true;
    i  <- 0;
      while (i < card (fdom GlobVar.v_ballots)){
       id <- nth witness (elems (fdom GlobVar.v_ballots)) i;
      (st,v,b) <- oget GlobVar.v_ballots.[id];
       s        <- oget GlobVar.v_sign.[id];
      r <@ S.valid_sig(GlobVar.pp, b, s);
      if (!r) {
        G.e <- false;
      }
      i <- i + 1;
   }

    (* GlobVar.vsd_blame gets updated *)            
    vsd_verify();

    (* adv adds blame from dishonest *)                
    dishonest_blamed <@ A.dishonest_blamed(GlobVar.vsd_blame);

    GlobVar.vsd_blame <- GlobVar.vsd_blame ++ dishonest_blamed;

    (* universal verification *)
    pl <@ S.judge(GlobVar.pp, GlobVar.bb, GlobVar.rez, 
                             GlobVar.vsd_blame);
    (* ground truth *)
    pl'<@ S.bad(GlobVar.pp, GlobVar.bb, GlobVar.rez, GlobVar.v_ballots, 
                GlobVar.vsd_blame);
    

    G.f <- (* Adv wins fairness if judge has blamed an honest party *)
              (exists x, Some x = pl /\ !(x \in pl')) ;

    return G.e /\ G.f;

  }

}. 

(*----------------------------------------*)
(*         Completeness experiment        *)
(*----------------------------------------*)

module Completeness = {
  
  module O = Acc_Oracle(Select(VSD))
  module A = A(O)
  module S = Select(VSD)

  proc init(): unit ={

    GlobVar.vsd_blame   <- [];
    GlobVar.v_ballots   <- empty;

  }

  proc vsd_verify(): vsd_evidence list ={

    var i, st, v, b, s, id,  vsd_evidence;

    i <- 0;
    
    (* verify run by all voters that honestly voted *)
    while (i < card (fdom GlobVar.v_ballots)){
      
      (* get state and ballot for voter id *)
            id <- nth witness (elems (fdom GlobVar.v_ballots)) i;
      (st,v,b) <- oget GlobVar.v_ballots.[id];
      s        <- oget GlobVar.v_sign.[id];

      vsd_evidence <@ S.vsd_verify(GlobVar.pp, st, v, b, s, GlobVar.bb, GlobVar.rez);

      if (vsd_evidence <> None) {
        GlobVar.vsd_blame <- GlobVar.vsd_blame ++ [oget vsd_evidence];
      }

        i <- i + 1;
    }

    (* return all blame evidence *)
    return GlobVar.vsd_blame;
    
  }



  (* main experiment *)

  proc main(): bool ={

    var dishonest_blamed, pl, pl', i, st, v, b,  s, id, r;

    init();

    GlobVar.pp <@ A.setup();
    (GlobVar.bb, GlobVar.rez, GlobVar.v_sign) <@ A.run();

   (* if A has not provided valid signatures it loses *)
    G.e <- true;
    i  <- 0;
      while (i < card (fdom GlobVar.v_ballots)){
       id <- nth witness (elems (fdom GlobVar.v_ballots)) i;
      (st,v,b) <- oget GlobVar.v_ballots.[id];
       s        <- oget GlobVar.v_sign.[id];
      r <@ S.valid_sig(GlobVar.pp, b, s);
      if (!r) {
        G.e <- false;
      }
      i <- i + 1;
   }

    (* GlobVar.vsd_blame gets updated *)            
    vsd_verify();

    (* adv adds blame fom dishonest *)                
    dishonest_blamed <@ A.dishonest_blamed(GlobVar.vsd_blame);

    (* use this order as (+) keeps last map if x \in m2 then m2.[x] else m1.[x] *)
    GlobVar.vsd_blame <- GlobVar.vsd_blame ++ dishonest_blamed;

    (* universal verification *)
    pl <@ S.judge(GlobVar.pp, GlobVar.bb, GlobVar.rez, 
                             GlobVar.vsd_blame);

    (* ground truth *)
    pl'<@ S.bad(GlobVar.pp, GlobVar.bb, GlobVar.rez, GlobVar.v_ballots, 
                GlobVar.vsd_blame);
    

    (* adversary wins when *)
    G.c <- (* no one is blamed and (more ballots or votes were introduced or honest votes were dropped) *)
            (pl = None
            /\ ((* limit on number of ballots *)
                 n_v < (size GlobVar.bb) 
                 \/ (* more votes than ballots *)
                 size GlobVar.bb  < size GlobVar.rez.`1 
                 \/ (* honest votes were dropped *)
                 !((oflist (lex (map (fun x=> (oget GlobVar.v_ballots.[x]).`2) (to_seq (dom GlobVar.v_ballots))))) \subset (oflist GlobVar.rez.`1))
              )
            );

    return G.e /\ G.c;
  }

}. 


(*----------------------------------------*)
(*   Relate accountability and fairness   *)
(*----------------------------------------*)

lemma acc_glob_fair : equiv[Fairness.main ~ Acc_glob.main : ={glob VSD, glob A} ==> res{1} => res{2}]. 
proof. 

proc;inline*. 
by conseq (: _ ==> ={G.e, G.f})=>/>; sim.
qed.   

lemma acc_glob_fair_pr &m : 
    Pr[Fairness.main() @ &m : res] <= Pr[Acc_glob.main() @ &m : res]
by byequiv acc_glob_fair => //.


(*----------------------------------------*)
(* Relate accountability and completeness *)
(*----------------------------------------*)

lemma acc_glob_comp : 
  equiv[Completeness.main 
        ~ Acc_glob.main  
  : ={glob VSD, glob A} ==> res{1} => res{2}]. 
proof. 
proc;inline*. 
by conseq (: _ ==> ={G.e, G.c})=>/>; sim.
qed.   
   

lemma acc_glob_comp_pr &m : Pr[Completeness.main() @ &m : res] <= Pr[Acc_glob.main() @ &m : res]
  by byequiv acc_glob_comp. 

(*----------------------------------------*)
(*      Trivial but helpful lemmas        *)
(*----------------------------------------*)
lemma acc_glob_res &m : Pr[Acc_glob.main() @ &m : res] = Pr[Acc_glob.main() @ &m : (G.e /\ G.f) \/ (G.e /\ G.c)]. 
byequiv (_: ={glob A, glob VSD} ==> _) => //.  
by proc;sim. 
qed. 

lemma fair_glob_res &m : Pr[Fairness.main() @ &m : res] = Pr[Fairness.main() @ &m : (G.e /\ G.f)]. 
proof. 
byequiv (_: ={glob A, glob VSD} ==> _) => //. 
by proc;sim. 
qed. 

lemma comp_glob_res &m : Pr[Completeness.main() @ &m : res] = Pr[Completeness.main() @ &m : (G.e /\ G.c)]. 
proof. 
byequiv (_: ={glob A,glob VSD} ==> _) => //. 
by proc;sim. 
qed. 

(*-----------------------------------------*)
(* Prove that accountability is bounded    *)
(* by the sum of fairness and completeness *)
(* in the accountability experiment        *)
(*-----------------------------------------*)

lemma acc_glob_pr_split &m : 
  Pr[Acc_glob.main() @ &m : (G.e /\ G.f) \/ (G.e /\ G.c)] <=
  Pr[Acc_glob.main() @ &m : (G.e /\ G.f)] + Pr[Acc_glob.main() @ &m : (G.e /\ G.c)]. 
proof. 
rewrite Pr[mu_or]. 
have H : 0%r <= Pr[Acc_glob.main() @ &m : (G.e /\ G.f) /\ G.e /\ G.c] by rewrite Pr[mu_ge0]. 
smt(). 
qed. 

(*----------------------------------------------*)
(* Relate Acc_glob to fairness and completeness *)
(*----------------------------------------------*)

lemma acc_glob_split_fair &m : 
    Pr[Acc_glob.main() @ &m : (G.e /\ G.f)] = Pr[Fairness.main() @ &m : (G.e /\ G.f)]. 
proof. 
byequiv (_: ={glob A, glob VSD} ==> _) => //. 
by proc;sim. 
qed. 

lemma acc_glob_split_comp &m : 
    Pr[Acc_glob.main() @ &m : (G.e /\ G.c)] = Pr[Completeness.main() @ &m : (G.e /\ G.c)]. 
proof. 
byequiv (_: ={glob A,  glob VSD} ==> _) => //. 
by proc;sim. 
qed. 

lemma acc_glob_fair_comp &m : 
  Pr[Acc_glob.main() @ &m : (G.e /\ G.f) \/ (G.e /\ G.c)] <=
  Pr[Fairness.main() @ &m : (G.e /\ G.f)] + Pr[Completeness.main() @ &m : (G.e /\ G.c)]. 
proof.
by rewrite -(acc_glob_split_comp) -(acc_glob_split_fair) (acc_glob_pr_split).
qed. 

(*----------------------------------------*)
(* Bound accountability by sum of         *)
(* fairness and completeness              *)
(*----------------------------------------*)
lemma acc_fair_comp_bound &m : 
    Pr[Acc(Select(VSD),A).main() @ &m : res] <=
    Pr[Fairness.main() @ &m : res] + Pr[Completeness.main() @ &m : res]. 
proof. 
by rewrite acc_glob_equiv_pr acc_glob_res fair_glob_res comp_glob_res acc_glob_fair_comp. 
qed.   


(*----------------------------------------*)
(*          Proof of completeness         *)
(*----------------------------------------*)
lemma completeness &m : Pr[Completeness.main() @ &m : res] = 0%r. 
    byphoare => //. hoare. proc.

    (* For all ids that cast a ballot, we have that *)
    seq 3 : (
     (* alpha2 is an encryption of (n_vot || n_vsd, candidate) *)
    (forall id, id \in GlobVar.v_ballots =>
      (oget GlobVar.v_ballots.[id]).`1.`5 = 
       enc (oget GlobVar.pp.`2.[2]) 
       (Plain ((oget GlobVar.v_ballots.[id]).`1.`1 || (oget GlobVar.v_ballots.[id]).`1.`2, 
       (oget GlobVar.v_ballots.[id]).`2.`2)) (oget GlobVar.v_ballots.[id]).`1.`4) /\

     (* alpha1 is an encryption of alpha2 *)
    (forall id, id \in GlobVar.v_ballots => 
      (oget GlobVar.v_ballots.[id]).`1.`7 = 
        enc (oget GlobVar.pp.`2.[1])
        (Hidden (oget GlobVar.v_ballots.[id]).`1.`5)
        (oget GlobVar.v_ballots.[id]).`1.`6) /\

    (* alpha0 is an encryption of alpha1 *)
    (forall id, id \in GlobVar.v_ballots => 
      (oget GlobVar.v_ballots.[id]).`3 = 
        enc (oget GlobVar.pp.`2.[0])
        (Hidden (oget GlobVar.v_ballots.[id]).`1.`7)
        (oget GlobVar.v_ballots.[id]).`1.`8) /\

    (* voter nonce stored in state is the same as in the submitted ballot *)
    (forall id, id \in GlobVar.v_ballots => 
      (oget GlobVar.v_ballots.[id]).`1.`1 = 
      (oget GlobVar.v_ballots.[id]).`2.`1) /\

    (* candidate stored in state is the same as in the submitted ballot *)
    (forall id, id \in GlobVar.v_ballots => 
      (oget GlobVar.v_ballots.[id]).`1.`3 = 
      (oget GlobVar.v_ballots.[id]).`2.`2)
    ). 

call(_: 
    (* alpha2 is an encryption of (n_vot || n_vsd, candidate) *)
    (forall id, id \in GlobVar.v_ballots =>
      (oget GlobVar.v_ballots.[id]).`1.`5 = 
       enc (oget GlobVar.pp.`2.[2]) 
       (Plain ((oget GlobVar.v_ballots.[id]).`1.`1 || (oget GlobVar.v_ballots.[id]).`1.`2, 
       (oget GlobVar.v_ballots.[id]).`2.`2)) (oget GlobVar.v_ballots.[id]).`1.`4) /\

     (* alpha1 is an encryption of alpha2 *)
    (forall id, id \in GlobVar.v_ballots => 
      (oget GlobVar.v_ballots.[id]).`1.`7 = 
        enc (oget GlobVar.pp.`2.[1])
        (Hidden (oget GlobVar.v_ballots.[id]).`1.`5)
        (oget GlobVar.v_ballots.[id]).`1.`6) /\

    (* alpha0 is an encryption of alpha1 *)
    (forall id, id \in GlobVar.v_ballots => 
      (oget GlobVar.v_ballots.[id]).`3 = 
        enc (oget GlobVar.pp.`2.[0])
        (Hidden (oget GlobVar.v_ballots.[id]).`1.`7)
        (oget GlobVar.v_ballots.[id]).`1.`8) /\

    (* voter nonce stored in state is the same as in the submitted ballot *)
    (forall id, id \in GlobVar.v_ballots => 
      (oget GlobVar.v_ballots.[id]).`1.`1 = 
      (oget GlobVar.v_ballots.[id]).`2.`1) /\

    (* candidate stored in state is the same as in the submitted ballot *)
    (forall id, id \in GlobVar.v_ballots => 
      (oget GlobVar.v_ballots.[id]).`1.`3 = 
      (oget GlobVar.v_ballots.[id]).`2.`2)
).

  proc. inline*. auto => />. call(_:true). auto => />;progress. rewrite !get_setE. 
  case (id1 = id{hr}) => id_eq. done. rewrite H. rewrite /dom get_setE in H7. 
  move: H7 => H7. rewrite id_eq //= in H7. done. 
  rewrite !get_setE. 
  case (id1 = id{hr}) => id_eq. done. rewrite H0. rewrite /dom get_setE in H7. 
  move: H7 => H7. rewrite id_eq //= in H7. done. 
  rewrite !get_setE. 
  case (id1 = id{hr}) => id_eq. done. rewrite H1. rewrite /dom get_setE in H7. 
  move: H7 => H7. rewrite id_eq //= in H7. done. 
  rewrite !get_setE. 
  case (id1 = id{hr}) => id_eq. done. rewrite H2. rewrite /dom get_setE in H7. 
  move: H7 => H7. rewrite id_eq //= in H7. done. 
  rewrite !get_setE. 
  case (id1 = id{hr}) => id_eq. done. rewrite H3. rewrite /dom get_setE in H7. 
  move: H7 => H7. rewrite id_eq //= in H7. done. 

  inline*. call(_:true). auto => />;progress;[1..5:by rewrite mem_empty in H]. 

    case (! (n_v < size GlobVar.bb \/ size GlobVar.bb < size GlobVar.rez.`1 \/ 
    !(oflist (lex (map (fun x=> (oget GlobVar.v_ballots.[x]).`2) 
          (to_seq (dom GlobVar.v_ballots)))) \subset (oflist GlobVar.rez.`1)))).

   wp. call(_:true); 1: by auto. 
    call(_:true); 1: by auto. 
    wp. call(_:true). 
    call(_:true); 1: by while true;auto. 
    while true;auto. progress. 
  
  rewrite negb_and. right. 
  rewrite negb_and. by right.

    rewrite //=.

    case (!(GlobVar.pp.`2.[0] <> None /\ is_valid_pkey (oget GlobVar.pp.`2.[0])
          /\ GlobVar.pp.`2.[1] <> None /\ is_valid_pkey (oget GlobVar.pp.`2.[1])
          /\ GlobVar.pp.`2.[2] <> None /\ is_valid_pkey (oget GlobVar.pp.`2.[2]))). 
 
    seq 7 : (pl <> None). inline*. 
    rcondt 23. auto => />. call(_:true).  while #pre. auto => />. auto => />. 
    while #pre. inline*. auto => />. auto => />. 
    auto => />. call(_:true). while #pre. inline*;auto => />. auto => />. 
    while #pre. inline*;1:auto => />. auto => />. 
    by auto => />. 

    case (n_v < size GlobVar.bb). 
    seq 7 : (#pre /\ pl <> None).  
    inline*.
    rcondf 23. wp. call(_:true). while #pre. auto => />. wp. while #pre. auto => />. auto => />.  
    seq 26 : (#pre /\ blame <> None). auto => />. call(_:true). 
    while #pre. auto => />. wp. while #pre. auto => />. 
    auto => />.  progress. rewrite negb_and. rewrite -ltzNge. by left.  
    auto => />. 
    wp. while #pre. auto => />. wp. while #pre. auto => />. auto => />.  
    by auto => />.  

    case (size GlobVar.bb < size GlobVar.rez.`1). 
    seq 7 : (#pre /\ pl <> None). inline*. 
    rcondf 23. wp. call(_:true). while #pre. auto => />. wp. while #pre. auto => />. auto => />.
    seq 29 : (#pre /\ blame <> None). auto => />;1:smt().  
    call(_:true). while #pre. auto => />. wp. while #pre. auto => />. 
    auto => />. smt().  
     wp. while #pre. auto => />. wp;while #pre. auto => />. auto => />. 
    by auto => />.     

    (* Now we get to the interesting case *)
    (*----------------------------------------*)    
    (*   First we rework the precondition     *)
    (*----------------------------------------*)

    (* There must be an honest voter who's ballots is not part of the result *)
    seq 0 : (#pre /\ (exists id, id \in GlobVar.v_ballots /\
                      (oget GlobVar.v_ballots.[id]).`2 \notin GlobVar.rez.`1)).
    + auto => /> &0 h0 h1 h2 h3 h4 [-> //|[-> //|]].
      rewrite /(\subset) negb_forall=> /= - [] [] n_v c_v.
      rewrite negb_imply=> />.
      rewrite mem_oflist mem_sort mapP=> - [] id />.
      by rewrite mem_oflist mem_to_seq 1:finite_dom /#.
    seq 0 : (#pre /\ exists id, id \in GlobVar.v_ballots{hr} /\ 
             !( (oget GlobVar.v_ballots{hr}.[id]).`2.`1 || (oget GlobVar.v_ballots{hr}.[id]).`1.`2, (oget GlobVar.v_ballots{hr}.[id]).`2.`2) \in 
                map (fun (x:(nonce*candidate)*nonce), (x.`1.`1 || x.`2, x.`1.`2)) (zip GlobVar.rez{hr}.`1 GlobVar.rez{hr}.`2.`1)).
    auto => />. progress. 
     exists id0. split=> //.
      have : injective (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2)).
      move => x y H15. elim H15 => H15 H16. apply concat_inj in H15. elim H15. smt().
     move => H15. have : forall s x, ! (mem (map (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2)) s) 
        ((fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2)) x)) <=> 
          ! (mem s x). move => s0 x. rewrite mem_map. trivial. done. move => H16.
        have :  ! ((fun (x0 : (nonce * candidate) * nonce) =>
   (x0.`1.`1 || x0.`2, x0.`1.`2)) ((oget GlobVar.v_ballots{hr}.[id0]).`2,(oget GlobVar.v_ballots{hr}.[id0]).`1.`2) \in
          map
            (fun (x0 : (nonce * candidate) * nonce) =>
               (x0.`1.`1 || x0.`2, x0.`1.`2)) (zip GlobVar.rez{hr}.`1 GlobVar.rez{hr}.`2.`1)) <=>
       ! ( ((oget GlobVar.v_ballots{hr}.[id0]).`2,(oget GlobVar.v_ballots{hr}.[id0]).`1.`2) \in  
             (zip GlobVar.rez{hr}.`1 GlobVar.rez{hr}.`2.`1)). smt(). move => H17. smt(mem_zip).
    
(* The validation of signatures doesn't matter *)
    inline Completeness.S.valid_sig. 
    seq 3 : (#pre /\
          (forall i, 0 <= i < card (fdom GlobVar.v_ballots) =>
        let id = nth witness (elems (fdom GlobVar.v_ballots)) i in
        (verify GlobVar.pp.`1 (oget GlobVar.v_ballots.[id]).`3)
        (oget GlobVar.v_sign.[id])) \/ !G.e         
     ).

  while (forall j, 0 <= j < i => let id = nth witness (elems (fdom GlobVar.v_ballots)) j in
   (verify GlobVar.pp.`1 (oget GlobVar.v_ballots.[id]).`3) (oget GlobVar.v_sign.[id]) \/ !G.e). 
  auto => />. progress. case (j = i{hr}) => h1.  smt().  
  have :  0 <= j && j < i{hr}. smt(). smt(). auto => />. 
  progress. rewrite ltzNge in H18. rewrite H17 in H18. done.
  smt().    

  (* If any signature is invalid, the adversary loses *)
  case (!G.e).
  wp. 
  call(_:true); 1:auto. 
  call(_:true); 1:auto. 
  wp. call(_:true).  
  call(_:true). 
  while true. auto => />. auto => />. 
  auto => />. auto => />.  

  case (size GlobVar.rez.`1 <> size GlobVar.rez.`2.`1). inline*. 
  rcondf 20. wp. call(_:true). while #pre. auto => />. auto => />. smt().  
  seq 35 : (#pre /\ pl <> None).
  seq 14 : (#pre /\ nL = GlobVar.rez.`2.`1 /\ outcome = GlobVar.rez.`1). auto => />. 
  auto => />. 
  seq 13 : (#pre /\ blame = Some (MixServer 2)).
  rcondt 13. auto => />.  progress. by rewrite eq_sym. 
  seq 12 : #pre. auto => />. auto => />. wp. 

  (* Seq forward and remember that someone misbehaved *)
  seq 3 : (
    ((((((((((((forall (id1 : ident),
                id1 \in GlobVar.v_ballots =>
                (oget GlobVar.v_ballots.[id1]).`1.`5 =
                enc (oget GlobVar.pp.`2.[2])
                  (Plain
                     ((oget GlobVar.v_ballots.[id1]).`1.`1 ||
                      (oget GlobVar.v_ballots.[id1]).`1.`2,
                      (oget GlobVar.v_ballots.[id1]).`2.`2))
                  (oget GlobVar.v_ballots.[id1]).`1.`4) /\
             (forall (id1 : ident),
                id1 \in GlobVar.v_ballots =>
                (oget GlobVar.v_ballots.[id1]).`1.`7 =
                enc (oget GlobVar.pp.`2.[1])
                  (Hidden (oget GlobVar.v_ballots.[id1]).`1.`5)
                  (oget GlobVar.v_ballots.[id1]).`1.`6) /\
             (forall (id1 : ident),
                id1 \in GlobVar.v_ballots =>
                (oget GlobVar.v_ballots.[id1]).`3 =
                enc (oget GlobVar.pp.`2.[0])
                  (Hidden (oget GlobVar.v_ballots.[id1]).`1.`7)
                  (oget GlobVar.v_ballots.[id1]).`1.`8) /\
             (forall (id1 : ident),
                id1 \in GlobVar.v_ballots =>
                (oget GlobVar.v_ballots.[id1]).`1.`1 =
                (oget GlobVar.v_ballots.[id1]).`2.`1) /\
             forall (id1 : ident),
               id1 \in GlobVar.v_ballots =>
               (oget GlobVar.v_ballots.[id1]).`1.`3 =
               (oget GlobVar.v_ballots.[id1]).`2.`2) /\
            (n_v < size GlobVar.bb \/
             size GlobVar.bb < size GlobVar.rez.`1 \/
             ! (oflist
                  (lex
                     (map
                        (fun x=> (oget GlobVar.v_ballots.[x]).`2)
                        (to_seq (dom GlobVar.v_ballots)))) \subset
                oflist GlobVar.rez.`1))) /\
           GlobVar.pp.`2.[0] <> None /\
           is_valid_pkey (oget GlobVar.pp.`2.[0]) /\
           GlobVar.pp.`2.[1] <> None /\
           is_valid_pkey (oget GlobVar.pp.`2.[1]) /\
           GlobVar.pp.`2.[2] <> None /\
           is_valid_pkey (oget GlobVar.pp.`2.[2])) /\
          ! n_v < size GlobVar.bb) /\
         ! size GlobVar.bb < size GlobVar.rez.`1) /\
        exists (id1 : ident),
          (id1 \in GlobVar.v_ballots) /\
          ((oget GlobVar.v_ballots.[id1]).`2 \notin GlobVar.rez.`1)) /\
       exists (id1 : ident),
         (id1 \in GlobVar.v_ballots) /\
         ! (((oget GlobVar.v_ballots.[id1]).`2.`1 ||
             (oget GlobVar.v_ballots.[id1]).`1.`2,
             (oget GlobVar.v_ballots.[id1]).`2.`2) \in
            map
              (fun (x : (nonce * candidate) * nonce) =>
                 (x.`1.`1 || x.`2, x.`1.`2))
              (zip GlobVar.rez.`1 GlobVar.rez.`2.`1))) /\
      forall (i8 : int),
        0 <= i8 && i8 < card (fdom GlobVar.v_ballots) =>
        verify GlobVar.pp.`1
          (oget
             GlobVar.v_ballots.[nth witness (elems (fdom GlobVar.v_ballots))
                                  i8]).`3
          (oget
             GlobVar.v_sign.[nth witness (elems (fdom GlobVar.v_ballots)) i8]) \/
      !G.e) /\
     G.e) /\
    size GlobVar.rez.`1 <> size GlobVar.rez.`2.`1) /\
   nL = GlobVar.rez.`2.`1 /\ outcome = GlobVar.rez.`1) /\
  (blame = Some (MixServer 2) \/ blame = Some (MixServer 1) \/ blame = Some (MixServer 0))
  ).

   auto => />; 1: smt().  
   
  seq 2 : (
    ((((((((((((forall (id1 : ident),
                id1 \in GlobVar.v_ballots =>
                (oget GlobVar.v_ballots.[id1]).`1.`5 =
                enc (oget GlobVar.pp.`2.[2])
                  (Plain
                     ((oget GlobVar.v_ballots.[id1]).`1.`1 ||
                      (oget GlobVar.v_ballots.[id1]).`1.`2,
                      (oget GlobVar.v_ballots.[id1]).`2.`2))
                  (oget GlobVar.v_ballots.[id1]).`1.`4) /\
             (forall (id1 : ident),
                id1 \in GlobVar.v_ballots =>
                (oget GlobVar.v_ballots.[id1]).`1.`7 =
                enc (oget GlobVar.pp.`2.[1])
                  (Hidden (oget GlobVar.v_ballots.[id1]).`1.`5)
                  (oget GlobVar.v_ballots.[id1]).`1.`6) /\
             (forall (id1 : ident),
                id1 \in GlobVar.v_ballots =>
                (oget GlobVar.v_ballots.[id1]).`3 =
                enc (oget GlobVar.pp.`2.[0])
                  (Hidden (oget GlobVar.v_ballots.[id1]).`1.`7)
                  (oget GlobVar.v_ballots.[id1]).`1.`8) /\
             (forall (id1 : ident),
                id1 \in GlobVar.v_ballots =>
                (oget GlobVar.v_ballots.[id1]).`1.`1 =
                (oget GlobVar.v_ballots.[id1]).`2.`1) /\
             forall (id1 : ident),
               id1 \in GlobVar.v_ballots =>
               (oget GlobVar.v_ballots.[id1]).`1.`3 =
               (oget GlobVar.v_ballots.[id1]).`2.`2) /\
            (n_v < size GlobVar.bb \/
             size GlobVar.bb < size GlobVar.rez.`1 \/
             ! (oflist
                  (lex
                     (map
                        (fun x=> (oget GlobVar.v_ballots.[x]).`2)
                        (to_seq (dom GlobVar.v_ballots)))) \subset
                oflist GlobVar.rez.`1))) /\
           GlobVar.pp.`2.[0] <> None /\
           is_valid_pkey (oget GlobVar.pp.`2.[0]) /\
           GlobVar.pp.`2.[1] <> None /\
           is_valid_pkey (oget GlobVar.pp.`2.[1]) /\
           GlobVar.pp.`2.[2] <> None /\
           is_valid_pkey (oget GlobVar.pp.`2.[2])) /\
          ! n_v < size GlobVar.bb) /\
         ! size GlobVar.bb < size GlobVar.rez.`1) /\
        exists (id1 : ident),
          (id1 \in GlobVar.v_ballots) /\
          ((oget GlobVar.v_ballots.[id1]).`2 \notin GlobVar.rez.`1)) /\
       exists (id1 : ident),
         (id1 \in GlobVar.v_ballots) /\
         ! (((oget GlobVar.v_ballots.[id1]).`2.`1 ||
             (oget GlobVar.v_ballots.[id1]).`1.`2,
             (oget GlobVar.v_ballots.[id1]).`2.`2) \in
            map
              (fun (x : (nonce * candidate) * nonce) =>
                 (x.`1.`1 || x.`2, x.`1.`2))
              (zip GlobVar.rez.`1 GlobVar.rez.`2.`1))) /\
      forall (i8 : int),
        0 <= i8 && i8 < card (fdom GlobVar.v_ballots) =>
        verify GlobVar.pp.`1
          (oget
             GlobVar.v_ballots.[nth witness (elems (fdom GlobVar.v_ballots))
                                  i8]).`3
          (oget
             GlobVar.v_sign.[nth witness (elems (fdom GlobVar.v_ballots)) i8]) \/
        !G.e) /\
     G.e) /\
    size GlobVar.rez.`1 <> size GlobVar.rez.`2.`1) /\
   nL = GlobVar.rez.`2.`1 /\ outcome = GlobVar.rez.`1) /\
  (blame = Some (MixServer 2) \/
   blame = Some (MixServer 1) \/ blame = Some (MixServer 0) \/ blame = Some AuthServer)
  ).

  while (blame = Some (MixServer 2) \/
   blame = Some (MixServer 1) \/ blame = Some (MixServer 0) \/ blame = Some AuthServer). 
  auto => />.  auto => />. progress. elim H20 => H20. rewrite H20. by left. 
  elim H20 => H20;  1:rewrite H20.   done.  rewrite H20.  done.   

  while (blame = Some (MixServer 2) \/
   blame = Some (MixServer 1) \/ blame = Some (MixServer 0) \/ blame = Some AuthServer). 
  auto => />. auto => />. progress. smt(). smt(). 
 
  auto => />. while #pre. auto => />.  

  rcondt 24. auto => />. 
  rcondt 34. auto. while #pre. auto => />. auto => />. 
  rcondt 44. auto. while #pre. auto => />. auto => />. 
  while #pre. auto => />. auto => />. 
  
  wp. while #pre. auto => />. 
  auto. while #pre. auto => />. auto. 
  while #pre. auto => />. by auto => />.  

   (*----------------------------------------------------------*)
   (* Someone complained - presumably the voter who got droped *)
   (*----------------------------------------------------------*)
   inline Completeness.vsd_verify Completeness.S.vsd_verify. 
    seq 2 : ((exists i, 0<= i < size GlobVar.vsd_blame /\
      let (vote, sign) = to_AS_evidence (nth witness GlobVar.vsd_blame i).`2 in
      verify GlobVar.pp.`1 vote sign /\ (vote \notin GlobVar.bb))
       \/ (exists i,  0<= i < size GlobVar.vsd_blame /\
        (enc (oget GlobVar.pp.`2.[0]) (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
          (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in  GlobVar.bb) /\
           (nth witness GlobVar.vsd_blame i).`1 = MixServer 0 /\
        (oget (bit_to_cip (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) \notin GlobVar.rez.`2.`2))
        \/ (exists i,  0<= i < size GlobVar.vsd_blame /\
        let (ciph, rand) = to_MS_evidence (nth witness GlobVar.vsd_blame i).`2 in
          (nth witness GlobVar.vsd_blame i).`1 = MixServer 1 /\
     (enc (oget  GlobVar.pp.`2.[1]) ciph rand \in GlobVar.rez.`2.`2) /\ (oget (bit_to_cip ciph) \notin GlobVar.rez.`2.`3))
       \/ (exists i,  0<= i < size GlobVar.vsd_blame /\
     let (ciph, rand) = to_MS_evidence (nth witness GlobVar.vsd_blame i).`2 in
        (nth witness GlobVar.vsd_blame i).`1 = MixServer 2 /\
     (enc (oget GlobVar.pp.`2.[2]) ciph rand \in GlobVar.rez.`2.`3) /\ 
      oget (bit_to_nc ciph) \notin map (fun (x:(nonce*candidate)*nonce), 
       (x.`1.`1 || x.`2, x.`1.`2)) (zip GlobVar.rez.`1 GlobVar.rez.`2.`1))).

       (* Why does the voter want to complain? *)
       while (#pre /\ 
   ((find (fun id  =>
       ( (oget GlobVar.v_ballots.[id]).`2.`1 || (oget GlobVar.v_ballots.[id]).`1.`2, (oget GlobVar.v_ballots.[id]).`2.`2)
           \notin map (fun (x:(nonce*candidate)*nonce), (x.`1.`1 || x.`2, x.`1.`2)) (zip GlobVar.rez.`1 GlobVar.rez.`2.`1)) 
         (elems (fdom (GlobVar.v_ballots)))) < i0 =>
       (exists i,  0<= i < size GlobVar.vsd_blame /\
    let (vote, sign) = to_AS_evidence (nth witness GlobVar.vsd_blame i).`2 in
      verify GlobVar.pp.`1 vote sign /\ (vote \notin GlobVar.bb))
          \/ (exists i,  0<= i < size GlobVar.vsd_blame /\
        (enc (oget GlobVar.pp.`2.[0]) (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
          (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in  GlobVar.bb) /\
           (nth witness GlobVar.vsd_blame i).`1 = MixServer 0 /\
        (oget (bit_to_cip (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) \notin GlobVar.rez.`2.`2))
        \/ (exists i,  0<= i < size GlobVar.vsd_blame /\
        let (ciph, rand) = to_MS_evidence (nth witness GlobVar.vsd_blame i).`2 in
          (nth witness GlobVar.vsd_blame i).`1 = MixServer 1 /\
     (enc (oget  GlobVar.pp.`2.[1]) ciph rand \in GlobVar.rez.`2.`2) /\ (oget (bit_to_cip ciph) \notin GlobVar.rez.`2.`3))
       \/ (exists i,  0<= i < size GlobVar.vsd_blame /\
     let (ciph, rand) = to_MS_evidence (nth witness GlobVar.vsd_blame i).`2 in
        (nth witness GlobVar.vsd_blame i).`1 = MixServer 2 /\
        (enc (oget GlobVar.pp.`2.[2]) ciph rand \in GlobVar.rez.`2.`3) /\ 
        oget (bit_to_nc ciph) \notin map (fun (x:(nonce*candidate)*nonce), 
          (x.`1.`1 || x.`2, x.`1.`2)) (zip GlobVar.rez.`1 GlobVar.rez.`2.`1)))).
          auto => />. progress.

       (* We now start dealing with the cases where different parties were blamed *) 
          smt(). smt(). smt(). smt(). smt().

          (* first of the hard cases - We have just added evidence blaming MS 0 *)
          right. left. exists (size (GlobVar.vsd_blame{hr})). split. rewrite size_cat.  
          rewrite size_ge0 //=. rewrite ltzS lezz. split. rewrite nth_cat. simplify.
          rewrite MS_evidence. simplify. elim H => H. 
          elim H => h1 h2. elim h1 => h1 h3. elim h1 => h1 h4.
          elim h1 => h1 h5. elim h1 => h1 h6. elim h1 => h1 h7. elim h1 => h1 h8.  
          elim h1 => h1 h9. 
          elim h9 => h9 h10. elim h10 => h10 h11. elim h11 => h11 h12.  
          have : nth witness (elems (fdom GlobVar.v_ballots{hr})) i0{hr} \in  GlobVar.v_ballots{hr}.  smt(@SmtMap @List).
          move => a. apply h10 in a.  smt(@List). smt(). rewrite nth_cat. simplify. rewrite MS_evidence. smt().

          (* second of the hard cases - Whe have just added evidence blaming AS *)
          left. exists (size (GlobVar.vsd_blame{hr})). split. rewrite size_cat. 
          rewrite size_ge0 //=. smt(). rewrite nth_cat. simplify.
          rewrite AS_evidence. simplify. split. elim H => H. elim H => h1 h2. apply h2.   
          rewrite H3. smt(@List). smt(). smt(). 

          (* third of hard cases - We have just added evidence blamming MS 2 *)
          right. right. right.  exists (size (GlobVar.vsd_blame{hr})). 
          split. rewrite size_cat. rewrite size_ge0 //=. smt(). 
          rewrite nth_cat. simplify.
          rewrite MS_evidence. simplify. split. elim H => H. 
          elim H => h1 h2. elim h1 => h1 h3. elim h1 => h1 h4.
          elim h1 => h1 h5. elim h1 => h1 h6. elim h1 => h1 h7. 
          elim h1 => h1 h8. elim h1 => h1 h9. elim h9 => h9 h10. elim h10 => h10 h11. elim h11 => h11 h12.  
          have : nth witness (elems (fdom GlobVar.v_ballots{hr})) i0{hr} \in  GlobVar.v_ballots{hr}. smt(@SmtMap @List).
          move => a. apply h1 in a. smt(). smt(). smt(mem_zip). 

          (* a couple more easy cases *)
          smt(). smt().

          (* fourth of hard cases - Whe have just added evidence blaming AS  *)
          left. exists (size (GlobVar.vsd_blame{hr})). split. 
          rewrite size_cat size_ge0 //=. smt(). rewrite nth_cat. simplify.
          rewrite AS_evidence. simplify. split. 
          elim H => H. elim H => h1 h2. apply h2. rewrite H3 //=.  
          smt(@List). smt(). smt(). 

          (* fifth of hard cases  - We have just added evidence blamming MS 1 *)
          right. right. left. exists (size (GlobVar.vsd_blame{hr})). 
          split. rewrite size_cat size_ge0 //=. smt(). 
          rewrite nth_cat. simplify.
          rewrite MS_evidence. simplify. split.  elim H => H. 
          elim H => h1 h2. elim h1 => h1 h3. elim h1 => h1 h4.
          elim h1 => h1 h5. elim h1 => h1 h6. elim h1 => h1 h7. 
          elim h1 => h1 h8. elim h1 => h1 h9. elim h9 => h9 h10. elim h10 => h10 h11. elim h11 => h11 h12. 
          have : nth witness (elems (fdom GlobVar.v_ballots{hr})) i0{hr} \in  GlobVar.v_ballots{hr}. smt(@SmtMap @List).
          move => a. apply h9 in a. smt(). smt(). smt().

          (* sixth of hard cases  - Whe have just added evidence blaming AS *)
          left. exists (size (GlobVar.vsd_blame{hr})). split. 
          rewrite size_cat size_ge0 //=. smt(). rewrite nth_cat. simplify.
          rewrite AS_evidence. simplify. split. elim H => H. 
          elim H => h1 h2. apply h2. rewrite H3. smt(@List). 
          smt(). smt(). 

          (* seventh of hard cases - We have just added evidence blaming MS 0 *)
          right. left. exists (size (GlobVar.vsd_blame{hr})). split. 
          rewrite size_cat size_ge0 //=. smt(). 
          split. rewrite nth_cat. simplify.
          rewrite MS_evidence. simplify. elim H => H. elim H => h1 h2. 
          elim h1 => h1 h3. elim h1 => h1 h4.
          elim h1 => h1 h5. elim h1 => h1 h6. elim h1 => h1 h7. 
          elim h1 => h1 h8. elim h1 => h1 h9. elim h8 => h10. smt(). 
          elim h10 => h10. smt(). elim h9 => h9 h11. elim h11 => h11 h12. elim h12 => h12 h13. 
          have : nth witness (elems (fdom GlobVar.v_ballots{hr})) i0{hr} \in  GlobVar.v_ballots{hr}. smt(@SmtMap @List).
          move => a. apply h11 in a. smt(). smt().   
          rewrite nth_cat.  simplify. rewrite MS_evidence. simplify. smt().

          (* eight of hard cases  - Whe have just added evidence blaming AS *)
          left. exists (size (GlobVar.vsd_blame{hr})). split. 
          rewrite size_cat size_ge0 //=. smt(). rewrite nth_cat. simplify.
          rewrite AS_evidence. simplify. split. elim H => H. 
          elim H => h1 h2. apply h2. rewrite H3. smt(@List). 
          smt(). smt(). 

          (*ninth of hard cases - we didn't blame anyone *)
          case (find  (fun (id1 : ident) =>  
          ( (oget GlobVar.v_ballots{hr}.[id1]).`2.`1 || (oget GlobVar.v_ballots{hr}.[id1]).`1.`2, (oget GlobVar.v_ballots{hr}.[id1]).`2.`2) 
            \notin map (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2))
          (zip GlobVar.rez{hr}.`1 GlobVar.rez{hr}.`2.`1))
          (elems (fdom GlobVar.v_ballots{hr}))=  i0{hr}) => h1. rewrite negb_and in H4. rewrite negb_and in H5.
          rewrite negb_and in H6. elim H6 => h2. smt(). elim H5 => h3. smt(). elim H4 => h4. smt(). clear h3 h2 H8.
          have : 
           ( (oget GlobVar.v_ballots{hr}.[nth witness (elems (fdom GlobVar.v_ballots{hr})) i0{hr}]).`2.`1 ||
             (oget GlobVar.v_ballots{hr}.[nth witness (elems (fdom GlobVar.v_ballots{hr})) i0{hr}]).`1.`2, 
             (oget GlobVar.v_ballots{hr}.[nth witness (elems (fdom GlobVar.v_ballots{hr})) i0{hr}]).`2.`2)
           \notin map (fun (x:(nonce*candidate)*nonce), (x.`1.`1 || x.`2, x.`1.`2)) (zip GlobVar.rez{hr}.`1 GlobVar.rez{hr}.`2.`1).    
          smt(@List). move => h3. left. exists i0{hr}. smt(@List @SmtMap). 

      have : find  (fun (id1 : ident) =>
         ( (oget GlobVar.v_ballots{hr}.[id1]).`2.`1 || (oget GlobVar.v_ballots{hr}.[id1]).`1.`2, (oget GlobVar.v_ballots{hr}.[id1]).`2.`2) 
            \notin  map (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2))
      (zip GlobVar.rez{hr}.`1 GlobVar.rez{hr}.`2.`1)) 
      (elems (fdom GlobVar.v_ballots{hr})) <  i0{hr}. smt(). move => h2. apply H2 in h2. apply h2.
       
       (* Clean up after while loop *)
          auto. progress. left. exists i0{hr}.  smt(@List). 
          apply H6.  elim H => h1. elim h1 => h1 h2. elim h1 => h1 h3. elim h3 => h3 h4.
          elim h1 => h1 h5. elim h1 => h1 h6. elim h1 => h1 h7. elim h1 => h1 h8. elim h1 => h1 h9. 
         elim h1 => h1 h10. elim h10 => h10 h11. elim h11 => h11 h12. elim h12 => h12 h13. 
         elim h9 => h9. smt(). elim h9 => h9. smt().  
          have : find (fun (id1 : ident) =>
           ( (oget GlobVar.v_ballots{hr}.[id1]).`2.`1 || (oget GlobVar.v_ballots{hr}.[id1]).`1.`2, 
             (oget GlobVar.v_ballots{hr}.[id1]).`2.`2)
             \notin map (fun (x:(nonce*candidate)*nonce), (x.`1.`1 || x.`2, x.`1.`2)) (zip GlobVar.rez{hr}.`1 GlobVar.rez{hr}.`2.`1))
           (elems (fdom GlobVar.v_ballots{hr})) <
           size (elems (fdom GlobVar.v_ballots{hr})). apply has_find. apply hasP. exists h3. simplify.  
          elim h4 => h4 h. split; last by smt(). rewrite -mem_fdom in h4.  smt(mem_oflist). smt(). smt().  

 
     (*What the adversary adds to blame doesn't matter *)
       seq 2 : #pre. auto. call(_:true). progress. auto. progress. elim H => H. left. elim H => h1 h2. exists h1.
       split. rewrite size_cat //=.  smt(size_ge0). 
       elim h2 => h2 h3. rewrite nth_cat. elim h2 => h2 h4. rewrite h4. simplify. done.   
       elim H => H. right. left. elim H => h1 h2. exists h1. 
       split. rewrite size_cat. smt(size_ge0). 
       elim h2 => h2 h3. rewrite nth_cat. elim h2 => h2 h4. rewrite h4. simplify. done. 
       elim H => H. right. right. left.  elim H => h1 h2. exists h1. 
       split. rewrite size_cat. smt(size_ge0). 
       rewrite nth_cat. elim h2 => h2 h3. elim h2 => h2 h4. rewrite h4. simplify. done. 
       right. right. right.
       elim H => h1 h2. exists h1. 
       split. rewrite size_cat. smt(size_ge0). 
       rewrite nth_cat. elim h2 => h2 h3. elim h2 => h2 h4. rewrite h4.
       simplify. done. 

     (*----------------------------------------*)
     (*     We hold someone accountable        *)
     (*----------------------------------------*)
       seq 1 : (pl <> None).
       inline *. 

        case (!(GlobVar.pp.`2.[0] <> None /\ is_valid_pkey (oget GlobVar.pp.`2.[0])
          /\ GlobVar.pp.`2.[1] <> None /\ is_valid_pkey (oget GlobVar.pp.`2.[1])
          /\ GlobVar.pp.`2.[2] <> None /\ is_valid_pkey (oget GlobVar.pp.`2.[2]))). 
       rcondt 16. auto => />. auto => />.

       rcondf 16. auto => />. 
       
       seq 26 : (#pre /\ ve = GlobVar.vsd_blame /\ pd0 = GlobVar.pp /\ bb0 = GlobVar.bb /\
       m1_out = GlobVar.rez.`2.`2 /\ m2_out = GlobVar.rez.`2.`3 /\ outcome = GlobVar.rez.`1 /\ nL0 = GlobVar.rez.`2.`1 /\
       fL0 = map (fun (x:(nonce*candidate)*nonce), (x.`1.`1 || x.`2, x.`1.`2)) (zip outcome nL0)).
       auto => />. auto.  
       seq 2 : (#pre /\ (forall (i : int),
     (0 <= i && i < size GlobVar.vsd_blame) /\
       verify GlobVar.pp.`1 (to_AS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
     (to_AS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 /\
     (to_AS_evidence (nth witness GlobVar.vsd_blame i).`2).`1 \notin GlobVar.bb => blame <> None)).
     while(#pre  /\ (forall (i : int),
     ((0 <= i && i < size GlobVar.vsd_blame) /\
       verify GlobVar.pp.`1  (to_AS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
       (to_AS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 /\
       (to_AS_evidence (nth witness GlobVar.vsd_blame i).`2).`1 \notin GlobVar.bb) => blame <> None \/ i1 <= i)).
       auto.  progress. case (i1{hr} = i3) => h2. rewrite negb_and in H8. elim H8 => H8. smt(). 
       have : ((to_AS_evidence (nth witness GlobVar.vsd_blame{hr} i3).`2).`1 \notin GlobVar.bb{hr}). smt(). smt().
       smt().  auto. progress. smt(). smt(). 
 
       seq 2 : (blame <> None).
       while ( #pre /\ 0 <= i1 /\ (forall (i : int),
       (0 <= i && i < size GlobVar.vsd_blame) /\
       ((let (vote0, sign) =
         to_AS_evidence (nth witness GlobVar.vsd_blame i).`2 in
       verify GlobVar.pp.`1 vote0 sign /\ (vote0 \notin GlobVar.bb)) \/
       ((enc (oget GlobVar.pp.`2.[0])
          (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
          (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in
            GlobVar.bb) /\
         (nth witness GlobVar.vsd_blame i).`1 = MixServer 0 /\
       (oget
          (bit_to_cip
             (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) \notin
        GlobVar.rez.`2.`2)) \/
       ((nth witness GlobVar.vsd_blame i).`1 = MixServer 1 /\
         (enc (oget GlobVar.pp.`2.[1]) (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
           (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in GlobVar.rez.`2.`2) /\
       (oget (bit_to_cip (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) \notin GlobVar.rez.`2.`3)) \/
      ((nth witness GlobVar.vsd_blame i).`1 = MixServer 2 /\
        (enc (oget GlobVar.pp.`2.[2]) (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
          (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in GlobVar.rez.`2.`3) /\
        (oget (bit_to_nc (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) \notin 
        map (fun (x:(nonce*candidate)*nonce), (x.`1.`1 || x.`2, x.`1.`2)) (zip GlobVar.rez.`1 GlobVar.rez.`2.`1))))
    => blame <> None \/ i1 <= i)). auto => />. smt(). 
        auto => />. smt(). by auto.
  
     (* And we are done *) 

    auto => />. 

    trivial. 

    qed.       


(*----------------------------------------*)
(*           Proof of fairness            *)
(*----------------------------------------*)
lemma fairness &m : Pr[Fairness.main() @ &m : res] = 0%r. 
proof. 
  byphoare => //. 
  hoare; proc; inline Fairness.S.is_valid; seq 3 : true; 1: by auto.

  (* Case on the public keys being valid *)
  case (GlobVar.pp.`2.[0] <> None /\                                               
  is_valid_pkey (oget  GlobVar.pp.`2.[0]) /\                                   
   GlobVar.pp.`2.[1] <> None /\                                               
   is_valid_pkey (oget GlobVar.pp.`2.[1]) /\                                   
   GlobVar.pp.`2.[2] <>  None /\                                               
   is_valid_pkey (oget GlobVar.pp.`2.[2])); last first.

   inline*. wp 81. rcondt 23. auto => />. call(_:true). while #pre. auto => />. wp. while #pre. auto => />. auto => />. 
 
   (* Since the keys are invalid, we blame the VA *)
   seq 24 : (#pre /\ pl = Some VotingAuthority). auto => />. call(_:true). 
   wp. while #pre. auto => />. auto => />. done.   

   seq 16 : (pl = Some VotingAuthority /\ VotingAuthority \in pl0). auto => />. by rewrite in_fsetU in_fset1. 

  wp. while #pre. auto => />. by rewrite in_fsetU in_fset1.   
  rcondt 8;1:auto.   
  rcondt 18. wp. while #pre. auto => />. auto => />. by rewrite in_fsetU in_fset1. 
  rcondt 28. wp. while #pre. auto. wp. while #pre. auto. auto => />. by rewrite in_fsetU in_fset1. 
   auto => />. smt(). 
  while #pre. auto => />. wp. while #pre. auto => />. 
  wp. while #pre. auto => />. auto => />. smt(in_fsetU in_fset1).  
  
   (* We now have valid keys and we seq forward to prove that *)
   (* anyone who is blamed did indeed misbehave *)
   seq 8 : (
    forall x, Some x = pl => x \in pl'); last by inline*;auto => />;1:smt().   

    (* Keep the fact that keys are valid down to the judge algorithm *)
    seq 6 : #pre.  
    auto; inline*; call(_:true); auto; while(#pre); auto.
    while #pre. auto => />. auto => />. 
    inline Fairness.S.judge Select(VSD).is_valid Select(VSD).valid_board.  

    rcondf 16. auto => />. 

    (* Case on all the ways x could be in pl *)
    seq 31 : (#pre /\ 
    (fL = map (fun (x:(nonce*candidate)*nonce),  (x.`1.`1 || x.`2, x.`1.`2)) (zip outcome nL)) 
    /\ nL = GlobVar.rez.`2.`1 
    /\ outcome = GlobVar.rez.`1
    /\ (pl = None 
    \/ (Some AuthServer = pl /\ !size GlobVar.bb <= n_v)
    \/ (Some AuthServer = pl /\ !uniq GlobVar.bb)
    \/ (Some AuthServer = pl /\ !is_lex GlobVar.bb)
    \/ (Some (MixServer 0) = pl /\ size  GlobVar.bb   < size  GlobVar.rez.`2.`2)
    \/ (Some (MixServer 1) = pl /\ size GlobVar.rez.`2.`2 < size GlobVar.rez.`2.`3)
    \/ (Some (MixServer 2) = pl /\ size GlobVar.rez.`2.`3 < size GlobVar.rez.`1)
    \/ (Some (MixServer 2) = pl /\ size GlobVar.rez.`2.`1 <> size GlobVar.rez.`1)
    \/ (Some (MixServer 0) = pl /\ (! is_lex  GlobVar.rez.`2.`2 \/ ! uniq  GlobVar.rez.`2.`2))
    \/ (Some (MixServer 1) = pl /\ (! is_lex  GlobVar.rez.`2.`3 \/ ! uniq  GlobVar.rez.`2.`3))
    \/ (Some (MixServer 2) = pl /\ (fL <> lex fL \/ ! uniq fL))


    \/ (Some AuthServer = pl /\ (exists i, 0<= i < size GlobVar.vsd_blame /\
       let (vote, sign) = to_AS_evidence (nth witness GlobVar.vsd_blame i).`2 in
       verify GlobVar.pp.`1 vote sign /\ (vote \notin GlobVar.bb)))

    \/ (Some (MixServer 0) = pl /\ (exists i,  0<= i < size GlobVar.vsd_blame /\
       (enc (oget GlobVar.pp.`2.[0]) (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
       (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in  GlobVar.bb) /\
       (oget (bit_to_cip (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) 
         \notin GlobVar.rez.`2.`2)))

     \/ (Some (MixServer 1) = pl  /\
        (exists i,  0<= i < size GlobVar.vsd_blame /\
        let (ciph, rand) = to_MS_evidence (nth witness GlobVar.vsd_blame i).`2 in
        (enc (oget  GlobVar.pp.`2.[1]) ciph rand \in GlobVar.rez.`2.`2) /\ 
        (oget (bit_to_cip ciph) \notin GlobVar.rez.`2.`3)))

     \/ ((Some (MixServer 2) = pl  /\
        (exists i,  0<= i < size GlobVar.vsd_blame /\
        let (ciph, rand) = to_MS_evidence (nth witness GlobVar.vsd_blame i).`2 in
        (enc (oget GlobVar.pp.`2.[2]) ciph rand \in GlobVar.rez.`2.`3) /\ 
        oget (bit_to_nc ciph) \notin fL))))
).


     wp. while (#pre /\ (blame = None 
    \/ (Some AuthServer = blame /\ !size bb <= n_v)
    \/ (Some AuthServer = blame /\ !uniq bb)
    \/ (Some AuthServer = blame /\ !is_lex bb)
    \/ (Some (MixServer 0) = blame /\ size bb < size m1_out)
    \/ (Some (MixServer 1) = blame /\ size m1_out < size m2_out)
    \/ (Some (MixServer 2) = blame /\ size m2_out < size outcome)
    \/ (Some (MixServer 2) = blame /\ size nL <> size outcome)
    \/ (Some (MixServer 0) = blame /\ (! is_lex m1_out \/ ! uniq m1_out))
    \/ (Some (MixServer 1) = blame /\ (! is_lex m2_out \/ ! uniq m2_out))
    \/ (Some (MixServer 2) = blame /\ (fL <> lex fL \/ ! uniq fL))

       \/ (Some AuthServer = blame /\ (exists i,  0<= i < size ve{hr} /\
     let (vote, sign) = to_AS_evidence (nth witness ve i).`2 in 
      verify  GlobVar.pp.`1 vote sign /\ (vote \notin  bb)))

       \/ (Some (MixServer 0) = blame /\ (exists i, 0<= i < size ve{hr} /\
     (enc (oget  GlobVar.pp.`2.[0]) (to_MS_evidence (nth witness ve i).`2).`1
       (to_MS_evidence (nth witness ve i).`2).`2 \in  bb) /\
     (oget (bit_to_cip (to_MS_evidence (nth witness ve i).`2).`1) \notin m1_out)))

       \/ (Some (MixServer 1) = blame /\ (exists i, 0<= i < size ve{hr} /\
      let (ciph, rand) = to_MS_evidence (nth witness ve i).`2 in
     (enc (oget  GlobVar.pp.`2.[1]) ciph rand \in m1_out) /\ 
     (oget (bit_to_cip ciph) \notin m2_out)))

       \/ (Some (MixServer 2) = blame /\ (exists i, 0<= i < size ve{hr} /\
     let (ciph, rand) = to_MS_evidence (nth witness ve i).`2 in
     (enc (oget  GlobVar.pp.`2.[2]) ciph rand \in m2_out) /\ 
       oget (bit_to_nc ciph) \notin fL)))

       /\ 0 <= i0 
       /\ pd = GlobVar.pp ).

  auto => />;1:smt().

   wp.  while (#pre /\ (blame = None 
    \/ (Some AuthServer = blame /\ !size bb <= n_v)
    \/ (Some AuthServer = blame /\ !uniq bb)
    \/ (Some AuthServer = blame /\ !is_lex bb)
    \/ (Some (MixServer 0) = blame /\ size bb < size m1_out)
    \/ (Some (MixServer 1) = blame /\ size m1_out < size m2_out)
    \/ (Some (MixServer 2) = blame /\ size m2_out < size outcome)
    \/ (Some (MixServer 2) = blame /\ size nL <> size outcome)
    \/ (Some (MixServer 0) = blame /\ (! is_lex m1_out \/ ! uniq m1_out))
    \/ (Some (MixServer 1) = blame /\ (! is_lex m2_out \/ ! uniq m2_out))
    \/ (Some (MixServer 2) = blame /\ (fL <> lex fL \/ ! uniq fL))

       \/ (Some AuthServer = blame /\ (exists i,  0 <= i < size ve{hr} /\
     let (vote, sign) = to_AS_evidence (nth witness ve i).`2 in  verify  GlobVar.pp.`1 vote sign /\ (vote \notin  bb)))

       \/ (Some (MixServer 0) = blame /\ (exists i,  0<= i < size ve{hr} /\
     (enc (oget  GlobVar.pp.`2.[0]) (to_MS_evidence (nth witness ve i).`2).`1
        (to_MS_evidence (nth witness ve i).`2).`2 \in  bb) /\
     (oget (bit_to_cip (to_MS_evidence (nth witness ve i).`2).`1) \notin m1_out)))

       \/ (Some (MixServer 1) = blame /\ (exists i,  0<= i < size ve{hr} /\
      let (ciph, rand) = to_MS_evidence (nth witness ve i).`2 in
     (enc (oget  GlobVar.pp.`2.[1]) ciph rand \in m1_out) /\ (oget (bit_to_cip ciph) \notin m2_out)))

       \/ (Some (MixServer 2) = blame /\ (exists i,  0<= i < size ve{hr} /\
     let (ciph, rand) = to_MS_evidence (nth witness ve i).`2 in
     (enc (oget  GlobVar.pp.`2.[2]) ciph rand \in m2_out) /\ oget (bit_to_nc ciph) \notin fL)))

       /\ 0 <= i0 /\ pd = GlobVar.pp).
       auto => />; 1:smt().
  auto => />;1:smt(). 

  (* Case 1 of 14: too many votes on the bulletin board *)
  case (Some AuthServer = pl /\ !size GlobVar.bb <= n_v). 
  inline*. seq 20 : (Some AuthServer = pl /\ AuthServer \in pl0). auto => />. by rewrite in_fsetU in_fset1.    
  wp;while #pre. auto => />. by rewrite in_fsetU in_fset1.  
  auto => />. smt(). 
  rcondt 4;1:auto. 
  rcondt 14. wp. while #pre;1:auto. auto.  
  rcondt 24. wp. while #pre. auto. wp. while #pre. auto. auto.  
  wp. while #pre. auto. wp. while #pre. auto. wp. while #pre. auto. auto => />. smt(in_fsetU in_fset1). 

  (* Case 2 of 14: bb contains duplicates *)
  case (Some AuthServer = pl /\ !uniq GlobVar.bb). 
  inline*. seq 20 : (Some AuthServer = pl /\ AuthServer \in pl0). auto => />. by rewrite in_fsetU in_fset1.   
  wp;while #pre. auto => />. by rewrite in_fsetU in_fset1. 
  auto => />. smt(). 
  rcondt 4;1:auto. 
  rcondt 14. wp. while #pre;1:auto. auto.  
  rcondt 24. wp. while #pre. auto. wp. while #pre. auto. auto.  
  wp. while #pre. auto. wp. while #pre. auto. wp. while #pre. auto. auto => />. smt(in_fsetU in_fset1). 

  (* Case 3 of 14: bb is not sorted *)
  case (Some AuthServer = pl /\ !is_lex GlobVar.bb). 
  inline*. seq 20 : (Some AuthServer = pl /\ AuthServer \in pl0). auto => />. by rewrite in_fsetU in_fset1. 
  wp;while #pre. auto => />. by rewrite in_fsetU in_fset1.
  auto => />. smt(). 
  rcondt 4;1:auto. 
  rcondt 14. wp. while #pre;1:auto. auto.  
  rcondt 24. wp. while #pre. auto. wp. while #pre. auto. auto.  
  wp. while #pre. auto. wp. while #pre. auto. wp. while #pre. auto. auto => />. smt(in_fsetU in_fset1). 

   (* Case 4 of 14: MS0 added extra ballots *)
  case (Some (MixServer 0) = pl /\ size GlobVar.bb  < size  GlobVar.rez.`2.`2). inline *.  
    seq 25 : (
      size (oget m0o) <= size GlobVar.bb /\
      Some (MixServer 0) = pl /\ size GlobVar.bb < size GlobVar.rez.`2.`2 /\ 
      l0 = GlobVar.rez.`2.`2).   
   rcondt 24;auto.  
   while (size alphaL <= i4 /\ i4 <= size (oget bb3) /\ l0 = GlobVar.rez.`2.`2). 
     auto => />; progress;[rewrite size_cat; 1:smt() | smt() | smt() | smt()]. 
   auto => />;progress. 
     rewrite size_ge0.  
     rewrite size_sort.
     have H13 : size (undup alphaL1) <= size alphaL1 by rewrite size_undup. smt(). 
   seq 10 : #pre. 
   rcondt 4;auto. 
   rcondt 14. wp;while #pre. auto. auto.
   wp;while #pre;auto. while #pre;auto. 
   seq 1 : ((MixServer 0) \in pl0 /\ Some (MixServer 0) = pl). 
   auto => />. progress. by rewrite in_fsetU in_fset1. 
     move: H H0 => H H0. rewrite H1 in H0. rewrite ltzNge in H0. rewrite H in H0. done. 
   auto => />. while (#pre). auto => />. by rewrite in_fsetU in_fset1.  
   auto => />. progress. by rewrite !in_fsetU !in_fset1.
   by rewrite !in_fsetU !in_fset1. 
   by rewrite !in_fsetU !in_fset1.
   by rewrite in_fsetU in_fset1.
   by rewrite !in_fsetU !in_fset1.
   by rewrite in_fsetU in_fset1.
   by rewrite in_fsetU in_fset1.

   
  (* Case 5 of 14: MS1 added extra ballots *)
     case (Some (MixServer 1) = pl /\ size GlobVar.rez.`2.`2 < size GlobVar.rez.`2.`3). inline *. 
       seq 30 : (
       size (oget m1o) <= size GlobVar.rez.`2.`2  /\ 
       l1 = GlobVar.rez.`2.`3 /\
       Some (MixServer 1) = pl /\ 
       size GlobVar.rez.`2.`2 < size GlobVar.rez.`2.`3).
       rcondt 24; auto. 
       rcondt 34. wp;while #pre. auto. auto => />.   
       auto => />;while (size alphaL0 <= i5 /\ i5 <= size (oget bb4) /\ l1 = GlobVar.rez.`2.`3). 
         auto => />;progress; [rewrite size_cat; 1:smt() | smt() | smt() | smt()]. 
       auto; while(#pre).  
       auto => />; progress. 
       auto => />; progress. 
         rewrite size_ge0. 
         rewrite size_sort. have H16 : size (undup alphaL00) <= size alphaL00 by rewrite size_undup. smt(). 
       seq 5 : #pre. 
       rcondt 4;auto. 
       auto;  while (#pre). auto => />. 
       auto => />.  
       seq 2 : ((MixServer 1) \in pl0 /\ Some (MixServer 1) = pl). 
        auto => />. progress. 
       by rewrite in_fsetU in_fset1.
       move: H => H. rewrite -H2 in H. rewrite ltzNge in H0. rewrite H0 in H. done. 
       by rewrite in_fsetU in_fset1.
       move: H => H. rewrite -H1 in H. rewrite ltzNge in H0. rewrite H0 in H. done.  
       auto => />; while (#pre). 
       auto => />.  by rewrite in_fsetU in_fset1.  
       auto => />. progress. by rewrite !in_fsetU !in_fset1. 
       by rewrite in_fsetU in_fset1. 
       by rewrite in_fsetU in_fset1. 

  (* Case 6 of 14: MS2 added extra ballots *)
    case (Some (MixServer 2) = pl /\ size GlobVar.rez.`2.`3 < size GlobVar.rez.`1). inline *. 
       seq 35 : (size (oget m2o).`1 <= size GlobVar.rez.`2.`3  /\ l2 = GlobVar.rez.`1 /\
       Some (MixServer 2) = pl /\  size GlobVar.rez.`2.`3 < size GlobVar.rez.`1). 
 
       rcondt 24; 1:auto.  
       rcondt 34. wp. while #pre. auto. auto. 
       rcondt 44. wp. while #pre; 1:auto. wp. while #pre; 1:auto. auto. 
       auto => />; while (size ncL <= i6 /\ i6 <= size (oget bb5) /\ l2 = GlobVar.rez.`1). 
       auto => />;progress. rewrite size_cat; 1:smt(). smt(). smt(). smt(). 
       auto; while(#pre).  
       auto => />; progress. 
       auto; while(#pre). 
       auto => />. 
       auto => />; progress. 
         rewrite size_ge0. 
         rewrite size_map size_sort.  smt(size_undup).  
       seq 4 : ((MixServer 2) \in pl0 /\ Some (MixServer 2) = pl). 
       auto => />; 1:smt(in_fset1 in_fsetU).
       auto => />. while (#pre). auto => />. by rewrite in_fsetU in_fset1. 
       by auto => />. 

  (* Case 7 of 14: nonces were added or dropped *)
  case (Some (MixServer 2) = pl /\ size GlobVar.rez.`2.`1 <> size GlobVar.rez.`1). inline*.   
  seq 35 : (size nL0 <= size GlobVar.rez.`2.`3 /\ size (oget m2o).`1 = size (oget m2o).`2 /\ l2 = GlobVar.rez.`1 /\ nL1 = GlobVar.rez.`2.`1 /\
          Some (MixServer 2) = pl /\ size GlobVar.rez.`2.`1 <> size GlobVar.rez.`1). 
  rcondt 24;1:auto. 
  rcondt 34. wp. while #pre. auto. auto. 
  rcondt 44. wp. while #pre;auto. while #pre;1:auto. auto => />. 
  auto; while (size ncL <= i6 /\ i6 <= size (oget bb5) /\ l2 = GlobVar.rez.`1  /\ 
         nL1 = GlobVar.rez.`2.`1 /\ (oget bb5) = GlobVar.rez.`2.`3 /\
         size GlobVar.rez.`2.`1 <> size GlobVar.rez.`1). 
  auto => />; progress. rewrite size_cat; 1:smt(). smt(). smt(). smt(). 
  auto;while(#pre).  
  auto => />. 
  auto; while(#pre). 
  auto => />.  
  auto => />; progress. rewrite size_ge0.  
  rewrite size_map size_sort. smt(size_undup). 
  by rewrite !size_map. 
  seq 4 : ((MixServer 2 \in pl0 /\ Some (MixServer 2) = pl)). 
  auto => />;1:smt(in_fset1 in_fsetU).
  auto;while #pre. 
  auto => />. by rewrite in_fsetU in_fset1. 
  by auto. 

  (* Case 8 of 14: output from MS0 was ill formed *)
  case (Some (MixServer 0) = pl /\ (! is_lex GlobVar.rez.`2.`2 \/ ! uniq GlobVar.rez.`2.`2)). inline *.  
    seq 25 : (#pre /\ l0 = GlobVar.rez.`2.`2 /\ is_lex (oget m0o) /\ uniq (oget m0o)).  
    rcondt 24;1:auto. 
    auto; while (#pre). auto => />. auto => />. progress. 
    rewrite /is_lex eq_sym. apply (sortK leq_b leq_b_tri leq_b_tan leq_b_asy).
    rewrite sort_uniq undup_uniq.   
    seq 11 : (#pre /\  (MixServer 0) \in pl0). 
    rcondt 4;1:auto. 
    rcondt 14. wp;while#pre;1:auto. auto => />. 
    auto; while(#pre). 
    auto => />. 
    auto; while(#pre). 
    auto => />. 
    auto => />. progress. by rewrite in_fsetU in_fset1. smt().  
    wp;while #pre. auto. auto => />. by rewrite in_fsetU in_fset1. 
    auto => />. by rewrite !in_fsetU !in_fset1. 

  (* Case 9 of 14: output from MS1 was ill formed *)
  case (Some (MixServer 1) = pl /\ (! is_lex GlobVar.rez.`2.`3 \/ ! uniq GlobVar.rez.`2.`3)). inline *.  
   seq 30 : (#pre /\ l1 = GlobVar.rez.`2.`3 /\ uniq (oget m1o) /\ is_lex (oget m1o)).  
   rcondt 24;1:auto. 
   rcondt 34. wp. while #pre. auto. auto => />. 
   
   auto; while (#pre). 
   auto => />. 
   auto; while (#pre). 
   auto => />. 
   auto => />;progress. 
     rewrite sort_uniq undup_uniq. 
   rewrite /is_lex eq_sym. apply (sortK leq_b leq_b_tri leq_b_tan leq_b_asy).
   seq 7 : (pl = Some (MixServer 1) /\  (MixServer 1) \in pl0). 
   rcondt 4;1:auto. 
   auto; while(#pre). 
   auto => />. 
   auto => />. progress. by rewrite in_fsetU in_fset1. smt(). 
    by rewrite in_fsetU in_fset1. smt(). 
   wp;while #pre. auto. by rewrite in_fsetU in_fset1.   
   auto => />. by rewrite !in_fsetU !in_fset1.

  (* Case 10 of 14: output from MS2 was ill formed *)
  case (Some (MixServer 2) = pl /\ (fL <> lex fL \/ ! uniq fL)). inline *.  
    seq 35 : (#pre /\ l2 = GlobVar.rez.`1 /\ nL1 = GlobVar.rez.`2.`1 /\ l2 = outcome /\ nL1 = nL /\ 
    (forall i, 0 <= i < size ncL => 
      nth witness ncL i = ( (div (nth witness ncL i).`1).`1 || (div (nth witness ncL i).`1).`2, (nth witness ncL i).`2)) /\
    uniq ncL /\ ncL = lex ncL /\ (oget m2o).`1 = map (fun (x:nonce*candidate), ((div x.`1).`1, x.`2)) ncL /\
    (oget m2o).`2 = map (fun (x:nonce*candidate), (div x.`1).`2) ncL). 
    rcondt 24; 1: auto. 
    rcondt 34. 
    wp;while #pre;1:auto. auto => />. 
    rcondt 44. 
    wp;while #pre;auto. while #pre;1:auto. auto => />. 
    wp;while #pre;auto. while #pre;auto. while #pre;1:auto.
    auto => />;progress. rewrite div_concat. smt().   
    rewrite sort_uniq undup_uniq.  
    rewrite /lex eq_sym. apply (sortK leq_nc leq_nc_tri leq_nc_tan leq_nc_asy).  
    
    seq 4 : (#pre /\  (MixServer 2) \in pl0). 
    case (l2 <> (oget m2o).`1).
    rcondt 3. auto. auto => />. by rewrite !in_fsetU !in_fset1. 
    case ((oget m2o).`2 <> nL1). 
    rcondt 4. auto. auto => />. auto => />. by rewrite !in_fsetU !in_fset1. rewrite //=. 

    seq 0 : (#pre /\ fL = lex fL /\ uniq fL).
    auto => />; progress.  
    rewrite eq_sym in H15. 
    rewrite H14 H15.  
    rewrite H12 H13. 
 
    rewrite (map_zip_nth witness witness (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2))
      (map (fun (x : nonce * candidate) => 
          ((div x.`1).`1, x.`2)) ncL{hr}) (map (fun (x : nonce * candidate) => (div x.`1).`2) ncL{hr})).
     by rewrite !size_map.  

     have -> : size (map (fun (x:nonce * candidate), ((div x.`1).`1, x.`2)) ncL{hr}) = size ncL{hr} by rewrite size_map. 
     simplify.  

    have -> : map (fun (i6 : int) =>
       ((nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`1 ||
         nth witness (map (fun (x : nonce * candidate) => (div x.`1).`2) ncL{hr}) i6,
      (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`2)) 
      (range 0 (size ncL{hr})) = ncL{hr}. 

   rewrite (eq_from_nth  witness (map (fun (i6 : int) =>
       ((nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`1 ||
         nth witness (map (fun (x : nonce * candidate) => (div x.`1).`2) ncL{hr}) i6,
        (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`2)) 
       (range 0 (size ncL{hr}))) (ncL{hr})). 
     rewrite size_map. 
     rewrite size_range //=. have -> : max 0 (size ncL{hr}) = size ncL{hr} by smt(size_ge0 size_eq0). done. 
     move => i6 i6_range. 
     rewrite size_map in i6_range. 
     rewrite size_range in i6_range. 
     have i6_r : 0 <= i6 < size ncL{hr} by smt(). 
     rewrite (nth_map witness witness (fun (i6_0 : int) =>
            ((nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6_0).`1 ||
              nth witness (map (fun (x : nonce * candidate) => (div x.`1).`2) ncL{hr}) i6_0,
             (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6_0).`2)) i6 
         (range 0 (size ncL{hr}))). 
    by rewrite size_range.  
    simplify. 
    rewrite H9. done. 
    rewrite div_concat. 
    have -> : nth witness (range 0 (size ncL{hr})) i6 = i6. rewrite nth_range //=.   
    have -> : (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`1 = 
    (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1)) ncL{hr}) i6). 
    rewrite (nth_map witness witness (fun (x : nonce * candidate) => (div x.`1).`1) i6 ncL{hr}). done. 
    simplify. 
    rewrite (nth_map witness witness (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) i6 ncL{hr}). done. 
    simplify. done. 
    have -> : (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`2 = 
              (nth witness (map (fun (x : nonce * candidate) => (x.`2)) ncL{hr}) i6).
   rewrite (nth_map witness witness (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) i6 ncL{hr}). done. 
  simplify.
  rewrite (nth_map witness witness snd i6 ncL{hr}). done. 
  simplify. done. 
  rewrite (nth_map witness witness snd i6 ncL{hr}). done. simplify. 
  rewrite (nth_map witness witness (fun (x : nonce * candidate) => (div x.`1).`1) i6 ncL{hr}). done. simplify. 
  rewrite (nth_map witness witness (fun (x : nonce * candidate) => (div x.`1).`2) i6 ncL{hr}). done. simplify. 
  by rewrite div_concat. done. done.  
 
  rewrite H14 -H15 H12 H13.  

   rewrite (map_zip_nth witness witness (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2))
    (map (fun (x : nonce * candidate) => 
        ((div x.`1).`1, x.`2)) ncL{hr}) (map (fun (x : nonce * candidate) => (div x.`1).`2) ncL{hr})).
      by rewrite !size_map.  

      have -> : size (map (fun (x:nonce * candidate), ((div x.`1).`1, x.`2)) ncL{hr}) = size ncL{hr} by rewrite size_map. 
      simplify.  

     have -> : map (fun (i6 : int) => 
             ((nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`1 ||
               nth witness (map (fun (x : nonce * candidate) => (div x.`1).`2) ncL{hr}) i6,
              (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`2)) 
          (range 0 (size ncL{hr})) = ncL{hr}. 

      rewrite (eq_from_nth witness (map (fun (i6 : int) =>
         ((nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`1 ||
           nth witness (map (fun (x : nonce * candidate) => (div x.`1).`2) ncL{hr}) i6,
          (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`2)) 
      (range 0 (size ncL{hr}))) (ncL{hr})). rewrite size_map. rewrite size_range => //=. smt(size_ge0 size_eq0). 
     move => i6 i6_range. rewrite size_map in i6_range. rewrite size_range in i6_range. 
     have i6_r : 0 <= i6 < size ncL{hr} by smt(). 
     rewrite (nth_map witness witness (fun (i6_0 : int) =>
        ((nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6_0).`1 ||
          nth witness (map (fun (x : nonce * candidate) => (div x.`1).`2) ncL{hr}) i6_0,
         (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6_0).`2)) i6 
       (range 0 (size ncL{hr}))). by rewrite size_range.  
    simplify. rewrite H9. done. rewrite div_concat. 
    have -> : nth witness (range 0 (size ncL{hr})) i6 = i6. rewrite nth_range => //=.   

    have -> : (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`1 = 
              (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1)) ncL{hr}) i6). 
    rewrite (nth_map witness witness (fun (x : nonce * candidate) => (div x.`1).`1) i6 ncL{hr}). done. simplify. 
    rewrite (nth_map witness witness (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) i6 ncL{hr}). done. simplify. done. 
    have -> : (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) ncL{hr}) i6).`2 = 
              (nth witness (map (fun (x : nonce * candidate) => (x.`2)) ncL{hr}) i6).
   rewrite (nth_map witness witness (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) i6 ncL{hr}). done. simplify.
  rewrite (nth_map witness witness snd i6 ncL{hr}). done. simplify. done. 
  rewrite (nth_map witness witness snd i6 ncL{hr}). done. simplify. 
  rewrite (nth_map witness witness (fun (x : nonce * candidate) => (div x.`1).`1) i6 ncL{hr}). done. simplify. 
  rewrite (nth_map witness witness (fun (x : nonce * candidate) => (div x.`1).`2) i6 ncL{hr}). done. simplify. 
  by rewrite div_concat. done. done.  

  auto => />;1:smt().  
  auto => />. while #pre; auto => />. progress. rewrite in_fsetU; 1: by left.  

  (* Case 11 of 14: AS dropped a ballot *)
  case (Some AuthServer = pl /\
    exists (i5 : int),  0 <= i5 < size GlobVar.vsd_blame /\
      let (vote1, sign) = to_AS_evidence (nth witness GlobVar.vsd_blame i5).`2 in
       verify GlobVar.pp.`1 vote1 sign /\ (vote1 \notin GlobVar.bb)). inline *.
       seq 39 : (#pre /\ pd1 = GlobVar.pp  /\ bb1 = GlobVar.bb /\ ve0 = GlobVar.vsd_blame).  
       rcondt 24;1:auto. 
       rcondt 34. wp;while #pre;1:auto. auto => />. auto => />. 
       rcondt 44. wp;while #pre;1:auto => />. wp;while #pre. auto => />.  
       auto => />. 
       auto => />;while (#pre).
       auto => />. auto => />. while (#pre). auto => />. auto => />. while(#pre); auto => />;progress.  
       wp. while (AuthServer \in pl0 \/ exists (i5 : int),  i2 <= i5 < size GlobVar.vsd_blame /\
       let (vote1, sign) = to_AS_evidence (nth witness ve0 i5).`2 in
       verify pd1{hr}.`1 vote1 sign /\ (vote1 \notin (bb1))). 
       auto => />;progress.        
       by rewrite in_fsetU in_fset1.  
       elim H => h1. by left.  
       right. elim h1 => h1 h2. 
       exists h1. case (i2{hr} = h1) => h3.  
       smt(). smt(). 
       auto => />; progress. right. exists i50. smt(). smt().  

  (* Case 12 of 14: MS0 dropped a ballot *)
    case (Some (MixServer 0) = pl /\
    exists (i5 : int),   0 <= i5 < size GlobVar.vsd_blame /\ 
      (enc (oget GlobVar.pp.`2.[0]) (to_MS_evidence (nth witness GlobVar.vsd_blame i5).`2).`1 
      (to_MS_evidence (nth witness GlobVar.vsd_blame i5).`2).`2 \in GlobVar.bb) /\
      (oget (bit_to_cip (to_MS_evidence (nth witness GlobVar.vsd_blame i5).`2).`1) \notin GlobVar.rez.`2.`2)). inline *. 
      rcondt 24; 1:auto. 
       (* We wish to seq forward remembering that everything in the ballotbox ends up in the honest output *)
        seq 30 : ( Some (MixServer 0) = pl /\ bb1 = GlobVar.bb /\
        (exists (i5_0 : int), (0 <= i5_0 && i5_0 < size GlobVar.vsd_blame) /\
         (enc (oget GlobVar.pp.`2.[0])
          (to_MS_evidence (nth witness GlobVar.vsd_blame i5_0).`2).`1
          (to_MS_evidence (nth witness GlobVar.vsd_blame i5_0).`2).`2 \in GlobVar.bb) /\
         (oget (bit_to_cip
          (to_MS_evidence (nth witness GlobVar.vsd_blame i5_0).`2).`1) \notin
     GlobVar.rez.`2.`2) /\ l0 = GlobVar.rez.`2.`2) /\
      (forall i, (0 <= i < size GlobVar.vsd_blame /\
          (enc (oget GlobVar.pp.`2.[0]) (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
      (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in bb1) =>
        oget (bit_to_cip (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) \in (oget m0o)))). 

       (* Begin early sequence - 3 goals go *)
        auto.
        while (esk = get_sk (oget GlobVar.pp.`2.[0]) /\ 0 <= size alphaL <= i4 <= size (oget bb3) /\ 
        (oget bb3) = GlobVar.bb /\
        (forall x y i, (0<= i < size (oget bb3) /\ (enc (oget  GlobVar.pp.`2.[0]) x y = nth witness (oget bb3) i) =>
          oget (bit_to_cip x) \in alphaL  \/ i4 -1 < i))). 

          (* Handling the while loop *)
          auto => />; progress. rewrite size_ge0. rewrite size_cat; 1:smt(). smt().
          have : ((oget (bit_to_cip x) \in alphaL{hr}) \/ i4{hr} - 1 < i7) by smt(). 
          move => h1. elim h1 => h1. rewrite mem_cat; 1:smt().  
          case (i4{hr} = i7) => h2. 
          rewrite eq_sym in H7. rewrite h2 H7. 
          rewrite enc_dec_correct. rewrite mem_cat; 1:smt(). rewrite mem_cat; 1:smt(). smt(). smt().
          have : ((oget (bit_to_cip x) \in alphaL{hr}) \/ i4{hr} - 1 < i7) by smt(). 
        move => h1. elim h1 => h1. smt().
        case(i4{hr} = i7) => h2. rewrite /= in H4.
        have : dec (get_sk (oget GlobVar.pp{hr}.`2.[0]))
         (enc (oget GlobVar.pp{hr}.`2.[0]) x y) =  None by  smt(). 
         move => h3. 
        rewrite enc_dec_correct in h3. smt(). smt().

          (* Ending while loop back to sequence *)
          auto => />;progress. rewrite mapE oget_omap_some. smt().  
          smt(). rewrite size_ge0. smt().   
          have : (0 <= (index
          (enc (oget GlobVar.pp{hr}.`2.[0])
             (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`1
             (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`2)
          GlobVar.bb{hr}) && (index
          (enc (oget GlobVar.pp{hr}.`2.[0])
             (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`1
             (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`2)
          GlobVar.bb{hr}) < size GlobVar.bb{hr}) by rewrite index_ge0 //= index_mem.   
               apply (nth_index witness _ GlobVar.bb{hr}) in H20. rewrite eq_sym in H20. move => H24.   
               rewrite mem_sort mem_undup. smt(). 

               seq 11 : (MixServer 0 \in pl0 /\ Some (MixServer 0) = pl). 
               seq 10: #pre.  
          rcondt 4;1:auto. 
          rcondt 14;1:auto. while #pre;1:auto. progress. smt(). auto => />. 
               auto. while (#pre). auto => />. auto => />. 
               auto;while (#pre).  auto => />;  progress. 
               by rewrite in_fsetU in_fset1. smt(). 
            auto. while (#pre). auto => />. 
        by rewrite !in_fsetU !in_fset1. 
       auto => />. by rewrite !in_fsetU !in_fset1.    


  (* Case 13 of 14: MS1 dropped a ballot *)
   case (Some (MixServer 1) = pl /\
    exists (i5 : int),   0 <= i5 < size GlobVar.vsd_blame /\
      let (ciph, rand0) = to_MS_evidence (nth witness GlobVar.vsd_blame i5).`2 in
      (enc (oget GlobVar.pp.`2.[1]) ciph rand0 \in GlobVar.rez.`2.`2) /\
      (oget (bit_to_cip ciph) \notin GlobVar.rez.`2.`3)). inline *. 
    rcondt 24; 1: auto.   

    rcondt 34. wp;while #pre; 1:auto => />. auto => />. 
       (* We wish to seq forward remembering that everything in the ballotbox ends up in the honest output *)
        seq 40 : ( Some (MixServer 1) = pl /\ (oget bb4) = GlobVar.rez.`2.`2 /\
        (exists (i5_0 : int), (0 <= i5_0 && i5_0 < size GlobVar.vsd_blame) /\
    (enc (oget GlobVar.pp.`2.[1])
       (to_MS_evidence (nth witness GlobVar.vsd_blame i5_0).`2).`1
       (to_MS_evidence (nth witness GlobVar.vsd_blame i5_0).`2).`2 \in
     GlobVar.rez.`2.`2) /\
    (oget (bit_to_cip
     (to_MS_evidence (nth witness GlobVar.vsd_blame i5_0).`2).`1) \notin
     GlobVar.rez.`2.`3) /\ l1 = GlobVar.rez.`2.`3) /\
      (forall i, (0 <= i < size GlobVar.vsd_blame /\
          (enc (oget GlobVar.pp.`2.[1]) (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
      (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in (oget bb4)) =>
        oget (bit_to_cip (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) \in (oget m1o)))).

       (* Begin early sequence - 3 goals go *)
        auto.
        while (esk0 = get_sk (oget GlobVar.pp.`2.[1]) /\ 0 <= size alphaL0 <= i5 <= size (oget bb4) /\ (oget bb4) = GlobVar.rez{hr}.`2.`2 /\
        (forall x y i, (0<= i < size (oget bb4) /\ (enc (oget  GlobVar.pp.`2.[1]) x y = nth witness (oget bb4) i) =>
          oget (bit_to_cip x) \in alphaL0  \/ i5 -1 < i))). 

          (* Handling the while loop *)
          auto => />;progress. rewrite size_ge0. rewrite size_cat; 1:smt(). smt().
          have : ((oget (bit_to_cip x) \in alphaL0{hr}) \/ i5{hr} - 1 < i7) by smt(). 
          move => h1. elim h1 => h1. rewrite mem_cat; 1:smt(). 
          case (i5{hr} = i7) => h2. rewrite eq_sym in H8. rewrite h2 H8. 
          rewrite enc_dec_correct. rewrite mem_cat; 1:smt(). rewrite mem_cat; 1:smt().
          smt(). smt().
          have : ((oget (bit_to_cip x) \in alphaL0{hr}) \/ i5{hr} - 1 < i7) by smt(). 
          move => h1. elim h1 => h1. smt().
          case(i5{hr} = i7) => h2. rewrite /= in H4.
          have : dec (get_sk (oget GlobVar.pp{hr}.`2.[1]))
         (enc (oget GlobVar.pp{hr}.`2.[1]) x y) =  None by smt(). 
         move => h3. rewrite enc_dec_correct in h3. smt(). smt().

          (* Ending while loop back to sequence *)
        auto. while(#pre). auto => />; smt(). 
        auto => />; progress. 
        rewrite mapE oget_omap_some. smt(). done. rewrite size_ge0. smt(). smt(). 
          have : (0 <= (index
          (enc (oget GlobVar.pp{hr}.`2.[1])
             (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`1
             (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`2)
          GlobVar.rez{hr}.`2.`2) && (index
          (enc (oget GlobVar.pp{hr}.`2.[1])
             (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`1
             (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`2)
          GlobVar.rez{hr}.`2.`2) < size GlobVar.rez.`2.`2{hr}) by rewrite index_ge0 index_mem.
         apply (nth_index witness _ GlobVar.rez{hr}.`2.`2) in H20. rewrite eq_sym in H20. 
         move => h1. rewrite mem_sort mem_undup. smt(). 
         seq 7 : (MixServer 1 \in pl0 /\ Some (MixServer 1) = pl). 
         seq 6: #pre.  
         rcondt 4;1:auto. auto. while (#pre).
         auto => />; progress. auto => />. 
         auto => />. progress. by rewrite !in_fsetU !in_fset1. smt().  
         wp;while#pre. auto => />. by rewrite !in_fsetU !in_fset1.  
         auto => />. by rewrite !in_fsetU !in_fset1. 

 
  (* Case 14 of 14: MS2 dropped a ballot *)
    case (Some (MixServer 2) = pl /\
    exists (i5 : int),   0 <= i5 < size GlobVar.vsd_blame /\
      let (ciph, rand0) = to_MS_evidence (nth witness GlobVar.vsd_blame i5).`2 in
      (enc (oget GlobVar.pp.`2.[2]) ciph rand0 \in GlobVar.rez.`2.`3) /\ oget (bit_to_nc ciph) \notin fL). inline *. 

    rcondt 24;1: auto => />.  
    rcondt 34. wp;while #pre;1:auto => />. auto => />.  
    rcondt 44. wp;while#pre;1:auto => />. wp;while #pre;1:auto => />. auto => />.  

  (* We wish to seq forward remembering that everything in the ballotbox ends up in the honest output *)
      seq 54 : (#pre /\ 
      Some (MixServer 2) = pl /\ 
      (oget bb5) = GlobVar.rez.`2.`3 /\

      fL = map (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2)) (zip outcome nL) /\
      nL = GlobVar.rez.`2.`1 /\
      outcome = GlobVar.rez.`1 /\
     
    (exists (i5_0 : int),
    (0 <= i5_0 && i5_0 < size GlobVar.vsd_blame) /\
    (enc (oget GlobVar.pp.`2.[2])
       (to_MS_evidence (nth witness GlobVar.vsd_blame i5_0).`2).`1
       (to_MS_evidence (nth witness GlobVar.vsd_blame i5_0).`2).`2 \in
     GlobVar.rez.`2.`3) /\ (oget (bit_to_nc (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i5_0).`2).`1) \notin fL)) /\ 

       l2 = GlobVar.rez.`1 /\ 
       l1 = GlobVar.rez.`2.`3 /\ 
       l0 = GlobVar.rez.`2.`2 /\ 
      nL1 = GlobVar.rez.`2.`1 /\
      ncL = lex ncL /\ 
      uniq ncL /\
       (forall i, 0 <= i < size ncL => 
         nth witness ncL i = ( (div (nth witness ncL i).`1).`1 || (div (nth witness ncL i).`1).`2, (nth witness ncL i).`2)) /\

       (oget m2o).`1 = map (fun (x:nonce*candidate), ((div x.`1).`1, x.`2)) ncL /\
       (oget m2o).`2 = map (fun (x:nonce*candidate), (div x.`1).`2) ncL /\

      (forall i, (0 <= i < size GlobVar.vsd_blame /\
          (enc (oget GlobVar.pp.`2.[2]) (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1
      (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`2 \in (oget bb5)) =>  
        oget (bit_to_nc (to_MS_evidence (nth witness GlobVar.vsd_blame i).`2).`1) \in 
        map (fun (x:(nonce*candidate)*nonce), (x.`1.`1 || x.`2, x.`1.`2)) (zip (oget m2o).`1 (oget m2o).`2)))
      ). 

       (* Begin early sequence - 3 goals go *)
        auto => />; 1:smt(). wp. 
        while (esk1 = get_sk (oget GlobVar.pp.`2.[2]) /\ 0 <= size ncL <= i6 <= size (oget bb5) /\ (oget bb5) = GlobVar.rez{hr}.`2.`3  /\
        (forall x y i, (0<= i < size (oget bb5) /\ (enc (oget  GlobVar.pp.`2.[2]) x y = nth witness (oget bb5) i) =>
          oget (bit_to_nc x) \in ncL  \/ i6 -1 < i))). 

          (* Handling the while loop *)
          auto => />. progress. rewrite size_ge0. rewrite size_cat; 1: smt(). smt(). 
          have : oget (bit_to_nc x) \in ncL{hr} \/ i6{hr} - 1 < i7 by smt(). 
          move => h1. elim h1 => h1. rewrite mem_cat; 1:smt().  
          case (i6{hr} = i7) => h2. rewrite eq_sym in H8. rewrite h2 H8. 
          rewrite enc_dec_correct. rewrite mem_cat; 1:smt(). rewrite mem_cat; 1:smt(). smt(). smt().
          have : oget (bit_to_nc x) \in ncL{hr} \/ i6{hr} - 1 < i7 by smt(). 
          move => h1. elim h1 => h1. by left. 
          case(i6{hr} = i7) => h2. rewrite /= in H4.
          have : dec (get_sk (oget GlobVar.pp{hr}.`2.[2]))
           (enc (oget GlobVar.pp{hr}.`2.[2]) x y) =  None by smt(). move => h3. rewrite enc_dec_correct in h3. smt(). smt().


        (* Ending while loop back to sequence *)
      wp;while #pre. auto => />. 
      wp;while #pre. auto => />.  
      auto => />. progress. 

      rewrite mapE oget_omap_some. smt(). done. 
      rewrite size_ge0. smt(). smt().    
      
      rewrite /lex eq_sym. apply (sortK leq_nc leq_nc_tri leq_nc_tan leq_nc_asy).  
      rewrite sort_uniq undup_uniq. rewrite div_concat; 1: smt(). 
        
    have -> : map (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2))
     (zip (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
     (sort leq_nc (undup ncL0)))
     (map (fun (x : nonce * candidate) => (div x.`1).`2)
     (sort leq_nc (undup ncL0)))) = sort leq_nc (undup ncL0). 
        
    rewrite (map_zip_nth witness witness (fun (x : (nonce * candidate) * nonce) => (x.`1.`1 || x.`2, x.`1.`2)) 
      (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
        (sort leq_nc (undup ncL0))) (map (fun (x : nonce * candidate) => (div x.`1).`2)
        (sort leq_nc (undup ncL0)))). by rewrite !size_map. simplify. 

    have -> : (range 0 (size  (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
           (sort leq_nc (undup ncL0))))) = range 0 (size (sort leq_nc (undup ncL0))). congr. by rewrite size_map. 

    have -> : size (sort leq_nc (undup ncL0)) = size (undup ncL0) by rewrite size_sort.   
     
     rewrite (eq_from_nth witness (map (fun (i7 : int) => 
           ((nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
            (sort leq_nc (undup ncL0))) i7).`1 ||
      nth witness (map (fun (x : nonce * candidate) => (div x.`1).`2)
           (sort leq_nc (undup ncL0))) i7,
      (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
            (sort leq_nc (undup ncL0))) i7).`2))
     (range 0 (size (undup ncL0)))) (sort leq_nc (undup ncL0))). rewrite size_map. 
     rewrite size_range size_sort //=. smt(size_ge0 size_eq0). 
     
    move => i8 i8_range. simplify. 

    have i8r : 0 <= i8 < size (range 0 (size (undup ncL0))) by rewrite size_map in i8_range. 
    have i8r' : 0 <= i8 < size (sort leq_nc (undup ncL0)). rewrite size_sort. 
    rewrite size_range in i8r. by smt(). 

    rewrite (nth_map witness witness ((fun (i7_0 : int) =>
        ((nth witness
            (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
               (sort leq_nc (undup ncL0))) i7_0).`1 ||
         nth witness
           (map (fun (x : nonce * candidate) => (div x.`1).`2)
              (sort leq_nc (undup ncL0))) i7_0,
         (nth witness
            (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
               (sort leq_nc (undup ncL0))) i7_0).`2))) i8 (range 0 (size (undup ncL0)))). done. simplify. 

   have -> : nth witness (range 0 (size (undup ncL0))) i8 = i8. rewrite nth_range. 
   by rewrite size_sort in i8r'. done. 

   have -> : (nth witness (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
       (sort leq_nc (undup ncL0))) i8).`1 = 
   nth witness (map (fun (x:nonce * candidate), (div x.`1).`1) (sort leq_nc (undup ncL0))) i8.
   rewrite (nth_map witness witness (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2)) i8 (sort leq_nc (undup ncL0))). 
   done.   

   simplify.
   rewrite (nth_map witness witness (fun (x:nonce*candidate), (div x.`1).`1) i8 (sort leq_nc (undup ncL0))). 
   done. 
   simplify. done. 

   rewrite (nth_map witness witness (fun (x:nonce*candidate), (div x.`1).`1) i8 (sort leq_nc (undup ncL0))). done. 
   simplify. 
   rewrite (nth_map witness witness (fun (x:nonce*candidate), (div x.`1).`2) i8 (sort leq_nc (undup ncL0))). done. 
   simplify. 

   have -> : (nth witness
    (map (fun (x : nonce * candidate) => ((div x.`1).`1, x.`2))
       (sort leq_nc (undup ncL0))) i8).`2 = (nth witness
    (map (fun (x : nonce * candidate) => (x.`2))
       (sort leq_nc (undup ncL0))) i8). 
   rewrite (nth_map witness witness (fun (x:nonce*candidate), ((div x.`1).`1, x.`2)) i8 (sort leq_nc (undup ncL0))). 
   done. simplify. 
   rewrite (nth_map witness witness snd i8 (sort leq_nc (undup ncL0))). 
   done. simplify. done. 
   rewrite div_concat.
   rewrite (nth_map witness witness snd i8 (sort leq_nc (undup ncL0))). 
   done. simplify. smt(). done. 

   rewrite mem_sort mem_undup.
   move: (H19 (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`1 
         (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`2 (index (enc (oget GlobVar.pp.`2.[2]){hr} 
         (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`1 
         (to_MS_evidence (nth witness GlobVar.vsd_blame{hr} i7).`2).`2) GlobVar.rez{hr}.`2.`3) _).
   + split.
     + by rewrite index_ge0 index_mem.
     by rewrite nth_index.
   smt(index_mem).

   seq 4 : (MixServer 2 \in pl0 /\ Some (MixServer 2) = pl). 
   seq 2: #pre.
   auto => />;progress.  
   auto => />. progress. by rewrite !in_fsetU !in_fset1. 
   by rewrite !in_fsetU !in_fset1. 
   by rewrite !in_fsetU !in_fset1. smt(). 
   auto;while #pre. auto => />. by rewrite !in_fsetU !in_fset1.  
   by auto => />. 
 
    (* We're all out of cases and all that's left is a big contradiction in the precondition *)
    call (_ : true). auto. auto. progress. elim H5 => H5. smt().
    elim H5 => H5. smt(). elim H5 => H5. smt(). elim H5 => H5. smt(). elim H5 => H5. smt().
    elim H5 => H5. smt(). elim H5 => H5. smt(). elim H5 => H5. elim H5 => H5. smt(). 
    elim H5 => H5. move: H5. smt(). elim H5 => H5. smt(). elim H5 => H5. smt(). 
    elim H5 => H5. 
    move: H5 H16. smt().  
    elim H5 => H5. smt(). 
    elim H5 => H5. move: H5 H18. smt().  
    rewrite H19 in H5. 

   trivial.   
 
  qed.


(*----------------------------------*)
(* The probability of A winning the *) 
(* accountability game is zero      *)
(*----------------------------------*)
lemma select_accountability &m : Pr[Acc(Select(VSD),A).main() @ &m : res] = 0%r. 
proof. 
have H : Pr[Acc(Select(VSD),A).main() @ &m : res] <= 
  Pr[Fairness.main() @ &m : res] + Pr[Completeness.main() @ &m : res] by exact/acc_fair_comp_bound. 
rewrite completeness in H. rewrite fairness in H. 
rewrite //= in H. 
have H0 : 0%r <= Pr[Acc(Select(VSD),A).main() @ &m : res] by rewrite Pr[mu_ge0].   
smt(). 
qed. 

end section. 

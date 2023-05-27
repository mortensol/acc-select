(********************************************************************************)
(***          In this file, we model the accountability experiment            ***)
(********************************************************************************)

(*-------------------------*)
(* Load necessary theories *)
(*-------------------------*)
require import Int FSet List SmtMap Finite.

(*------------------------------*)
(*     Types and operators      *)
(*------------------------------*)

type apkey. (* authetication server public key *)
type ident. (* voter identity *)
type state. (* voter state *)
type vote.  (* vote submitted by voters *)
type ballot. (* ballot, e.g. encrypted vote *)
type signature. (* signature *)
type vsd_evidence. (* evidence output by voter devices if someone misbehaved *)
type party. (* type for the different parties in the protocol *)
type extra_public. (* any extra public information in addition to apkey *)
type public_parameters = apkey * extra_public. (* all the public parameters *)
type extra_result. (* Everything other than the final result, e.g. public information output by mix servers *)
type result = (vote list) * extra_result. (* result: list of votes and possibly other things *)

op n: int. (* number of voters *)
op lexicographic: vote list -> vote list. (* operator for sorting in lexicographic order *)


(*-----------------------------------------*)
(* Global variables used in the experiment *)
(*-----------------------------------------*)
module GlobVar ={

  (* public parameters *)
  var pp : public_parameters

  (* finite map from voter id to their state, vote and ballot *)
  var v_ballots  : (ident, state * vote * ballot) fmap

  (* list of evidence produced by voter devices *)
  var vsd_blame  : (vsd_evidence) list

  (* finite map from voter id to signatures *)
  var v_sign     :  (ident, signature) fmap

  (* list of ballots *)
  var bb  : ballot list

  (* election result *)
  var rez : result
 

}.

(*-----------------------------------------------------------------*)
(*      Minimal Functions for Voting System's accountability       *)
(* Note this excludes (honest) proc which are not used in the game *)
(*-----------------------------------------------------------------*)
    
module type CoreVote_System ={

  (* vote casting algorithm *)
  proc vote (id: ident, pd: public_parameters, v: vote)
       : state * ballot
  
  (* verification algorithm for voters device *)
  proc vsd_verify (pd: public_parameters,
                   st: state, v: vote, b: ballot, s: signature, 
                   bb: ballot list, 
                   mi: result)
        : vsd_evidence option

  (* judge: deciding who to blame *)
  proc judge(pd: public_parameters, 
                        bb: ballot list, 
                        mi: result,  
                        ve: (vsd_evidence) list) : party option
  
  (* checking if public parameters are valid *)
  proc is_valid(pd: public_parameters)
       : bool

  (* checking if bulletin board is valid *)
  proc valid_board(bb: ballot list)
       : bool

  (* checking if a signature is valid *)
  proc valid_sig(pd : public_parameters, b: ballot, s: signature)
      : bool

  (* bad: a technical artifiact which exists to provide a ground truth
  and has no corresponding algorithm when the system is run *)
  proc bad (pd: public_parameters, 
            bb: ballot list, 
            mi: result,  
            vb: (ident, state * vote * ballot) fmap,
            ve: ( vsd_evidence) list)
       : party fset
}.

(*-----------------------*)
(* Accountability Oracle *)
(*-----------------------*)
module type Acc_Oracle ={

  proc vote(id: ident, v: vote): ballot

}.

module Acc_Oracle (V: CoreVote_System)={

  proc vote(id: ident, v: vote): ballot ={
  
    var st, b;

    (st,b) <@ V.vote(id, GlobVar.pp, v);
    
    GlobVar.v_ballots.[id] <- (st, v, b);
    
    return b;
  }
}.


(*--------------------------*)
(* Accountability Adversary *)
(*--------------------------*)
module type Acc_Adv (O: Acc_Oracle) ={

  (* setup: returning public parameters *)
  proc setup(): public_parameters 
                { }

  (* rung: returns list of ballots, result and signatures *)
  proc run()  : (ballot list) * result * (ident, signature) fmap
                {O.vote}

  (* the adversary can falsely blame honest parties *)
  proc dishonest_blamed (_:vsd_evidence list)
              : vsd_evidence list
                { }
}.


(*------------------------------*)
(*  Accountability definition   *)
(*------------------------------*)
module Acc(V: CoreVote_System, A: Acc_Adv) ={

  module O = Acc_Oracle(V)
  module A = A(O)

  (* initialize global variables *)
  proc init(): unit ={

    GlobVar.vsd_blame   <- [];
    GlobVar.v_ballots   <- empty;

  }
 
  (* procedure for verification and producing evidence *)
  proc vsd_verify(): vsd_evidence list ={

    var i, st, v, b, s, id,  vsd_evidence;

    i <- 0;
    
    (* verify run by all voters that honestly voted *)
    while (i < card (fdom GlobVar.v_ballots)){
      
      (* get state and ballot for voter id *)
            id <- nth witness (elems (fdom GlobVar.v_ballots)) i;
      (st,v,b) <- oget GlobVar.v_ballots.[id];
      s        <- oget GlobVar.v_sign.[id];

      vsd_evidence <@ V.vsd_verify(GlobVar.pp, st, v, b, s, GlobVar.bb, GlobVar.rez);

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
    var dishonest_blamed, pl, pl', es, e, i, st, v, b,  s, id, r;

    (* initialize *)
    init();

    (* Adb creates public parameters, ballots, result and signatures *)
    GlobVar.pp <@ A.setup();
    (GlobVar.bb, GlobVar.rez, GlobVar.v_sign) <@ A.run();

   (* if A has not provided valid signatures it loses *)
    es <- true;
    i  <- 0;
      while (i < card (fdom GlobVar.v_ballots)){
       id <- nth witness (elems (fdom GlobVar.v_ballots)) i;
      (st,v,b) <- oget GlobVar.v_ballots.[id];
       s        <- oget GlobVar.v_sign.[id];
      r <@ V.valid_sig(GlobVar.pp, b, s);
      if (!r) {
        es <- false;
      }
      i <- i + 1;
   }

    (* GlobVar.vsd_blame gets updated *)            
    vsd_verify();

    (* adv adds blame from dishonest voters *)                
    dishonest_blamed <@ A.dishonest_blamed(GlobVar.vsd_blame);
    GlobVar.vsd_blame <- GlobVar.vsd_blame ++ dishonest_blamed;

    (* Judging procedure *)
    pl <@ V.judge(GlobVar.pp, GlobVar.bb, GlobVar.rez, 
                             GlobVar.vsd_blame);

    (* bad provides ground truth *)
    pl'<@ V.bad(GlobVar.pp, GlobVar.bb, GlobVar.rez, GlobVar.v_ballots, 
                GlobVar.vsd_blame);
    


    (* adversary wins if everything looks valid when *)
    e <- es
         /\ (
              (* adv could falsely blame honest parties - tricking universal verification, 
                 bad: will never blame honest parties *)
              (exists x, Some x = pl /\ !(x \in pl'))
            
              \/ (* or no one is blamed 
                       and (more ballots or votes were introduced or honest votes were dropped) *)
                 (pl = None
                 /\ (   (* limit on number of ballots *)
                         n < (size GlobVar.bb) 
                      \/ (* more votes than ballots *)
                         size GlobVar.bb  < size GlobVar.rez.`1 
                      \/ (* honest votes were dropped *)
                         !((oflist (lexicographic (map (fun x=> (oget GlobVar.v_ballots.[x]).`2) 
                             (to_seq (dom GlobVar.v_ballots))))) \subset (oflist GlobVar.rez.`1))
                         
                    )
                  )
            );

    return e;

  }

}.

(*--------------------*)
(*    Typechecking    *)
(*--------------------*)
section Definition_Test.

require import Real.

declare module V <: CoreVote_System.
declare module A <: Acc_Adv.

lemma acc_bound &m:
  exists eps,
    Pr [Acc(V,A).main() @ &m: res] <= eps by [].

end section Definition_Test.

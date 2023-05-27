(********************************************************************************)
(***             In this file, model the sElect voting protocol               ***)
(********************************************************************************)

(*--------------------------------------------------*)
(*          Load necessary theories                 *)
(*--------------------------------------------------*)
require import AllCore List Distr SmtMap FinType FSet.
require (*  *) AccountabilityDefinition. 


(*--------------------------------------------------*)
(*                 Preliminaries                    *)
(*--------------------------------------------------*)

type params. (* public parameters: election identifier etc *)
type nonce. (* nonce used for verification *)
type candidate. (* candidate the voters can vote for *)
type ident. (* voter identifier *)
type rand. (* random coins for encryption *)
type ciphertext. (* encrypted vote *)
type signature. (* signature on encrypted votes *)
type spkey. (* signature scheme public key *)
type sskey. (* signature scheme secret key *)
type epkey. (* encryption public key *)
type eskey. (* encryption secret key *)

(* Mixservers encrypt elements of type bitstring *)
(* This is either a plaintext (nonce, candidate) pair *)
(* or a ciphertext                                    *)
type bitstring = [
  |  Hidden of ciphertext
  |  Plain  of (nonce * candidate)
].

(* Conversion from bitstring to ciphertext *)
op bit_to_cip (b: bitstring) =
  with b = Hidden c  => Some c
  with b = Plain  _ => None.

(* Conversion from bitstring to (nonce, candidate) *)
op bit_to_nc (b: bitstring) =
  with b = Hidden c  => None
  with b = Plain nc => Some nc.

(* Instantiate voter state *)
type state = nonce * nonce * candidate
             * rand * ciphertext 
             * rand * ciphertext 
             * rand.

(* All the parties involved in the voting protocol *)
type party = [
  | AuthServer
  | VotingAuthority
  | MixServer  of int
  | Voter      of ident
].

(* Conversion between bitstrings and evidence produced by voters' devices *)
type vsd_evidence = (party*bitstring).
op to_AS_evidence : bitstring -> (ciphertext * signature).
op from_AS_evidence : (ciphertext * signature) -> bitstring.
op to_MS_evidence : bitstring -> (bitstring * rand).
op from_MS_evidence : (bitstring * rand) -> bitstring.

axiom AS_evidence : forall x y, to_AS_evidence(from_AS_evidence (x, y)) = (x,y).
axiom MS_evidence : forall x y, to_MS_evidence(from_MS_evidence (x, y)) = (x,y).


(* Number of voters *)
const n_v : { int | 0 < n_v } as gt0_n_v. 


(* Lossless distribution on nonces *)
op [lossless] dnonce : nonce distr. 

(** Operator for concatenating nonces **)
op (||) : nonce -> nonce -> nonce.
op div : nonce -> nonce * nonce.
axiom concat_div( n1 n2: nonce):
  div (n1 || n2) = (n1, n2).
axiom div_concat n : ((div n).`1 || (div n).`2) = n. 
axiom concat_inj x1 y1 x2 y2: 
	(x1 || y1) = (x2 || y2) => x1 = x2 /\ y1 = y2.


(* Distribution on random coins for encryption *)
op [lossless uniform full] drand : rand distr. 

(* Operators for sorting lists *)
op leq_b  : ciphertext -> ciphertext -> bool. 
op leq_nc : (nonce * candidate) -> (nonce * candidate) -> bool.
op lex (cL : (nonce * candidate) list) : (nonce*candidate) list
= sort leq_nc cL.

axiom leq_b_tri : (forall x y, leq_b x y \/ leq_b y x).
axiom leq_b_tan : (forall y x z, leq_b x y => leq_b y z => leq_b x z).
axiom leq_b_asy : (forall x y, leq_b x y => leq_b y x => x = y).

axiom leq_nc_tri : (forall x y, leq_nc x y \/ leq_nc y x).
axiom leq_nc_tan : (forall y x z, leq_nc x y => leq_nc y z => leq_nc x z).
axiom leq_nc_asy : (forall x y, leq_nc x y => leq_nc y x => x = y).

op is_lex ( cL: ciphertext list): bool
   = (cL = (sort leq_b cL)).

(* Abbreviation of the negation of an element being in a list *)
op (\notin) (z: 'a) (s: 'a list) = !(z \in s).

(* Operator for checking if keys are valid -- this is left abstract *)
op is_valid_pkey (_: epkey): bool.

(* Operator for extracting decryption key from encryption key *)
(* Note: this is only used by bad which is assumed to be comp. unbounded *)
op get_sk: epkey -> eskey.

(* Clone FinType *)
clone include FinType with 
  type t <- ident. 

(* Clone Accountability Definition *)
clone include AccountabilityDefinition with
  type apkey        <- spkey,
  type ident        <- ident,
  type state        <- state,
  type vote         <- nonce * candidate,
  type ballot       <- ciphertext, 
  type signature    <- signature,
  type vsd_evidence <- vsd_evidence,
  type party        <- party,
  type extra_public <- (int, epkey) fmap, 
  type extra_result <- nonce list * ciphertext list * ciphertext list,
  op n              <- n_v,
  op lexicographic  <- lex.

(*----------------------------------------*)
(*  Encryption and decryption operators   *)
(*----------------------------------------*) 
op enc : epkey -> bitstring -> rand -> ciphertext.
op dec : eskey -> ciphertext -> bitstring option.
op sign : sskey -> ciphertext -> rand -> signature.
op verify : spkey -> ciphertext -> signature -> bool.

(* Correctness axiom on encryption scheme *)
axiom enc_dec_correct epk b r : dec (get_sk epk) (enc epk b r) = Some b.  

(*--------------------------------------------------*)
(*            Abstract module for VSD               *)
(*--------------------------------------------------*)
module type VSD = {
  proc nonce_gen() : nonce
}. 


(*--------------------------------------------------*)
(*              Algorithms for sElect               *)
(*    We model the system using three mix servers   *) 
(*--------------------------------------------------*)

module Select(VSD:VSD): CoreVote_System  = {

  (* Voter id votes v *)
  proc vote(id: ident,
            pd: spkey * ((int, epkey) fmap), 
            v: nonce * candidate)
       : state  
         * ciphertext = {


    var n_vsd, n_vot, c, n_fin, alpha0, alpha1, alpha2;
    var r0, r1, r2;
    var st, as_pk;

    var mi_pk: (int, epkey) fmap;

    (n_vot, c)     <- v;
    (as_pk, mi_pk) <- pd;

    (* Generate verification code *)
    n_vsd  <@ VSD.nonce_gen();
    n_fin  <- n_vot || n_vsd;

    r0 <$ drand;
    r1 <$ drand;
    r2 <$ drand;
    
    (* Computed nested encryption of (n_fin, c) *)
    alpha2 <- enc (oget mi_pk.[2]) (Plain (n_fin, c)) r2;
    alpha1 <- enc (oget mi_pk.[1]) (Hidden alpha2) r1;
    alpha0 <- enc (oget mi_pk.[0]) (Hidden alpha1) r0;

    (* voter state *)
    st <- (n_vot, n_vsd, c, r2, alpha2, r1, alpha1, r0);
 
    return (st, alpha0);
  }

  
  (* First mix server *)
  proc mixing_fst ( pd: spkey * ((int, epkey) fmap), 
               esk: eskey, 
               bb: (ciphertext list) option)
       : (ciphertext list) option * party option ={

    var  alphaL, i, blame, out;
    
    if (bb <> None) {
      alphaL <- [];
      i      <- 0;
    
      while (i < size (oget bb)) { 
  
        if (dec esk (nth witness (oget bb) i) <> None){
          alphaL<- alphaL ++ [oget (bit_to_cip (oget (dec esk (nth witness (oget bb) i))))];
        }

        i <- i + 1;
      }

      alphaL <- sort leq_b (undup alphaL);
      blame  <- None;
      out    <- Some alphaL;
    } else {
      out <- None;
      blame <- Some AuthServer;
    }
      return (out, blame);
  }


  (* Mix Server 2 *)
  proc mixing_mid ( pd: spkey * ((int, epkey) fmap), 
               esk: eskey, 
               bb: (ciphertext list) option)
       : (ciphertext list) option * party option ={

    var  alphaL, i, blame, out;
    
    if (bb <> None) {
      alphaL <- [];
      i      <- 0;
    
      while (i < size (oget bb)) { 
  
        if (dec esk (nth witness (oget bb) i) <> None){
          alphaL<- alphaL ++ [oget (bit_to_cip (oget (dec esk (nth witness (oget bb) i))))];
        }

        i <- i + 1;
      }

      alphaL <- sort leq_b (undup alphaL);
      blame  <- None;
      out    <- Some alphaL;
    } else {
      out   <- None;
      blame <- Some (MixServer 0);
    }
      return (out, blame);
  }

  (* Last mix server  *)
  proc mixing_last (pd: spkey * ((int, epkey) fmap), 
               esk: eskey, 
               bb: (ciphertext list) option)
       : ((nonce * candidate) list * nonce list) option * party option  ={

    var ncL, nL, i, nonce, candidate, ncL2, blame, out;
    
    if (bb <> None) {
    
      ncL <- [];
      ncL2 <- [];
      nL  <- [];

      i   <- 0;
      while (i < size (oget bb)) {
       if (dec esk (nth witness (oget bb) i) <> None){
        (nonce, candidate) <- oget (bit_to_nc (oget (dec esk (nth witness (oget bb) i))));
         ncL <- ncL ++ [(nonce,candidate)];
       }
       i <- i + 1;
     }

      ncL <- sort leq_nc (undup ncL); 
      nL <- map (fun (x:nonce*candidate), (div x.`1).`2) ncL;
      ncL2 <- map (fun (x:nonce*candidate), ( (div x.`1).`1, x.`2 )) ncL;
      blame <- None;
      out <- Some (ncL2, nL);
    } else {
      out <- None;
      blame <- Some (MixServer 1);
    }
   
    return (out, blame);
  }

  (* user vsd verification and blame algorithm 
     - pd is trusted 
       //in the sense that it hasn't changed from beginning of election 
     - v is correct
       //voter has decided on this
     - st is correct 
       // honest vsd provides this *)
  proc vsd_verify (pd: spkey * ((int, epkey) fmap),
                   st: state, 
                   v: (nonce * candidate),
                   b: ciphertext, 
                   s: signature, 
                   bb: ciphertext list, 
                   mi: result)
      : vsd_evidence option ={

    var n_vot, n_vsd, n_fin, c, r2, alpha2, r1, alpha1, r0;
    var pl, as_pk, mi_pk, nv, ca, l;
    var l0, l1, l2, nL, fL;

    (as_pk, mi_pk)  <- pd;
    (nv, ca)        <- v;
    (l2, l)         <- mi;
    (nL, l0, l1)        <- l;

    (n_vot, n_vsd, c, r2, alpha2, 
          r1, alpha1, r0) <- st;
      n_fin <- n_vot || n_vsd;

    fL <- map (fun (x:(nonce*candidate)*nonce),  (x.`1.`1 || x.`2, x.`1.`2)) (zip l2 nL);

    pl <- None;
   

    (* Blame Mixnet 2 if vote is deleted when alpha2 is given as input *)
    if (alpha2 \in l1 /\ (n_vot || n_vsd, ca) \notin fL){
      pl <- Some (MixServer 2, from_MS_evidence (Plain (n_fin, ca), r2));
    }

        (* Blame Mixnet 1 if alpha2 is deleted when alpha1 is given as input *)
    if (alpha1 \in l0 /\ alpha2 \notin l1){
      pl <- Some (MixServer 1, from_MS_evidence (Hidden alpha2, r1));
    }
    
   
    (* Blame Mixnet 0 if alpha1 is deleted when alpha0 is given as input *)
    if (b \in bb /\ alpha1 \notin l0){
      pl <- Some (MixServer 0, from_MS_evidence (Hidden alpha1, r0));
    }
        
      (* or ballot not on board blame AS *)
      if (b \notin bb){
        pl <- Some (AuthServer, from_AS_evidence (b, s));
      }

    return pl;
  }

  proc is_valid (pd: spkey * (int, epkey) fmap): bool ={

    var e, i, as_pk, mi_pks;

    (as_pk, mi_pks) <- pd;

    i <- 0;
    e <-    (* ensure all 3 MixServers have valid pks *)
            (* valid key server 0 *)
            mi_pks.[0] <> None /\ is_valid_pkey (oget mi_pks.[0])
         /\ (* valid key server 1 *)
            mi_pks.[1] <> None /\ is_valid_pkey (oget mi_pks.[1])
         /\ (* valid key server 2 *)
            mi_pks.[2] <> None /\ is_valid_pkey (oget mi_pks.[2]);

    return e;
  }

  (* valid board:
     + bb containst at most n ciphertexts
     + each ciphertext is expected length/format - ensured by easycrypt
     + all ciphertexts are unique
     + in lexicographic order *)
  proc valid_board(bb: ciphertext list): bool ={

   var e: bool;

   e <-    size bb <= n_v
        /\ uniq bb
        /\ is_lex bb;

   return e;
  }

  proc judge (pd: spkey * ((int, epkey) fmap), 
                         bb: ciphertext list, 
                         mi: result, 
                         ve:  vsd_evidence list)
      : party option ={

      var m1_out, m2_out, blame, outcome, i, cipher,rand, j, vote, sig, nL, fL;
      var epk, ebb;

      blame <- None;
      nL    <- mi.`2.`1;
      m1_out <- mi.`2.`2;
      m2_out <- mi.`2.`3;
      outcome <- mi.`1;

      fL <- map (fun (x:(nonce*candidate)*nonce),  (x.`1.`1 || x.`2, x.`1.`2)) (zip outcome nL);

      (* Check that public keys for the authentication server and mix servers are well formed *)
      (* If not, then blame the voting authority and abort the election *)
      epk <@ is_valid(pd);
      
      if (!epk) {
        blame <- Some VotingAuthority;
      } else {
      

        (* Check that the board is valid. If not, blame the authentication server *)
        ebb <@ valid_board(bb);
        if (!ebb) {blame <- Some AuthServer;}
    
        (* Check the output of each mix server contains at most as many elements as the mix server received as inputs *)
        if (size bb < size m1_out){ blame <- Some (MixServer 0); }
        if (size m1_out < size m2_out){ blame <- Some (MixServer 1); }
        if (size m2_out < size outcome){ blame <- Some (MixServer 2);}
        if (size nL  <> size outcome){ blame <- Some (MixServer 2);}

        (* Check that outputs are duplicate free and in lexicographic order. *)
        if (!(is_lex m1_out) \/ !(uniq m1_out)) { blame <- Some (MixServer 0); }
        if (!(is_lex m2_out) \/ !(uniq m2_out)) { blame <- Some (MixServer 1); }
        if (!(fL = lex fL) \/ !(uniq fL)) { blame <- Some (MixServer 2); }
    
        (* Check the evidence for any ciphertext and signature pairs,
        if the signatures is valid and ciphertext is not in BB then blame AS. *)
        i <- 0;
        while (i < size (ve)){
          (vote, sig) <- to_AS_evidence (nth witness ve i).`2; 
          (* If we have a signature which is valid but the ballot does not appear in the bb then the AS is to blame *)
          if(verify pd.`1 vote sig /\ vote \notin bb){
            blame <- Some AuthServer;
          }

        i <- i + 1;
      } 
     
        (* Check the evidence for any triple (j,αj+1,rj), if Encpkj (αj+1)
        is in input to the jth mix but αi is not it it’s output blame j+1
          the jth mixer. *)
       i <- 0;
       while (i < size (ve)){
         j <- (nth witness ve i).`1;
         (cipher, rand) <- to_MS_evidence (nth witness ve i).`2;
          if (j = MixServer 0) {
            if (enc (oget pd.`2.[0]) cipher rand \in bb /\ (oget (bit_to_cip cipher) \notin m1_out)){
               blame <- Some (MixServer 0);
            }
          }
          if (j = MixServer 1){
              if (enc (oget pd.`2.[1]) cipher rand \in m1_out /\ (oget (bit_to_cip cipher) \notin m2_out)){
               blame <- Some (MixServer 1);
            }}
          if (j = MixServer 2){
            if (enc (oget pd.`2.[2]) cipher rand \in m2_out /\ oget (bit_to_nc cipher) \notin fL) {
             blame <- Some (MixServer 2);
            }}
            i <- i + 1;
      } 
    }
    return blame; 
  }

  (* Signature verification *)
  proc valid_sig(pp : public_parameters, c:ciphertext, s:signature) ={
      return verify pp.`1 c s;
  }
  


  (* Bad: list of parties blamed, can be empty
     + never blame honest party
     + calc secret key for each mix server based on pkey
     + recomp bb' mixnet info from bb, if deviates blames Mixserver i
     + check all ballots in v_ballots are in bb, if not blame AS 
  *)

  proc bad (pd : public_parameters, 
            bb: ciphertext list, 
            mi: result,  
            vb: (ident, state * (nonce * candidate) * ciphertext) fmap,
            ve: vsd_evidence list)
       : party fset ={
  

    var as_pk, mi_pks, l, l0, l1, l2, i, vote, sig, nL1, epk, ebb;
    var bl0, bl1, bl2;
    var m0o, m1o, m2o;

    var mi_sks: (int, eskey) fmap;
    var pl: party fset;

    pl <- fset0;

    (as_pk, mi_pks) <- pd;
    (l2, l)         <- mi;
    (nL1, l0,l1)         <- l;

    (* compute skey for mixservers *)
    mi_sks <- map (fun x y=> get_sk y) mi_pks;

    (* check that public keys are valid and blame VA if not *)
    epk <@ is_valid((as_pk, mi_pks));
    if (!epk) {pl <- pl `|` (fset1 VotingAuthority);}

    (* check if ballot board is valid and blame AS if not *)
    ebb <@ valid_board(bb);
    if (!ebb) {pl <- pl `|` (fset1 AuthServer);}

    (* for all 3 mix servers recompute the ballot list and info *)
    (m0o, bl0) <@ mixing_fst(pd, oget mi_sks.[0], Some bb);
    (m1o, bl1) <@ mixing_mid(pd, oget mi_sks.[1], Some l0);
    (m2o, bl2) <@ mixing_last(pd, oget mi_sks.[2], Some l1);

    (* Blame Mix Servers if mix output is different *)
    if (l0 <> oget m0o){
      pl <- pl `|` (fset1 (MixServer 0));
    }
    if (l1 <> oget m1o){
      pl <- pl `|` (fset1 (MixServer 1));
    }
    if (l2 <> (oget m2o).`1){
      pl <- pl `|` (fset1 (MixServer 2));
    }
    if ((oget m2o).`2 <> nL1){
      pl <- pl `|` (fset1 (MixServer 2));
    }

 
    (* Blame AS if voter has signed ballot, but ballot not in ballot box *) 
    i <- 0;
    
    (* Check the signatures *)
    while (i < size (ve)){
       (vote,sig) <- to_AS_evidence (nth witness ve i).`2;
        (* If we have a signature which is valid but the ballot does not appear in the bb then the AS is to blame *)
        if (verify pd.`1 vote sig  /\ (vote \notin bb)){
          pl <- pl `|` (fset1 AuthServer);
        }
      i <- i + 1;
    } 
        
    (* return all blamed parties *) 
    return pl;
  }


}.

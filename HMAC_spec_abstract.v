(* This spec was written by Adam Petcher.
Subsequent modifications and proofs are by Katherine Ye and Lennart Beringer. *)

Set Implicit Arguments.


Require Import Bvector.
Require Import List.
Require Import Arith.
Require Import HMAC_spec_list.
Require Import HMAC_common_defs.

Lemma VectorToList_cons A n: forall (a:A) l,
      Vector.to_list (Vector.cons A a n l) =
      cons a (Vector.to_list l).
Proof. intros. reflexivity. Qed. 

Lemma VectorToList_length {A}: forall n (v: Vector.t A n), length (Vector.to_list v) = n.
Proof.
  apply Vector.t_rec. reflexivity.
  intros. rewrite VectorToList_cons. simpl. rewrite H. trivial.
Qed.

Lemma VectorToList_combine A n: forall (a:A) b v1 v2,
     combine (Vector.to_list (Vector.cons A a n v1))
             (Vector.to_list (Vector.cons A b n v2))
   = (a,b) :: combine (Vector.to_list v1) (Vector.to_list v2).
Proof. intros. simpl. f_equal. Qed.
   
Module HMAC_Abstract.

(*Definition Blist := list bool. already in HMAC_common_defs*)

Fixpoint splitVector (A : Set) (n m : nat) :
  Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
  match n with
    | 0 => 
      fun (v : Vector.t A (O + m)) => (@Vector.nil A, v)
    | S n' => 
      fun (v : Vector.t A (S n' + m)) => 
        let (v1, v2) := splitVector _ _ (Vector.tl v) in
          (Vector.cons _ (Vector.hd v) _ v1, v2)
  end.

Section HMAC.

  (* c is the output size, b is the block size (larger than the output size),
     and p is the difference between them *)
  Variable c p : nat.
  Definition b := c + p.
  
  (* The compression function *)
  Variable h : Bvector c -> Bvector b -> Bvector c.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Bvector c.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star (k : Bvector c) (m : list (Bvector b)) : Bvector c :=
    fold_left h m k.

  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words : list (Bvector b) -> Bvector c :=
    h_star iv.

  Variable splitAndPad : Blist -> list (Bvector b).
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.
  
  Variable fpad : Bvector c -> Bvector p. 
  Definition app_fpad (x : Bvector c) : Bvector b :=
    (Vector.append x (fpad x)).

  Definition h_star_pad (k : Bvector c) (x : list (Bvector b)) : Bvector b :=
    app_fpad (h_star k x).

  Definition GNMAC (k : Bvector (c + c)) (m : list (Bvector b)) : Bvector c :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Bvector (b + b)) (m : list (Bvector b)) : Bvector c :=
    let (k_Out, k_In) := splitVector b b k in
      let h_in := (hash_words (k_In :: m)) in 
        hash_words (k_Out :: (app_fpad h_in) :: nil).
  
  Definition HMAC_2K (k : Bvector (b + b)) (m : Blist) : Bvector c :=
    GHMAC_2K k (splitAndPad m).

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Bvector b.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Bvector b) : list (Bvector b) -> Bvector c :=
    GHMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

  Definition HMAC (k : Bvector b) : Blist -> Bvector c :=
    HMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

End HMAC.

End HMAC_Abstract.




(* Can't directly prove equality here, just equivalence via length preservation.

-----

1. 
Prove the following functions are equivalent when Vector is converted to List:

Rewritten functions:
Vector.append ~ ++
BVxor ~ BLxor
splitVector ~ splitList

TODO: May need to admit the equivalence of these three functions.
Need more lemmas that relate vectors and lists.

Functions changed mostly just in type:
h_star <-- correct if h is
hash_words <-- correct if h_star is
app_fpad <-- correct if ++ and fpad are 
h_star_pad (not used in HMAC)
GNMAC (not used in HMAC)
GHMAC (not used in HMAC)
GHMAC_2K <-- correct if splitList, app_fpad, and hash_words are 
HMAC_2K <-- correct if GHMAC_2K and splitAndPad are 
HMAC <-- correct if HMAC_2K, BLxor, and ++ are 

TODO: does this compose correctly if the three functions above are admitted?

Primitives: BLxor, ++, splitList, splitAndPad, h, app_fpad (and the constants)

Let f_l ~. f_v := 
    l ~ v -> f_l l ~ f_v v
(function equivalence given input equivalence)
where l ~ v :=
      l = Vector.to_list v.

-----

2. Prove that the given parameters (e.g. fpad) have the right type. Correctness isn't needed; there's no vector specification to check the list version against.

> For all parameters, prove that given an input of the right size, they will give an output of the right size. Then, prove that the initial input is of the right size. 

constants: c, p, iv, opad, ipad
functions: h, splitAndPad, fpad

-----

This should be informally equal to HMAC_Abstract, though I don't think there is a formal way to do and check module equivalence in Coq. *)


Theorem xor_eq' : forall (n : nat) (v1 v2 : Bvector n),
                   BLxor (Vector.to_list v1) (Vector.to_list v2) = 
                   Vector.to_list (BVxor n v1 v2).
Proof.
  eapply Vector.rect2.
  reflexivity.
  intros. simpl. rewrite (VectorToList_cons (xorb a b)).
   rewrite <- H. clear H. unfold BLxor. 
   rewrite VectorToList_combine. reflexivity.
Qed. 

Theorem xor_eq : forall (n : nat) (v1 v2 : Bvector n) (l1 l2 : Blist),
                   l1 = Vector.to_list v1 ->
                   l2 = Vector.to_list v2 ->
                   BLxor l1 l2 = Vector.to_list (BVxor n v1 v2).
Proof. intros; subst. apply xor_eq'. Qed.

Theorem app_eq' : forall (m:nat) (v2:Bvector m) (n : nat) (v1 : Bvector n),
                   (Vector.to_list v1) ++ (Vector.to_list v2) = 
                   Vector.to_list (Vector.append v1 v2).
Proof. intros m v2.
  eapply Vector.t_rec.
  reflexivity.
  intros. simpl. rewrite (VectorToList_cons h). f_equal. rewrite <- H. f_equal.
Qed.

Theorem app_eq : forall (n : nat) (v1 v2 : Bvector n),
                   (Vector.to_list v1) ++ (Vector.to_list v2) = 
                   Vector.to_list (Vector.append v1 v2).
Proof.
  intros. apply app_eq'.
Qed. (*
Check HMAC_Abstract.splitVector.
Definition sV (n m k:nat) (NM: k = n+m) (v:Bvector k) : Bvector n * Bvector m.
 subst k.
 apply (@HMAC_Abstract.splitVector bool n m v).
Defined.
Definition myP: forall (k : nat) (v:Vector.t bool k), Type.
intros.
apply (forall n m (NM: k=n+m), 
                   splitList n (Vector.to_list v) = match sV _ _ NM v with (L,R) =>
                     (Vector.to_list L,
                      Vector.to_list R) end).
Defined.

Theorem split_eq : forall (k : nat) (v : Bvector k) n m (NM:k=n+m),
                   splitList n (Vector.to_list v) = match sV _ _ NM v with (L,R) =>
                     (Vector.to_list L,
                      Vector.to_list R) end.
Proof. intros n m.
 apply (Vector.t_rect bool myP); unfold myP, sV; intros.
   assert (n0 = 0 /\ m0 = 0). eapply plus_is_O. rewrite <- NM; trivial.
   destruct H. subst n0 m0. simpl. unfold eq_rec_r, eq_rec, eq_rect. simpl.
    remember (eq_sym NM). destruct e. in (_ = y) return (Bvector y -> Bvector 0 * Bvector 0)). 
   simpl. 
  apply H.
 Check (@Vector.t_rec bool). eapply (@Vector.t_rec bool).
Print Vector.
 intros k v.
  eapply Vector.t_rec. 3: eassumption.
  intros n. induction n. reflexivity. 
  unfold Bvector. 
  intros m v. assert (S n + m = S (n+m)) by omega. rewrite H in v. rewrite Sn_plus. 
apply Vector.caseS. intros. unfold splitList. simpl. Print Vector. caseS. destruct v.
Print splitList.
Theorem split_eq : forall (k : nat) (v : Bvector k) n m (NM:k=n+m) (v1: Bvector n),
                   splitList n (Vector.to_list v) =
                     (Vector.to_list (fst (HMAC_Abstract.splitVector n m v1)),
                      Vector.to_list (snd (HMAC_Abstract.splitVector n m v2))).
Proof.
  intros n. induction n. reflexivity. 
  unfold Bvector. 
  intros m v. assert (S n + m = S (n+m)) by omega. rewrite H in v. rewrite Sn_plus. 
apply Vector.caseS. intros. unfold splitList. simpl. Print Vector. caseS. destruct v.
Print splitList.

Theorem split_eq : forall (n m : nat) (v : Bvector (n + m)),
                   splitList n (Vector.to_list v) =
                     (Vector.to_list (fst (HMAC_Abstract.splitVector n m v)),
                      Vector.to_list (snd (HMAC_Abstract.splitVector n m v))).
Proof.
  intros n. induction n. reflexivity. 
  unfold Bvector. 
  intros m v. assert (S n + m = S (n+m)) by omega. rewrite H in v. rewrite Sn_plus. 
apply Vector.caseS. intros. unfold splitList. simpl. Print Vector. caseS. destruct v.
Print splitList.
Lemma X {A}: forall n (l:list A), 
  splitList (S n) l = match splitList n l with (x,y::t) => (x ++ (y::nil), t) | _ => end.
  unfold splitList.
  apply Vector.t_rec. simpl. reflexivity.
  Defintion myP: forall k, Bvector k -> 
Theorem split_eq : forall (n m : nat) (v : Bvector (n + m)),
                   splitList n (Vector.to_list v) =
                     (Vector.to_list (fst (HMAC_Abstract.splitVector n m v)),
                      Vector.to_list (snd (HMAC_Abstract.splitVector n m v))).
Proof.
  intros n m v. 
  eapply (Vector.t_rec bool). Focus 3.
  split.
  * 
    unfold splitList.
    unfold HMAC_Abstract.splitVector.
    simpl.

Admitted.
Theorem split_eq : forall (n m : nat) (v : Bvector (n + m)),
                     fst (splitList n (Vector.to_list v)) =
                     Vector.to_list (fst (HMAC_Abstract.splitVector n m v))
                     /\
                     snd (splitList n (Vector.to_list v)) =
                     Vector.to_list (snd (HMAC_Abstract.splitVector n m v)).
Proof.
  intros n m v l vl_eq.
  split.
  * 
    unfold splitList.
    unfold HMAC_Abstract.splitVector.
    simpl.

Admitted.
Theorem split_eq : forall (n m : nat) (v : Bvector (n + m)) (l : Blist),
                     l = Vector.to_list v ->
                     fst (splitList n l) =
                     Vector.to_list (fst (HMAC_Abstract.splitVector n m v))
                     /\
                     snd (splitList n l) =
                     Vector.to_list (snd (HMAC_Abstract.splitVector n m v)).
Proof.
  intros n m v l vl_eq.
  split.
  * 
    unfold splitList.
    unfold HMAC_Abstract.splitVector.
    simpl.

Admitted.
*)

(* TODO: will prove that the list equivalents have this type *)
Parameter h_v : Bvector c -> Bvector b -> Bvector c.
Parameter iv_v : Bvector c.
Parameter splitAndPad_v : Blist -> list (Bvector b).
Parameter fpad_v : Bvector c -> Bvector p. 
Parameter opad_v ipad_v : Bvector b.

(* TODO: prove fpad has right type *)
Lemma fpad_eq : forall (v : Bvector c) (l : Blist),
                  l = Vector.to_list v ->
                  fpad l = Vector.to_list (fpad_v v).
Proof.
  intros v l inputs_eq.
Admitted.  

Lemma app_fpad_eq : forall (v : Bvector c) (l : Blist),
                      l = Vector.to_list v ->
                      HMAC_List.app_fpad fpad l =
                      Vector.to_list (HMAC_Abstract.app_fpad fpad_v v).
Proof.
  intros v l inputs_eq.
  subst.
  unfold HMAC_List.app_fpad. unfold HMAC_Abstract.app_fpad. 
  rewrite <- app_eq. erewrite fpad_eq; reflexivity. 
Qed.     

(* iv *)
Lemma iv_eq : sha_iv = Vector.to_list iv_v.
Proof. Admitted.

(* h *)
Lemma h_eq : forall (block_v : Bvector b) (block_l : Blist),
               block_l = Vector.to_list block_v ->
               sha_h sha_iv block_l = Vector.to_list (h_v iv_v block_v).
Proof.
  intros block_v block_l blocks_eq.
  pose proof iv_eq as iv_eq.
  subst.
  rewrite -> iv_eq.
  
Admitted.

Check HMAC_Abstract.h_star.

(* also h_star *)
Lemma hash_words_eq : forall (v : list (Bvector b)) (l : list Blist),
                        (* TODO: figure out how to state equivalence between v and l *)
                      (*l = Vector.to_list v -> *)
                      HMAC_List.hash_words sha_h sha_iv l =
                      Vector.to_list (HMAC_Abstract.hash_words p h_v iv_v v).
Proof.
  (*apply (Vector.t_rec bool).*)
  intros v l. (* inputs_eq.*)
  unfold HMAC_List.hash_words. unfold HMAC_Abstract.hash_words.
  unfold HMAC_List.h_star. unfold HMAC_Abstract.h_star.
  generalize dependent v.
(*  eapply (Vector.t_rec bool).*)
  induction l as [ | bl bls].
  *
    admit.
  *
    intros v. generalize dependent bl.
    generalize dependent bls. induction v as [| bv bvs].
    -
      intros.
      simpl.
      admit.
    - intros.
      simpl.
      (* apply IHbls. *)
      (* TODO order of params? *)
      (* TODO each element of v and l are equal, and the lists themselves are the same length *)
      (* TODO should be able to use h_eq *)
      admit.
Qed.   

Lemma SPLIT: forall m (v2 : Bvector m) n (v1 : Bvector n),
      HMAC_Abstract.splitVector n m (Vector.append v1 v2)  = (v1, v2).
Proof.
  intros m v2.
  eapply Vector.t_rec.
  reflexivity.
  intros. simpl. rewrite H. trivial.
Qed.

(* TODO: opad and ipad should be in HMAC_common_parameters (factor out of all spec) *)
Theorem HMAC_eq : forall (kv : Bvector b) (kl m op ip : Blist),
                    kl = Vector.to_list kv ->
                    HMAC_List.HMAC c p sha_h sha_iv sha_splitandpad_blocks fpad op ip kl m
                    = Vector.to_list
                        (HMAC_Abstract.HMAC h_v iv_v splitAndPad_v
                                            fpad_v opad_v ipad_v kv m).
Proof.
  intros kv kl m op ip keys_eq.
  unfold HMAC_List.HMAC. unfold HMAC_Abstract.HMAC.
  unfold HMAC_List.HMAC_2K. unfold HMAC_Abstract.HMAC_2K.
  unfold HMAC_List.GHMAC_2K. unfold HMAC_Abstract.GHMAC_2K.
  subst.
  rewrite SPLIT.
  apply hash_words_eq.
Qed.  





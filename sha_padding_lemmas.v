Require Import pure_lemmas.
Require Import Coqlib.
Require Import Integers.
(* Require Import HMAC_spec_harvard_concat. *)
Require Import SHA256.
Require Import functional_prog.

(* Lemma 1: M = Prefix(Pad(M)) *)

Inductive Prefix {X : Type} : list X -> list X -> Prop :=
  | p_nil : forall (l : list X), Prefix [] l
  | p_self : forall (l : list X), Prefix l l
  | p_cons : forall (l1 l2 : list X) (x : X), Prefix l1 l2 -> Prefix (x :: l1) (x :: l2)
  | p_append : forall (l1 l2 : list X) (l3 : list X), Prefix l1 l2 -> Prefix l1 (l2 ++ l3).
  (* | p_trans : forall (l1 l2 l3 : list X), Prefix l1 l2 -> Prefix l2 l3 -> Prefix l1 l2. *)

(* TODO: replace InWords with InBlocks 4? *)
Inductive InWords : list Z -> Prop :=
  | words_nil : InWords []
  | words_word : forall (a b c d : Z) (msg : list Z),
                   InWords msg -> InWords (a :: b :: c :: d :: msg).

(* *** New definition for this lemma. *)
Definition pad (msg : list Z) : list Z := 
  let n := Zlength msg in
  msg ++ [128%Z] 
      ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0
      ++ intlist_to_Zlist ([Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]).

Definition generate_and_pad' (msg : list Z) : list int :=
  Zlist_to_intlist (pad msg).

(* TODO: total_pad_len_Zlist  *)
Inductive InBlocks {A : Type} (n : nat) : list A -> Prop :=
  | list_nil : InBlocks n []
  | list_block : forall (front back full : list A),
                   length front = n ->
                   full = front ++ back ->
                   InBlocks n back ->
                   InBlocks n full. 

(* ----------------- ^ Definitions *)
(*
Check NPeano.divide.
Print NPeano.divide.
Check list_repeat.
Print list_repeat.
*)

Lemma fstpad_len :
  forall (msg : list Z),
    Datatypes.length (msg ++ [128]
                 ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0)
= (Datatypes.length msg + (S (Z.to_nat (- (Zlength msg + 9) mod 64))))%nat.
Proof.
  intros msg.
  simpl.
  SearchAbout length.
  rewrite -> app_length.
  simpl.
  SearchAbout list_repeat.
  rewrite -> length_list_repeat.
  reflexivity.
Qed.  

Lemma InWords_len4 : forall (l : list Z),
                       NPeano.divide (Z.to_nat WORD) (length l) -> InWords l.
Proof.
  intros l [x H].
  revert l H.
  induction x.
  intros l H. simpl in H. 
  destruct l.
    apply words_nil.
    simpl in H. inversion H.
  intros l H.
  destruct l as [ | a [ | b [ | c [ | d ? ]]]].
    inversion H.
    inversion H.
    inversion H.
    inversion H.
    specialize (IHx l).
      apply words_word.
      apply IHx.
      simpl in H. inversion H.
      simpl. apply H1.
Qed.  

Lemma InBlocks_len : forall {A : Type} (l : list A) (n : nat),
                       NPeano.divide (n) (length l) -> InBlocks n l.
Proof.
  intros A l n div.
  destruct div.
  revert A l n H.
  induction x; intros; simpl in *.
  -
    admit.
  -
    Print InBlocks.

    (* apply list_block. *)

Admitted.

(*
Print NPeano.div.
Print NPeano.divide.
SearchAbout NPeano.divide.
*)


(* TODO: clear out the SearchAbouts / clean up proof *)
Lemma pad_len_64_mod : forall (msg : list Z), 
                           (Zlength (pad msg)) mod 64 = 0.
Proof.
  intros msg.
  unfold pad.
  rewrite -> Zlength_correct.
  repeat rewrite -> app_length.
  simpl.
  assert (succ: forall (n : nat), S n = (n + 1)%nat).
    intros. induction n. reflexivity. omega.
  rewrite -> succ.
  assert ((length msg +
      (length (list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0%Z) + 8 +
       1))%nat = (length msg +
      (length (list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0%Z) + 9))%nat) by omega.
  rewrite -> H. clear H.

  SearchAbout generate_and_pad.
  rewrite -> Zlength_correct.
  rewrite -> length_list_repeat.

  SearchAbout Z.of_nat.
  SearchAbout (Z.of_nat (_ + _)).
  repeat rewrite -> Nat2Z.inj_add.
  SearchAbout (Z.of_nat (Z.to_nat _)).
  rewrite -> Z2Nat.id.

  assert (move : forall (a b c : Z), a + (b + c) = (a + c) + b).
  intros. omega.

  rewrite -> move.
  SearchAbout (_ + (_ mod _)).
  rewrite -> Zplus_mod_idemp_r.

  SearchAbout (_ + (Z.of_nat _)).
  assert (Z_9 : 9 = Z.of_nat (9%nat)). reflexivity.
  rewrite -> Z_9.

  repeat rewrite <- Nat2Z.inj_add.
  
  assert (forall (x : Z), x + (-x) = 0). intros. omega.

  rewrite -> H.
  reflexivity.

  *
    SearchAbout (0 <= _ mod _).
    apply Z.mod_pos_bound.
    omega.
Qed.

SearchAbout roundup.

(* more usable versions *)
Lemma pad_len_64 : forall (msg : list Z), exists (n : Z),
                           Zlength (pad msg) = 64 * n /\ n >= 0.
Proof.
  intros msg.
  pose proof pad_len_64_mod msg as pad_len_mod.

  SearchAbout (_ mod _).
  rewrite -> Zmod_divides in *.

  destruct pad_len_mod.
  exists x.
  split.
  apply H.

  *
    admit.
  (* TODO x >= 0 -- true? necessary? 
     a >= 0 -> b > 0 -> a mod b = 0 -> exists c, a = b * c, c >= 0
     by contradiction: already know exists c, a = b * c (c of any sign)
     if c were negative, then exactly one of a or b would have to be negative
 *)
  * omega.
Qed.

Lemma pad_len_64_nat : forall (msg : list Z), exists (n : nat),
                           (length (pad msg))%nat = (64 * n)%nat.
Proof.
  intros msg.
  pose proof pad_len_64 msg as pad_len_64.

  rewrite -> Zlength_correct in *.
  destruct pad_len_64.
  exists (Z.to_nat x).
  destruct H.

  assert (app_each : Z.to_nat (Z.of_nat (length (pad msg))) = Z.to_nat (64 * x)).
    rewrite -> H. reflexivity.

  SearchAbout (Z.to_nat (Z.of_nat _)).

  rewrite -> Nat2Z.id in app_each.

  rewrite -> app_each.
  SearchAbout (Z.to_nat (_ * _)).
  rewrite -> Z2Nat.inj_mul.
  assert (n_64 : Z.to_nat 64 = 64%nat). reflexivity.

  rewrite -> n_64.
  reflexivity.

  * omega.
  * omega.
Qed.

Lemma total_pad_len_Zlist : forall (msg : list Z), exists (n : nat),
     length
       (msg ++ [128] ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0)
     =  (n * Z.to_nat WORD (* 4 *))%nat.
Proof.
  intros msg.
  pose proof pad_len_64_nat msg as pad_len_64_nat.

  unfold pad in *.
  repeat rewrite -> app_length in *.
  destruct pad_len_64_nat.
  assert (sym: (64 * x)%nat = (x * 64)%nat) by omega.
  rewrite -> sym in *. clear sym.

  simpl in *.
  assert (Pos.to_nat 4 = 4%nat) by reflexivity.
  rewrite -> H0. clear H0.

  rewrite -> length_list_repeat in *.

  assert (add_both: (length msg + S (Z.to_nat (- (Zlength msg + 9) mod 64) ))%nat =
      (x * 64 - 8)%nat) by omega. clear H.
  
  rewrite -> add_both.
  assert ((x * 64 - 8)%nat = (4 * (16 * x - 2))%nat) by omega.

  rewrite -> H.
  exists (16 * x - 2)%nat.
  omega.
Qed.

Lemma total_pad_len_Zlist' : forall (msg : list Z), 
     length
       (msg ++ [128] ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0)
     = (
         (NPeano.div (Z.to_nat (Zlength msg) + 8) 4%nat + 14%nat)
          * Z.to_nat WORD
     )%nat.
Proof.
  intros msg.
  repeat rewrite -> fstpad_len.
  replace (S (Z.to_nat (- (Zlength msg + 9) mod 64)))
    with (1 + (Z.to_nat (- (Zlength msg + 9) mod 64)))%nat by omega.
  
  (* simpl. *)
  (* TODO *)

Admitted.

Lemma pad_inwords :
  forall (msg : list Z),
    InWords (msg ++ [128]
                 ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0).
Proof.
  intros msg.
  apply InWords_len4.
  pose proof total_pad_len_Zlist.
  specialize (H msg).
  unfold NPeano.divide.
  apply H.
Qed.  

Definition fulllen (len : Z) :=
  len + 1%Z + (- (len + 9) mod 64).

Eval compute in fulllen 0.      (* 56 / 4 = 14 32-bit ints;
                                   56 + 8 = 64 bytes;
                                   64 / 4 = 16 32-bit ints;
                                   16 * 32 = 512 bits; 512 / 256 = 2 blocks of length 256 *)
Eval compute in fulllen 1.      (* 56 / 4 = 14 *)
Eval compute in fulllen 2.      (* 56 / 4 = 14 *)
Eval compute in fulllen 55.      (* 56 / 4 = 14 *)
Eval compute in fulllen 56.      (* 120 / 4 = 30 *)
Eval compute in fulllen 119.     (* 120 *)
Eval compute in fulllen 120.    (* 184 *)
Eval compute in fulllen 121.
Eval compute in fulllen 200.    (* 248 + 8 = 256 *)

Eval compute in (-1) mod 5.
(* SearchAbout modulo. *)
(* SearchAbout mod. *)

(* C-c C-l *)
SearchAbout Zlist_to_intlist.

Lemma app_left : forall (a b c d : list Z),
   a ++ b ++ c ++ d = (a ++ b ++ c) ++ d.
(* a ++ (b ++ (c ++ d)) = (a ++ (b ++ c)) ++ d *)
Proof.
   intros a b c d.
   assert (b ++ (c ++ d) = (b ++ c) ++ d) as assert1.
     rewrite -> app_assoc. reflexivity.
   rewrite -> assert1.
   rewrite -> app_assoc.
   reflexivity.
Qed.

(* can use extensionality *)
Theorem pad_compose_equal : forall (msg : list Z),
                              generate_and_pad' msg = generate_and_pad msg.
Proof.
  intros msg.
  unfold generate_and_pad'.
  unfold pad.
  unfold generate_and_pad.
  (* need il => ZIL (IZL il), and
     ZIL a ++ Zil b = ZIL (a ++ b) (with length a being a multiple of 4)
   *)
  pose proof pad_inwords as pad_inwords.
  specialize (pad_inwords msg).
  rewrite -> app_left.
  induction pad_inwords.
  (* case none *)
    assert (forall l : list Z, [] ++ l = l) as Happend. reflexivity.
    specialize (Happend (intlist_to_Zlist
        [Int.repr (Zlength msg * 8 / Int.modulus),
        Int.repr (Zlength msg * 8)])).
    rewrite -> Happend.
    rewrite -> intlist_to_Zlist_to_intlist.
    reflexivity.
  (* case a :: b :: c :: d :: msg0 *)
    Opaque intlist_to_Zlist.
    simpl.
    apply f_equal.
    apply IHpad_inwords.
Qed.    

(* Proof easy with pad definition *)
Theorem prefix : forall (msg : list Z),
                   Prefix msg (pad msg).
Proof.
  intros msg.
  unfold pad.
  apply p_append.
  apply p_self.
Qed.  
  
  
(* ------------------------------------------------ *)

(* Lemma 2: |M1| = |M2| -> |Pad(M1)| = |Pad(M2)| *)

Print NPeano.divide.
Print NPeano.div.
Check NPeano.div.
              
Theorem length_equal_pad_length : forall (msg1 : list Z) (msg2 : list Z),
     Zlength msg1  = Zlength msg2 ->
     Zlength (generate_and_pad msg1) = Zlength (generate_and_pad msg2).
Proof.
  intros m1 m2 H.
  repeat rewrite -> functional_prog.length_generate_and_pad.
  rewrite -> H.
  reflexivity.
Qed.  

(* ------------------------------------------------ *)

(* Lemma 3: |M1| =/= |M2| ->
last block of Pad(M1) =/= last block of Pad(M2) 

or, if one-to-one property is desired (for HMAC), only need to prove that
the padded messages differ
*)

Definition generate_and_pad_copy msg := 
  let n := Zlength msg in
   Zlist_to_intlist (msg ++ [128%Z] 
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0)
           ++ [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)].

(* Probably easier to use the rewritten version; already "proved"
 that that's in blocks of 4 *)

Theorem length_differ_pad_differ : forall (m1 m2 : list Z),
                                     Zlength m1 <> Zlength m2 ->
                                     generate_and_pad m1 <> generate_and_pad m2.
Proof.
  intros m1 m2 len_diff.
  unfold generate_and_pad.
  
  
  SearchAbout ( _ <> _).
  
Admitted.

(* TODO prove equivalent to above *)
Theorem contrapositive_gap : forall (m1 m2 : list Z),
                                     generate_and_pad m1 = generate_and_pad m2 ->
                                     Zlength m1 = Zlength m2.

Proof.
  intros m1 m2 gap_eq.
  unfold generate_and_pad in *.
  
  
Admitted.


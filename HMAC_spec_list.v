Set Implicit Arguments.


Require Import Bvector.
Require Import List.
Require Import HMAC_common_defs.
Require Import Arith.
Require Import HMAC_spec_concat.
Require Import ByteBitRelations.
Require Import sha_padding_lemmas.

Module HMAC_List.

Section HMAC.

  Variable c p : nat.
  Definition b := c + p.
  
  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (Blist)) :=
    fold_left h m k.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Variable splitAndPad : Blist -> list (Blist).
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  (* fpad can be a constant *)
  Variable fpad : Blist -> Blist. 
  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad x.

  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  Definition GNMAC k m :=
    let (k_Out, k_In) := splitList c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b k in
      let h_in := (hash_words (k_In :: m)) in 
        hash_words (k_Out :: (app_fpad h_in) :: nil).
  
  Definition HMAC_2K (k : Blist) (m : Blist) :=
    GHMAC_2K k (splitAndPad m).

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Blist.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Blist) :=
    GHMAC_2K (BLxor k opad ++ BLxor k ipad).

  Definition HMAC (k : Blist) :=
    HMAC_2K (BLxor k opad ++ BLxor k ipad).

End HMAC.

End HMAC_List.

Require Import SHA256.

Function toBlocks (l : Blist) {measure length l} : list Blist :=
  match l with
    | nil => nil
    | _ :: _ => firstn 512 l :: toBlocks (skipn 512 l)
  end.
Proof.
  intros.
  rewrite -> skipn_length.
  assert (Hlen : forall {A : Type} (l : list A), length l >= 0%nat).
      intros. destruct l0; simpl. omega. omega.
  specialize (Hlen bool (b :: l0)).
  destruct Hlen.
  simpl.
  
  
Admitted.

Definition sha_splitandpad_blocks (msg : Blist) : list Blist :=
  toBlocks (sha_splitandpad_inc msg).

Definition sha_splitandpad_inc' (msg : Blist) : Blist :=
  concat (sha_splitandpad_blocks msg).

(* TODO can use either toBlocks or toBlocks' *)
Lemma concat_toBlocks_id : forall (l : Blist),
                             InBlocks 512 l ->
                             concat (toBlocks l) = l.
Proof.
  intros l len.
  unfold concat.
  induction len.

  * rewrite -> toBlocks_equation. reflexivity.
  *
    rewrite -> toBlocks_equation.
    rewrite -> H0.
    rewrite -> firstn_exact. rewrite -> skipn_exact.
    rewrite -> length_not_emp.
    simpl.
    rewrite -> IHlen.
    unfold id.
    reflexivity.
  -
    rewrite -> app_length. rewrite -> H. omega.
  - apply H.
  - apply H.
Qed.

(* since sha_splitandpad_inc is used instead of the modified version in the Concat-Pad proof *)
(* TODO: go through and verify that all the proofs chain *)
Lemma sha_splitandpad_inc_eq : forall (msg : Blist),
                                 True ->
                                 sha_splitandpad_inc msg = sha_splitandpad_inc' msg.
Proof.
  intros msg msg_blocks.
  unfold sha_splitandpad_inc'. unfold sha_splitandpad_blocks.
  symmetry.
  apply concat_toBlocks_id.
  apply msg_blocks.
Qed.  

Theorem fold_hash_blocks_eq_ind : forall (l : list Blist) (iv : Blist),
                                    Forall (fun x => length x = 512%nat) l ->
                                    fold_left sha_h l iv =
                                    hash_blocks_bits sha_h iv (concat l).
Proof.
  intros l.
  induction l as [ | l ls]; intros iv len_l.

  * simpl. reflexivity.
  *
    rewrite -> Forall_forall in len_l.
    Opaque firstn. Opaque skipn.  simpl.
    unfold id.
    rewrite hash_blocks_bits_equation.    
    rewrite -> firstn_exact. rewrite -> skipn_exact.
    rewrite -> length_not_emp.
    apply IHls.
    apply Forall_forall; intros.
    apply len_l.
    apply in_cons.
    apply H.
    
  -
    rewrite -> app_length.

    assert (length l = 512%nat). apply len_l. unfold In. auto.
    rewrite -> H.
    assert (Hlen : forall {A : Type} (l : list A), length l >= 0%nat).
      intros. destruct l0; simpl. omega. omega.
    specialize (Hlen Blist ls).
    omega.

  - apply len_l. unfold In. auto.

  - apply len_l. unfold In. auto.
Qed.


Lemma fpad_list_concat_eq :
  HMAC_List.app_fpad = HMAC_Concat.app_fpad.
Proof. reflexivity. Qed.

Theorem HMAC_list_concat : forall (k m : Blist) (op ip : Blist),
                             (* assumption on length m? TODO *)
                             length k = b ->
                             True ->
                             length op = b ->
                             length ip = b ->
  HMAC_List.HMAC c p sha_h sha_iv sha_splitandpad_blocks fpad op ip k m =
  (* Note use of sha_splitandpad_blocks and sha_splitandpad_inc' (= concat the blocks) *)
  HMAC_Concat.HMAC c p sha_h sha_iv sha_splitandpad_inc' fpad op ip k m.
Proof.
  intros k m op ip k_len m_len op_len ip_len.
  unfold c, p in *. simpl in *.
  unfold HMAC_List.HMAC. unfold HMAC_Concat.HMAC.
  unfold HMAC_List.HMAC_2K. unfold HMAC_Concat.HMAC_2K.
  unfold HMAC_List.GHMAC_2K. unfold HMAC_Concat.GHMAC_2K.

  repeat rewrite -> split_append_id.
  unfold HMAC_List.hash_words. unfold HMAC_Concat.hash_words.
  rewrite -> fpad_list_concat_eq.

  unfold HMAC_List.h_star.
  unfold HMAC_Concat.h_star.

  unfold sha_splitandpad_inc'.
  Check fold_hash_blocks_eq.
  rewrite <- fold_hash_blocks_eq. (* important *)
  assert (forall (l1 l2 : Blist), l1 ++ l2 = l1 ++ concat (l2 :: nil)) as create_concat.
    intros. unfold concat. simpl.
    rewrite -> app_nil_r. reflexivity.

  rewrite -> create_concat.
  rewrite <- fold_hash_blocks_eq. (* again *)
  reflexivity.

  * apply BLxor_length. apply k_len. apply op_len.
  * admit.
  * apply BLxor_length. apply k_len. apply ip_len.
  * admit.
  * apply BLxor_length. apply k_len. apply op_len.
  * apply BLxor_length. apply k_len. apply ip_len.
  * apply BLxor_length. apply k_len. apply op_len.
  * apply BLxor_length. apply k_len. apply ip_len.
Qed.  

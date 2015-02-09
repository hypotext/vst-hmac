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
    | _ :: _ => if leb (length l) 511 then [firstn 512 l] 
                else firstn 512 l :: toBlocks (skipn 512 l)
  end.
Proof.
  intros. subst. remember (b :: l0) as l. clear Heql.
  apply leb_complete_conv in teq0.
  rewrite skipn_length; omega.
Qed.
(*Function toBlocks (l : Blist) {measure length l} : list Blist :=
  match l with
    | nil => nil
    | _ :: _ => firstn 512 l :: toBlocks (skipn 512 l)
  end.
Proof.
  intros. subst. SearchAbout skipn length.
  assert (skip : length (skipn 512 (b :: l0)) <= length l0).
  
  unfold skipn.
  SearchAbout skipn.
    
  (* rewrite -> skipn_length. *)
  (* assert (Hlen : forall {A : Type} (l : list A), length l >= 0%nat). *)
  (*     intros. destruct l0; simpl. omega. omega. *)
  (* specialize (Hlen bool (b :: l0)). *)
  (* destruct Hlen. *)
  (* simpl. *)
  
  
Admitted.
*)
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
    destruct full. 
      assert (@length bool nil = length (front ++ back)). rewrite <- H0; reflexivity. 
      rewrite app_length, H in H1. remember (length back). clear - H1. rewrite plus_comm in H1. simpl in H1. omega.
    rewrite H0, app_length, H, leb_correct_conv. 2: omega.
    rewrite -> firstn_exact; trivial.
    rewrite -> skipn_exact; trivial.
    (*rewrite -> length_not_emp.*)
    simpl.
    rewrite -> IHlen.
    unfold id.
    reflexivity.
Qed.
(*
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
*)

(* since sha_splitandpad_inc is used instead of the modified version in the Concat-Pad proof *)
(* TODO: go through and verify that all the proofs chain *)
Lemma sha_splitandpad_inc_eq : forall (msg : Blist),
                                 sha_splitandpad_inc msg = sha_splitandpad_inc' msg.
Proof.
  intros msg.
  unfold sha_splitandpad_inc'. unfold sha_splitandpad_blocks.
  symmetry.
  apply concat_toBlocks_id.
  * (* InBlocks 512 (sha_splitandpad_inc msg) *)
    admit.

Qed.  

Lemma len_min : forall {A : Type} (l : list A), length l >= 0%nat.
Proof. intros. destruct l; simpl. omega. omega. Qed.

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
    specialize (len_min ls).
    omega.

  - apply len_l. unfold In. auto.

  - apply len_l. unfold In. auto.
Qed.

Theorem fold_hash_blocks_eq : forall (l : Blist) (ls : list Blist),
                                length l = 512%nat ->
                                Forall (fun x => length x = 512%nat) ls ->
                                fold_left sha_h (l :: ls) sha_iv =
                                hash_blocks_bits sha_h sha_iv (l ++ concat ls).
Proof.
  intros l ls len_l len_ls.
  pose proof fold_hash_blocks_eq_ind as fold_ind.
  simpl.
  rewrite hash_blocks_bits_equation.    
  rewrite -> firstn_exact. rewrite -> skipn_exact.
  rewrite -> length_not_emp.
  apply fold_ind.
  * apply len_ls.
  *
    rewrite -> app_length.
    rewrite len_l.
    specialize (len_min ls).
    omega.
  * apply len_l.
  * apply len_l.
Qed.

Lemma fpad_list_concat_eq :
  HMAC_List.app_fpad = HMAC_Concat.app_fpad.
Proof. reflexivity. Qed.

Lemma mult_triv x : forall y, y=2%nat -> x * y = x*2.
Proof. intros. subst. omega. Qed.

Lemma fold_left_iv_length: forall k (HK: forall iv x, length iv = k -> length (sha_h iv x) = k) l iv x , 
  length iv = k ->
  length (fold_left sha_h l (sha_h iv x)) = k.
Proof. intros k HK l.
  induction l. simpl. apply HK. 
  simpl. intros.  rewrite IHl. trivial. apply HK. trivial.
Qed. 

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
  (* Check fold_hash_blocks_eq. *)
  rewrite <- fold_hash_blocks_eq. (* important *)
  assert (forall (l1 l2 : Blist), l1 ++ l2 = l1 ++ concat (l2 :: nil)) as create_concat.
    intros. unfold concat. simpl.
    rewrite -> app_nil_r. reflexivity.

  rewrite -> create_concat.
  rewrite <- fold_hash_blocks_eq. (* again *)
  reflexivity.

  * apply BLxor_length. apply k_len. apply op_len.
  * unfold HMAC_Concat.app_fpad.
    unfold fpad.
    admit.
    (*Lennart: here is an attempt to push this proof a bit further.
      constructor. 2: constructor. rewrite app_length, bytesToBits_len.
        unfold fpad_inner. repeat rewrite app_length. 
        rewrite Coqlib.length_list_repeat, pure_lemmas.length_intlist_to_Zlist.
        rewrite (mult_triv 4). 2: reflexivity.
        rewrite bitsToBytes_len; simpl.
       But here we get a contradiction - clearly the two remaining subgoals
        can't both be true. Once we have the right value (and maybe specialze b to 512??),
        I'd like to prove the second goal sth like this:
       Focus 2.  apply fold_left_iv_length.*)
  * apply BLxor_length. apply k_len. apply ip_len.
  * 
  (*  Forall (fun x : list bool => length x = 512%nat)
     (sha_splitandpad_blocks m) *)
    admit.
  * apply BLxor_length. apply k_len. apply op_len.
  * apply BLxor_length. apply k_len. apply ip_len.
  * apply BLxor_length. apply k_len. apply op_len.
  * apply BLxor_length. apply k_len. apply ip_len.
Qed.  

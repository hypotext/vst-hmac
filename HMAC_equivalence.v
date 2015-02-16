Require Import Coqlib.
Require Import Bvector.
Require Import List.
Require Import BinNums.
(*Require Import Arith.
Require Import HMAC_spec_list.*)
Require Import HMAC_functional_prog.
Require Import ByteBitRelations.
Require Import HMAC_common_defs.
Require Import HMAC_common_lemmas.
Require Import HMAC_spec_abstract.

Require Import BinNums.

Lemma sha_h_length iv blk: length iv = c -> length blk = b ->
      length (sha_h iv blk) = c.
Proof. intros.
 unfold sha_h, intsToBits.
  rewrite bytesToBits_len, pure_lemmas.length_intlist_to_Zlist.
  rewrite common_lemmas.length_hash_block. reflexivity.
  unfold bitsToInts. erewrite pure_lemmas.length_Zlist_to_intlist. reflexivity. 
  erewrite bitsToBytes_len_gen. reflexivity.
  rewrite H; reflexivity.
  unfold bitsToInts. erewrite pure_lemmas.length_Zlist_to_intlist. reflexivity. 
  erewrite bitsToBytes_len_gen. reflexivity.
  rewrite H0; reflexivity.
Qed.

(*Duplicates the definition in Blist.v - could eliminate this once after merging with FCF*)
Definition of_list_length (A : Set)(m : nat)(ls : list A)(pf : length ls = m) : Vector.t A m :=
  match pf with
    | eq_refl => Vector.of_list ls
  end. 

Section EQUIV.

Definition h_v (iv:Bvector c) (blk:Bvector b): Bvector c :=
  of_list_length _ _ _
   (sha_h_length (Vector.to_list iv) (Vector.to_list blk) (VectorToList_length _)
               (VectorToList_length _)).

Lemma h_eq : forall (block_v : Bvector b) (block_l : Blist)
               (HVL: block_l = Vector.to_list block_v)
               ivA ivB (IV: ivA = Vector.to_list ivB),
               sha_h ivA block_l = Vector.to_list (h_v ivB block_v).
Proof. intros. unfold h_v, of_list_length. 
  destruct (sha_h_length (Vector.to_list ivB) (Vector.to_list block_v)
      (VectorToList_length ivB) (VectorToList_length block_v)). 
  symmetry. subst. apply Vector.to_list_of_list_opp.
Qed. 

Definition iv_v : Bvector c := Vector.of_list sha_iv.

Lemma iv_eq : sha_iv = Vector.to_list iv_v.
Proof. unfold iv_v. 
  rewrite <- Vector.to_list_of_list_opp.
  reflexivity.
Qed.

Lemma opad_length:
  length (bytesToBits (HMAC_functional_prog_Z.HMAC_progZ.HMAC_SHA256.sixtyfour
                       HMAC_functional_prog_Z.HMAC_progZ.Opad)) = b.
Proof. rewrite bytesToBits_len, length_SF. reflexivity. Qed.
 
Definition opad_v: Bvector b := of_list_length _ _ _ opad_length.

Lemma ipad_length:
  length (bytesToBits (HMAC_functional_prog_Z.HMAC_progZ.HMAC_SHA256.sixtyfour
                       HMAC_functional_prog_Z.HMAC_progZ.Ipad)) = b.
Proof. rewrite bytesToBits_len, length_SF. reflexivity. Qed. 
 
Definition ipad_v: Bvector b := of_list_length _ _ _ ipad_length.

Lemma fpad_length (v:Bvector c): length (fpad (Vector.to_list v)) = p.
Proof. unfold fpad, fpad_inner. rewrite bytesToBits_len.
  repeat rewrite app_length. rewrite length_list_repeat, pure_lemmas.length_intlist_to_Zlist.
  rewrite (mult_comm 4), plus_comm, Zlength_correct.
  rewrite bitsToBytes_len_gen with (n:=32%nat).
    reflexivity.
    apply VectorToList_length.
Qed. 

Definition fpad_v (v:Bvector c): Bvector p := of_list_length _ _ _ (fpad_length v).
  
Lemma fpad_eq : forall (v : Bvector c) (l : Blist),
                  l = Vector.to_list v ->
                  fpad l = Vector.to_list (fpad_v v).
Proof. intros. unfold fpad_v, of_list_length. 
  destruct (fpad_length v).
  rewrite Vector.to_list_of_list_opp.
  subst; reflexivity.
Qed.

Definition splitAndPad_v (m: Blist): list (Bvector b). Admitted.

Lemma length_splitandpad_inner : forall (m : Blist),
   Forall2
     (fun (bv : Vector.t bool b) (bl : list bool) => bl = Vector.to_list bv)
     (splitAndPad_v m) (HMAC_spec_list.sha_splitandpad_blocks m).
Admitted.

Lemma Equivalence kv m 
      (LM: NPeano.divide 8 (length m))
      (LK: length (Vector.to_list kv) = b):
      Vector.to_list (HMAC_Abstract.HMAC h_v iv_v splitAndPad_v
                      fpad_v opad_v ipad_v kv m) = 
      bytesToBits (HP.HMAC256 (bitsToBytes m)
                              (bitsToBytes (Vector.to_list kv))).
Proof. intros.
  erewrite <- HMAC_eq; try reflexivity.
  2: apply fpad_eq.
  2: apply h_eq.
  2: apply length_splitandpad_inner.
  rewrite HMAC_spec_list.HMAC_list_concat; trivial.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  rewrite <- HMAC_spec_list.saP_eq.
  rewrite <- HMAC_spec_concat.HMAC_concat_pad; trivial.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  eapply bits_bytes_ind_comp.
    apply isbyte_hmac.
  eapply HMAC_spec_pad.HMAC_Pad.HMAC_Pad_Concrete_equiv.
  Focus 7.  reflexivity.
  Focus 7. symmetry. apply HMAC_functional_prog_Z.HMAC_progZ.HMAC_functional_prog_Z_equiv.

  { rewrite bitsToBytes_len_gen with (n:=64%nat). 
    reflexivity.
    rewrite LK; reflexivity. }

  { rewrite bitsToBytes_len. reflexivity. apply LK. }

  { apply bytes_bits_comp_ind. trivial.
    eapply HMAC_spec_pad.HMAC_Pad.bitsToBytes_isbyteZ; reflexivity.
    rewrite  bits_bytes_bits_id; trivial.
    apply HMAC_spec_concat.block_8. assumption. }

  { apply bytes_bits_comp_ind.
    eapply HMAC_spec_pad.HMAC_Pad.bitsToBytes_isbyteZ; reflexivity.
    rewrite bits_bytes_bits_id; trivial. 
    apply sha_padding_lemmas.InBlocks_len; trivial. }

  { apply bytes_bits_comp_ind.
    apply pure_lemmas.Forall_list_repeat. unfold HMAC_functional_prog_Z.HMAC_progZ.Opad. omega.
    unfold opad_v, of_list_length.
      destruct opad_length.  
      apply Vector.to_list_of_list_opp. }

  { apply bytes_bits_comp_ind. 
    apply pure_lemmas.Forall_list_repeat. unfold HMAC_functional_prog_Z.HMAC_progZ.Ipad. omega.
    unfold ipad_v, of_list_length.
      destruct ipad_length.  
      apply Vector.to_list_of_list_opp. }
Qed.

End EQUIV.

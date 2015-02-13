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
(*Lemma toBlocks_consD h t: toBlocks (cons h t) = 
      if leb (length (cons h t) ) 511 then [firstn 512 (cons h t) ] 
      else firstn 512 (cons h t)  :: toBlocks (skipn 512 (cons h t) ).
Proof. rewrite toBlocks_equation. reflexivity. Qed.*)

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

(*NEW*) Require Import pure_lemmas.
(*NEW*) Require Import Coqlib.
(*NEW*) Require Import Integers.

(*NEW*) Lemma sha_splitandpad_inc_nil: length (sha_splitandpad_inc nil) = 512%nat.
Proof. reflexivity. Qed.

(*NEW*) Lemma add_blocksize_length l n: 0<=n ->
      BinInt.Z.add n (Zcomplements.Zlength l) = Zcomplements.Zlength ((Coqlib.list_repeat (Z.to_nat n) true) ++ l).
Proof. intros. do 2 rewrite Zlength_correct.
  rewrite app_length, length_list_repeat, Nat2Z.inj_add, Z2Nat.id; trivial.
Qed. 

(*NEW*) Lemma pad_inc_length: forall l, exists k, (0 < k /\ length (pad_inc l) = k*64)%nat.
Proof. unfold pad_inc.
  induction l. 
  simpl. exists (1%nat). omega.
  destruct IHl as [k [K HK]]. repeat rewrite app_length in *. rewrite length_list_repeat in *.
  rewrite pure_lemmas.length_intlist_to_Zlist in *.
  remember (BinInt.Z.to_nat
        (BinInt.Z.modulo
           (BinInt.Z.opp
              (BinInt.Z.add (BinInt.Z.add BlockSize (Zcomplements.Zlength l))
                 9)) 64)).
  remember (BinInt.Z.to_nat
      (BinInt.Z.modulo
         (BinInt.Z.opp
            (BinInt.Z.add
               (BinInt.Z.add BlockSize (Zcomplements.Zlength (a :: l))) 9))
         64)).
  simpl. simpl in HK.
  assert ((BinInt.Z.add
                   (BinInt.Z.add BlockSize (Zcomplements.Zlength (a :: l))) 9) =
          BinInt.Z.add 1 (BinInt.Z.add
                   (BinInt.Z.add BlockSize (Zcomplements.Zlength l)) 9)).
        rewrite BinInt.Z.add_assoc. f_equal.
          rewrite BinInt.Z.add_assoc. rewrite (BinInt.Z.add_comm 1). rewrite <- (BinInt.Z.add_assoc _ 1).
          f_equal. 
          repeat rewrite Zcomplements.Zlength_correct. SearchAbout BinInt.Z.add BinInt.Z.of_nat.
          apply (Znat.Nat2Z.inj_add 1 (length l)).
   rewrite H in Heqn0; clear H. 
   remember (BinInt.Z.add (BinInt.Z.add BlockSize (Zcomplements.Zlength l)) 9). clear Heqz.
   subst n n0. rewrite Z.opp_add_distr. rewrite <- (Z.add_comm (-z)). remember (-z) as zz. clear Heqzz.
   simpl.
   destruct (zeq (zz mod 64) 0).
     rewrite e in HK.
     assert ((zz+-1) mod 64 = 63). clear - e.  apply Zmod_divides in e. 2:omega. 
        destruct e. subst. rewrite Zplus_mod. rewrite Z.mul_comm. rewrite Z_mod_mult. simpl.
        rewrite Zmod_mod. apply Zmod_unique with (a:=(-1)). omega. omega.
     rewrite H. clear H e. simpl in *. exists (S k). omega.
   assert ((zz + -1) mod 64 = (zz mod 64) - 1 /\ 0 <= (zz mod 64) - 1). 
     clear -n. rewrite Zplus_mod. assert (0 <= zz mod 64 < 64). apply Z.mod_pos_bound. omega.
     split. 2: omega.
     symmetry. eapply Z.mod_unique. left. omega.
     assert (63 = -1 mod 64). eapply Z.mod_unique. left; omega. instantiate (1:=-1). omega.
     rewrite <- H0. instantiate (1:=1). omega.
   destruct H. rewrite H. clear H.   
   assert (Z.to_nat (zz mod 64 - 1) = minus (Z.to_nat (zz mod 64)) 1).
     clear - n H0. remember (zz mod 64).  clear Heqz. rewrite Z2Nat.inj_sub. reflexivity. omega. 
   rewrite H; clear H. rewrite <- NPeano.Nat.add_sub_swap. rewrite minus_Sn_m. simpl. exists k. omega.
   omega. apply (Z2Nat.inj_le 1). omega. omega. omega.
Qed. 

(*NEW*) Lemma sha_splitandpad_inc_length: forall m, exists k, 
      (0<k /\ length (sha_splitandpad_inc m) = k * 512)%nat.
Proof. intros. unfold sha_splitandpad_inc.
  destruct (pad_inc_length (bitsToBytes m)) as [k [K HK]].
  rewrite bytesToBits_len, HK. exists k. split. trivial. omega.
Qed.

(* since sha_splitandpad_inc is used instead of the modified version in the Concat-Pad proof *)
(* TODO: go through and verify that all the proofs chain *)
Lemma sha_splitandpad_inc_eq : forall (msg : Blist),
                                 sha_splitandpad_inc msg = sha_splitandpad_inc' msg.
Proof.
  intros msg.
  unfold sha_splitandpad_inc'. unfold sha_splitandpad_blocks.
  rewrite toBlocks_equation. 
  remember (sha_splitandpad_inc msg). 
  destruct b. reflexivity. unfold sha_splitandpad_inc in Heqb. rewrite Heqb. clear Heqb.
  destruct (sha_splitandpad_inc_length msg) as [k [K HK]].
  unfold sha_splitandpad_inc in HK. rewrite HK.
  rewrite leb_correct_conv. 2: omega.
  remember (pad_inc (bitsToBytes msg)). clear Heql.
  symmetry. 
  assert (HH: firstn 512 (bytesToBits l) :: toBlocks (skipn 512 (bytesToBits l)) = toBlocks  (bytesToBits l)).
    remember (bytesToBits l) as bits. rewrite (toBlocks_equation bits).
    destruct bits. destruct l; simpl in *. omega. discriminate.
    (*rewrite Heqbits. clear Heqbits. *)
    rewrite leb_correct_conv. trivial. rewrite HK. omega. 
  rewrite HH. apply concat_toBlocks_id.
  apply InBlocks_len. rewrite HK. exists k. omega.
Qed.

(*NEW*) Lemma length_mul_split A k (K:(0<k)%nat) n (N:(0<n)%nat): forall (l:list A), length l = (k * n)%nat -> 
      exists l1, exists l2, l=l1++l2 /\ length l1=n /\ length l2 = ((k-1) * n)%nat.
Proof.
  intros. 
  assert ((k * n = n + (k-1) * n)%nat). rewrite mult_minus_distr_r. simpl. rewrite plus_0_r.  
      rewrite NPeano.Nat.add_sub_assoc. rewrite minus_plus. trivial.
      SearchAbout le mult. specialize (mult_le_compat_r 1 k n). simpl; rewrite plus_0_r. simpl; intros. apply H0. omega.
  rewrite H0 in H; clear H0. 
  apply (list_splitLength _ _ _ H).
Qed.   

(*NEW, should be put into pure_lemmas or so *) Lemma skipn_short {A}: forall n (l:list A), (length l <= n)%nat -> skipn n l = nil.
Proof. induction n; simpl; intros. 
  destruct l; trivial. simpl in H. omega.
  destruct l; trivial.
  apply IHn. simpl in H. omega.
Qed.

(*NEW*) Lemma concat_length {A}: forall L (l:list A), In l L -> (length (concat L) >= length l)%nat.
Proof.  unfold concat. induction L; simpl; intros. contradiction.
  rewrite app_length. 
  destruct H; subst. unfold id. omega.
  specialize (IHL _ H). omega.
Qed.

(*NEW*) Lemma toBlocks_app_split l1 l2: length l1 = 512%nat ->
      toBlocks (l1 ++ l2) = toBlocks l1 ++ toBlocks l2.
Proof. intros.
  rewrite toBlocks_equation. rewrite app_length. 
  rewrite firstn_exact; trivial.
  rewrite skipn_exact; trivial.
  remember (l1 ++ l2).
  destruct l. 
  { assert (@length bool nil = length (l1 ++ l2)). rewrite <- Heql; trivial.
    rewrite app_length, H in H0. rewrite plus_comm in H0. simpl in H0. omega. }
  { rewrite  leb_correct_conv. 2: rewrite H, plus_comm; omega.
    remember (toBlocks l2).
    rewrite toBlocks_equation.
    destruct l1. simpl in H; omega. 
    rewrite leb_correct_conv. 2: rewrite H; omega.
    rewrite firstn_same. 2: rewrite H; omega. 
    rewrite skipn_short. 2: rewrite H; omega. 
    rewrite toBlocks_equation. trivial. }
Qed. 

(*NEW*) Lemma sha_splitandpad_inc_InBlocks m : InBlocks 512 (sha_splitandpad_inc m).
Proof. intros. apply InBlocks_len.
  destruct (sha_splitandpad_inc_length m) as [k [K HK]].
  rewrite HK. exists k. trivial.
Qed.

(*NEW*) Lemma InBlocks_Forall_512 b: (InBlocks 512 b) ->
      Forall (fun x : list bool => length x = 512%nat) (toBlocks b).
Proof. intros.
  remember (toBlocks b). generalize dependent b.
  induction l. simpl; intros. constructor.
  simpl; intros. rewrite toBlocks_equation in Heql. destruct b. discriminate.
  inv H.
  rewrite H1, app_length, H0 in Heql. 
  rewrite leb_correct_conv in Heql. 2: omega.
  rewrite firstn_exact in Heql; trivial.
  rewrite skipn_exact in Heql; trivial. inv Heql.
  constructor. trivial.
  apply (IHl _ H2 (eq_refl _)).
Qed.

(*NEW*) Lemma sha_splitandpad_blocks_512 m:
      Forall (fun x => length x = 512%nat) (sha_splitandpad_blocks m).
Proof. apply InBlocks_Forall_512. apply sha_splitandpad_inc_InBlocks. 
Qed.

Lemma len_min : forall {A : Type} (l : list A), (length l >= 0)%nat.
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

Lemma mult_triv x : forall y, y=2%nat -> (x * y = x*2)%nat.
Proof. intros. subst. omega. Qed.

Lemma fold_left_iv_length: forall k (HK: forall iv x, length iv = k -> length (sha_h iv x) = k) l iv x , 
  length iv = k ->
  length (fold_left sha_h l (sha_h iv x)) = k.
Proof. intros k HK l.
  induction l. simpl. apply HK. 
  simpl. intros.  rewrite IHl. trivial. apply HK. trivial.
Qed. 

(*NEW2*) Lemma sha_iv_length: length sha_iv = 256%nat.
Proof. reflexivity. Qed.

(*NEW2*) Lemma hash_blocks_bits_len: forall r l, length r = 256%nat -> 
      InBlocks 512 l ->
      length (hash_blocks_bits sha_h r l) = 256%nat.
Proof. intros r l.
  apply hash_blocks_bits_ind.
  intros. trivial.
  simpl; intros. destruct _x. contradiction. subst msg; clear y.
  inv H1.
  apply H; clear H. unfold sha_h, intsToBits. rewrite bytesToBits_len, length_intlist_to_Zlist.
  rewrite length_hash_block. omega.
  unfold bitsToInts. erewrite length_Zlist_to_intlist. reflexivity.
    rewrite bitsToBytes_len_gen with (n:=32%nat). reflexivity. apply H0.
  unfold bitsToInts. erewrite length_Zlist_to_intlist. reflexivity.
    erewrite bitsToBytes_len_gen with (n:=64%nat). reflexivity.
    rewrite H3, firstn_exact. apply H2. apply H2.
    rewrite H3, skipn_exact. assumption. apply H2. 
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

    (*NEW2*)
    constructor. 2: constructor.
    rewrite app_length, fold_hash_blocks_eq.
      2: apply BLxor_length; trivial. 
      2: apply sha_splitandpad_blocks_512.
    assert (IB: InBlocks 512 (BLxor k ip ++ concat (sha_splitandpad_blocks m))).
      unfold sha_splitandpad_blocks. 
      rewrite concat_toBlocks_id. 2: apply sha_splitandpad_inc_InBlocks.
      econstructor.
        2: reflexivity.
        2: apply sha_splitandpad_inc_InBlocks.
        apply BLxor_length; trivial.
    rewrite bytesToBits_len.
        unfold fpad_inner. repeat rewrite app_length. 
        rewrite Coqlib.length_list_repeat, pure_lemmas.length_intlist_to_Zlist.
        rewrite (mult_triv 4). 2: reflexivity.
    rewrite (hash_blocks_bits_len sha_iv sha_iv_length IB). 
    rewrite Zlength_correct. 
    erewrite bitsToBytes_len_gen with (n:=32%nat).
    reflexivity.
    apply (hash_blocks_bits_len sha_iv sha_iv_length IB).
  * apply BLxor_length. apply k_len. apply ip_len.
  * 
  (*  Forall (fun x : list bool => length x = 512%nat)
     (sha_splitandpad_blocks m) *)
    apply sha_splitandpad_blocks_512.
  * apply BLxor_length. apply k_len. apply op_len.
  * apply BLxor_length. apply k_len. apply ip_len.
  * apply BLxor_length. apply k_len. apply op_len.
  * apply BLxor_length. apply k_len. apply ip_len.
Qed.  

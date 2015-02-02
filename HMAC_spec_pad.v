(* admits: 14 + 2

- front ~ FRONT, back ~ BACK <-- have paper proof but am stuck
   - make following code compile

- SHA proofs related to generate_and_pad
   - pushed 2 admits back to sha_padding_lemma (InBlocks corr + positive n)

- range: bytes in range
- pad + intlist_to_Zlist preserve in range, fix the Forall

------

- modules
- linking proofs

*)

Set Implicit Arguments.

Require Import List. Import ListNotations.
Require Import Arith.

Require Import HMAC_functional_prog_Z.
Require Import Integers.
Require Import Coqlib.
Require Import sha_padding_lemmas.
Require Import functional_prog.
Require Import hmac_common_lemmas.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import SHA256.
Require Import ByteBitRelations.
Require Import XorCorrespondence.
Require Import HMAC_functional_prog_Z.
Require Import HMAC_common_defs.
(* TODO remove useless imports *)

Require Import Coq.Program.Basics. (* for function composition: ∘ *)

Module HMAC_Pad.

Local Open Scope program_scope.

Section HMAC.

(* b = block size
   c = digest (output) size
   p = padding = b - c (fixed) *)
  Variable c p : nat.
  Definition b := (c + p)%nat.

  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)

  Definition h_star k (m : Blist) :=
    hash_blocks_bits h k m.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Variable splitAndPad : Blist -> Blist.

  Definition hash_words_padded : Blist -> Blist :=
    hash_words ∘ splitAndPad.

  (* ----- *)

  Hypothesis splitAndPad_1_1 :
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  (* constant-length padding. *)
  Variable fpad : Blist.

  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad.
  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  (* TODO fix this -- not used by HAMC *)
  Definition GNMAC k m :=
    let (k_Out, k_In) := splitList c k in
    h k_Out (h_star_pad k_In m).

  (* The "two-key" version of GHMAC and HMAC. *)
  (* Concatenate (K xor opad) and (K xor ipad) *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b k in (* concat earlier, then split *)
      let h_in := (hash_words_padded (k_In ++ m)) in
        hash_words_padded (k_Out ++ h_in).

  Definition HMAC_2K (k : Blist) (m : Blist) :=
    (* GHMAC_2K k (splitAndPad m). *)
    GHMAC_2K k m.

(* opad and ipad are constants defined in the HMAC spec. *)
Variable opad ipad : Blist.

Definition GHMAC (k : Blist) :=
  GHMAC_2K (BLxor k opad ++ BLxor k ipad).

Definition HMAC (k : Blist) :=
  HMAC_2K (BLxor k opad ++ BLxor k ipad).

End HMAC.

(* ----------------------------------------------- *)

Definition c:nat := (HMAC_progZ.SHA256_.DigestLength * 8)%nat.
Definition p:=(32 * 8)%nat.

Definition sha_iv : Blist :=
  bytesToBits (SHA256.intlist_to_Zlist SHA256.init_registers).

Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  bytesToBits (SHA256.intlist_to_Zlist
                 (SHA256.hash_block (SHA256.Zlist_to_intlist (bitsToBytes regs))
                                     (SHA256.Zlist_to_intlist (bitsToBytes block))
              )).

Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).

Definition convert (l : list int) : list bool :=
  bytesToBits (SHA256.intlist_to_Zlist l).


(* ------------------------------------------------- *)
(* Neat conversion functions (TODO move rest of spec over *)

(*
Definition c := (HMAC_progZ.SHA256_.DigestLength * 8)%nat.
Definition p := (32 * 8)%nat.

Definition intsToBits (l : list int) : list bool :=
  bytesToBits (SHA256.intlist_to_Zlist l).

Definition bitsToInts (l : Blist) : list int :=
  SHA256.Zlist_to_intlist (bitsToBytes l).

Definition sha_iv : Blist :=
  intsToBits SHA256.init_registers.

Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  intsToBits (SHA256.hash_block (bitsToInts regs) (bitsToInts block)).

Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).
*)


(* -------------------------------------------------------- LEMMAS *)

(* Lemma 1: ++ equivalence on list *)
(* Lemma 2: xor equivalence on list *)
(* Lemma 3: SHA (iterated hash) equivalence on list *)

Lemma concat_equiv :
  forall (l1 : Blist) (l2 : list Z) (m1 : Blist) (m2 : list Z),
    bytes_bits_lists l1 l2
    -> bytes_bits_lists m1 m2
    -> bytes_bits_lists (l1 ++ m1) (l2 ++ m2).
Proof.
  intros l1 l2 m1 m2.
  intros fst_eq snd_eq.
  generalize dependent m1. generalize dependent m2.
  induction fst_eq; intros.
  - repeat rewrite app_nil_l.
    apply snd_eq.
  - simpl.
    apply eq_cons.
    + apply IHfst_eq.
      apply snd_eq.
    + apply H.
Qed.

(* --------------------------------- *)

(* Lemma 2 *)

(* Prove that the inner xor lemma is true on at least one example *)
Section XOR_Example.

 Definition k:Blist := concat (list_repeat 64 [true; true; false; false; true; false; true; true]).
 Definition K:list Z := list_repeat 64 211.

 Lemma conv : convertByteBits [true; true; false; false; true; false; true; true] 211.
   repeat eexists.
  (* eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists. *)
  (* split. reflexivity. simpl. reflexivity. *)
 Qed.
 Lemma kKcorrect: bytes_bits_lists k K.
   unfold K, k. simpl.
   repeat constructor; try apply conv.
  Qed.


 Definition ip:Blist := concat (list_repeat 64 [false; true; false; false; true; false; true; true]).
 Definition IP:Z := 210.
 Transparent Byte.repr.

Definition byte_to_64list (byte : byte) : list Z :=
   map Byte.unsigned (HMAC_progZ.HMAC_SHA256.sixtyfour byte).

 Lemma ip_conv : convertByteBits [false; true; false; false; true; false; true; true] 210.
   repeat eexists.
 Qed.
 Lemma ipcorrect: bytes_bits_lists ip (HMAC_progZ.HMAC_SHA256.sixtyfour IP).
   unfold ip, IP. simpl. unfold byte_to_64list, HMAC_progZ.HMAC_SHA256.sixtyfour. simpl.
   repeat constructor; try apply ip_conv.
  Qed.

Lemma ONE: convertByteBits [true; false; false; false; false; false; false; false] 1.
  repeat eexists. Qed.

Lemma inner_fst_equiv_example : exists k (ip  : Blist) K (IP : Z),
                          ((length K) * 8)%nat = (c + p)%nat /\
                          Zlength K = Z.of_nat HMAC_progZ.SHA256_.BlockSize /\
                          (* TODO: first implies this *)
                          bytes_bits_lists k K /\
                          bytes_bits_lists ip (HMAC_progZ.HMAC_SHA256.sixtyfour IP) /\
                          bytes_bits_lists (BLxor k ip)
                                           ((HMAC_progZ.HMAC_SHA256.mkArg (HMAC_progZ.HMAC_SHA256.mkKey K) IP)).

Proof.
  exists k, ip, K, IP. repeat split.
   apply kKcorrect. apply ipcorrect.
  unfold k, K, ip, IP. simpl. unfold BLxor. simpl.
  repeat constructor; apply ONE.
Qed.

End XOR_Example.

(* See XorCorrespondence.v *)

Lemma inner_general_map : forall (ip : Blist) (IP_list : list Z) (k : Blist) (K : list Z),
                            bytes_bits_lists ip IP_list ->
                            bytes_bits_lists k K ->
     bytes_bits_lists (BLxor k ip)
                      (map (fun p0 : Z * Z => Z.lxor (fst p0) (snd p0))
                           (combine K IP_list)).
Proof.
  intros ip IP_list k K ip_eq k_eq.
  unfold BLxor. simpl.
  generalize dependent ip. generalize dependent IP_list.
  induction k_eq; intros.
  - simpl. constructor.
  -
    induction ip_eq.
    +
      simpl. constructor.
    +
      simpl.
      constructor.
      * apply IHk_eq.
        apply ip_eq.
      *
        apply xor_correspondence.
        apply H. apply H0.
Qed.

Lemma xor_equiv_Z : forall (xpad  : Blist) (XPAD : Z)
                                           (k : Blist) (K : list Z),
                          bytes_bits_lists xpad (HMAC_progZ.HMAC_SHA256.sixtyfour XPAD) ->
                          ((length K) * 8)%nat = (c + p)%nat ->
                          Zlength K = Z.of_nat HMAC_progZ.SHA256_.BlockSize ->
                          (* TODO: first implies this *)
                          bytes_bits_lists k K ->
                          bytes_bits_lists (BLxor k xpad)
       (HMAC_progZ.HMAC_SHA256.mkArg (HMAC_progZ.HMAC_SHA256.mkKey K) XPAD).
Proof.
  intros xpad XPAD k K.
  intros xpad_equiv len_k zlen_k k_equiv.
  unfold HMAC_progZ.HMAC_SHA256.mkArg, HMAC_progZ.HMAC_SHA256.mkKey.
  Opaque HMAC_progZ.HMAC_SHA256.sixtyfour.
  simpl. rewrite zlen_k. simpl. unfold HMAC_progZ.HMAC_SHA256.zeroPad.
  assert (byte_key_length_blocksize: length K = 64%nat).
    * unfold p, c in *. simpl in *. omega.
  *
    rewrite byte_key_length_blocksize.  simpl.  rewrite app_nil_r.
    apply inner_general_map.

  - apply xpad_equiv.
  - apply k_equiv.
Qed.

(* ------------------------------------------------------ *)
(* Lemma 3 *)

(* --- abstract version *)

Parameter A B : Type.
Parameter convert_BA : B -> A.
Parameter convert_AB : A -> B.

Fixpoint iterate {A : Type} (n : nat) (f : A -> A) (x : A) :=
  match n with
    | O => x
    | S n' => f (iterate n' f x) (* or [iterate n' f (f x)] *)
  end.

Definition id {X : A} (x : A) : A := x.
Definition wrap (F : B -> B) : A -> A :=
  convert_BA ∘ F ∘ convert_AB.
Definition roundtrip : B -> B :=
  convert_AB ∘ convert_BA.

(* Axiom *)
Lemma roundtrip_id :
  forall (X : B), convert_AB (convert_BA X) = X.
Proof. Admitted.

Lemma once_eq :
    forall (x : A) (X : B) (f : A -> A) (F : B -> B),
      x = convert_BA X ->
      f = wrap F ->
      X = roundtrip X ->
      f x = convert_BA (F X).
Proof.
  intros x X f F inputs_eq f_def roundtrip_id.
  unfold roundtrip in *.
  rewrite -> inputs_eq.
  rewrite -> f_def.
  unfold wrap in *.
  change ((convert_BA ∘ F ∘ convert_AB) (convert_BA X)) with
    (convert_BA (F ((convert_AB ∘ convert_BA) X))).
  rewrite <- roundtrip_id.
  reflexivity.
Qed.

(* a simplified version of fold_equiv *)
Lemma iterate_equiv :
  forall (x : A) (X : B) (f : A -> A) (F : B -> B) (n : nat),
    x = convert_BA X ->
    f = wrap F ->
    X = roundtrip X ->
    iterate n f x = convert_BA (iterate n F X).
Proof.
  intros. revert x X f F H H0 H1.
  induction n as [ | n']; intros x X f F input_eq func_wrap roundtrip';
  unfold wrap in *; unfold roundtrip in *.
  -
    simpl. apply input_eq.
  -
    simpl.
    pose proof once_eq as once_eq.
    apply once_eq.
    apply IHn'; assumption.
    * unfold wrap. apply func_wrap.
    * symmetry. apply roundtrip_id.
Qed.

(* ----- concrete version *)

(* Definition of InBlocks in sha_padding_lemmas *)

(* Lemma test : InBlocks 512 (list_repeat 512 true). *)
(* Proof. *)
(*   eapply list_block. *)
(*   instantiate (1 := list_repeat 512 true). *)
(*   - reflexivity. *)
(*   - instantiate (1 := []). rewrite -> app_nil_r. reflexivity. *)
(*   - apply list_nil. *)
(* Qed. *)

Lemma splitandpad_equiv : forall (bits : Blist) (bytes : list Z),
                            bytes_bits_lists bits bytes ->
                            bytes_bits_lists
                              (sha_splitandpad bits)
                              (sha_padding_lemmas.pad bytes).
Proof.
  intros bits bytes inputs_eq.
  unfold concat.
  unfold sha_splitandpad.

  apply bytes_bits_ind_comp in inputs_eq.
  rewrite inputs_eq.
  apply bytes_bits_def_eq.
  admit.                        (* padding preserves in-range *)
  admit.
Qed.

Lemma hash_block_equiv :
  forall (bits : Blist) (bytes : list Z)
         (regs : Blist) (REGS : SHA256.registers),
    (length bits)%nat = 512%nat ->
    (length bytes)%nat = 64%nat -> (* removes firstn 16 (Zlist->intlist bytes) *)

    regs = bytesToBits (SHA256.intlist_to_Zlist REGS) ->
    bits = bytesToBits bytes ->

    sha_h regs bits =
    bytesToBits (SHA256.intlist_to_Zlist
                   (SHA256.hash_block REGS
                                      (SHA256.Zlist_to_intlist bytes))).
Proof.
  intros bits bytes regs REGS bits_blocksize bytes_blocksize regs_eq input_eq.
  unfold sha_h.
  apply f_equal.
  apply f_equal.

  rewrite -> regs_eq.
  rewrite -> input_eq.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
  reflexivity.
  admit. admit.                 (* intlist_to_Zlist preserves in-range *)
Qed.

(* front/back equivalence theorems: stuck *)

Lemma front_equiv :
  (* forall (front back : Blist) (FRONT BACK : list int), *)
  forall (back : Blist) (BACK : list int) (front : Blist) (FRONT : list int),
    Forall (fun b : Z => 0 <= b < 256) (SHA256.intlist_to_Zlist (FRONT ++ BACK)) ->
    (length front)%nat = 512%nat ->
    (length FRONT)%nat = 16%nat ->
    InBlocks 512 front ->
    InBlocks 16 FRONT ->
    InBlocks 512 back ->
    InBlocks 16 BACK ->         (* shouldn't need these two *)
    front ++ back = convert (FRONT ++ BACK) ->
    front = convert FRONT.
Proof.
  intros back BACK front FRONT range f_len F_len fblocks Fblocks bblocks Bblocks concat_eq.
  unfold convert in *.
  rewrite -> pure_lemmas.intlist_to_Zlist_app in concat_eq.
  (* can prove InBlocks 512 (convert (FRONT ++ BACK)) *)
  rewrite -> bytesToBits_app in concat_eq.

  (* my proof:
  concat_eq : front ++ back =
              bytesToBits (intlist_to_Zlist FRONT) ++
              bytesToBits (intlist_to_Zlist BACK)

  x0 :: ... :: x511 :: back = x0' :: ... :: x511' :: convert BACK

  BACK is the right length such that the overall lists are the same length
    why? we know that
    full = convert FULL so 
    length (front ++ back) = 32 * length (FRONT ++ BACK)
  thus, by list equality, xn = xn' (otherwise, contradiction)

  x0 :: ... :: x511 = x0' :: ... :: x511'
  front = convert FRONT

and back = convert BACK
 *)

  (* but induction on the front needs to be in pairs? can't pair each one-cons
     somehow have to use InBlocks for both AND the length constraint
     (each is exactly one block)
   *)
  revert FRONT back BACK Fblocks bblocks Bblocks range f_len F_len concat_eq.
  induction fblocks; intros.
  -
    revert back BACK bblocks Bblocks range f_len F_len concat_eq; induction Fblocks; intros.
    *
      reflexivity.
    *
      simpl in *.
      omega.
  -
    (* what to induct on here? fronts/backs confusing *)
    revert back0 back BACK front full fblocks bblocks Bblocks range f_len F_len concat_eq
           H H0 IHfblocks.
    (* need to figure out how to name induction *)
    induction Fblocks.
    *
      intros.
      simpl in *.
      omega.
    *
      (* look at the intros here *)
      intros.
      rewrite -> H0 in *.
      rewrite -> H2 in *.
      (* frontFinal = front0 ++ back1; FRONTFINAL = front ++ back (confusing)  *)

Admitted.
(* don't induct on the back blocks -- induction case is unprovable 
   see history for deleted notes
*)

(* --------- *)
    
(* it's more of an iteration theorem than a fold theorem *)
(* conversion function: bytesToBits @ SHA256.intlist_to_Zlist *)
Lemma fold_equiv_blocks :
  forall (l : Blist) (acc : Blist)
         (L : list int) (ACC : list int),
    (* length assumptions about list *)
      InBlocks 512 l ->
      InBlocks 16 L ->
      l = convert L ->
      acc = convert ACC ->
      hash_blocks_bits sha_h acc l = convert (SHA256.hash_blocks ACC L).
Proof.
  intros l acc L ACC bit_blocks bytes_blocks inputs_eq acc_eq.
  
  revert acc ACC L inputs_eq acc_eq bytes_blocks.
  induction bit_blocks; intros.
  *
    revert acc ACC inputs_eq acc_eq.
    induction bytes_blocks; intros.

    -                             (* both empty *)
      rewrite -> SHA256.hash_blocks_equation.
      rewrite -> hash_blocks_bits_equation.
      apply acc_eq.

    -
      rewrite -> H0 in *.
      unfold convert in inputs_eq. 
      destruct front.
      { inversion H. }
      { simpl in inputs_eq. inversion inputs_eq. }

  *
    revert front back full H H0 bit_blocks IHbit_blocks acc ACC
           inputs_eq acc_eq.
    induction bytes_blocks; intros.
    (* TODO: clear IHbytes_blocks *)

    -
      simpl in inputs_eq.
      rewrite -> H0 in inputs_eq.
      unfold convert in inputs_eq.
      destruct front.
      { inversion H. }
      { simpl in inputs_eq. inversion inputs_eq. }

    - 
      rewrite -> SHA256.hash_blocks_equation.
      rewrite -> hash_blocks_bits_equation.
      repeat rewrite -> length_not_emp.

      rewrite -> H0.
      rewrite -> H2.
      (* TODO: generalize these (it's true by hyp) *)
      assert (H_first_512 : firstn 512 (front0 ++ back0) = front0).
        apply firstn_exact. assumption.
      assert (H_skip_512 : skipn 512 (front0 ++ back0) = back0).
        apply skipn_exact. assumption.
      assert (H_first_16 : firstn 16 (front ++ back) = front).
        apply firstn_exact. assumption.
      assert (H_skip_16 : skipn 16 (front ++ back) = back).
        apply skipn_exact. assumption.

      rewrite -> H_first_512.
      rewrite -> H_skip_512.
      rewrite -> H_first_16.
      rewrite -> H_skip_16.

      apply IHbit_blocks; auto; clear IHbytes_blocks IHbit_blocks.
      +                         (* TODO: backs are equivalent *)
        rewrite -> H0 in inputs_eq.
        rewrite -> H2 in inputs_eq.
        (* could refactor out the pose/destruct but leaves more stuff in context *)
        (* pose proof blocks_equiv front0 back0 front back as blocks_equiv. *)
        (* destruct blocks_equiv. *)
        (* apply inputs_eq. *)
        (* apply H4. *)
        admit.
      +
        pose proof hash_block_equiv as hash_block_equiv.
        specialize (hash_block_equiv front0 (SHA256.intlist_to_Zlist front) acc ACC).
        rewrite -> hash_block_equiv; auto. clear hash_block_equiv.
        rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
        reflexivity.
        {
          rewrite -> pure_lemmas.length_intlist_to_Zlist.
          rewrite -> H.
          omega.
        }
        {
          (* TODO: prove the fronts are equivalent *)
          rewrite -> H0 in inputs_eq.
          rewrite -> H2 in inputs_eq.
          (* pose proof blocks_equiv front0 back0 front back as blocks_equiv. *)
          (* destruct blocks_equiv. *)
          (* apply inputs_eq. *)
          (* apply H3. *)
          admit.
        }
     +
       rewrite -> H0. rewrite -> app_length. rewrite -> H. omega.
     +
       rewrite -> H2. rewrite -> app_length. rewrite -> H1. omega.
Qed.

Lemma SHA_equiv_pad : forall (bits : Blist) (bytes : list Z),
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (hash_words_padded sha_h sha_iv sha_splitandpad bits)
                      (HMAC_progZ.SHA256_.Hash bytes).

Proof.
  intros bits bytes input_eq.
  unfold HMAC_progZ.SHA256_.Hash.
  rewrite -> functional_prog.SHA_256'_eq.
  unfold SHA256.SHA_256.
  unfold hash_words_padded.
  change ((hash_words sha_h sha_iv ∘ sha_splitandpad) bits) with
  (hash_words sha_h sha_iv (sha_splitandpad bits)).

  -
    repeat rewrite <- sha_padding_lemmas.pad_compose_equal in *.
    unfold sha_padding_lemmas.generate_and_pad' in *.
    unfold hash_words.
    unfold h_star.

    pose proof splitandpad_equiv as splitandpad_equiv.
    specialize (splitandpad_equiv bits bytes input_eq).

      apply bytes_bits_comp_ind.
      pose proof fold_equiv_blocks as fold_equiv_blocks.
      admit.
      (* TODO: in-range preserved by hash_blocks and intlist_to_Zlist *)
      apply fold_equiv_blocks.
      *                         (* padding -> blocks of 512 *)
        unfold sha_splitandpad in *.
        apply bytes_bits_length in input_eq.
        pose proof pad_len_64_nat (bitsToBytes bits) as pad_len_64.
        apply InBlocks_len.
        rewrite -> bytesToBits_len.
        (* eexists. *)
        destruct pad_len_64.
        rewrite -> H.
        exists x.
        omega.
      *
        pose proof pad_len_64_nat bytes as pad_len_64.
        apply InBlocks_len.
        destruct pad_len_64.

        assert (H' : length (pad bytes) = (Z.to_nat WORD * (16 * x))%nat).
          rewrite -> H.
          assert (Z.to_nat WORD = 4%nat) by reflexivity.
          rewrite -> H0.
          omega.

        apply pure_lemmas.length_Zlist_to_intlist in H'.
        rewrite H'.
        eexists x.
        omega.

      * unfold sha_splitandpad.
        unfold convert.
        rewrite -> pure_lemmas.Zlist_to_intlist_to_Zlist.
        f_equal.
        apply bytes_bits_ind_comp in input_eq.
        rewrite -> input_eq.
        reflexivity.
        + admit.                (* bytes in range *)
        +
          pose proof pad_len_64_nat bytes as pad_len_64.
          destruct pad_len_64.
          rewrite -> H.
          assert (four : Z.to_nat WORD = 4%nat) by reflexivity.
          rewrite -> four.
          exists (x * 16)%nat.
          omega.
        + admit.                        (* padding in range *)

     * unfold sha_iv. reflexivity.
Qed.

(* --------------------------------------- *)

(* MAIN THEOREM *)

(* Relates the HMAC padded spec to the HMAC functional program (version that uses Z) *)

Theorem HMAC_Pad_Concrete_equiv : forall
                            (K M H : list Z) (OP IP : Z)
                            (k m h : Blist) (op ip : Blist),
  ((length K) * 8)%nat = (c + p)%nat ->
  Zlength K = Z.of_nat HMAC_progZ.SHA256_.BlockSize ->
  (* TODO: first implies this *)
  bytes_bits_lists k K ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HMAC_progZ.HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HMAC_progZ.HMAC_SHA256.sixtyfour IP) ->
  HMAC c p sha_h sha_iv sha_splitandpad op ip k m = h ->
  HMAC_progZ.HMAC_SHA256.HMAC IP OP M K = H ->
  bytes_bits_lists h H.
Proof.
  intros K M H OP IP k m h op ip.
  intros padded_key_len padded_key_len_byte padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.

  intros.
  unfold p, c in *.
  simpl in *.

  rewrite <- HMAC_abstract. rewrite <- HMAC_concrete.

  unfold HMAC. unfold HMAC_progZ.HMAC_SHA256.HMAC. unfold HMAC_progZ.HMAC_SHA256.OUTER. unfold HMAC_progZ.HMAC_SHA256.INNER.
  unfold HMAC_progZ.HMAC_SHA256.outerArg. unfold HMAC_progZ.HMAC_SHA256.innerArg.

  unfold HMAC_2K. unfold GHMAC_2K. rewrite -> split_append_id.

  simpl.
  
  (* Major lemmas *)
  apply SHA_equiv_pad.
  apply concat_equiv.
  apply xor_equiv_Z; try assumption.

  *
    apply SHA_equiv_pad.
    apply concat_equiv.

  - apply xor_equiv_Z; try assumption.
  - assumption.
    (* xors preserve length : TODO factor this out*)
    *
      Locate padded_keys_eq.
      unfold b in *. simpl. unfold BLxor. rewrite -> list_length_map.
      rewrite -> combine_length.
      pose proof bytes_bits_length op (HMAC_progZ.HMAC_SHA256.sixtyfour OP) as ops_len.
      rewrite -> ops_len.
      pose proof bytes_bits_length k K as keys_len.
      rewrite -> keys_len.
      rewrite -> padded_key_len.
      Transparent HMAC_progZ.HMAC_SHA256.sixtyfour.
      unfold HMAC_progZ.HMAC_SHA256.sixtyfour.
      rewrite -> length_list_repeat.
      reflexivity.
      apply padded_keys_eq.     (* given: bytes_bits_lists k K *)
      apply ops_eq.             (* given: bytes_bits_lists op (64 OP) *)

    *
      unfold b in *. simpl. unfold BLxor. rewrite -> list_length_map.
      rewrite -> combine_length.
      pose proof bytes_bits_length ip (HMAC_progZ.HMAC_SHA256.sixtyfour IP) as ips_len.
      rewrite -> ips_len.
      pose proof bytes_bits_length k K as keys_len.
      rewrite -> keys_len.
      rewrite -> padded_key_len.
      unfold HMAC_progZ.HMAC_SHA256.sixtyfour.
      rewrite -> length_list_repeat.
      reflexivity.
      apply padded_keys_eq.
      apply ips_eq.
Qed.

End HMAC_Pad.
(* TODO move this End to the end of the spec definition + rename and recompile things *)

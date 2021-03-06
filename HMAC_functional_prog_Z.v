Require Import Integers.
Require Import Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List. Import ListNotations.
Require Import HMAC_functional_prog.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Bruteforce.

Require Import pure_lemmas.

Module HMAC_progZ.

(*SHA256: blocksize = 64bytes 
    corresponds to 
    #define SHA_LBLOCK	16
    #define SHA256_CBLOCK	(SHA_LBLOCK*4) *)

Module Type HASH_FUNCTION.
  Parameter BlockSize:nat. (*measured in bytes; 64 in SHA256*)
  Parameter DigestLength: nat. (*measured in bytes; 32 in SHA256*)
  Parameter Hash : list Z -> list Z.
End HASH_FUNCTION.


Module Type HMAC_Module.
  Parameter HMAC: Z -> Z -> list Z -> list Z -> list Z.
End HMAC_Module.

Module HMAC_FUN (HF:HASH_FUNCTION)  <: HMAC_Module.

Definition sixtyfour {A} (i:A): list A:= list_repeat HF.BlockSize i.

(*Reading rfc4231 reveals that padding happens on the right*)
Definition zeroPad (k: list Z) : list Z :=
  k ++ list_repeat (HF.BlockSize-length k) Z0.

Definition mkKey (l:list Z) : list Z :=
  if Z.gtb (Zlength l) (Z.of_nat HF.BlockSize)
  then (zeroPad (HF.Hash l)) 
  else zeroPad l.

(* TODO: turns both Zs into bytes, then back into Zs.
can I eliminate byte.xor? *)
(*
Definition mkArg (key:list byte) (pad:Z): list byte := 
       (map (fun p => Byte.xor (fst p) (snd p))
          (combine key (map Byte.repr (sixtyfour pad)))).

Definition mkArgZ key (pad:Z): list Z := 
     map Byte.unsigned (mkArg key pad).
*)

Definition mkArg (key:list Z) (pad:Z): list Z := 
       (map (fun p => Z.lxor (fst p) (snd p))
          (combine key (sixtyfour pad))).

(*
Definition Ipad := P.Ipad.  
Definition Opad := P.Opad.
*)
(*innerArg to be applied to message, (map Byte.repr (mkKey password)))*)
Definition innerArg IP (text: list Z) key : list Z :=
  (mkArg key IP) ++ text.

Definition INNER IP k text := HF.Hash (innerArg IP text k).

Definition outerArg OP (innerRes: list Z) key: list Z :=
  (mkArg key OP) ++ innerRes.

Definition OUTER OP k innerRes := HF.Hash (outerArg OP innerRes k).

Definition HMAC IP OP txt password: list Z := 
  (* let key := map Byte.repr (mkKey password) in *)
  let key := mkKey password in
  OUTER OP key (INNER IP key txt).

End HMAC_FUN.

Require Import SHA256.
Require Import functional_prog.

Module SHA256_ <: HASH_FUNCTION.
  Definition BlockSize:= 64%nat.
  Definition DigestLength:= 32%nat.
  Definition Hash : list Z -> list Z := SHA_256'.
End SHA256_.

Module HMAC_SHA256 := HMAC_FUN SHA256_.

Definition Ipad := (* Byte.repr *) 54. (*0x36*) 
Definition Opad := (* Byte.repr *) 92. (*0x5c*)

Definition HMAC256 := HMAC_SHA256.HMAC Ipad Opad.

(* ------------------------------------------------------ *)

(* Proof of equivalence with HMAC_functional_prog *)

Theorem HMAC_SHA_eq : forall (m : list Z), HP.SHA256_.Hash m = SHA256_.Hash m.
Proof.
  intros.
  unfold HP.SHA256_.Hash. unfold SHA256_.Hash. reflexivity.
Qed.

Theorem HMAC_mkKey_eq : forall (k : list Z),
                          HP.HMAC_SHA256.mkKey k = HMAC_SHA256.mkKey k.
Proof.
  intros.
  unfold HP.HMAC_SHA256.mkKey.
  unfold HMAC_SHA256.mkKey.
  unfold HP.SHA256_.BlockSize.
  unfold SHA256_.BlockSize.
  rewrite -> HMAC_SHA_eq.
  unfold HP.HMAC_SHA256.zeroPad.
  unfold HMAC_SHA256.zeroPad.
  repeat rewrite -> Nlist_repeat.
  unfold HP.SHA256_.BlockSize.
  unfold SHA256_.BlockSize.
  reflexivity.
Qed.

Theorem HMAC_64_eq : forall {A : Type} (x : A),
                       HP.HMAC_SHA256.sixtyfour x = HMAC_SHA256.sixtyfour x.
Proof.
  intros A x.
  unfold HP.HMAC_SHA256.sixtyfour. unfold HMAC_SHA256.sixtyfour.
  simpl. reflexivity.
Qed.

Lemma map_repeat : forall {A B : Type} (f : A -> B) (x : A) (n : nat),
                     list_repeat n (f x) = map f (list_repeat n x).
Proof.
  intros.
  revert A B f x.
  induction n as [ | n'].
  * reflexivity.
  *
    intros.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.
  
Theorem combine_map : forall {A B : Type} (f : A -> B) (l1 : list A) (l2 : list A),
                        combine (map f l1) (map f l2) =
                        map (fun p => (f (fst p), f (snd p))) (combine l1 l2).
Proof.
  intros.
  revert f l2.
  induction l1 as [ | x1 xs1].
  *
    intros. reflexivity.
  * intros.
    revert x1 xs1 IHxs1 f.
    induction l2 as [ | x2 xs2].
    -
      intros. reflexivity.
    -
      intros.
      simpl.
      f_equal.
      apply IHxs1.
Qed.

Theorem xor_inrange : forall (x y : Z),
                        x = x mod Byte.modulus
                        -> y = y mod Byte.modulus
                        -> Z.lxor x y = (Z.lxor x y) mod Byte.modulus.
Proof.
  intros. symmetry. apply Byte.equal_same_bits. intros.
  assert (ZZ: Z.lxor x y mod Byte.modulus =
        Z.lxor x y mod two_p (Z.of_nat Byte.wordsize)).
        rewrite Byte.modulus_power. reflexivity.
  rewrite ZZ; clear ZZ.     
  rewrite Byte.Ztestbit_mod_two_p; trivial.
  destruct (zlt i (Z.of_nat Byte.wordsize)). trivial. 
  symmetry. rewrite Z.lxor_spec.
  assert (BB: Byte.modulus = two_p (Z.of_nat Byte.wordsize)).
    apply Byte.modulus_power. 
  rewrite BB in H, H0.

  rewrite H; clear H; rewrite H0; clear H0 BB.
   rewrite Byte.Ztestbit_mod_two_p; try omega.
   rewrite Byte.Ztestbit_mod_two_p; try omega.
   destruct (zlt i (Z.of_nat Byte.wordsize)); trivial. omega.
Qed.

Lemma mkArgZ_mkArg_eq : forall (pad : Z) (k : list Z),
   HP.HMAC_SHA256.mkArgZ (map Byte.repr (HP.HMAC_SHA256.mkKey k))
     (Byte.repr pad) = HMAC_SHA256.mkArg (HMAC_SHA256.mkKey k) pad.
Proof.
  intros pad k.
  unfold HP.HMAC_SHA256.mkArgZ.
  unfold HMAC_SHA256.mkArg.
  unfold HP.HMAC_SHA256.mkArg.
  rewrite -> HMAC_mkKey_eq.
  rewrite -> HMAC_64_eq.
  rewrite -> map_map.
  unfold Byte.xor.
  unfold HMAC_SHA256.sixtyfour.
  rewrite -> map_repeat.

  (* Deal with Byte.repr and Byte.unsigned round trip *)
  rewrite -> combine_map.
  rewrite -> map_map.
  Opaque list_repeat.
  simpl.
  (* unfold HMAC_SHA256.mkKey. *)
  f_equal.
  (* TODO: f_equal loses info that key, pad e.g. 92 in range --
    we don't actually know key in range *)
  apply functional_extensionality.
  intros x.
  destruct x.
  simpl.
  repeat rewrite -> Byte.unsigned_repr_eq.

  symmetry.

  (* We know either pad (e.g. 92) is in range (info lost) *)
  assert (z_eq : z = z mod Byte.modulus). admit.
  (* We don't know that the resulting key is in range *)
  assert (z0_eq : z0 = z0 mod Byte.modulus). admit.
  rewrite <- z_eq.
  rewrite <- z0_eq.
  apply xor_inrange.
  apply z_eq. apply z0_eq.
Qed.

Theorem HMAC_functional_prog_Z_equiv : forall (m k : list Z),
                                         HP.HMAC256 m k = HMAC256 m k.
Proof.
  intros m k.
  unfold HMAC256.
  unfold HMAC_SHA256.HMAC.

  unfold HP.HMAC256.
  unfold HP.HMAC_SHA256.HMAC.

  unfold HMAC_SHA256.OUTER.
  unfold HMAC_SHA256.INNER.
  unfold HMAC_SHA256.outerArg.
  unfold HMAC_SHA256.innerArg.

  unfold HP.HMAC_SHA256.OUTER.
  unfold HP.HMAC_SHA256.INNER.
  unfold HP.HMAC_SHA256.outerArg.
  unfold HP.HMAC_SHA256.innerArg.

  rewrite -> HMAC_SHA_eq.
  f_equal.
  f_equal.

  *
    unfold HP.Opad.
    unfold Opad.
    apply mkArgZ_mkArg_eq.
  *
    rewrite -> HMAC_SHA_eq.
    f_equal.
    f_equal.
    unfold HP.Ipad.
    unfold Ipad.
    apply mkArgZ_mkArg_eq.
Qed.

(* ----------------- *)


Definition HMACString (txt passwd:string): list Z :=
  HMAC256 (str_to_Z txt) (str_to_Z passwd).

Definition HMACHex (text password:string): list Z := 
  HMAC256 (hexstring_to_Zlist text) (hexstring_to_Zlist password).

Definition check password text digest := 
  listZ_eq (HMACString text password) (hexstring_to_Zlist digest) = true.

(*a random example, solution obtained via 
  http://www.freeformatter.com/hmac-generator.html#ad-output*)

Goal check "bb" "aa"
      "c1201d3dccfb84c069771d07b3eda4dc26e5b34a4d8634b2bba84fb54d11e265". 
vm_compute. reflexivity. Qed.

Lemma RFC4231_exaple4_2: 
  check "Jefe" "what do ya want for nothing?" 
      "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843".
vm_compute. reflexivity. Qed.

Definition checkHex password text digest := 
  listZ_eq (HMACHex text password) (hexstring_to_Zlist digest) = true.

Lemma RFC6868_example4_2hex: 
  checkHex "4a656665" 
           "7768617420646f2079612077616e7420666f72206e6f7468696e673f"
           "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843".
vm_compute. reflexivity. Qed.

Lemma RFC6868_example4_5hex: 
  checkHex 
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 
    "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374"
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54".
vm_compute. reflexivity. Qed.

Lemma RFC6868_exampleAUTH256_2: 
  checkHex 
  "4a6566654a6566654a6566654a6566654a6566654a6566654a6566654a656665"
  "7768617420646f2079612077616e7420666f72206e6f7468696e673f"
  "167f928588c5cc2eef8e3093caa0e87c9ff566a14794aa61648d81621a2a40c6".
vm_compute. reflexivity. Qed.

End HMAC_progZ.
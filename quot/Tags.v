(* lib/Tags.v

   A generic *tagging* layer over [ZFSet]: a value carries a natural-number
   *tag* in its first component,

        Tag n p = ⟨ natZ n , p ⟩

   so that tag-aware code can recover the tag ([tagOf]) and the payload
   ([payload]) and — crucially — tell values with *different* tags apart.
   Any [nat] may be used as a tag; distinct tags give provably distinct
   values ([Tag_neq]).

   This is pure [ZFSet] infrastructure, independent of any object language and
   of any particular tagged datatype.  A concrete recursive universe of values
   built on top of it (with two tags [Base]/[Fun]) lives in [lib/V2.v]; it was
   factored out of [Timbda.Parametricity]. *)

From Stdlib Require Import ssreflect.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import ClassicalEpsilon.

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.

Require Import ZFSetFacts.
Require Import ZFNotation.
Require Import Diagonal.
Require Import Projections.

(* ================================================================== *)
(** * Tagged values.

    [Tag n p] pairs the numeral tag [natZ n] with a payload [p].  A tagged
    value is just a couple, so [pfst]/[psnd] read off the tag and payload. *)

Definition Tag (n : nat) (p : ZFSet) : ZFSet := ⟨ natZ n , p ⟩.

(* Recognizers: the tag and the payload of a value. *)
Definition tagOf   (v : ZFSet) : ZFSet := pfst v.
Definition payload (v : ZFSet) : ZFSet := psnd v.

Lemma tagOf_Tag   : forall n p, tagOf (Tag n p) = natZ n.
Proof. intros n p. unfold tagOf, Tag. apply pfst_Couple. Qed.
Lemma payload_Tag : forall n p, payload (Tag n p) = p.
Proof. intros n p. unfold payload, Tag. apply psnd_Couple. Qed.

(* The datatype laws: a tagged value determines both its tag and its payload,
   and values with distinct tags are distinct. *)
Lemma Tag_inj_payload : forall n p q, Tag n p = Tag n q -> p = q.
Proof. intros n p q H. exact (Couple_inj_right _ _ _ _ H). Qed.

Lemma Tag_inj_tag : forall n m p q, Tag n p = Tag m q -> n = m.
Proof.
  intros n m p q H. destruct (PeanoNat.Nat.eq_dec n m) as [Heq | Hneq].
  - exact Heq.
  - exfalso. apply (natZ_neq _ _ Hneq). exact (Couple_inj_left _ _ _ _ H).
Qed.

Lemma Tag_neq : forall n m p q, n <> m -> Tag n p <> Tag m q.
Proof.
  intros n m p q Hneq H. apply (natZ_neq _ _ Hneq).
  exact (Couple_inj_left _ _ _ _ H).
Qed.

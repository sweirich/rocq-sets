(** * Foundation.v — membership and pairing are well-founded on [ZFSet].

    The one set-theoretic principle the rest of the library never needed:
    there is no infinite descending [∈]-chain, hence no [∈]-cycle
    [x ∈ … ∈ x].  It is *not* derivable from the other axioms — Aczel's
    anti-foundation axiom is consistent with them, and under AFA the cyclic
    sets this file rules out do exist.  What discharges it here is the
    concrete representation: [Ens] is the inductive type of well-founded
    trees ([sup : forall A : Type, (A -> Ens) -> Ens], with the leaves
    [atom n] and the binary nodes [pair a b]), so [Acc] follows by
    structural induction on the tree, and the quotient by [EQ] carries it to
    [ZFSet] — no rank function or ordinal machinery needed, because the
    quotient identifies [EQ]-equal representatives for us.

    With primitive couples, membership alone does not see the components of
    a couple ([⟨a,b⟩] has no members), so the relation that is well-founded is
    [Below]: "is a member of, or a component of".  Its transitive closure
    [BelowTC] is irreflexive, which is what rules out a value containing (a
    couple containing …) itself.

    Where this matters: a value built by pairing cannot contain itself, which
    is why [LambdaSet]'s [fix] has no coinductive fixed points (a stream
    [o = ⟨1,o⟩] would be such a cycle).  See [PZFSet.PairV_ne_snd] in
    [lib/P_ZFSet.v] and [eval_fix_pair_snd] in [LambdaSet/semantics.v]. *)

Require zf.zfc.Sets.
Import zf.zfc.Sets.

Require Import utils.axioms.
Require Import EnsDefs.

From Stdlib Require Import Relation_Operators.
From Stdlib Require Import Transitive_Closure.
From Stdlib Require Import Wellfounded.Inclusion.

Require Import ZFSetCore.
Require Import ZFNotation.

Open Scope zf_scope.

(** Membership as a relation, for [Acc] / [well_founded]. *)
Definition InRel (x y : ZFSet) : Prop := In x y.

(** Being a component of a couple. *)
Definition CompRel (x y : ZFSet) : Prop :=
  exists z : ZFSet, y = ⟨ x , z ⟩ \/ y = ⟨ z , x ⟩.

(** Member or component. *)
Definition Below (x y : ZFSet) : Prop := InRel x y \/ CompRel x y.

(** A couple is [mk] of a [pair] representative; its components are [mk]
    of the representative's components. *)
Lemma Couple_mk_inv : forall (Y Z : ZFSet) (e : Ens),
  mk e = ⟨ Y , Z ⟩ -> exists a b : Ens, EQ e (pair a b) /\ Y = mk a /\ Z = mk b.
Proof.
  intros Y Z e H.
  rewrite <- (mk_repr Y), <- (mk_repr Z) in H. rewrite Couple_mk in H.
  apply mk_inj in H.
  exists (repr Y), (repr Z). split; [ exact H | split; symmetry; apply mk_repr ].
Qed.

(** The tree under a representative is accessible: a member of [mk (sup A f)]
    is [EQ] to some [f a], and a component of [mk (pair a b)] is [mk a] or
    [mk b]; the quotient turns those [EQ]s into equalities of [ZFSet]s, so the
    structural induction hypotheses apply directly.  Atoms have neither
    members nor components. *)
Lemma Acc_Below_mk : forall e : Ens, Acc Below (mk e).
Proof.
  induction e as [n | a IHa b IHb | A f IH].
  - constructor. intros Y HY. destruct HY as [HY | [z [HY | HY]]].
    + unfold InRel in HY. rewrite <- (mk_repr Y) in HY. rewrite In_mk in HY.
      destruct HY.
    + destruct (Couple_mk_inv _ _ _ HY) as [a [b [He _]]]. destruct He.
    + destruct (Couple_mk_inv _ _ _ HY) as [a [b [He _]]]. destruct He.
  - constructor. intros Y HY. destruct HY as [HY | [z [HY | HY]]].
    + unfold InRel in HY. rewrite <- (mk_repr Y) in HY. rewrite In_mk in HY.
      destruct HY.
    + destruct (Couple_mk_inv _ _ _ HY) as [a' [b' [He [HY' _]]]].
      destruct He as [Ha _]. rewrite HY'. rewrite <- (mk_eq _ _ Ha). exact IHa.
    + destruct (Couple_mk_inv _ _ _ HY) as [a' [b' [He [_ HY']]]].
      destruct He as [_ Hb]. rewrite HY'. rewrite <- (mk_eq _ _ Hb). exact IHb.
  - constructor. intros Y HY. destruct HY as [HY | [z [HY | HY]]].
    + revert HY. pattern Y; apply ZFSet_ind1; clear Y; intros ey HY.
      unfold InRel in HY. rewrite In_mk in HY.
      destruct HY as [a Ha].
      rewrite (mk_eq ey (f a) Ha). exact (IH a).
    + destruct (Couple_mk_inv _ _ _ HY) as [a [b [He _]]]. destruct He.
    + destruct (Couple_mk_inv _ _ _ HY) as [a [b [He _]]]. destruct He.
Qed.

Theorem Below_wf : well_founded Below.
Proof. intro X. pattern X; apply ZFSet_ind1. exact Acc_Below_mk. Qed.

Theorem InRel_wf : well_founded InRel.
Proof.
  apply wf_incl with Below; [ | exact Below_wf ].
  intros x y H. left. exact H.
Qed.

(** The transitive closures: [x] is *hereditarily* a member of [y], resp.
    hereditarily a member or component. *)
Definition InTC : ZFSet -> ZFSet -> Prop := clos_trans ZFSet InRel.
Definition BelowTC : ZFSet -> ZFSet -> Prop := clos_trans ZFSet Below.

Theorem InTC_wf : well_founded InTC.
Proof. apply wf_clos_trans. exact InRel_wf. Qed.

Theorem BelowTC_wf : well_founded BelowTC.
Proof. apply wf_clos_trans. exact Below_wf. Qed.

Lemma Acc_irrefl {A : Type} (R : A -> A -> Prop) (x : A) : Acc R x -> ~ R x x.
Proof. induction 1 as [x _ IH]. intro H. exact (IH x H H). Qed.

(** **Foundation.**  No value is hereditarily a member or component of itself. *)
Theorem BelowTC_irrefl : forall x : ZFSet, ~ BelowTC x x.
Proof. intro x. apply Acc_irrefl. apply BelowTC_wf. Qed.

Theorem InTC_irrefl : forall x : ZFSet, ~ InTC x x.
Proof. intro x. apply Acc_irrefl. apply InTC_wf. Qed.

(** No set is a member of itself — the one-step instance. *)
Corollary In_irrefl : forall x : ZFSet, ~ (x ∈ x).
Proof. intros x Hx. apply (InTC_irrefl x). apply t_step. exact Hx. Qed.

(** The chains below are built by hand rather than by a tactic, so the
    combinators are worth naming. *)
Lemma InTC_step (x y : ZFSet) : x ∈ y -> InTC x y.
Proof. intro H. apply t_step. exact H. Qed.

Lemma InTC_cons (x y z : ZFSet) : x ∈ y -> InTC y z -> InTC x z.
Proof. intros H1 H2. exact (t_trans _ _ _ _ _ (t_step _ _ _ _ H1) H2). Qed.

Lemma BelowTC_mem (x y : ZFSet) : x ∈ y -> BelowTC x y.
Proof. intro H. apply t_step. left. exact H. Qed.

Lemma BelowTC_fst (x z : ZFSet) : BelowTC x ⟨ x , z ⟩.
Proof. apply t_step. right. exists z. left. reflexivity. Qed.

Lemma BelowTC_snd (x z : ZFSet) : BelowTC x ⟨ z , x ⟩.
Proof. apply t_step. right. exists z. right. reflexivity. Qed.

Lemma BelowTC_cons_mem (x y z : ZFSet) : x ∈ y -> BelowTC y z -> BelowTC x z.
Proof. intros H1 H2. exact (t_trans _ _ _ _ _ (BelowTC_mem _ _ H1) H2). Qed.

Lemma BelowTC_trans (x y z : ZFSet) : BelowTC x y -> BelowTC y z -> BelowTC x z.
Proof. intros H1 H2. exact (t_trans _ _ _ _ _ H1 H2). Qed.

(** A four-step [∈]-cycle is impossible. *)
Corollary In_no_4cycle (a b c d : ZFSet) :
  a ∈ b -> b ∈ c -> c ∈ d -> d ∈ a -> False.
Proof.
  intros H1 H2 H3 H4. apply (InTC_irrefl a).
  apply (InTC_cons a b a H1).
  apply (InTC_cons b c a H2).
  apply (InTC_cons c d a H3).
  apply InTC_step. exact H4.
Qed.

(** No couple is one of its own components. *)
Corollary Couple_ne_fst : forall a b : ZFSet, ⟨ a , b ⟩ <> a.
Proof.
  intros a b H. apply (BelowTC_irrefl a).
  rewrite <- H at 2. apply BelowTC_fst.
Qed.

Corollary Couple_ne_snd : forall a b : ZFSet, ⟨ a , b ⟩ <> b.
Proof.
  intros a b H. apply (BelowTC_irrefl b).
  rewrite <- H at 2. apply BelowTC_snd.
Qed.

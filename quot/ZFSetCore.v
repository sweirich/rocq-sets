(** * ZFSetCore.v — the quotient construction and the Ens-lifted interface.

    This file is the *implementation* layer of the quotient set theory: it
    is the only place that knows [ZFSet = quot Ens].  Everything here is
    either a definition of a ZFSet operation (lifted from [EnsDefs.v]) or a
    lemma proved by *descending to the underlying [Ens] representation* —
    the proofs use [quot_ind], [mk], [In_mk], [mk_eq], the [*_mk]
    computation rules, and the [EnsLib] / [EnsNat] / [Hierarchy] lemmas.

    The *abstract* theory built on top of this interface — reasoning purely
    at the [ZFSet] level, never unfolding [mk] — lives in [ZFSetFacts.v].
    Downstream code should [Require Import ZFSets], the umbrella that
    re-exports both. *)

Require zf.zfc.Sets.
Require zf.zfc.Axioms.
Require zf.zfc.Cartesian.
Require zf.zfc.Omega.
Require zf.zfc.Hierarchy.

Import zf.zfc.Sets.
Import zf.zfc.Axioms.
Import zf.zfc.Cartesian.
Import zf.zfc.Omega.
Import zf.zfc.Hierarchy.

Require Import utils.axioms.
Require Import EnsNotation.
Require EnsLib.
Require EnsNat.

From Stdlib Require Import Logic.Epsilon.

(* Re-enable just the typeclass instances from [EnsLib] (Proper /
   Equivalence) without bringing its bare lemma names into scope —
   they are referenced as [EnsLib.X] throughout this file. *)
#[export] Existing Instances
  EnsLib.EQ_Equivalence
  EnsLib.Sing_Proper
  EnsLib.Paire_Proper
  EnsLib.Couple_Proper
  EnsLib.Union_Proper
  EnsLib.BinUnion_Proper
  EnsLib.IN_Proper_left
  EnsLib.IN_Proper_right
  EnsLib.INC_Proper_left
  EnsLib.INC_Proper_right
  EnsLib.iUnion_Proper
  EnsLib.pfst_Proper
  EnsLib.psnd_Proper
  EnsLib.dom_Proper
  EnsLib.rng_Proper
  EnsLib.image_Proper
  EnsLib.Power_Proper
  EnsLib.Prod_Proper
  EnsNat.natZAdd_Proper
  EnsNat.natZSucc_Proper
  EnsNat.natZPred_Proper.

(* [ens_scope] is transitively opened by EnsLib via EnsNotation and
   is kept open inside this file so that Ens-level terms appearing in
   ZFSet definitions and proofs render with the [⟨·,·⟩], [{|·|}], [≃],
   [∈], etc. notations. It is closed at the bottom of the file because
   downstream [ZFNotation.v] rebinds the same symbols in [zf_scope]. *)

From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Logic.Epsilon.

(** * Quotient-based set theory.

    [ZFSet] is the quotient of the sorted [Ens] (atoms, couples, sets) by
    extensional equality [EQ]; equality on [ZFSet] is Coq's Leibniz [=].
    The sort of a value is read off through [IsAtom] / [IsPair] / [IsSet].  Each [Ens]-level
    operation whose soundness lemma is in [EnsDefs.v] / [EnsLib.v] /
    [EnsNat.v] lifts to a [ZFSet]-level operation using [quot_map] /
    [quot_map2], and its lemmas are restated here on [ZFSet].

    Operations that take a function argument ([iUnion], [Pi])
    are lifted via [repr], which chooses a representative of a
    [ZFSet] using Hilbert's epsilon (the development already relies
    on this through [natOfEns]). *)


(** ** The quotient type and helpers *)

Definition ZFSet : Type := quot EQ.
Definition mk (e : Ens) : ZFSet := to_quot e.

Lemma mk_eq : forall x y : Ens, x ≃ y -> mk x = mk y.
Proof. intros x y H; apply quot_ext; exact H. Qed.

Lemma mk_inj : forall x y : Ens, mk x = mk y -> x ≃ y.
Proof. intros x y H; apply quot_eq; exact H. Qed.


Lemma ZFSet_ind1 :
  forall P : ZFSet -> Prop,
  (forall x : Ens, P (mk x)) -> forall X, P X.
Proof. intros P H X; pattern X; apply quot_ind. exact H. Qed.

Lemma ZFSet_ind2 :
  forall P : ZFSet -> ZFSet -> Prop,
  (forall x y : Ens, P (mk x) (mk y)) -> forall X Y, P X Y.
Proof.
  intros P H X Y.
  pattern X; apply quot_ind. intros x.
  pattern Y; apply quot_ind. intros y.
  apply H.
Qed.

Lemma ZFSet_ind3 :
  forall P : ZFSet -> ZFSet -> ZFSet -> Prop,
  (forall x y z : Ens, P (mk x) (mk y) (mk z)) ->
  forall X Y Z, P X Y Z.
Proof.
  intros P H X Y Z.
  pattern X; apply quot_ind. intros x.
  pattern Y; apply quot_ind. intros y.
  pattern Z; apply quot_ind. intros z.
  apply H.
Qed.

(** ** Choosing a representative of a [ZFSet].

    [repr X] picks some [Ens] with [mk (repr X) = X]; used to lift
    [ZFSet -> ZFSet] arguments back down to [Ens -> Ens]. *)

Definition repr (X : ZFSet) : Ens :=
  epsilon (inhabits ∅) (fun e => to_quot e = X).

Lemma repr_eq : forall X : ZFSet, to_quot (repr X) = X.
Proof.
  intros X. unfold repr.
  apply (epsilon_spec (inhabits ∅) (fun e => to_quot e = X)).
  pattern X; apply quot_ind. intros x. exists x. reflexivity.
Qed.

Lemma mk_repr : forall X : ZFSet, mk (repr X) = X.
Proof. exact repr_eq. Qed.

Lemma repr_sound : forall X Y : ZFSet, X = Y -> repr X ≃ repr Y.
Proof.
  intros X Y H. apply quot_eq. rewrite !repr_eq. exact H.
Qed.

Definition liftF (F : ZFSet -> ZFSet) (e : Ens) : Ens := repr (F (mk e)).

#[global] Instance liftF_Proper (F : ZFSet -> ZFSet) :
  Proper (EQ ==> EQ) (liftF F).
Proof.
  intros x y H. unfold liftF.
  apply repr_sound. f_equal. apply quot_ext; exact H.
Qed.


(** ** Constants and operations lifted from [EnsDefs.v] *)

Definition Empty    : ZFSet                  := mk ∅.
Definition Omega    : ZFSet                  := mk ω.

Definition Sing     : ZFSet -> ZFSet         := quot_map Sing.
Definition Paire    : ZFSet -> ZFSet -> ZFSet := quot_map2 Paire.
Definition Couple   : ZFSet -> ZFSet -> ZFSet := quot_map2 Couple.
Definition Union    : ZFSet -> ZFSet         := quot_map Union.


(** *** Membership and inclusion.

    [IN] and [INC] are lifted by a double [quot_rec]; the inner
    instance ([{IN,INC}_inner_Proper]) discharges the soundness
    obligation of the outer [quot_rec]. *)

#[global] Instance In_inner_Proper (B : ZFSet) :
  Proper (EQ ==> eq) (fun x : Ens => quot_rec (IN x) B).
Proof.
  intros x x' Hx.
  pattern B; apply quot_ind. intros y.
  rewrite !quot_rec_eq. apply prop_ext.
  split; intro H.
  - apply IN_sound_left with x; assumption.
  - apply IN_sound_left with x';
      [apply EQ_sym; assumption | assumption].
Qed.

(* Set membership *)
Definition In (a B : ZFSet) : Prop :=
  quot_rec (fun x : Ens => quot_rec (IN x) B) a.

#[global] Instance Inc_inner_Proper (B : ZFSet) :
  Proper (EQ ==> eq) (fun x : Ens => quot_rec (INC x) B).
Proof.
  intros x x' Hx.
  pattern B; apply quot_ind. intros y.
  rewrite !quot_rec_eq.
  apply EnsLib.INC_Proper_left; exact Hx.
Qed.

Lemma In_mk : forall x y : Ens, In (mk x) (mk y) = (x ∈ y).
Proof.
  intros x y. unfold In, mk.
  rewrite quot_rec_eq, quot_rec_eq. reflexivity.
Qed.


(* Set inclusion *)
Definition Inc (a B : ZFSet) : Prop :=
  quot_rec (fun x : Ens => quot_rec (INC x) B) a.

Lemma Inc_mk : forall x y : Ens, Inc (mk x) (mk y) = (x ⊆ y).
Proof.
  intros x y. unfold Inc, mk.
  rewrite quot_rec_eq, quot_rec_eq. reflexivity.
Qed.


(** *** The three sorts of values.

    A value is an atom (a numeral), a couple, or a set; the predicates lift
    the [Ens]-level sort tests.  [IsSet] is a *class*, so that the sortedness
    premises of the lemmas below ([Inc_def], [Union_Sing], [Inc_IN_Power], …)
    are discharged by instance resolution whenever the set is built by a
    set-former. *)

#[global] Instance is_set_Proper : Proper (EQ ==> eq) is_set.
Proof. intros x y H. apply prop_ext. apply EnsLib.is_set_iff. exact H. Qed.

#[global] Instance is_atom_Proper : Proper (EQ ==> eq) is_atom.
Proof.
  intros x y H. apply prop_ext. split; intro Hs.
  - apply EQ_is_atom with x; assumption.
  - apply EQ_is_atom with y; [ apply EQ_sym | ]; assumption.
Qed.

#[global] Instance is_pair_Proper : Proper (EQ ==> eq) is_pair.
Proof.
  intros x y H. apply prop_ext. split; intro Hs.
  - apply EQ_is_pair with x; assumption.
  - apply EQ_is_pair with y; [ apply EQ_sym | ]; assumption.
Qed.

Definition IsSet  (X : ZFSet) : Prop := quot_rec is_set X.
Definition IsAtom (X : ZFSet) : Prop := quot_rec is_atom X.
Definition IsPair (X : ZFSet) : Prop := quot_rec is_pair X.

Existing Class IsSet.

Lemma IsSet_mk  : forall e : Ens, IsSet (mk e) = is_set e.
Proof. intro e. unfold IsSet, mk. rewrite quot_rec_eq. reflexivity. Qed.

Lemma IsAtom_mk : forall e : Ens, IsAtom (mk e) = is_atom e.
Proof. intro e. unfold IsAtom, mk. rewrite quot_rec_eq. reflexivity. Qed.

Lemma IsPair_mk : forall e : Ens, IsPair (mk e) = is_pair e.
Proof. intro e. unfold IsPair, mk. rewrite quot_rec_eq. reflexivity. Qed.

(** A [ZFSet] known to be a set has a set as representative. *)
Lemma IsSet_repr : forall X : ZFSet, IsSet X -> is_set (repr X).
Proof. intros X H. rewrite <- IsSet_mk. rewrite mk_repr. exact H. Qed.

(** Every value is an atom, a couple, or a set. *)
Lemma ZFSet_sorts : forall X : ZFSet, IsAtom X \/ IsPair X \/ IsSet X.
Proof.
  intro X. pattern X; apply quot_ind. intros e.
  rewrite IsAtom_mk, IsPair_mk, IsSet_mk.
  destruct e; [ left | right; left | right; right ]; exact I.
Qed.

(** The sorts are exclusive. *)
Lemma IsAtom_not_IsSet : forall X : ZFSet, IsAtom X -> ~ IsSet X.
Proof.
  intro X. pattern X; apply quot_ind. intros e. rewrite IsAtom_mk, IsSet_mk.
  destruct e; simpl; tauto.
Qed.

Lemma IsPair_not_IsSet : forall X : ZFSet, IsPair X -> ~ IsSet X.
Proof.
  intro X. pattern X; apply quot_ind. intros e. rewrite IsPair_mk, IsSet_mk.
  destruct e; simpl; tauto.
Qed.

Lemma IsAtom_not_IsPair : forall X : ZFSet, IsAtom X -> ~ IsPair X.
Proof.
  intro X. pattern X; apply quot_ind. intros e. rewrite IsAtom_mk, IsPair_mk.
  destruct e; simpl; tauto.
Qed.

(** Only a set has members. *)
Lemma In_IsSet : forall x X : ZFSet, In x X -> IsSet X.
Proof.
  apply (ZFSet_ind2 (fun x X => In x X -> IsSet X)). intros ex eX.
  rewrite In_mk, IsSet_mk. apply IN_is_set.
Qed.

(** *** Equality is extensional.

    [Inc_def] reads an inclusion off the members; its [<-] direction needs
    the left side to be a set (an atom or couple is included only in itself).
    The premise is a class argument, so [apply Inc_def] / [rewrite Inc_def]
    discharge it by instance resolution on any set-former. *)

Lemma Inc_def (A B : ZFSet) (H : IsSet A) :
  Inc A B <-> (forall x, In x A -> In x B).
Proof.
  revert A B H.
  apply (ZFSet_ind2 (fun A B => IsSet A -> (Inc A B <-> (forall x, In x A -> In x B)))).
  intros eA eB H.
  rewrite IsSet_mk in H. rewrite Inc_mk. split.
  - intros HINC x. pattern x; apply quot_ind. intros ex.
    rewrite !In_mk. exact (INC_elim _ _ HINC ex).
  - intros H0. apply INC_intro; [ exact H | ].
    intros ex Hex. specialize (H0 (mk ex)). rewrite !In_mk in H0.
    apply H0; exact Hex.
Qed.

(** Introduction: a set included member-wise.  [apply] does not resolve the
    class premise after unification, so the tactic [inc_def] below applies
    the lemma and discharges the premise by instance resolution. *)
Lemma Inc_intro (A B : ZFSet) (H : IsSet A) :
  (forall x, In x A -> In x B) -> Inc A B.
Proof. intro H0. apply (Inc_def A B H). exact H0. Qed.

(** Elimination, for every sort of [A]: no premise. *)
Lemma Inc_elim (A B : ZFSet) : Inc A B -> forall x, In x A -> In x B.
Proof.
  revert A B. apply (ZFSet_ind2 (fun A B => Inc A B -> forall x, In x A -> In x B)).
  intros eA eB HI x. pattern x; apply quot_ind. intros ex.
  rewrite Inc_mk in HI. rewrite !In_mk. exact (INC_elim _ _ HI ex).
Qed.

Ltac inc_def := apply Inc_intro; [ typeclasses eauto | ].

(** Turn an inclusion hypothesis into its member-wise form. *)
Ltac inc_elim H :=
  let H' := fresh "H" in
  pose proof (Inc_elim _ _ H) as H'; clear H; rename H' into H.

(** Forward application of an inclusion, for every sort of [A]. *)
Lemma Inc_IN : forall A B x, Inc A B -> In x A -> In x B.
Proof.
  apply (ZFSet_ind3 (fun A B x => Inc A B -> In x A -> In x B)). intros eA eB ex.
  rewrite Inc_mk, !In_mk. intros HI Hx. exact (INC_elim _ _ HI ex Hx).
Qed.

(** Something included in a set is a set (an atom or couple is included only
    in itself). *)
Lemma Inc_IsSet : forall X Y : ZFSet, Inc X Y -> IsSet Y -> IsSet X.
Proof.
  apply (ZFSet_ind2 (fun X Y => Inc X Y -> IsSet Y -> IsSet X)). intros eX eY.
  rewrite Inc_mk, !IsSet_mk. intros HI HY.
  destruct eX as [n | a b | A f]; [ | | exact I ]; simpl in HI;
    destruct eY; simpl in HY; contradiction.
Qed.

(** Inclusion out of a non-set is equality; inclusion of a set into a non-set
    forces the set to be empty. *)
Lemma Inc_not_set_eq : forall X Y : ZFSet, ~ IsSet X -> Inc X Y -> X = Y.
Proof.
  apply (ZFSet_ind2 (fun X Y => ~ IsSet X -> Inc X Y -> X = Y)). intros eX eY.
  rewrite IsSet_mk, Inc_mk. intros HX HI. apply mk_eq.
  destruct eX as [n | a b | A f]; [ exact HI | exact HI | exfalso; apply HX; exact I ].
Qed.

Lemma Inc_not_set_no_mem : forall X Y : ZFSet, ~ IsSet Y -> Inc X Y -> forall z, ~ In z X.
Proof.
  intros X Y HY HI z Hz. apply HY. apply In_IsSet with z. exact (Inc_IN _ _ _ HI Hz).
Qed.

(** Extensionality needs no sortedness premise: inclusion is kind-aware. *)
Lemma set_ext : forall X Y, Inc X Y -> Inc Y X -> X = Y.
Proof.
  apply (ZFSet_ind2 (fun X Y => Inc X Y -> Inc Y X -> X = Y)). intros eX eY H1 H2.
  rewrite Inc_mk in H1, H2. apply mk_eq. apply INC_EQ; assumption.
Qed.

(** Extensionality for sets, member-wise. *)
Lemma set_ext_mem : forall X Y, IsSet X -> IsSet Y ->
  (forall z, In z X <-> In z Y) -> X = Y.
Proof.
  intros X Y HX HY H. apply set_ext.
  - apply (Inc_intro X Y HX). intros z Hz. apply H; exact Hz.
  - apply (Inc_intro Y X HY). intros z Hz. apply H; exact Hz.
Qed.


(** *** Comprehension. *)

Lemma Comp_mk_Proper (P : ZFSet -> Prop) :
  Proper (EQ ==> EQ) (fun e => ⦃ x ∈ e | P (mk x) ⦄).
Proof.
  intros e e' H.
  apply EnsLib.Comp_sound_left; [|exact H].
  intros w1 w2 Pw Heq.
  assert (mk w1 = mk w2) as Hmk by (apply quot_ext; exact Heq).
  rewrite <- Hmk. exact Pw.
Qed.

Definition Comp (E : ZFSet) (P : ZFSet -> Prop) : ZFSet :=
  quot_rec (fun e => mk (⦃ x ∈ e | P (mk x) ⦄))
    (p := fun e e' H => quot_ext _ _ (Comp_mk_Proper P e e' H)) E.

(** Comprehension helpers: introduction, elimination, and inclusion.
    Predicates [P : ZFSet -> Prop] are automatically sound under [=]
    on [ZFSet], so the Ens-level soundness side condition collapses. *)

Lemma Comp_mk : forall (e : Ens) (P : ZFSet -> Prop),
  Comp (mk e) P = mk ⦃ x ∈ e | P (mk x) ⦄.
Proof. intros e P. unfold Comp, mk. rewrite quot_rec_eq. reflexivity. Qed.

(* Predicates [P : ZFSet -> Prop] composed with [mk] are sound under
   [EQ] on [Ens] because [EQ w1 w2] implies [mk w1 = mk w2]. *)
Local Lemma Comp_pred_sound (P : ZFSet -> Prop) :
  forall w1 w2 : Ens, P (mk w1) -> EQ w1 w2 -> P (mk w2).
Proof.
  intros w1 w2 Pw1 Hw12.
  rewrite <- (mk_eq _ _ Hw12). exact Pw1.
Qed.

Lemma In_Comp_P : forall (E : ZFSet) (P : ZFSet -> Prop) (x : ZFSet),
  In x (Comp E P) -> P x.
Proof.
  intros E P x.
  pattern E; apply quot_ind; intros eE.
  pattern x; apply quot_ind; intros ex.
  rewrite Comp_mk. unfold mk; rewrite In_mk; intro H.
  exact (IN_Comp_P eE ex (fun y => P (mk y)) (Comp_pred_sound P) H).
Qed.

Lemma In_P_Comp : forall (E : ZFSet) (P : ZFSet -> Prop) (x : ZFSet),
  In x E -> P x -> In x (Comp E P).
Proof.
  intros E P x.
  pattern E; apply quot_ind; intros eE.
  pattern x; apply quot_ind; intros ex.
  rewrite Comp_mk. unfold mk; rewrite !In_mk; intros HxE HPx.
  exact (IN_P_Comp eE ex (fun y => P (mk y))
           (Comp_pred_sound P) HxE HPx).
Qed.


(** [Inter E] is the intersection of all members of [E]. Defined
    ZF-style via comprehension over [⋃ E], so that the (membership
    on ZFSet is Leibniz) predicate carries no soundness obligation.
    Matches zfc's [Inter'] (extensionally equal to its primitive
    [Inter]). When [E] is empty, [Inter E] is [Empty] under this
    definition (rather than a proper class). *)
Definition Inter (E : ZFSet) : ZFSet :=
  Comp (Union E) (fun x => forall a : ZFSet, In a E -> In x a).


(** *** Indexed union, dependent product. *)

#[global] Instance iUnion_liftF_Proper (F : ZFSet -> ZFSet) :
  Proper (EQ ==> EQ) (fun e => x ← e ;; liftF F x).
Proof.
  intros e e' H. apply (EnsLib.iUnion_Proper _ _ H).
  intros u v Huv. apply liftF_Proper; exact Huv.
Qed.

Definition iUnion (E : ZFSet) (F : ZFSet -> ZFSet) : ZFSet :=
  quot_map (fun e => x ← e ;; liftF F x) E.

Definition Power : ZFSet -> ZFSet := quot_map Power.
Definition Prod  : ZFSet -> ZFSet -> ZFSet := quot_map2 Prod.



(** *** Werner-pair projections.

    [pfst]/[psnd] are the irreducible lifted primitives, and live here.
    Everything derived from them — the discriminators [is_subsingleton] /
    [is_nonempty], the pattern unions [iUnion_pat] / [iUnion_pat3], the triple
    projections [proj1]/[proj2]/[proj3], the relational [dom]/[rng]/[image] and
    [applyFun] — is in [zf/quot/ZFDefs.v]. *)

Definition pfst : ZFSet -> ZFSet := quot_map EnsDefs.pfst.
Definition psnd : ZFSet -> ZFSet := quot_map EnsDefs.psnd.


(** *** Naturals (from [EnsNat.v]). *)

Definition natZ (n : nat) : ZFSet := mk (EnsDefs.natZ n).
Definition natZAdd : ZFSet -> ZFSet -> ZFSet := quot_map2 EnsNat.natZAdd.
Definition natZSucc : ZFSet -> ZFSet         := quot_map EnsNat.natZSucc.
Definition natZPred : ZFSet -> ZFSet         := quot_map EnsNat.natZPred.


(** ** Computation rules for the lifted operations. *)

Lemma Union_mk    e   : Union (mk e)        = mk (⋃ e).
Proof. apply quot_map_eq. Qed.

Lemma Sing_mk     e   : Sing (mk e)         = mk {| e |}.
Proof. apply quot_map_eq. Qed.

Lemma natZSucc_mk e   : natZSucc (mk e)     = mk (EnsNat.natZSucc e).
Proof. apply quot_map_eq. Qed.

Lemma natZPred_mk e   : natZPred (mk e)     = mk (EnsNat.natZPred e).
Proof. apply quot_map_eq. Qed.

Lemma Paire_mk    e f : Paire (mk e) (mk f) = mk {| e ; f |}.
Proof. apply quot_map2_eq. Qed.

Lemma Couple_mk   e f : Couple (mk e) (mk f) = mk ⟨ e , f ⟩.
Proof. apply quot_map2_eq. Qed.

(** A singleton is the pair of its element with itself. *)
Lemma Sing_eq_Paire : forall X : ZFSet, Sing X = Paire X X.
Proof.
  intro X. pattern X; apply quot_ind. intro e. rewrite Sing_mk, Paire_mk. reflexivity.
Qed.

Lemma pfst_mk     e   : pfst (mk e) = mk (EnsDefs.pfst e).
Proof. apply quot_map_eq. Qed.

Lemma psnd_mk     e   : psnd (mk e) = mk (EnsDefs.psnd e).
Proof. apply quot_map_eq. Qed.


Lemma Power_mk e : Power (mk e) = mk (Axioms.Power e).
Proof. apply quot_map_eq. Qed.

Lemma Prod_mk  e f : Prod (mk e) (mk f) = mk (Cartesian.Prod e f).
Proof. apply quot_map2_eq. Qed.

Lemma natZAdd_mk  e f : natZAdd (mk e) (mk f) = mk (EnsNat.natZAdd e f).
Proof. apply quot_map2_eq. Qed.


(** ** Lifted lemmas. *)

(** *** Membership-introduction lemmas (from [Sets.v] / [Axioms.v]). *)

Lemma IN_Sing : forall x : ZFSet, In x (Sing x).
Proof.
  intro x. pattern x; apply quot_ind. intros e.
  unfold Sing. rewrite quot_map_eq.
  unfold mk. rewrite In_mk. apply IN_Sing.
Qed.

Lemma IN_Sing_EQ :
  forall x y : ZFSet, In x (Sing y) -> x = y.
Proof.
  intros x y. pattern x; apply quot_ind. intros ex.
  pattern y; apply quot_ind. intros ey.
  unfold Sing. rewrite quot_map_eq.
  unfold mk. rewrite In_mk.
  intro H. apply mk_eq, IN_Sing_EQ; exact H.
Qed.

Lemma IN_Paire_left  : forall a b : ZFSet, In a (Paire a b).
Proof.
  intros a b. pattern a; apply quot_ind. intros ea.
  pattern b; apply quot_ind. intros eb.
  rewrite Paire_mk. unfold mk; rewrite In_mk.
  apply IN_Paire_left.
Qed.

Lemma IN_Paire_right : forall a b : ZFSet, In b (Paire a b).
Proof.
  intros a b. pattern a; apply quot_ind. intros ea.
  pattern b; apply quot_ind. intros eb.
  rewrite Paire_mk. unfold mk; rewrite In_mk.
  apply IN_Paire_right.
Qed.

Lemma Paire_IN :
  forall a b x : ZFSet, In x (Paire a b) -> x = a \/ x = b.
Proof.
  intros a b x.
  pattern x; apply quot_ind. intros ex.
  pattern a; apply quot_ind. intros ea.
  pattern b; apply quot_ind. intros eb.
  rewrite Paire_mk. unfold mk; rewrite In_mk.
  intro H. destruct (Paire_IN _ _ _ H) as [Heq | Heq];
    [left | right]; apply mk_eq; assumption.
Qed.


(** *** Union laws (from [Axioms.v] and [EnsLib.v]). *)

Lemma IN_Union :
  forall E Y X : ZFSet, In Y E -> In X Y -> In X (Union E).
Proof.
  intros E Y X.
  pattern E; apply quot_ind. intros eE.
  pattern Y; apply quot_ind. intros eY.
  pattern X; apply quot_ind. intros eX.
  rewrite Union_mk. unfold mk. rewrite !In_mk.
  apply IN_Union.
Qed.

Lemma IN_Inc_Union :
  forall (E Y : ZFSet) (H : IsSet Y), In Y E -> Inc Y (Union E).
Proof.
  apply (ZFSet_ind2 (fun E Y => IsSet Y -> In Y E -> Inc Y (Union E))). intros eE eY.
  rewrite Union_mk, IsSet_mk, In_mk, Inc_mk.
  apply IN_INC_Union.
Qed.

Lemma Union_IN :
  forall E X : ZFSet,
  In X (Union E) -> exists Y : ZFSet, In Y E /\ In X Y.
Proof.
  intros E X.
  pattern E; apply quot_ind. intros eE.
  pattern X; apply quot_ind. intros eX.
  rewrite Union_mk. unfold mk. rewrite In_mk.
  intro H. destruct (Union_IN _ _ H) as [eY [HYE HXY]].
  exists (mk eY). unfold mk; rewrite !In_mk. split; assumption.
Qed.

Lemma Union_mon :
  forall E E' : ZFSet, Inc E E' -> Inc (Union E) (Union E').
Proof.
  intros E E'.
  pattern E; apply quot_ind. intros eE.
  pattern E'; apply quot_ind. intros eE'.
  rewrite !Union_mk, !Inc_mk. apply Union_mon.
Qed.

Lemma Union_Sing : forall (E : ZFSet) (H : IsSet E), Union (Sing E) = E.
Proof.
  intro E. pattern E; apply quot_ind. intros e H.
  rewrite IsSet_mk in H. rewrite Sing_mk, Union_mk.
  apply mk_eq, EnsLib.Union_Sing. exact H.
Qed.



(** *** Indexed union laws (from [EnsLib.v]).

    The [iUnion] introduction / elimination and equational laws are
    stated; the proofs of the equational laws depend on
    [EnsLib.iUnion_Sing_l] / [EnsLib.iUnion_Sing_r] / [EnsLib.iUnion_assoc] in [EnsLib.v]
    which are themselves still admitted there. *)

Lemma iUnion_mk (e0 : Ens) (F : ZFSet -> ZFSet) :
  iUnion (mk e0) F = mk (EnsDefs.iUnion e0 (liftF F)).
Proof.
  unfold iUnion, mk.
  exact (quot_map_eq (fun e1 => EnsDefs.iUnion e1 (liftF F)) e0).
Qed.

(** ** Sortedness instances: every set-former yields a set. *)

#[global] Instance IsSet_Empty : IsSet Empty.
Proof. unfold Empty. rewrite IsSet_mk. exact I. Qed.

#[global] Instance IsSet_Omega : IsSet Omega.
Proof. unfold Omega. rewrite IsSet_mk. exact I. Qed.

#[global] Instance IsSet_Sing : forall X : ZFSet, IsSet (Sing X).
Proof. intro X. pattern X; apply quot_ind. intro e. rewrite Sing_mk, IsSet_mk. exact I. Qed.

#[global] Instance IsSet_Paire : forall X Y : ZFSet, IsSet (Paire X Y).
Proof.
  apply (ZFSet_ind2 (fun X Y => IsSet (Paire X Y))). intros ex ey.
  rewrite Paire_mk, IsSet_mk. exact I.
Qed.

#[global] Instance IsSet_Union : forall X : ZFSet, IsSet (Union X).
Proof.
  intro X. pattern X; apply quot_ind. intro e. rewrite Union_mk, IsSet_mk.
  apply Union_is_set.
Qed.

#[global] Instance IsSet_Comp : forall (E : ZFSet) (P : ZFSet -> Prop), IsSet (Comp E P).
Proof.
  intros E P. pattern E; apply quot_ind. intro e. rewrite Comp_mk, IsSet_mk.
  apply Comp_is_set.
Qed.

#[global] Instance IsSet_Inter : forall E : ZFSet, IsSet (Inter E).
Proof. intro E. unfold Inter. apply IsSet_Comp. Qed.

#[global] Instance IsSet_iUnion : forall (E : ZFSet) (F : ZFSet -> ZFSet), IsSet (iUnion E F).
Proof.
  intros E F. pattern E; apply quot_ind. intro e. rewrite iUnion_mk, IsSet_mk.
  apply EnsLib.iUnion_is_set.
Qed.

(** An indexed union over a non-set is empty. *)
Lemma iUnion_not_set : forall (E : ZFSet) (F : ZFSet -> ZFSet), ~ IsSet E -> iUnion E F = Empty.
Proof.
  intros E F. pattern E; apply quot_ind. intros e H. rewrite IsSet_mk in H.
  rewrite iUnion_mk. unfold Empty. apply mk_eq.
  destruct e as [n | a b | A f]; [ apply EQ_refl | apply EQ_refl | exfalso; apply H; exact I ].
Qed.

#[global] Instance IsSet_Power : forall X : ZFSet, IsSet (Power X).
Proof.
  intro X. pattern X; apply quot_ind. intro e. rewrite Power_mk, IsSet_mk.
  apply Power_is_set.
Qed.

#[global] Instance IsSet_Prod : forall X Y : ZFSet, IsSet (Prod X Y).
Proof.
  apply (ZFSet_ind2 (fun X Y => IsSet (Prod X Y))). intros ex ey.
  rewrite Prod_mk, IsSet_mk. apply Prod_is_set.
Qed.


Lemma iUnion_Vide :
  forall F : ZFSet -> ZFSet, iUnion Empty F = Empty.
Proof.
  intro F. unfold Empty. rewrite iUnion_mk.
  apply mk_eq, EnsLib.iUnion_Vide.
Qed.

Lemma iUnion_Sing_r :
  forall (E : ZFSet) (H : IsSet E), iUnion E (fun x => Sing x) = E.
Proof.
  intro E.
  pattern E; apply quot_ind. intros eE H.
  rewrite IsSet_mk in H.
  cbv beta. fold (mk eE).
  rewrite iUnion_mk.
  apply mk_eq.
  apply EQ_tran with (EnsDefs.iUnion eE Axioms.Sing).
  - apply EnsLib.iUnion_Proper. apply EQ_refl.
    intros u v Huv.
    apply EQ_tran with (Axioms.Sing u);
      [| apply Sing_sound; exact Huv].
    apply quot_eq. unfold liftF.
    rewrite repr_eq. apply Sing_mk.
  - apply EnsLib.iUnion_Sing_r. exact H.
Qed.

Lemma iUnion_Sing_l :
  forall (E : ZFSet) (F : ZFSet -> ZFSet) (H : IsSet (F E)),
  iUnion (Sing E) F = F E.
Proof.
  intros E F.
  pattern E; apply quot_ind. intros eE H.
  cbv beta. fold (mk eE).
  rewrite Sing_mk. rewrite iUnion_mk.
  transitivity (mk (liftF F eE)).
  - apply mk_eq, EnsLib.iUnion_Sing_l.
    unfold liftF. apply IsSet_repr. exact H.
  - unfold liftF. apply mk_repr.
Qed.

Lemma iUnion_assoc :
  forall (E : ZFSet) (F G : ZFSet -> ZFSet),
  iUnion (iUnion E F) G = iUnion E (fun x => iUnion (F x) G).
Proof.
  intros E F G.
  pattern E; apply quot_ind. intros eE.
  cbv beta. fold (mk eE).
  rewrite !iUnion_mk.
  apply mk_eq.
  apply EQ_tran
    with (EnsDefs.iUnion eE (fun x => EnsDefs.iUnion (liftF F x) (liftF G))).
  - apply EnsLib.iUnion_assoc.
    + intros u v Huv. apply (liftF_Proper F); exact Huv.
    + intros u v Huv. apply (liftF_Proper G); exact Huv.
  - apply EnsLib.iUnion_Proper. apply EQ_refl.
    intros u v Huv.
    apply EQ_tran with (EnsDefs.iUnion (liftF F v) (liftF G)).
    + apply EnsLib.iUnion_sound_l.
      * intros a b Hab. apply (liftF_Proper G); exact Hab.
      * apply (liftF_Proper F); exact Huv.
    + apply quot_eq.
      transitivity (iUnion (F (mk v)) G).
      * transitivity (iUnion (mk (liftF F v)) G).
        -- symmetry. apply iUnion_mk.
        -- f_equal. unfold liftF. apply mk_repr.
      * symmetry. unfold liftF. apply mk_repr.
Qed.

Lemma IN_iUnion :
  forall (E : ZFSet) (F : ZFSet -> ZFSet) (y x : ZFSet),
  In y E -> In x (F y) -> In x (iUnion E F).
Proof.
  intros E F y x.
  pattern E; apply quot_ind. intros eE.
  pattern y; apply quot_ind. intros ey.
  pattern x; apply quot_ind. intros ex.
  cbv beta. intros HyE HxFy.
  rewrite iUnion_mk, In_mk.
  apply EnsLib.IN_iUnion with (y := ey).
  - intros u v Huv. apply liftF_Proper; exact Huv.
  - rewrite In_mk in HyE. exact HyE.
  - assert (HF : mk (liftF F ey) = F (mk ey))
      by (unfold liftF; apply mk_repr).
    rewrite <- In_mk, HF. exact HxFy.
Qed.

Lemma iUnion_IN :
  forall (E : ZFSet) (F : ZFSet -> ZFSet) (x : ZFSet),
  In x (iUnion E F) ->
  exists y : ZFSet, In y E /\ In x (F y).
Proof.
  intros E F x.
  pattern E; apply quot_ind. intros eE.
  pattern x; apply quot_ind. intros ex.
  cbv beta. rewrite iUnion_mk. rewrite In_mk.
  intro H.
  destruct (EnsLib.iUnion_IN _ _ _ H) as [ey [HyE Hex]].
  exists (mk ey). split.
  - rewrite In_mk. exact HyE.
  - assert (HF : F (mk ey) = mk (liftF F ey))
      by (unfold liftF; symmetry; apply mk_repr).
    rewrite HF. rewrite In_mk. exact Hex.
Qed.

(** Subset rule for [iUnion]: a union is included in [T] exactly when
    every [F x] is.  This is the [Inc]-level counterpart of [iUnion_IN],
    letting one prove [⊆] goals over a union without unfolding to
    pointwise membership. *)
Lemma iUnion_Inc :
  forall (E : ZFSet) (F : ZFSet -> ZFSet) (T : ZFSet),
  (forall y, In y E -> Inc (F y) T) -> Inc (iUnion E F) T.
Proof.
  intros E F T h. inc_def. intros x xIn.
  apply iUnion_IN in xIn. destruct xIn as [y [yIn xFy]].
  exact (Inc_IN _ _ _ (h y yIn) xFy).
Qed.


(** *** Power-set laws (from [Axioms.v]). *)

Lemma IN_Power_Inc :
  forall E X : ZFSet, In X (Power E) -> Inc X E.
Proof.
  intros E X.
  pattern E; apply quot_ind. intros eE.
  pattern X; apply quot_ind. intros eX.
  rewrite Power_mk. unfold mk. rewrite In_mk, Inc_mk.
  apply IN_Power_INC.
Qed.

Lemma Inc_IN_Power :
  forall (E X : ZFSet) (H : IsSet E), Inc X E -> In X (Power E).
Proof.
  apply (ZFSet_ind2 (fun E X => IsSet E -> Inc X E -> In X (Power E))). intros eE eX.
  rewrite Power_mk, IsSet_mk, In_mk, Inc_mk.
  apply INC_IN_Power.
Qed.

(** [inc_in_power] applies [Inc_IN_Power] and discharges its class premise
    by instance resolution, for the common case of a visible set-former. *)
Ltac inc_in_power := apply Inc_IN_Power; [ typeclasses eauto | ].

Lemma Power_mon :
  forall (E E' : ZFSet) (H : IsSet E'), Inc E E' -> Inc (Power E) (Power E').
Proof.
  apply (ZFSet_ind2 (fun E E' => IsSet E' -> Inc E E' -> Inc (Power E) (Power E'))). intros eE eE'.
  rewrite !Power_mk, IsSet_mk, !Inc_mk. apply Power_mon.
Qed.


(** *** Comprehension inclusion (from [Axioms.v]). *)

Lemma Comp_Inc :
  forall (E : ZFSet) (P : ZFSet -> Prop), Inc (Comp E P) E.
Proof.
  intros E P. pattern E; apply quot_ind. intros eE.
  rewrite Comp_mk, Inc_mk. apply Comp_INC.
Qed.


(** *** Intersection laws (from [Axioms.v]). *)

Lemma IN_Inter_all :
  forall E X : ZFSet,
  In X (Inter E) -> forall A : ZFSet, In A E -> In X A.
Proof.
  intros E X HX.
  apply (In_Comp_P (Union E)
           (fun x => forall a : ZFSet, In a E -> In x a) X HX).
Qed.

Lemma all_IN_Inter :
  forall E X Y : ZFSet,
  In Y E ->
  (forall A : ZFSet, In A E -> In X A) ->
  In X (Inter E).
Proof.
  intros E X Y HY HX. apply In_P_Comp.
  - apply IN_Union with Y; [exact HY | apply HX; exact HY].
  - exact HX.
Qed.

Lemma Inter_Inc_Union : forall E : ZFSet, Inc (Inter E) (Union E).
Proof. intros E. apply Comp_Inc. Qed.


(** *** Inclusion is reflexive and transitive (from [Sets.v]). *)

Lemma Inc_refl : forall X : ZFSet, Inc X X.
Proof.
  intros X. pattern X; apply quot_ind. intros e.
  rewrite Inc_mk. apply INC_refl.
Qed.

Lemma Inc_tran :
  forall X Y Z : ZFSet, Inc X Y -> Inc Y Z -> Inc X Z.
Proof.
  intros X Y Z.
  pattern X; apply quot_ind. intros eX.
  pattern Y; apply quot_ind. intros eY.
  pattern Z; apply quot_ind. intros eZ.
  rewrite !Inc_mk. apply INC_tran.
Qed.


(** *** Empty-set laws (from [Axioms.v]). *)

Lemma not_In_Empty : forall X : ZFSet, ~ In X Empty.
Proof.
  intros X. pattern X; apply quot_ind. intros e Hin.
  change Empty with (mk ∅) in Hin.
  rewrite In_mk in Hin.
  elim (Vide_est_vide _ Hin).
Qed.

Lemma all_empty_eq_Empty :
  forall (X : ZFSet) (H : IsSet X), (forall Y : ZFSet, ~ In Y X) -> X = Empty.
Proof.
  intros X. pattern X; apply quot_ind. intros eX Hs HX.
  rewrite IsSet_mk in Hs.
  change Empty with (mk ∅). apply mk_eq.
  apply tout_vide_est_Vide; [ exact Hs | ]. intros eY HY.
  exfalso. apply (HX (mk eY)). rewrite In_mk. exact HY.
Qed.


(** *** Further singleton laws (from [Axioms.v]). *)

Lemma Sing_inj : forall a b : ZFSet, Sing a = Sing b -> a = b.
Proof.
  intros a b. pattern a; apply quot_ind. intros ea.
  pattern b; apply quot_ind. intros eb.
  rewrite !Sing_mk. intros H. apply mk_inj in H.
  apply mk_eq, EQ_Sing_EQ. exact H.
Qed.

Lemma Sing_neq_Empty : forall a : ZFSet, Sing a <> Empty.
Proof.
  intros a. pattern a; apply quot_ind. intros ea.
  rewrite Sing_mk. unfold Empty.
  intro H. apply mk_inj in H. elim (not_EQ_Sing_Vide _ H).
Qed.

Lemma Empty_neq_Sing : forall a : ZFSet, Empty <> Sing a.
Proof.
  intros a H. apply (Sing_neq_Empty a). symmetry. exact H.
Qed.




(** *** Werner-pair projection laws (from [EnsLib.v]). *)

Lemma Couple_inj_left :
  forall A A' B B' : ZFSet,
  Couple A A' = Couple B B' -> A = B.
Proof.
  intros A A' B B'.
  pattern A; apply quot_ind. intros eA.
  pattern A'; apply quot_ind. intros eA'.
  pattern B; apply quot_ind. intros eB.
  pattern B'; apply quot_ind. intros eB'.
  rewrite !Couple_mk. intro H.
  apply mk_inj in H. apply mk_eq.
  exact (Couple_inj_left _ _ _ _ H).
Qed.

Lemma Couple_inj_right :
  forall A A' B B' : ZFSet,
  Couple A A' = Couple B B' -> A' = B'.
Proof.
  intros A A' B B'.
  pattern A; apply quot_ind. intros eA.
  pattern A'; apply quot_ind. intros eA'.
  pattern B; apply quot_ind. intros eB.
  pattern B'; apply quot_ind. intros eB'.
  rewrite !Couple_mk. intro H.
  apply mk_inj in H. apply mk_eq.
  exact (Couple_inj_right _ _ _ _ H).
Qed.

Lemma Couple_IN_Prod :
  forall E1 E2 X1 X2 : ZFSet,
  In X1 E1 -> In X2 E2 -> In (Couple X1 X2) (Prod E1 E2).
Proof.
  intros E1 E2 X1 X2.
  pattern E1; apply quot_ind. intros e1.
  pattern E2; apply quot_ind. intros e2.
  pattern X1; apply quot_ind. intros x1.
  pattern X2; apply quot_ind. intros x2.
  rewrite Couple_mk, Prod_mk. unfold mk. rewrite !In_mk.
  apply Couple_IN_Prod.
Qed.

Lemma Couple_Prod_IN :
  forall E1 E2 X1 X2 : ZFSet,
  In (Couple X1 X2) (Prod E1 E2) -> In X1 E1 /\ In X2 E2.
Proof.
  intros E1 E2 X1 X2.
  pattern E1; apply quot_ind. intros e1.
  pattern E2; apply quot_ind. intros e2.
  pattern X1; apply quot_ind. intros x1.
  pattern X2; apply quot_ind. intros x2.
  rewrite Couple_mk, Prod_mk. unfold mk. rewrite !In_mk.
  apply Couple_Prod_IN.
Qed.


Lemma IN_Prod_EXType :
  forall E E' X : ZFSet,
  In X (Prod E E') ->
  exists A B : ZFSet, Couple A B = X.
Proof.
  intros E E' X.
  pattern E; apply quot_ind. intros eE.
  pattern E'; apply quot_ind. intros eE'.
  pattern X; apply quot_ind. intros eX.
  rewrite Prod_mk. unfold mk. rewrite In_mk.
  intros H. destruct (IN_Prod_EXType _ _ _ H) as [eA [eB Hab]].
  exists (mk eA), (mk eB).
  rewrite Couple_mk. apply mk_eq. exact Hab.
Qed.

(** Bundled pair extractor: every element of [Prod E1 E2] is a [Couple]
    of components witnessed in [E1] and [E2]. *)
Lemma IN_Prod_EX :
  forall E1 E2 y : ZFSet, In y (Prod E1 E2) ->
  exists a b : ZFSet, In a E1 /\ In b E2 /\ y = Couple a b.
Proof.
  intros E1 E2 y Hy.
  destruct (IN_Prod_EXType _ _ _ Hy) as [a [b Hab]].
  subst y. destruct (Couple_Prod_IN _ _ _ _ Hy) as [Ha Hb].
  exists a, b. repeat split; assumption.
Qed.

Lemma Prod_Sing_Sing :
  forall a b : ZFSet, Prod (Sing a) (Sing b) = Sing (Couple a b).
Proof.
  intros a b. apply set_ext; inc_def; intros y Hy.
  - apply IN_Prod_EX in Hy. destruct Hy as [a' [b' [Ha [Hb Heq]]]].
    apply IN_Sing_EQ in Ha, Hb. subst a' b' y. apply IN_Sing.
  - apply IN_Sing_EQ in Hy. subst y.
    apply Couple_IN_Prod; apply IN_Sing.
Qed.


Lemma pfst_Couple : forall a b : ZFSet, pfst (Couple a b) = a.
Proof.
  intros a b.
  pattern a; apply quot_ind. intros ea.
  pattern b; apply quot_ind. intros eb.
  rewrite Couple_mk, pfst_mk.
  apply mk_eq, EnsLib.pfst_Couple.
Qed.

Lemma psnd_Couple : forall a b : ZFSet, psnd (Couple a b) = b.
Proof.
  intros a b.
  pattern a; apply quot_ind. intros ea.
  pattern b; apply quot_ind. intros eb.
  rewrite Couple_mk, psnd_mk.
  apply mk_eq, EnsLib.psnd_Couple.
Qed.




(* ----- naturals, foundation and Omega (Ens-lifted) ----- *)

(** *** Naturals (from [EnsNat.v]). *)

(** *** Foundation / Omega laws (from [Omega.v]). *)

Lemma not_In_self : forall X : ZFSet, ~ In X X.
Proof.
  intros X. pattern X; apply quot_ind. intros e Hin.
  unfold mk in Hin. rewrite In_mk in Hin.
  elim (E_not_IN_E _ Hin).
Qed.

Lemma natZAdd_natZ :
  forall k1 k2 : nat,
  natZAdd (natZ k1) (natZ k2) = natZ (k1 + k2).
Proof.
  intros k1 k2. unfold natZ.
  rewrite natZAdd_mk. apply mk_eq, EnsNat.natZAdd_natZ.
Qed.

Lemma natZSucc_natZ : forall k : nat, natZSucc (natZ k) = natZ (S k).
Proof.
  intro k. unfold natZ.
  rewrite natZSucc_mk. apply mk_eq, EnsNat.natZSucc_natZ.
Qed.

Lemma natZPred_natZ : forall k : nat, natZPred (natZ k) = natZ (pred k).
Proof.
  intro k. unfold natZ.
  rewrite natZPred_mk. apply mk_eq, EnsNat.natZPred_natZ.
Qed.


Lemma natZ_mem_omega : forall n : nat, In (natZ n) Omega.
Proof.
  intro n. unfold natZ, Omega, mk.
  rewrite In_mk. apply EnsNat.natZ_mem_natSet.
Qed.

(* TODO: add a counterpart to IN_Omega_EXType, which extracts an abstract nat. *)

Lemma In_omega : forall X, In X Omega -> { n | (natZ n) = X }.
Proof.
  intros X HX.
  set (eX := repr X).
  assert (HmkeX : mk eX = X) by apply mk_repr.
  assert (HIN : eX ∈ ω).
  { rewrite <- HmkeX in HX.
    change Omega with (mk ω) in HX.
    rewrite In_mk in HX. exact HX. }
  exists (epsilon (inhabits 0%nat) (fun k => Nat k ≃ eX)).
  unfold natZ. rewrite <- HmkeX. apply mk_eq.
  apply (epsilon_spec (inhabits 0%nat) (fun k => Nat k ≃ eX)).
  destruct (IN_Omega_EXType eX HIN) as [k Hk].
  exists k. exact Hk.
Qed.


(** *** Numerals are atoms: memberless, and distinct from every set and
    every couple. *)

Lemma natZ_IsAtom : forall n : nat, IsAtom (natZ n).
Proof. intro n. unfold natZ. rewrite IsAtom_mk. exact I. Qed.

Lemma natZ_not_IsSet : forall n : nat, ~ IsSet (natZ n).
Proof. intros n H. unfold natZ in H. rewrite IsSet_mk in H. exact H. Qed.

Lemma not_In_natZ : forall (x : ZFSet) (n : nat), ~ In x (natZ n).
Proof.
  intros x n. pattern x; apply quot_ind. intros ex H.
  unfold natZ in H. rewrite In_mk in H. exact H.
Qed.

Lemma natZ_neq_Empty : forall n : nat, natZ n <> Empty.
Proof.
  intros n H. apply (natZ_not_IsSet n). rewrite H. unfold Empty. rewrite IsSet_mk. exact I.
Qed.

(** A set is never a numeral. *)
Lemma IsSet_neq_natZ : forall (X : ZFSet) (n : nat), IsSet X -> X <> natZ n.
Proof. intros X n HX H. apply (natZ_not_IsSet n). rewrite <- H. exact HX. Qed.

(** *** Couples are memberless and are neither sets nor numerals. *)

Lemma Couple_IsPair : forall a b : ZFSet, IsPair (Couple a b).
Proof.
  apply (ZFSet_ind2 (fun a b => IsPair (Couple a b))). intros ea eb.
  rewrite Couple_mk, IsPair_mk. exact I.
Qed.

Lemma Couple_not_IsSet : forall a b : ZFSet, ~ IsSet (Couple a b).
Proof.
  apply (ZFSet_ind2 (fun a b => ~ IsSet (Couple a b))). intros ea eb H.
  rewrite Couple_mk, IsSet_mk in H. exact H.
Qed.

Lemma not_In_Couple : forall x a b : ZFSet, ~ In x (Couple a b).
Proof.
  apply (ZFSet_ind3 (fun x a b => ~ In x (Couple a b))). intros ex ea eb H.
  rewrite Couple_mk, In_mk in H. exact H.
Qed.

Lemma Couple_neq_natZ : forall (a b : ZFSet) (n : nat), Couple a b <> natZ n.
Proof.
  intros a b n. revert a b. apply (ZFSet_ind2 (fun a b => Couple a b <> natZ n)). intros ea eb H.
  unfold natZ in H. rewrite Couple_mk in H. apply mk_inj in H. exact H.
Qed.

Lemma IsSet_neq_Couple : forall X a b : ZFSet, IsSet X -> X <> Couple a b.
Proof. intros X a b HX H. apply (Couple_not_IsSet a b). rewrite <- H. exact HX. Qed.

(** A couple is the couple of its projections; off couples both projections
    are the empty set. *)
Lemma IsPair_Couple : forall X : ZFSet, IsPair X -> exists a b : ZFSet, X = Couple a b.
Proof.
  intro X. pattern X; apply quot_ind. intros e H. rewrite IsPair_mk in H.
  destruct e as [n | a b | A f]; try contradiction.
  exists (mk a), (mk b). rewrite Couple_mk. reflexivity.
Qed.

Lemma pfst_not_pair : forall X : ZFSet, ~ IsPair X -> pfst X = Empty.
Proof.
  intro X. pattern X; apply quot_ind. intros e H. rewrite IsPair_mk in H.
  rewrite pfst_mk. unfold Empty. apply mk_eq.
  destruct e as [n | a b | A f]; [ apply EQ_refl | exfalso; apply H; exact I | apply EQ_refl ].
Qed.

Lemma psnd_not_pair : forall X : ZFSet, ~ IsPair X -> psnd X = Empty.
Proof.
  intro X. pattern X; apply quot_ind. intros e H. rewrite IsPair_mk in H.
  rewrite psnd_mk. unfold Empty. apply mk_eq.
  destruct e as [n | a b | A f]; [ apply EQ_refl | exfalso; apply H; exact I | apply EQ_refl ].
Qed.


Lemma Nat_inj :
  forall k1 k2 : nat, natZ k1 = natZ k2 -> k1 = k2.
Proof.
  intros k1 k2 H. apply EnsNat.Nat_inj.
  apply mk_inj. exact H.
Qed.

(** Distinct naturals denote distinct sets (contrapositive of [Nat_inj]). *)
Lemma natZ_neq : forall n m : nat, n <> m -> natZ n <> natZ m.
Proof. intros n m Hnm H. apply Hnm, Nat_inj, H. Qed.



Lemma Sing_Inc_IN X Y:
  In X Y ->  Inc (Sing X) Y.
Proof.
  intro h. inc_def. intros x XIn.
  apply IN_Sing_EQ in XIn. subst. auto.
Qed.

(** A singleton inclusion is just a membership: the [Inc]-level
    characterization of [Sing], so [⊆] goals with a singleton source
    reduce to a single membership without introducing the element. *)
Lemma Sing_Inc X Y : Inc (Sing X) Y <-> In X Y.
Proof.
  split.
  - intro h. exact (Inc_IN _ _ _ h (IN_Sing X)).
  - apply Sing_Inc_IN.
Qed.




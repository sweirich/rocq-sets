(** * Universes.v — the Grothendieck tower [U0 ∈ U1] and its closure theory.

    The universe layer of the [zf] library, split out from the general set
    theory: the two universes [U0 ∈ U1], the derived universe-level sets
    ([anyId], [smallId], [bigId], [is_type]), and the closure ("smallness")
    lemmas that say each universe is closed under the set-formers — the
    material a model needs to read a *type* as a small set.

    This is the one part of [zf] that [ZFSets.v] does **not** re-export.
    Requiring the umbrella therefore gets the set theory without committing to
    a universe; a file that wants [U0] / [U1] asks for them:

        Require Import Universes.

    Everything here is exactly what [lib/universe.v] abstracts as the module
    types [UNIVERSE] / [UNIVERSE1] and instantiates in the witness
    [LambdaSetBig] — so a model built over that interface (the LambdaSet
    semantics, the PredF / PLC embeddings) never needs this file, only the
    signature.

    Layers, mirroring where the material used to live:

      - the universes themselves and the *Ens-lifted* lemmas about them
        (proved by descending through [mk] to the [Ens] representation, as in
        [ZFSetCore.v] — this file is the one other place that does that);
      - the derived definitions ([anyId], [smallId], [bigId], [is_type]),
        which are [ZFDefs.v]-style but mention a universe;
      - the pure smallness toolkit ([small_of_Inc] … [U1_Pi]), proved through
        the abstract interface as in [ZFSetFacts.v];
      - the diagonal / partial-identity facts about [U0] and [U1], the
        universe-specific half of [Diagonal.v]. *)

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

(* [EnsDefs] is imported (not just required) for the universe name [ulib],
   which it declares; [ZFSets] is imported after it, so the ZFSet-level
   names and notations shadow the [Ens]-level ones. *)
Require Import utils.axioms.
Require Import EnsDefs.
Require EnsLib.
Require EnsNat.

From Stdlib Require Import Logic.Epsilon.

(* The umbrella, which does *not* re-export this file — no cycle. *)
Require Import ZFSets.

(* ================================================================== *)
(** * The universes [U0] and [U1] (lifted across the quotient) *)
(* ================================================================== *)

(** ** Inaccessible cardinals: the "U0" set, lifted from [zf.zfc.Hierarchy].

    [zf.zfc.Hierarchy] takes a step towards inaccessible cardinals by carving
    out the *small* sets [Ens'] — those built below one [Type] universe —
    and collecting them into a single [Ens]-level set [U0 := sup Ens' inj].
    [U0] behaves like a Grothendieck universe: it is transitive and closed
    under power sets, so it models an (uncountable, strongly) inaccessible
    stage of the cumulative hierarchy.

    Here we lift that material across the quotient to [ZFSet].  The witness
    type [Ens'] and its injection [inj : Ens' -> Ens] live *below* the
    quotient, so a small set appears on [ZFSet] as [mk (inj E')]; the
    lemmas characterise membership in [U0] in those terms. *)

Definition U0 : ZFSet := mk Hierarchy.U0@{ulib}.

(** [U0] is a set (the quotient of a [sup]). *)
#[global] Instance IsSet_U0 : IsSet U0.
Proof. unfold U0. rewrite IsSet_mk. exact I. Qed.

(** Every small set is a member of [U0]. *)
Lemma U0_is_big_Z : forall E' : Ens', In (mk (inj@{ulib} E')) U0.
Proof.
  intro E'. unfold U0, mk. rewrite In_mk. exact (U0_is_big E').
Qed.

(** Conversely, every member of [U0] is (the image of) a small set. *)
Lemma IN_U0_small_Z :
  forall X : ZFSet, In X U0 -> exists E' : Ens', X = mk (inj@{ulib} E').
Proof.
  intro X. pattern X; apply quot_ind. intros eX.
  unfold U0, mk. rewrite In_mk. intro H.
  destruct (IN_U0_small eX H) as [E' HE'].
  exists E'. apply mk_eq. exact HE'.
Qed.

(** Members of a small set are themselves small — the key downward-closure
    property behind transitivity. *)
Lemma IN_small_small_Z :
  forall (X : ZFSet) (E' : Ens'),
  In X (mk (inj@{ulib} E')) -> exists E1 : Ens', X = mk (inj@{ulib} E1).
Proof.
  intros X E'. pattern X; apply quot_ind. intros eX.
  unfold mk. rewrite In_mk. intro H.
  destruct (IN_small_small eX E' H) as [E1 HE1].
  exists E1. apply mk_eq. exact HE1.
Qed.

(** [U0] is transitive: a member of a member of [U0] is again in [U0]. *)
Lemma U0_transitive :
  forall X Y : ZFSet, In X Y -> In Y U0 -> In X U0.
Proof.
  intros X Y HXY HYB.
  destruct (IN_U0_small_Z Y HYB) as [F' HF']. subst Y.
  destruct (IN_small_small_Z X F' HXY) as [E1 HE1]. subst X.
  apply U0_is_big_Z.
Qed.

(** [U0] is closed under power sets — the strong-inaccessibility clause. *)
Lemma In_Power_U0 :
  forall X : ZFSet, In X U0 -> In (Power X) U0.
Proof.
  intro X. pattern X; apply quot_ind. intros eX. fold (mk eX).
  unfold U0. rewrite Power_mk. unfold mk. rewrite !In_mk.
  apply U0_closed_for_power.
Qed.

(** *** Smallness toolkit.

    [U0] is closed under the basic set-formers (it behaves like a
    Grothendieck universe), so concrete sets — in particular the von
    Neumann naturals — are members of the universe.  Each lemma lifts the
    corresponding [inj]-soundness/closure theorem of [zf.zfc.Hierarchy]
    across the quotient. *)

Lemma Empty_small : In Empty U0.
Proof.
  unfold Empty, U0. rewrite In_mk. apply U0_contains_Vide.
Qed.

Lemma Sing_small : forall X : ZFSet, In X U0 -> In (Sing X) U0.
Proof.
  intro X. pattern X; apply quot_ind. intros eX. fold (mk eX).
  unfold U0. rewrite Sing_mk. unfold mk. rewrite !In_mk.
  apply U0_closed_Sing.
Qed.

Lemma Paire_small :
  forall X Y : ZFSet, In X U0 -> In Y U0 -> In (Paire X Y) U0.
Proof.
  intros X Y. pattern X; apply quot_ind. intros eX.
  pattern Y; apply quot_ind. intros eY. fold (mk eX). fold (mk eY).
  unfold U0. rewrite Paire_mk. unfold mk. rewrite !In_mk.
  apply U0_closed_Paire.
Qed.

Lemma Union_small : forall X : ZFSet, In X U0 -> In (Union X) U0.
Proof.
  intro X. pattern X; apply quot_ind. intros eX. fold (mk eX).
  unfold U0. rewrite Union_mk. unfold mk. rewrite !In_mk.
  apply U0_closed_Union.
Qed.

(** Every numeral is small: atoms are members of the universe [U0]. *)
Lemma natZ_small : forall k : nat, In (natZ k) U0.
Proof.
  intro k. unfold natZ, U0. rewrite In_mk. apply U0_contains_atom.
Qed.

(** Couples of small values are small, and conversely. *)
Lemma Couple_small : forall X Y : ZFSet, In X U0 -> In Y U0 -> In (Couple X Y) U0.
Proof.
  intros X Y. pattern X; apply quot_ind. intros eX.
  pattern Y; apply quot_ind. intros eY. fold (mk eX). fold (mk eY).
  unfold U0. rewrite Couple_mk. unfold mk. rewrite !In_mk.
  apply U0_closed_pair.
Qed.

Lemma Couple_small_inv : forall X Y : ZFSet, In (Couple X Y) U0 -> In X U0 /\ In Y U0.
Proof.
  intros X Y. pattern X; apply quot_ind. intros eX.
  pattern Y; apply quot_ind. intros eY. fold (mk eX). fold (mk eY).
  unfold U0. rewrite Couple_mk. unfold mk. rewrite !In_mk.
  apply IN_U0_pair_inv.
Qed.

(** The projections of a small value are small (they are [∅] off couples). *)
Lemma pfst_small : forall X : ZFSet, In X U0 -> In (pfst X) U0.
Proof.
  intros X HX. destruct (ZFSet_sorts X) as [HA | [HP | HS]].
  - rewrite pfst_not_pair; [ apply Empty_small | ].
    intro HP. revert HA HP. pattern X; apply quot_ind. intros e.
    rewrite IsAtom_mk, IsPair_mk. destruct e; simpl; tauto.
  - destruct (IsPair_Couple X HP) as [a [b Hab]]. subst X.
    rewrite pfst_Couple. destruct (Couple_small_inv _ _ HX) as [H1 _]. exact H1.
  - rewrite pfst_not_pair; [ apply Empty_small | ].
    intro HP. revert HS HP. pattern X; apply quot_ind. intros e.
    rewrite IsSet_mk, IsPair_mk. destruct e; simpl; tauto.
Qed.

Lemma psnd_small : forall X : ZFSet, In X U0 -> In (psnd X) U0.
Proof.
  intros X HX. destruct (ZFSet_sorts X) as [HA | [HP | HS]].
  - rewrite psnd_not_pair; [ apply Empty_small | ].
    intro HP. revert HA HP. pattern X; apply quot_ind. intros e.
    rewrite IsAtom_mk, IsPair_mk. destruct e; simpl; tauto.
  - destruct (IsPair_Couple X HP) as [a [b Hab]]. subst X.
    rewrite psnd_Couple. destruct (Couple_small_inv _ _ HX) as [_ H2]. exact H2.
  - rewrite psnd_not_pair; [ apply Empty_small | ].
    intro HP. revert HS HP. pattern X; apply quot_ind. intros e.
    rewrite IsSet_mk, IsPair_mk. destruct e; simpl; tauto.
Qed.

(** [ω] itself is small: it is the image of the small type [nat], so it
    is a member of the universe [U0] (the closure-under-[ω] clause of
    inaccessibility). *)
Lemma Omega_small : In Omega U0.
Proof.
  unfold Omega, U0. rewrite In_mk. apply U0_contains_Omega.
Qed.

(** ** The second universe [U1], with [U0 ∈ U1].

    [U1] collects every [big]-level [Ens] set, gathered one level up at
    [ulib].  [U0 : Ens@{ulib}] is one of its members: it is the [injp]
    image of [U0 : Ens@{big}] (via [Hierarchy.injp_U0]), so the [ulib]
    quotient sees the two-level Grothendieck tower [U0 ∈ U1]. *)
Definition U1 : ZFSet := mk (Hierarchy.Univ@{big ulib}).

#[global] Instance IsSet_U1 : IsSet U1.
Proof. unfold U1. rewrite IsSet_mk. exact I. Qed.

Lemma U0_in_U1 : In U0 U1.
Proof.
  unfold U1, U0. rewrite In_mk. unfold Hierarchy.Univ.
  exists Hierarchy.U0@{big}.
  apply EQ_sym. apply Hierarchy.injp_U0.
Qed.

(** *** [U1] smallness toolkit.

    [U1] is a concrete Grothendieck universe one level up, so it enjoys the
    same closure facts as [U0].  Each lemma lifts the corresponding
    [Univ_closed_*]/[Univ_transitive] theorem of [zf.zfc.Hierarchy] (at the
    instance [@{big ulib}]) across the quotient — mirroring the [U0]
    toolkit above.  [apply] threads the polymorphic [Sets.IN] conclusions
    straight onto the [In]-goals. *)

(** [U1] is transitive: a member of a member of [U1] is again in [U1]. *)
Lemma U1_transitive :
  forall X Y : ZFSet, In X Y -> In Y U1 -> In X U1.
Proof.
  intros X Y. pattern X; apply quot_ind. intros eX.
  pattern Y; apply quot_ind. intros eY.
  unfold U1, mk. rewrite !In_mk.
  apply Hierarchy.Univ_transitive.
Qed.

(** [U1] is closed under power sets. *)
Lemma In_Power_U1 :
  forall X : ZFSet, In X U1 -> In (Power X) U1.
Proof.
  intro X. pattern X; apply quot_ind. intros eX. fold (mk eX).
  unfold U1. rewrite Power_mk. unfold mk. rewrite !In_mk.
  apply Hierarchy.Univ_closed_Power.
Qed.

(** [U1] is closed under unions. *)
Lemma Union_U1 : forall X : ZFSet, In X U1 -> In (Union X) U1.
Proof.
  intro X. pattern X; apply quot_ind. intros eX. fold (mk eX).
  unfold U1. rewrite Union_mk. unfold mk. rewrite !In_mk.
  apply Hierarchy.Univ_closed_Union.
Qed.

(** [U1] is closed under (unordered) pairing. *)
Lemma Paire_U1 :
  forall X Y : ZFSet, In X U1 -> In Y U1 -> In (Paire X Y) U1.
Proof.
  intros X Y. pattern X; apply quot_ind. intros eX.
  pattern Y; apply quot_ind. intros eY. fold (mk eX). fold (mk eY).
  unfold U1. rewrite Paire_mk. unfold mk. rewrite !In_mk.
  apply Hierarchy.Univ_closed_Paire.
Qed.

Lemma U0_sub_U1_Sing : forall X : ZFSet, In X U1 -> In (Sing X) U1.
Proof. intros X HX. rewrite Sing_eq_Paire. apply Paire_U1; exact HX. Qed.

Lemma U0_sub_U1_Empty : In Empty U1.
Proof.
  apply U1_transitive with U0; [ apply Empty_small | apply U0_in_U1 ].
Qed.

(** [U1] is closed under couples, and conversely. *)
Lemma Couple_U1 :
  forall X Y : ZFSet, In X U1 -> In Y U1 -> In (Couple X Y) U1.
Proof.
  intros X Y. pattern X; apply quot_ind. intros eX.
  pattern Y; apply quot_ind. intros eY. fold (mk eX). fold (mk eY).
  unfold U1. rewrite Couple_mk. unfold mk. rewrite !In_mk.
  apply Hierarchy.Univ_closed_pair.
Qed.

Lemma Couple_U1_inv : forall X Y : ZFSet, In (Couple X Y) U1 -> In X U1 /\ In Y U1.
Proof.
  intros X Y. pattern X; apply quot_ind. intros eX.
  pattern Y; apply quot_ind. intros eY. fold (mk eX). fold (mk eY).
  unfold U1. rewrite Couple_mk. unfold mk. rewrite !In_mk.
  apply Hierarchy.IN_Univ_pair_inv.
Qed.

Lemma psnd_U1 : forall X : ZFSet, In X U1 -> In (psnd X) U1.
Proof.
  intros X HX. destruct (ZFSet_sorts X) as [HA | [HP | HS]].
  - rewrite psnd_not_pair; [ apply U0_sub_U1_Empty | ].
    intro HP. revert HA HP. pattern X; apply quot_ind. intros e.
    rewrite IsAtom_mk, IsPair_mk. destruct e; simpl; tauto.
  - destruct (IsPair_Couple X HP) as [a [b Hab]]. subst X.
    rewrite psnd_Couple. destruct (Couple_U1_inv _ _ HX) as [_ H2]. exact H2.
  - rewrite psnd_not_pair; [ apply U0_sub_U1_Empty | ].
    intro HP. revert HS HP. pattern X; apply quot_ind. intros e.
    rewrite IsSet_mk, IsPair_mk. destruct e; simpl; tauto.
Qed.

(** *** [U1] is closed under indexed unions (replacement).

    This is the one Grothendieck-universe closure property that is not
    definitional in the Aczel encoding: a [ulib]-indexed union of members of
    [Univ] need not itself be a [Univ]-member unless the index set is genuinely
    *small*.  The Aczel-level core [iUnion_Univ_Ens] supplies the argument;
    [iUnion_U1] lifts it across the quotient.  It is what makes [U1] closed
    under dependent products [Pi] (see [ZFSetFacts.U1_Pi]). *)

(** Replacement for [Univ] ([U1]'s carrier), at the Aczel [Ens] level: if
    [E ∈ Univ] and [G] carries every element of [E] into [Univ], then the
    indexed union [EnsDefs.iUnion E G] is in [Univ].

    [E ∈ Univ] means [E] is [EQ] to the [injp]-image of a genuinely small
    ([big]-level) set [sup I0 f0], so the [ulib]-indexed family [fun a =>
    G (fE a)] can be re-indexed by the small [I0].  Each of its (small)
    elements has a [big]-level preimage, picked with Hilbert's [epsilon] — the
    informative content [IN]/[EXType] withholds, since membership is
    [Prop]-valued.  This is the same classical choice the quotient already uses
    for [repr].  [G] must respect [EQ]; in the application [G = liftF B] does,
    since it factors through [mk]. *)
Lemma iUnion_Univ_Ens :
  forall (G : Ens -> Ens),
    (forall x y : Ens, EQ x y -> EQ (G x) (G y)) ->
    forall E : Ens,
      IN E Hierarchy.Univ@{big ulib} ->
      (forall a : Ens, IN a E -> IN (G a) Hierarchy.Univ@{big ulib}) ->
      IN (EnsDefs.iUnion E G) Hierarchy.Univ@{big ulib}.
Proof.
  intros G HG E HE HB.
  destruct E as [n | a b | IE fE].
  { (* a non-set indexes the empty union *)
    cbn [EnsDefs.iUnion]. unfold Hierarchy.Univ, IN. exists Vide.
    apply EQ_sym. apply Hierarchy.injp_Vide. }
  { cbn [EnsDefs.iUnion]. unfold Hierarchy.Univ, IN. exists Vide.
    apply EQ_sym. apply Hierarchy.injp_Vide. }
  (* [iUnion (sup IE fE) G = Union (sup IE (fun a => G (fE a)))]; [Univ] is
     closed under [Union], so it suffices to place the family-[sup] in [Univ]. *)
  cbn [EnsDefs.iUnion].
  apply Hierarchy.Univ_closed_Union.
  (* [E]'s small preimage [sup I0 f0] (index [I0] genuinely at level [big]). *)
  destruct (Hierarchy.IN_Univ_small _ HE) as [E' HEE'].
  destruct E' as [n0 | a0 b0 | I0 f0]; try (simpl in HEE'; contradiction).
  change (Hierarchy.injp@{big ulib} (sup I0 f0))
    with (sup I0 (fun k => Hierarchy.injp@{big ulib} (f0 k))) in HEE'.
  (* each [injp (f0 i)] is a member of [E], so [G] sends it into [Univ]. *)
  assert (Hmem : forall i : I0, IN (Hierarchy.injp@{big ulib} (f0 i)) (sup IE fE)).
  { intro i.
    apply IN_sound_right
      with (E' := sup I0 (fun k => Hierarchy.injp@{big ulib} (f0 k))).
    - apply EQ_sym; exact HEE'.
    - exists i; apply EQ_refl. }
  assert (Hex : forall i : I0,
             exists e, EQ (G (Hierarchy.injp@{big ulib} (f0 i)))
                          (Hierarchy.injp@{big ulib} e)).
  { intro i.
    apply (Hierarchy.IN_Univ_small (G (Hierarchy.injp@{big ulib} (f0 i)))).
    apply HB; apply Hmem. }
  (* choose a [big]-level preimage of each image element (classical [epsilon]). *)
  pose (h := fun i : I0 =>
     epsilon (inhabits (sup I0 f0))
        (fun e => EQ (G (Hierarchy.injp@{big ulib} (f0 i)))
                     (Hierarchy.injp@{big ulib} e))).
  assert (Hh : forall i : I0,
     EQ (G (Hierarchy.injp@{big ulib} (f0 i))) (Hierarchy.injp@{big ulib} (h i))).
  { intro i.
    exact (epsilon_spec (inhabits (sup I0 f0))
             (fun e => EQ (G (Hierarchy.injp@{big ulib} (f0 i)))
                          (Hierarchy.injp@{big ulib} e)) (Hex i)). }
  (* [sup I0 h : Ens@{big}] is the small witness placing the family in [Univ]. *)
  unfold Hierarchy.Univ, IN.
  exists (sup I0 h).
  change (Hierarchy.injp@{big ulib} (sup I0 h))
    with (sup I0 (fun i => Hierarchy.injp@{big ulib} (h i))).
  destruct HEE' as [Hfwd Hbwd].
  split.
  - intro x. destruct (Hfwd x) as [i Hi]. exists i.
    apply EQ_tran with (G (Hierarchy.injp@{big ulib} (f0 i))).
    + apply HG; exact Hi.
    + exact (Hh i).
  - intro i. destruct (Hbwd i) as [x Hx]. exists x.
    apply EQ_tran with (G (Hierarchy.injp@{big ulib} (f0 i))).
    + apply HG; exact Hx.
    + exact (Hh i).
Qed.

(** [U1] is closed under indexed unions, lifting [iUnion_Univ_Ens] across the
    quotient. *)
Lemma iUnion_U1 : forall (A : ZFSet) (B : ZFSet -> ZFSet),
  In A U1 -> (forall a, In a A -> In (B a) U1) -> In (iUnion A B) U1.
Proof.
  intros A B. pattern A; apply quot_ind. intros eA. fold (mk eA).
  intros HA HB.
  rewrite iUnion_mk. unfold U1. rewrite In_mk.
  apply iUnion_Univ_Ens.
  - intros x y Hxy. exact (liftF_Proper B x y Hxy).
  - unfold U1 in HA. rewrite In_mk in HA. exact HA.
  - intros a Ha.
    assert (Hmem : In (mk a) (mk eA)) by (rewrite In_mk; exact Ha).
    specialize (HB (mk a) Hmem).
    unfold U1 in HB. rewrite <- (mk_repr (B (mk a))) in HB. rewrite In_mk in HB.
    exact HB.
Qed.

(** *** [U0] is closed under indexed unions (replacement).

    The [U0] analogue of [iUnion_U1], one universe level down: [U0]'s carrier
    is [sup Ens' inj] (the *small* sets, injected by [inj : Ens' -> Ens]) rather
    than [Univ = sup Ens injp].  The replacement argument is identical, with the
    small witnesses now living at the [small] universe and picked with the same
    classical [epsilon].  It is what makes [U0] closed under dependent products
    [Pi] (see [ZFSetFacts.U0_Pi]). *)

(** Replacement for [U0]'s carrier, at the Aczel [Ens] level: if [E ∈ U0] and
    [G] carries every element of [E] into [U0], then the indexed union
    [EnsDefs.iUnion E G] is in [U0].

    [E ∈ U0] means [E] is [EQ] to the [inj]-image of a genuinely small set
    [sup I0 f0] (index [I0 : Type@{small}]), so the family [fun a => G (fE a)]
    can be re-indexed by the small [I0].  Each of its (small) elements has a
    small preimage, picked with Hilbert's [epsilon] — the informative content
    [IN]/[EXType] withholds, since membership is [Prop]-valued.  [G] must respect
    [EQ]; in the application [G = liftF B] does, since it factors through [mk]. *)
Lemma iUnion_U0_Ens :
  forall (G : Ens -> Ens),
    (forall x y : Ens, EQ x y -> EQ (G x) (G y)) ->
    forall E : Ens,
      IN E Hierarchy.U0@{ulib} ->
      (forall a : Ens, IN a E -> IN (G a) Hierarchy.U0@{ulib}) ->
      IN (EnsDefs.iUnion E G) Hierarchy.U0@{ulib}.
Proof.
  intros G HG E HE HB.
  destruct E as [n | a b | IE fE].
  { cbn [EnsDefs.iUnion]. apply Hierarchy.U0_contains_Vide. }
  { cbn [EnsDefs.iUnion]. apply Hierarchy.U0_contains_Vide. }
  (* [iUnion (sup IE fE) G = Union (sup IE (fun a => G (fE a)))]; [U0] is
     closed under [Union], so it suffices to place the family-[sup] in [U0]. *)
  cbn [EnsDefs.iUnion].
  apply Hierarchy.U0_closed_Union.
  (* [E]'s small preimage [sup I0 f0] (index [I0] genuinely at level [small]). *)
  destruct (Hierarchy.IN_U0_small _ HE) as [E' HEE'].
  destruct E' as [n0 | a0 b0 | I0 f0]; try (simpl in HEE'; contradiction).
  change (Hierarchy.inj@{ulib} (sup I0 f0))
    with (sup I0 (fun k => Hierarchy.inj@{ulib} (f0 k))) in HEE'.
  (* each [inj (f0 i)] is a member of [E], so [G] sends it into [U0]. *)
  assert (Hmem : forall i : I0, IN (Hierarchy.inj@{ulib} (f0 i)) (sup IE fE)).
  { intro i.
    apply IN_sound_right
      with (E' := sup I0 (fun k => Hierarchy.inj@{ulib} (f0 k))).
    - apply EQ_sym; exact HEE'.
    - exists i; apply EQ_refl. }
  assert (Hex : forall i : I0,
             exists e, EQ (G (Hierarchy.inj@{ulib} (f0 i)))
                          (Hierarchy.inj@{ulib} e)).
  { intro i.
    apply (Hierarchy.IN_U0_small (G (Hierarchy.inj@{ulib} (f0 i)))).
    apply HB; apply Hmem. }
  (* choose a small preimage of each image element (classical [epsilon]). *)
  pose (h := fun i : I0 =>
     epsilon (inhabits (sup I0 f0))
        (fun e => EQ (G (Hierarchy.inj@{ulib} (f0 i)))
                     (Hierarchy.inj@{ulib} e))).
  assert (Hh : forall i : I0,
     EQ (G (Hierarchy.inj@{ulib} (f0 i))) (Hierarchy.inj@{ulib} (h i))).
  { intro i.
    exact (epsilon_spec (inhabits (sup I0 f0))
             (fun e => EQ (G (Hierarchy.inj@{ulib} (f0 i)))
                          (Hierarchy.inj@{ulib} e)) (Hex i)). }
  (* [sup I0 h : Ens'] is the small witness placing the family in [U0]. *)
  unfold Hierarchy.U0.
  exists (sup I0 h).
  change (Hierarchy.inj@{ulib} (sup I0 h))
    with (sup I0 (fun i => Hierarchy.inj@{ulib} (h i))).
  destruct HEE' as [Hfwd Hbwd].
  split.
  - intro x. destruct (Hfwd x) as [i Hi]. exists i.
    apply EQ_tran with (G (Hierarchy.inj@{ulib} (f0 i))).
    + apply HG; exact Hi.
    + exact (Hh i).
  - intro i. destruct (Hbwd i) as [x Hx]. exists x.
    apply EQ_tran with (G (Hierarchy.inj@{ulib} (f0 i))).
    + apply HG; exact Hx.
    + exact (Hh i).
Qed.

(** [U0] is closed under indexed unions, lifting [iUnion_U0_Ens] across the
    quotient. *)
Lemma iUnion_U0 : forall (A : ZFSet) (B : ZFSet -> ZFSet),
  In A U0 -> (forall a, In a A -> In (B a) U0) -> In (iUnion A B) U0.
Proof.
  intros A B. pattern A; apply quot_ind. intros eA. fold (mk eA).
  intros HA HB.
  rewrite iUnion_mk. unfold U0. rewrite In_mk.
  apply iUnion_U0_Ens.
  - intros x y Hxy. exact (liftF_Proper B x y Hxy).
  - unfold U0 in HA. rewrite In_mk in HA. exact HA.
  - intros a Ha.
    assert (Hmem : In (mk a) (mk eA)) by (rewrite In_mk; exact Ha).
    specialize (HB (mk a) Hmem).
    unfold U0 in HB. rewrite <- (mk_repr (B (mk a))) in HB. rewrite In_mk in HB.
    exact HB.
Qed.


(** The product is the replacement of the couples over the two factors. *)
Lemma Prod_eq_iUnion : forall A B : ZFSet,
  Prod A B = iUnion A (fun a => iUnion B (fun b => Sing (Couple a b))).
Proof.
  intros A B. apply set_ext; inc_def; intros y Hy.
  - apply IN_Prod_EX in Hy. destruct Hy as [a [b [Ha [Hb Heq]]]]. subst y.
    apply IN_iUnion with a; [ exact Ha | ].
    apply IN_iUnion with b; [ exact Hb | apply IN_Sing ].
  - apply iUnion_IN in Hy. destruct Hy as [a [Ha Hy]].
    apply iUnion_IN in Hy. destruct Hy as [b [Hb Hy]].
    apply IN_Sing_EQ in Hy. subst y. apply Couple_IN_Prod; assumption.
Qed.

(** [U0] is closed under cartesian products: a product is a small-indexed
    union of small-indexed unions of singleton couples. *)
Lemma Prod_small : forall A B : ZFSet,
  A ∈ U0 -> B ∈ U0 -> Prod A B ∈ U0.
Proof.
  intros A B HA HB. rewrite Prod_eq_iUnion.
  apply iUnion_U0; [ exact HA | ]. intros a Ha.
  apply iUnion_U0; [ exact HB | ]. intros b Hb.
  apply Sing_small. apply Couple_small.
  - exact (U0_transitive _ _ Ha HA).
  - exact (U0_transitive _ _ Hb HB).
Qed.

Lemma Prod_U1 : forall A B : ZFSet,
  A ∈ U1 -> B ∈ U1 -> Prod A B ∈ U1.
Proof.
  intros A B HA HB. rewrite Prod_eq_iUnion.
  apply iUnion_U1; [ exact HA | ]. intros a Ha.
  apply iUnion_U1; [ exact HB | ]. intros b Hb.
  apply U0_sub_U1_Sing. apply Couple_U1.
  - exact (U1_transitive _ _ Ha HA).
  - exact (U1_transitive _ _ Hb HB).
Qed.

(* ================================================================== *)
(** * Derived universe-level sets *)
(* ================================================================== *)

(** The full diagonal on the universe [U0] — the identity relation on
    every small set. *)
(* notation:  diag U0  (no special syntax) *)
Definition anyId : ZFSet := diag U0.

(** [smallId]: the small partial identities — small subsets of the
    diagonal on [U0].  The predicative type universe. *)
(* notation:  ⦃ r ∈ U0 | r ⊆ diag U0 ⦄ *)
Definition smallId : ZFSet :=
  Comp U0 (fun r => Inc r (diag U0)).

(** [bigId]: the *big* partial identities — the [smallId] construction
    transported up one level of the tower [U0 ∈ U1].  These are the
    subsets of the diagonal on [U1] that are themselves members of [U1];
    the extra [r ∈ U1] bound (over [Power (diag U1)]) is what makes the
    universe of [□]-types closed under [(□,□)] products (see
    [paper/polymorphism.md]). *)
(* notation:  ⦃ r ∈ U1 | r ⊆ diag U1 ⦄ *)
Definition bigId : ZFSet :=
  Comp U1 (fun r => Inc r (diag U1)).

(** The identity relation on the partial identities [pIdFun U0] — the
    diagonal {⟨f,f⟩ : f ∈ pIdFun U0} — the type universe of the triple
    semantics (see [Timbda.Timbda2]). *)
(* notation:  diag (pIdFun U0)  (no special syntax) *)
Definition is_type : ZFSet := diag (pIdFun U0).

(* ================================================================== *)
(** * The smallness toolkit *)
(* ================================================================== *)

(** A subset of a member of [U0] is again a member of [U0]: it lies in
    the (small) power set of that member, and [U0] is transitive. *)
Lemma small_of_Inc : forall X V : ZFSet, X ⊆ V -> V ∈ U0 -> X ∈ U0.
Proof.
  intros X V HXV HV.
  destruct (ZFSet_sorts V) as [HVA | [HVP | HVS]].
  - (* [V] is an atom: [X] is [V], or an empty set *)
    destruct (ZFSet_sorts X) as [HXA | [HXP | HXS]].
    + rewrite (Inc_not_set_eq X V); [ exact HV | | exact HXV ].
      intro HS. revert HXA HS. pattern X; apply quot_ind. intros e.
      rewrite IsAtom_mk, IsSet_mk. destruct e; simpl; tauto.
    + rewrite (Inc_not_set_eq X V); [ exact HV | | exact HXV ].
      intro HS. revert HXP HS. pattern X; apply quot_ind. intros e.
      rewrite IsPair_mk, IsSet_mk. destruct e; simpl; tauto.
    + rewrite (all_empty_eq_Empty X HXS); [ apply Empty_small | ].
      apply Inc_not_set_no_mem with V; [ | exact HXV ].
      intro HS. revert HVA HS. pattern V; apply quot_ind. intros e.
      rewrite IsAtom_mk, IsSet_mk. destruct e; simpl; tauto.
  - destruct (ZFSet_sorts X) as [HXA | [HXP | HXS]].
    + rewrite (Inc_not_set_eq X V); [ exact HV | | exact HXV ].
      intro HS. revert HXA HS. pattern X; apply quot_ind. intros e.
      rewrite IsAtom_mk, IsSet_mk. destruct e; simpl; tauto.
    + rewrite (Inc_not_set_eq X V); [ exact HV | | exact HXV ].
      intro HS. revert HXP HS. pattern X; apply quot_ind. intros e.
      rewrite IsPair_mk, IsSet_mk. destruct e; simpl; tauto.
    + rewrite (all_empty_eq_Empty X HXS); [ apply Empty_small | ].
      apply Inc_not_set_no_mem with V; [ | exact HXV ].
      intro HS. revert HVP HS. pattern V; apply quot_ind. intros e.
      rewrite IsPair_mk, IsSet_mk. destruct e; simpl; tauto.
  - apply U0_transitive with (Power V).
    + apply Inc_IN_Power; [ exact HVS | exact HXV ].
    + apply In_Power_U0; exact HV.
Qed.

Lemma BinUnion_small : forall A B : ZFSet,
  A ∈ U0 -> B ∈ U0 -> A ∪ B ∈ U0.
Proof.
  intros A B HA HB. rewrite BinUnion_eq_Union_Paire.
  apply Union_small, Paire_small; assumption.
Qed.


(* ===== the same smallness toolkit, one level up at [U1] ===== *)

(** [U0 ⊆ U1] as sets: a member of [U0] is a member of [U1] (the tower
    [U0 ∈ U1] plus transitivity of [U1]). *)
Lemma U0_sub_U1 : forall X : ZFSet, X ∈ U0 -> X ∈ U1.
Proof.
  intros X HX. apply U1_transitive with U0.
  - exact HX.
  - apply U0_in_U1.
Qed.

(** A member of [U1] is a subset of [U1] (transitivity). *)
Lemma U1_subset : forall S : ZFSet, IsSet S -> S ∈ U1 -> S ⊆ U1.
Proof.
  intros S HSs HS. apply (Inc_intro _ _ HSs). intros x Hx. exact (U1_transitive _ _ Hx HS).
Qed.

(** A subset of a member of [U1] is again a member of [U1]. *)
Lemma big_of_Inc : forall X V : ZFSet, X ⊆ V -> V ∈ U1 -> X ∈ U1.
Proof.
  intros X V HXV HV.
  destruct (ZFSet_sorts V) as [HVA | [HVP | HVS]].
  - destruct (ZFSet_sorts X) as [HXA | [HXP | HXS]].
    + rewrite (Inc_not_set_eq X V); [ exact HV | | exact HXV ].
      intro HS. revert HXA HS. pattern X; apply quot_ind. intros e.
      rewrite IsAtom_mk, IsSet_mk. destruct e; simpl; tauto.
    + rewrite (Inc_not_set_eq X V); [ exact HV | | exact HXV ].
      intro HS. revert HXP HS. pattern X; apply quot_ind. intros e.
      rewrite IsPair_mk, IsSet_mk. destruct e; simpl; tauto.
    + rewrite (all_empty_eq_Empty X HXS); [ apply U0_sub_U1_Empty | ].
      apply Inc_not_set_no_mem with V; [ | exact HXV ].
      intro HS. revert HVA HS. pattern V; apply quot_ind. intros e.
      rewrite IsAtom_mk, IsSet_mk. destruct e; simpl; tauto.
  - destruct (ZFSet_sorts X) as [HXA | [HXP | HXS]].
    + rewrite (Inc_not_set_eq X V); [ exact HV | | exact HXV ].
      intro HS. revert HXA HS. pattern X; apply quot_ind. intros e.
      rewrite IsAtom_mk, IsSet_mk. destruct e; simpl; tauto.
    + rewrite (Inc_not_set_eq X V); [ exact HV | | exact HXV ].
      intro HS. revert HXP HS. pattern X; apply quot_ind. intros e.
      rewrite IsPair_mk, IsSet_mk. destruct e; simpl; tauto.
    + rewrite (all_empty_eq_Empty X HXS); [ apply U0_sub_U1_Empty | ].
      apply Inc_not_set_no_mem with V; [ | exact HXV ].
      intro HS. revert HVP HS. pattern V; apply quot_ind. intros e.
      rewrite IsPair_mk, IsSet_mk. destruct e; simpl; tauto.
  - apply U1_transitive with (Power V).
    + apply Inc_IN_Power; [ exact HVS | exact HXV ].
    + apply In_Power_U1; exact HV.
Qed.

(** Binary union is small at [U1] whenever both arguments are. *)
Lemma BinUnion_U1 : forall A B : ZFSet,
  A ∈ U1 -> B ∈ U1 -> A ∪ B ∈ U1.
Proof.
  intros A B HA HB. rewrite BinUnion_eq_Union_Paire.
  apply Union_U1, Paire_U1; assumption.
Qed.

(** [U0] is closed under function space.  A function space [A → B] is realised
    set-theoretically as the product [Pi A (fun _ => B)], whose elements are
    functional graphs: subsets of [A × B].  Hence [Pi A (fun _ => B) ⊆
    Power (A × B)], and [U0] — being closed under products ([Prod_small]) and
    power sets ([In_Power_U0]) — contains it. *)
Lemma Arr_small : forall A B : ZFSet,
  In A U0 -> In B U0 -> In (Pi A (fun _ => B)) U0.
Proof.
  intros A B HA HB.
  apply small_of_Inc with (V := Power (Prod A (iUnion A (fun _ => B)))).
  - (* a [Pi] is carved by separation out of [Power (A × ⋃B)] *)
    unfold Pi. apply Comp_Inc.
  - apply In_Power_U0. apply Prod_small.
    + exact HA.
    + (* [⋃_{a∈A} B ⊆ B], so it is small *)
      apply small_of_Inc with (V := B).
      * apply iUnion_Inc. intros y _. apply Inc_refl.
      * exact HB.
Qed.

(** [U0] / [U1] are closed under *dependent* products [Pi A B].  This
    generalises [Arr_small] (the constant-family case) to a codomain [B] that
    varies with the argument.  The same carrier bound
    [Pi A B ⊆ Power (Prod A (iUnion A B))] applies, but smallness of the
    codomain-union [iUnion A B] now needs *replacement* — a small-indexed union
    of small sets is small.  ([Arr_small] sidesteps it because the constant
    family satisfies [iUnion A (fun _ => B) ⊆ B].)

    The replacement step is discharged by [iUnion_U1] / [iUnion_U0] (in
    [ZFSetCore.v]), whose Aczel-level cores [iUnion_Univ_Ens] / [iUnion_U0_Ens]
    realise Grothendieck-universe replacement for the two carriers ([Univ] for
    [U1], [sup Ens' inj] for [U0]).  [U0_Pi] is used by the dependent /
    polymorphic embeddings (PredF's [∀], PLC — [lang/PLC/set_model.v],
    [LambdaSet/embedding/PLC.v]); the LambdaSet core only ever needs the
    constant-family [Arr_small]. *)
Lemma U0_Pi : forall (A : ZFSet) (B : ZFSet -> ZFSet),
  A ∈ U0 -> (forall a, a ∈ A -> B a ∈ U0) -> Pi A B ∈ U0.
Proof.
  intros A B HA HB.
  apply small_of_Inc with (V := Power (Prod A (iUnion A B))).
  - unfold Pi. apply Comp_Inc.
  - apply In_Power_U0. apply Prod_small.
    + exact HA.
    + apply iUnion_U0; [ exact HA | exact HB ].
Qed.

(** [U1] is closed under *dependent* products, via the carrier bound
    [Pi A B ⊆ Power (Prod A (iUnion A B))] and the replacement lemma
    [iUnion_U1] for the codomain-union. *)
Lemma U1_Pi : forall (A : ZFSet) (B : ZFSet -> ZFSet),
  A ∈ U1 -> (forall a, a ∈ A -> B a ∈ U1) -> Pi A B ∈ U1.
Proof.
  intros A B HA HB.
  apply big_of_Inc with (V := Power (Prod A (iUnion A B))).
  - unfold Pi. apply Comp_Inc.
  - apply In_Power_U1. apply Prod_U1.
    + exact HA.
    + apply iUnion_U1; [ exact HA | exact HB ].
Qed.

(* Unioning a graph's images over all small sources recovers its range
   (moved here from timbda/Timbda0_rewrites.v). *)
Lemma image_U0_rng (f : ZFSet) :
  (forall a b, In (Couple a b) f -> In a U0) ->
  (v ← U0 ;; image f {| v |}) = rng f.
Proof.
  intro Hsmall. apply set_ext; inc_def; intros b Hb.
  - apply iUnion_IN in Hb. destruct Hb as [v [_ Hb]].
    apply image_elim in Hb. destruct Hb as [a [_ Hab]].
    exact (rng_intro f a b Hab).
  - apply rng_elim in Hb. destruct Hb as [a Hab].
    apply (IN_iUnion U0 (fun v => image f {| v |}) a b).
    + exact (Hsmall a b Hab).
    + exact (image_intro f {| a |} b a (IN_Sing a) Hab).
Qed.

(* ================================================================== *)
(** * Diagonals, and the partial-identity universes *)
(* ================================================================== *)

(** The diagonal of a subset of [U0] is a subset of the diagonal on [U0]. *)
Lemma diag_Inc S : (forall x, x ∈ S -> x ∈ U0) -> diag S ⊆ diag U0.
Proof.
  intros HS. inc_def. intros x Hx.
  unfold diag in Hx. apply iUnion_IN in Hx. destruct Hx as [a [Ha Hx]].
  apply IN_Sing_EQ in Hx. rewrite Hx.
  unfold diag. apply IN_iUnion with (y := a); [ exact (HS a Ha) | apply IN_Sing ].
Qed.

(** The diagonal of a small set is small. *)
Lemma diag_small S : S ∈ U0 -> diag S ∈ U0.
Proof.
  intros HS. apply small_of_Inc with (V := Prod S S).
  - inc_def. intros x Hx. unfold diag in Hx.
    apply iUnion_IN in Hx. destruct Hx as [a [Ha Hx]]. apply IN_Sing_EQ in Hx.
    rewrite Hx. apply Couple_IN_Prod; exact Ha.
  - apply Prod_small; exact HS.
Qed.

(** A member of [U0] is a subset of [U0] (transitivity). *)
Lemma U0_subset S : IsSet S -> S ∈ U0 -> S ⊆ U0.
Proof. intros HSs HS. apply (Inc_intro _ _ HSs). intros x Hx. exact (U0_transitive _ _ Hx HS). Qed.

(** The range of a small set is small. *)
Lemma rng_small X : X ∈ U0 -> rng X ∈ U0.
Proof.
  intros HX. apply small_of_Inc with (V := iUnion X (fun p => Sing (psnd p))).
  - unfold rng. apply Comp_Inc.
  - apply iUnion_U0; [ exact HX | ]. intros p Hp.
    apply Sing_small. apply psnd_small. exact (U0_transitive _ _ Hp HX).
Qed.

(** A small partial identity is small. *)
Lemma smallId_small r : r ∈ smallId -> r ∈ U0.
Proof. intro H. unfold smallId in H. exact (Inc_IN _ _ _ (Comp_Inc _ _) H). Qed.

(** The diagonal of any small set is a small partial identity. *)
Lemma diag_in_smallId S : S ∈ U0 -> diag S ∈ smallId.
Proof.
  intro HS. unfold smallId. apply In_P_Comp.
  - apply diag_small; exact HS.
  - apply diag_Inc. intros x Hx. exact (U0_transitive _ _ Hx HS).
Qed.

(** A small partial identity is the diagonal of its own range — every element
    of [smallId] is a (full) diagonal. *)
Lemma diag_rng_smallId f : f ∈ smallId -> diag (rng f) = f.
Proof.
  intro Hf. pose proof (In_Comp_P _ _ _ Hf) as Hsub.   (* f ⊆ diag U0 *)
  pose proof (Inc_IsSet _ _ Hsub (IsSet_diag _)) as HfS.
  apply set_ext; [ inc_def | apply (Inc_intro _ _ HfS) ]; intros p Hp.
  - (* diag (rng f) ⊆ f *)
    apply iUnion_IN in Hp. destruct Hp as [b [Hb Hp]]. apply IN_Sing_EQ in Hp. subst p.
    apply rng_elim in Hb. destruct Hb as [a Hab].
    pose proof (Inc_IN _ _ _ Hsub Hab) as Hd.
    apply iUnion_IN in Hd. destruct Hd as [c [_ Hc]]. apply IN_Sing_EQ in Hc.
    pose proof (Couple_inj_left _ _ _ _ Hc) as Ea.
    pose proof (Couple_inj_right _ _ _ _ Hc) as Eb. subst a b. exact Hab.
  - (* f ⊆ diag (rng f) *)
    pose proof (Inc_IN _ _ _ Hsub Hp) as Hd.
    apply iUnion_IN in Hd. destruct Hd as [c [_ Hpc]]. apply IN_Sing_EQ in Hpc. subst p.
    apply IN_iUnion with (y := c); [ apply (rng_intro _ c c); exact Hp | apply IN_Sing ].
Qed.

(* ================================================================== *)
(** * The big partial identities [bigId], one level up at [U1].

    Everything above transports up the tower [U0 ∈ U1]: [bigId] is
    [smallId] built over [U1] instead of [U0].  These are the analogues
    used to model the sort [□] of PLC, where the [r ∈ U1] bound is what
    keeps [(□,□)] products inside the universe (see
    [paper/polymorphism.md]). *)
(* ================================================================== *)

(** The diagonal of a [U1]-set is in [U1]. *)
Lemma diag_small_U1 S : S ∈ U1 -> diag S ∈ U1.
Proof.
  intros HS. apply big_of_Inc with (V := Prod S S).
  - inc_def. intros x Hx. unfold diag in Hx.
    apply iUnion_IN in Hx. destruct Hx as [a [Ha Hx]]. apply IN_Sing_EQ in Hx.
    rewrite Hx. apply Couple_IN_Prod; exact Ha.
  - apply Prod_U1; exact HS.
Qed.

(** The range of a [U1]-set is in [U1]. *)
Lemma rng_big X : X ∈ U1 -> rng X ∈ U1.
Proof.
  intros HX. apply big_of_Inc with (V := iUnion X (fun p => Sing (psnd p))).
  - unfold rng. apply Comp_Inc.
  - apply iUnion_U1; [ exact HX | ]. intros p Hp.
    apply U0_sub_U1_Sing. apply psnd_U1. exact (U1_transitive _ _ Hp HX).
Qed.

(** A big partial identity is a member of [U1]. *)
Lemma bigId_big r : r ∈ bigId -> r ∈ U1.
Proof. intro H. unfold bigId in H. exact (Inc_IN _ _ _ (Comp_Inc _ _) H). Qed.

(** The diagonal of any [U1]-set is a big partial identity. *)
Lemma diag_in_bigId S : S ∈ U1 -> diag S ∈ bigId.
Proof.
  intro HS. unfold bigId. apply In_P_Comp.
  - apply diag_small_U1; exact HS.
  - inc_def. intros x Hx.
    unfold diag in Hx. apply iUnion_IN in Hx. destruct Hx as [a [Ha Hx]].
    apply IN_Sing_EQ in Hx. rewrite Hx.
    unfold diag. apply IN_iUnion with (y := a); [ exact (U1_transitive _ _ Ha HS) | apply IN_Sing ].
Qed.

(** The type universe [∗] (value [diag smallId]) is a big partial identity:
    the axiom [∗ : □] is discharged by the tower [U0 ∈ U1] — [smallId ⊆ U0 ∈
    U1] gives [smallId ∈ U1], and then [diag smallId ∈ bigId]. *)
Lemma diag_smallId_in_bigId : diag smallId ∈ bigId.
Proof.
  apply diag_in_bigId.
  apply big_of_Inc with (V := U0).
  - unfold smallId. apply Comp_Inc.
  - apply U0_in_U1.
Qed.

(** A big partial identity is the diagonal of its own range. *)
Lemma diag_rng_bigId f : f ∈ bigId -> diag (rng f) = f.
Proof.
  intro Hf. pose proof (In_Comp_P _ _ _ Hf) as Hsub.   (* f ⊆ diag U1 *)
  pose proof (Inc_IsSet _ _ Hsub (IsSet_diag _)) as HfS.
  apply set_ext; [ inc_def | apply (Inc_intro _ _ HfS) ]; intros p Hp.
  - apply iUnion_IN in Hp. destruct Hp as [b [Hb Hp]]. apply IN_Sing_EQ in Hp. subst p.
    apply rng_elim in Hb. destruct Hb as [a Hab].
    pose proof (Inc_IN _ _ _ Hsub Hab) as Hd.
    apply iUnion_IN in Hd. destruct Hd as [c [_ Hc]]. apply IN_Sing_EQ in Hc.
    pose proof (Couple_inj_left _ _ _ _ Hc) as Ea.
    pose proof (Couple_inj_right _ _ _ _ Hc) as Eb. subst a b. exact Hab.
  - pose proof (Inc_IN _ _ _ Hsub Hp) as Hd.
    apply iUnion_IN in Hd. destruct Hd as [c [_ Hpc]]. apply IN_Sing_EQ in Hpc. subst p.
    apply IN_iUnion with (y := c); [ apply (rng_intro _ c c); exact Hp | apply IN_Sing ].
Qed.

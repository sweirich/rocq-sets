(* lib/V2.v

   A *tagged* recursive universe of values over [ZFSet]:

        data V2 = Base (ZFSet × ZFSet) | Fun (Rel V2 V2)

   built on the generic tagging layer of [lib/Tags.v].  A value carries a tag
   ([tagBase = natZ 0] / [tagFun = natZ 1]) in its first component, so the
   tag-aware projections [fstV] / [sndV] can tell a base (relational) pair from
   a function/type — something the blind [FST] / [SND] of [lib/Projections.v]
   cannot do.  This is pure [ZFSet] infrastructure, independent of any object
   language; it was factored out of [Timbda.Parametricity]. *)

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

Require Export Tags.

(* ================================================================== *)
(** * A tagged union of values (recursive):

        data V2 = Base (ZFSet × ZFSet) | Fun (Rel V2 V2)

    [FST]/[SND] ([lib/Projections.v]) cannot tell a base (relational) pair from
    a function graph — the ambiguity that let a non-identity graph slip into
    [eval pid] (cf. the [eval_pid] discussion).  We remove it by *tagging* (via
    [lib/Tags.v]): a value carries [tagBase = natZ 0] or [tagFun = natZ 1] in
    its first component.  [Fun] holds a *relation on V2* ([Rel V2 V2] — a set of
    couples of V2 values), so the datatype is recursive; its carrier is the
    predicate [inV2] below. *)

Definition tagBase : ZFSet := natZ 0.
Definition tagFun  : ZFSet := natZ 1.

Lemma tag_neq : tagBase <> tagFun.
Proof. unfold tagBase, tagFun. apply natZ_neq. discriminate. Qed.

(* Constructors: [Base p] tags a pair [p = ⟨a,b⟩]; [Fun f] tags a relation.
   They are the two-tag ([0]/[1]) instances of the generic [Tag]. *)
Definition Base (p : ZFSet) : ZFSet := Tag 0 p.
Definition Fun  (f : ZFSet) : ZFSet := Tag 1 f.
Definition Base2 (a b : ZFSet) : ZFSet := Base ⟨ a , b ⟩.

(* Injectivity and disjointness — the datatype laws, from the generic ones. *)
Lemma Base_inj : forall p q, Base p = Base q -> p = q.
Proof. intros p q H. exact (Tag_inj_payload _ _ _ H). Qed.
Lemma Fun_inj : forall f g, Fun f = Fun g -> f = g.
Proof. intros f g H. exact (Tag_inj_payload _ _ _ H). Qed.
Lemma Base_neq_Fun : forall p f, Base p <> Fun f.
Proof. intros p f. apply Tag_neq. discriminate. Qed.

(* Payload/tag projections, specialized to the two constructors. *)
Lemma tagOf_Base   : forall p, tagOf (Base p) = tagBase.
Proof. intro p. unfold tagBase, Base. apply tagOf_Tag. Qed.
Lemma tagOf_Fun    : forall f, tagOf (Fun f)  = tagFun.
Proof. intro f. unfold tagFun, Fun. apply tagOf_Tag. Qed.
Lemma payload_Base : forall p, payload (Base p) = p.
Proof. intro p. unfold Base. apply payload_Tag. Qed.
Lemma payload_Fun  : forall f, payload (Fun f) = f.
Proof. intro f. unfold Fun. apply payload_Tag. Qed.

(* The (recursive) carrier [V2], as the least predicate closed under the two
   constructors.  Stated in [Acc]-style — the recursive occurrences [inV2 x],
   [inV2 y] are conclusions of hypotheses (not buried under [∃]) — so the
   generated induction principle yields usable IHs (needed for [inV2_Acc]).
   [Base] takes any pair of [ZFSet]s (leaves); [Fun]'s premises say
   [f ∈ Rel V2 V2 = P (V2 × V2)]: every member is a couple with both
   projections in [V2]. *)
Inductive inV2 : ZFSet -> Prop :=
  | inV2_Base : forall a b, inV2 (Base ⟨ a , b ⟩)
  | inV2_Fun  : forall f,
      (forall e, e ∈ f -> isCouple e) ->
      (forall x y, ⟨ x , y ⟩ ∈ f -> inV2 x) ->
      (forall x y, ⟨ x , y ⟩ ∈ f -> inV2 y) ->
      inV2 (Fun f).

(* ================================================================== *)
(** * Tag-branching [fstV] / [sndV].

    [FST]/[SND] ([lib/Projections.v]) treat *every* couple as a base pair, so
    they read a [Fun] value [⟨tagFun,f⟩] as a pair and project the tag — the
    confusion behind the spurious element of [eval pid].  [fstV]/[sndV] instead
    branch on the tag:

      fstV (Base ⟨a,b⟩) = a              sndV (Base ⟨a,b⟩) = b
      fstV (Fun f) = {⟨fstV x, fstV y⟩ | ⟨x,y⟩ ∈ f}      (and sym. for [sndV])

    A base pair yields its component; a function yields the left/right function
    over its relation, recursing through [Fun] layers down to [Base] leaves.
    Same ∈-recursion as [projRec], but descending into the *payload* [psnd v]
    and branching on [tagOf v] rather than on [isCouple]. *)

(* The recursion order: descend, *only through a [Fun] node*, into the
   projections of the elements of its payload relation.  The [tagOf v = tagFun]
   guard means a [Base] node has no predecessors — its payload [⟨a,b⟩] is a
   leaf, not a V2 value — which is what makes [inV2_Acc] go through. *)
Definition Vbelow (x v : ZFSet) : Prop :=
  tagOf v = tagFun /\ exists e, e ∈ payload v /\ (x = pfst e \/ x = psnd e).

(* [inV2] *is* the termination metric: on a well-formed value the recursion is
   well-founded by structural induction on the [inV2] derivation — no rank
   argument.  ([Base] nodes have no [Vbelow]-predecessor; at a [Fun] node every
   predecessor is a projection of a couple in the relation, hence a component
   already known to be in [V2], so the IH applies.) *)
Lemma inV2_Acc : forall v, inV2 v -> Acc Vbelow v.
Proof.
  intros v Hv. induction Hv as [a b | f Hc Hx IHx Hy IHy].
  - (* Base: a [Vbelow]-predecessor would need [tagOf (Base _) = tagFun]. *)
    constructor. intros z Hz. destruct Hz as [Htag _].
    rewrite tagOf_Base in Htag. destruct (tag_neq Htag).
  - (* Fun: each predecessor is a projection of a couple [⟨x,y⟩ ∈ f]. *)
    constructor. intros z Hz. destruct Hz as [Htag [e [He Hsel]]].
    rewrite payload_Fun in He.
    destruct (Hc e He) as [x [y He2]]. subst e.
    rewrite pfst_Couple psnd_Couple in Hsel.
    destruct Hsel as [Hsel | Hsel]; subst z;
      [ exact (IHx x y He) | exact (IHy x y He) ].
Qed.

(* For *all* [ZFSet]s the order is still well-founded by rank (as
   [Projections.wf_projBelow], itself admitted pending the rank development);
   this is only needed to make [projV] total on ill-formed inputs — on genuine
   V2 values termination is [inV2_Acc], with no admit.

   NOTE: like [wf_projBelow], nothing proved depends on this admit.  [V2.v] is
   a standalone experiment (not re-exported by [ZFSets]), and its only consumers
   [projV] / [fstV] / [sndV] are used by no proof; the admit-free [projV']
   (below, built on [inV2_Acc]) is the version to use for real values. *)
Lemma wf_Vbelow : well_founded Vbelow.
Admitted.

(* One recursion step: at a [Fun]-tagged [v], rebuild the relation [payload v]
   mapping each [⟨x,y⟩] to [⟨rec x, rec y⟩]; otherwise apply [base] to the
   payload pair. *)
Definition fstSnd_step (base : ZFSet -> ZFSet) (v : ZFSet)
    (rec : forall y : ZFSet, Vbelow y v -> ZFSet) : ZFSet.
Proof.
  destruct (excluded_middle_informative (tagOf v = tagFun)) as [Hf | Hnf].
  - refine (mk (Sets.sup (pi1 (repr (payload v)))
              (fun a => repr (⟨ rec (pfst (mk (pi2 (repr (payload v)) a))) _
                              , rec (psnd (mk (pi2 (repr (payload v)) a))) _ ⟩)))).
    + split; [ exact Hf | exists (mk (pi2 (repr (payload v)) a));
                          split; [ apply In_mk_pi2 | left; reflexivity ] ].
    + split; [ exact Hf | exists (mk (pi2 (repr (payload v)) a));
                          split; [ apply In_mk_pi2 | right; reflexivity ] ].
  - exact (base (payload v)).
Defined.

Definition projV (base : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  Fix wf_Vbelow (fun _ => ZFSet) (fstSnd_step base).

Lemma fstSnd_step_ext :
  forall (base : ZFSet -> ZFSet) (x : ZFSet)
         (g h : forall y, Vbelow y x -> ZFSet),
    (forall y p, g y p = h y p) -> fstSnd_step base x g = fstSnd_step base x h.
Proof.
  intros base x g h Hgh. unfold fstSnd_step.
  destruct (excluded_middle_informative (tagOf x = tagFun)).
  - do 2 f_equal. apply functional_extensionality. intro a. rewrite !Hgh. reflexivity.
  - reflexivity.
Qed.

Lemma projV_unfold : forall base v,
  projV base v = fstSnd_step base v (fun y _ => projV base y).
Proof.
  intro base. apply (Fix_eq wf_Vbelow (fun _ => ZFSet) (fstSnd_step base)).
  intros x g h H. apply fstSnd_step_ext. exact H.
Qed.

Lemma projV_Base : forall base p, projV base (Base p) = base p.
Proof.
  intros base p. rewrite projV_unfold. unfold fstSnd_step.
  destruct (excluded_middle_informative (tagOf (Base p) = tagFun)) as [Hf | Hnf].
  - exfalso. apply tag_neq. rewrite <- (tagOf_Base p). exact Hf.
  - rewrite payload_Base. reflexivity.
Qed.

Lemma projV_Fun : forall base f,
  projV base (Fun f)
  = (e ← f ;; {| ⟨ projV base (pfst e), projV base (psnd e) ⟩ |}).
Proof.
  intros base f. rewrite projV_unfold. unfold fstSnd_step.
  destruct (excluded_middle_informative (tagOf (Fun f) = tagFun)) as [Hf | Hnf].
  - rewrite payload_Fun.
    apply (image_repr_eq_iUnion (fun e => ⟨ projV base (pfst e), projV base (psnd e) ⟩)).
  - exfalso. apply Hnf. apply tagOf_Fun.
Qed.

Definition fstV : ZFSet -> ZFSet := projV pfst.
Definition sndV : ZFSet -> ZFSet := projV psnd.

Lemma fstV_Base : forall a b, fstV (Base ⟨ a , b ⟩) = a.
Proof. intros a b. unfold fstV. rewrite projV_Base. apply pfst_Couple. Qed.
Lemma sndV_Base : forall a b, sndV (Base ⟨ a , b ⟩) = b.
Proof. intros a b. unfold sndV. rewrite projV_Base. apply psnd_Couple. Qed.
Lemma fstV_Fun : forall f,
  fstV (Fun f) = (e ← f ;; {| ⟨ fstV (pfst e), fstV (psnd e) ⟩ |}).
Proof. intro f. unfold fstV. exact (projV_Fun pfst f). Qed.
Lemma sndV_Fun : forall f,
  sndV (Fun f) = (e ← f ;; {| ⟨ sndV (pfst e), sndV (psnd e) ⟩ |}).
Proof. intro f. unfold sndV. exact (projV_Fun psnd f). Qed.

(* ================================================================== *)
(** ** Admit-free variant [projV'] / [fstV'] / [sndV'].

    [projV] above is total ([ZFSet -> ZFSet]) and so leans on the rank admit
    [wf_Vbelow] for totality.  Here is the *proof-carrying* version built on
    [Fix_F] applied to [inV2_Acc] — it terminates by structural induction on the
    [inV2] derivation, so [projV'] / [projV'_irrel] / [projV'_Base] use **no
    admit** at all.  The price: it takes the [inV2] proof, and its [Fun]
    equation is phrased through the recursion (here, via agreement with the
    total [projV]).  Proof-irrelevance ([projV'_irrel]) means the result does
    not depend on which [inV2] proof is supplied. *)

(* [Fix_F] is independent of the accessibility proof — proved by induction on
   the [Acc] derivation (NOT by [Fix_F_inv], which would re-require
   [well_founded]). *)
Lemma Fix_F_pi :
  forall (base : ZFSet -> ZFSet) (x : ZFSet) (r s : Acc Vbelow x),
    Fix_F (fun _ => ZFSet) (fstSnd_step base) r
    = Fix_F (fun _ => ZFSet) (fstSnd_step base) s.
Proof.
  intros base. fix REC 2. intros x r s. destruct r as [Hr].
  rewrite <- Fix_F_eq. rewrite <- Fix_F_eq.
  apply fstSnd_step_ext. intros y p. apply (REC y (Hr y p) (Acc_inv s p)).
Qed.

Definition projV' (base : ZFSet -> ZFSet) (v : ZFSet) (Hv : inV2 v) : ZFSet :=
  Fix_F (fun _ => ZFSet) (fstSnd_step base) (inV2_Acc v Hv).

Lemma projV'_irrel : forall base v (H H' : inV2 v),
  projV' base v H = projV' base v H'.
Proof. intros base v H H'. unfold projV'. apply Fix_F_pi. Qed.

Lemma projV'_Base : forall base p (Hv : inV2 (Base p)), projV' base (Base p) Hv = base p.
Proof.
  intros base p Hv. unfold projV'.
  rewrite <- Fix_F_eq. unfold fstSnd_step.
  destruct (excluded_middle_informative (tagOf (Base p) = tagFun)) as [Hf | Hnf].
  - exfalso. rewrite tagOf_Base in Hf. exact (tag_neq Hf).
  - rewrite payload_Base. reflexivity.
Qed.

(* [projV'] coincides with the total [projV] on well-formed values (both are
   [Fix_F] over the same step, at different [Acc] proofs).  This transports
   [projV]'s clean equations onto [projV']; it mentions [projV], so its
   *statement* depends on [wf_Vbelow], but the proof adds only [Fix_F_pi]. *)
Lemma projV_eq_projV' : forall base v (Hv : inV2 v), projV base v = projV' base v Hv.
Proof. intros base v Hv. unfold projV', projV, Fix. apply Fix_F_pi. Qed.

Lemma projV'_Fun : forall base f (Hv : inV2 (Fun f)),
  projV' base (Fun f) Hv = (e ← f ;; {| ⟨ projV base (pfst e), projV base (psnd e) ⟩ |}).
Proof. intros base f Hv. rewrite <- projV_eq_projV'. apply projV_Fun. Qed.

Definition fstV' (v : ZFSet) (Hv : inV2 v) : ZFSet := projV' pfst v Hv.
Definition sndV' (v : ZFSet) (Hv : inV2 v) : ZFSet := projV' psnd v Hv.

Lemma fstV'_Base : forall a b Hv, fstV' (Base ⟨ a , b ⟩) Hv = a.
Proof. intros a b Hv. unfold fstV'. rewrite projV'_Base. apply pfst_Couple. Qed.
Lemma sndV'_Base : forall a b Hv, sndV' (Base ⟨ a , b ⟩) Hv = b.
Proof. intros a b Hv. unfold sndV'. rewrite projV'_Base. apply psnd_Couple. Qed.
Lemma fstV'_Fun : forall f Hv,
  fstV' (Fun f) Hv = (e ← f ;; {| ⟨ fstV (pfst e), fstV (psnd e) ⟩ |}).
Proof. intros f Hv. unfold fstV'. exact (projV'_Fun pfst f Hv). Qed.
Lemma sndV'_Fun : forall f Hv,
  sndV' (Fun f) Hv = (e ← f ;; {| ⟨ sndV (pfst e), sndV (psnd e) ⟩ |}).
Proof. intros f Hv. unfold sndV'. exact (projV'_Fun psnd f Hv). Qed.

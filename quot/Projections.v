(** * Projections.v — the [FST] / [SND] operations on ZFSets.

    Following the relation reading:

      FST(x,y) = x                 SND(x,y) = y
      FST(f)   = { ⟨FST x, FST y⟩ | ⟨x,y⟩ ∈ f }
      SND(f)   = { ⟨SND x, SND y⟩ | ⟨x,y⟩ ∈ f }

    [FST]/[SND] are defined by recursion on set *rank* (∈-recursion), not by
    structural recursion: the recursive calls land on the components
    [pfst e] / [psnd e] of the couples [e ∈ f], which are smaller in rank but
    are not structural subterms of [f].  We therefore use well-founded
    recursion over the relation [projBelow] ("is a component of a couple
    member of") — well-founded by [Foundation.Below_wf], now that couples are
    primitive.  Whether a value is a couple is decided by [isCoupleb], which
    reads the constructor of a representative through [quot_rec]; it needs
    no choice or excluded middle.  Working directly on [ZFSet] (whose
    equality is Leibniz [=]) keeps these ordinary Rocq functions.

    [FST] and [SND] differ only in the base case, so both are instances of a
    single recursor [projRec] parameterised by the base operation.  The
    recursive clause ranges over the couple members of [f]: a non-couple
    member has no components and is dropped. *)

From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Relation_Operators Morphisms.
From Stdlib Require Import Wellfounded.Inclusion.

Require Import utils.axioms.
Require Import Sets.
Require Import Axioms.
Require Import Cartesian.

Require Import ZFSetFacts.
Require Import ZFNotation.
Require Import Diagonal.
Require Import Foundation.

(** ** Membership helpers for the [mk]/[repr]/[sup] interface. *)

(* Every [pi2]-component of an [Ens] is a member of it. *)
Lemma IN_pi2 : forall (E : Ens) (a : pi1 E), IN (pi2 E a) E.
Proof.
  intros E a. destruct E as [n | b c | A g]; simpl in a.
  - destruct a.
  - destruct a.
  - apply (EXTypei _ _ a). apply EQ_refl.
Qed.

(* The [a]-th representative element of [X] really is a member of [X]. *)
Lemma In_mk_pi2 : forall (X : ZFSet) (a : pi1 (repr X)),
  In (mk (pi2 (repr X) a)) X.
Proof.
  intros X a.
  assert (H : In (mk (pi2 (repr X) a)) (mk (repr X))).
  { rewrite In_mk. revert a. generalize (repr X). intros e a.
    destruct e as [n | b c | A g]; simpl in a.
    - destruct a.
    - destruct a.
    - apply (EXTypei _ _ a). apply EQ_refl. }
  rewrite mk_repr in H. exact H.
Qed.

(* Membership in a [mk (sup A F)] is exactly "is one of the [mk (F a)]". *)
Lemma In_mk_sup_iff : forall (A : Type) (F : A -> Ens) (w : ZFSet),
  In w (mk (sup A F)) <-> exists a, w = mk (F a).
Proof.
  intros A F w. split.
  - intro H. rewrite <- (mk_repr w) in H. rewrite In_mk in H.
    destruct (IN_EXType (sup A F) (repr w) H) as [a Ha].
    exists a. rewrite <- (mk_repr w). apply mk_eq. exact Ha.
  - intros [a Ha]. subst w. rewrite In_mk.
    apply (EXTypei _ _ a). apply EQ_refl.
Qed.

(* Conversely, a member of [f] is [mk] of some representative component. *)
Lemma In_inv_pi2 : forall (e f : ZFSet),
  In e f -> exists a, e = mk (pi2 (repr f) a).
Proof.
  intros e f H.
  rewrite <- (mk_repr f) in H. rewrite <- (mk_repr e) in H. rewrite In_mk in H.
  destruct (IN_EXType (repr f) (repr e) H) as [a Ha].
  exists a. rewrite <- (mk_repr e). apply mk_eq. exact Ha.
Qed.

(** ** Couples. *)

(* [f] is a couple iff it is the couple of its two projections. *)
Definition isCouple (f : ZFSet) : Prop := exists x y, f = ⟨ x , y ⟩.

Lemma isCouple_IsPair : forall f : ZFSet, isCouple f <-> IsPair f.
Proof.
  intro f. split.
  - intros [x [y H]]. rewrite H. apply Couple_IsPair.
  - intro H. revert H. pattern f; apply ZFSet_ind1. intros e H.
    rewrite IsPair_mk in H. destruct e as [n | a b | A g]; try contradiction.
    exists (mk a), (mk b). rewrite Couple_mk. reflexivity.
Qed.

(* A boolean test for couples: the constructor of any representative.  [EQ]
   preserves the constructor, so this lifts through [quot_rec] without choice. *)
Definition is_pairb (e : Ens) : bool :=
  match e with pair _ _ => true | _ => false end.

#[global] Instance is_pairb_Proper : Proper (EQ ==> eq)%signature is_pairb.
Proof.
  intros x y H. destruct x, y; simpl in H; try contradiction; reflexivity.
Qed.

Definition isCoupleb : ZFSet -> bool := quot_rec is_pairb.

Lemma isCoupleb_mk : forall e : Ens, isCoupleb (mk e) = is_pairb e.
Proof. intro e. unfold isCoupleb, mk. apply quot_rec_eq. Qed.

Lemma isCoupleb_true : forall f : ZFSet, isCoupleb f = true <-> isCouple f.
Proof.
  intro f. rewrite isCouple_IsPair. pattern f; apply ZFSet_ind1. intro e.
  rewrite isCoupleb_mk, IsPair_mk. destruct e; simpl; split; intro H;
    solve [ reflexivity | exact I | discriminate H | contradiction ].
Qed.

Lemma isCoupleb_false : forall f : ZFSet, isCoupleb f = false <-> ~ isCouple f.
Proof.
  intro f. rewrite <- isCoupleb_true. destruct (isCoupleb f); split; intro H;
    solve [ discriminate H | reflexivity | exfalso; apply H; reflexivity | intro; discriminate ].
Qed.

(* No couple is a *member* of another couple — couples are memberless. *)
Lemma Couple_not_in_Couple : forall a v c d, ⟨ a , v ⟩ ∈ ⟨ c , d ⟩ -> False.
Proof. intros a v c d H. exact (not_In_Couple _ _ _ H). Qed.

(* Every couple is the couple of its projections. *)
Lemma isCouple_proj : forall f : ZFSet, isCouple f -> f = ⟨ pfst f , psnd f ⟩.
Proof.
  intros f [x [y H]]. subst f. rewrite pfst_Couple, psnd_Couple. reflexivity.
Qed.

(** ** The recursion: rank order and the generic step. *)

(* The well-founded order for the recursion: [x] is [pfst] or [psnd] of some
   couple member of [y]. *)
Definition projBelow (x y : ZFSet) : Prop :=
  exists e, In e y /\ isCouple e /\ (x = pfst e \/ x = psnd e).

Lemma projBelow_BelowTC : forall x y, projBelow x y -> BelowTC x y.
Proof.
  intros x y [e [He [Hc Hx]]].
  apply BelowTC_trans with e; [ | apply BelowTC_mem; exact He ].
  destruct Hc as [u [v Hev]]. subst e. rewrite pfst_Couple, psnd_Couple in Hx.
  destruct Hx as [Hx | Hx]; subst x; [ apply BelowTC_fst | apply BelowTC_snd ].
Qed.

Lemma wf_projBelow : well_founded projBelow.
Proof. apply wf_incl with BelowTC; [ exact projBelow_BelowTC | exact BelowTC_wf ]. Qed.

(* The couple members of [f]. *)
Definition couples (f : ZFSet) : ZFSet := Comp f isCouple.

Lemma In_couples : forall e f, In e (couples f) <-> In e f /\ isCouple e.
Proof.
  intros e f. unfold couples. split.
  - intro H. split; [ exact (Inc_IN _ _ _ (Comp_Inc _ _) H) | exact (In_Comp_P _ _ _ H) ].
  - intros [H1 H2]. apply In_P_Comp; assumption.
Qed.

(* One step of the recursion, parameterised by the base operation [base]
   applied to couples.  Off couples, rebuild the set mapping every couple
   member ⟨x,y⟩ to ⟨rec x, rec y⟩.  The recursive branch is built on a
   representative of [couples f] so that the index supplies the membership
   proofs [projBelow] requires ([iUnion]/[Comp] would hide them). *)
Definition proj_step (base : ZFSet -> ZFSet) (f : ZFSet)
    (rec : forall y : ZFSet, projBelow y f -> ZFSet) : ZFSet.
Proof.
  destruct (isCoupleb f).
  - exact (base f).
  - refine (mk (sup (pi1 (repr (couples f)))
              (fun a => repr (⟨ rec (pfst (mk (pi2 (repr (couples f)) a))) _
                              , rec (psnd (mk (pi2 (repr (couples f)) a))) _ ⟩)))).
    + exists (mk (pi2 (repr (couples f)) a)).
      pose proof (In_mk_pi2 (couples f) a) as Hm. apply In_couples in Hm.
      destruct Hm as [Hm Hcp]. split; [ exact Hm | split; [ exact Hcp | left; reflexivity ] ].
    + exists (mk (pi2 (repr (couples f)) a)).
      pose proof (In_mk_pi2 (couples f) a) as Hm. apply In_couples in Hm.
      destruct Hm as [Hm Hcp]. split; [ exact Hm | split; [ exact Hcp | right; reflexivity ] ].
Defined.

Definition projRec (base : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  Fix wf_projBelow (fun _ => ZFSet) (proj_step base).

(** ** Unfolding lemmas for the generic recursor. *)

(* [proj_step] uses its recursive argument only by applying it, so it does not
   depend on the [projBelow] proofs — the hypothesis [Fix_eq] needs. *)
Lemma proj_step_ext :
  forall (base : ZFSet -> ZFSet) (x : ZFSet)
         (g h : forall y, projBelow y x -> ZFSet),
    (forall (y : ZFSet) (p : projBelow y x), g y p = h y p) ->
    proj_step base x g = proj_step base x h.
Proof.
  intros base x g h Hgh. unfold proj_step.
  destruct (isCoupleb x).
  - reflexivity.
  - do 2 f_equal. apply functional_extensionality. intro a.
    rewrite !Hgh. reflexivity.
Qed.

Lemma projRec_unfold :
  forall (base : ZFSet -> ZFSet) (f : ZFSet),
    projRec base f = proj_step base f (fun y _ => projRec base y).
Proof.
  intro base.
  apply (Fix_eq wf_projBelow (fun _ => ZFSet) (proj_step base)).
  intros x g h H. apply proj_step_ext. exact H.
Qed.

(* The image-of-singletons construction on a representative is just the
   [iUnion]/replacement of those singletons; key to the relational unfolding. *)
Lemma image_repr_eq_iUnion : forall (G : ZFSet -> ZFSet) (f : ZFSet),
  mk (sup (pi1 (repr f)) (fun a => repr (G (mk (pi2 (repr f) a)))))
  = (e ← f ;; {| G e |}).
Proof.
  intros G f. apply set_ext.
  - apply Inc_intro; [ rewrite IsSet_mk; exact I | ]. intros w Hw.
    apply In_mk_sup_iff in Hw. destruct Hw as [a Ha]. rewrite mk_repr in Ha.
    apply IN_iUnion with (y := mk (pi2 (repr f) a)).
    + apply In_mk_pi2.
    + rewrite Ha. apply IN_Sing.
  - inc_def. intros w Hw.
    apply iUnion_IN in Hw. destruct Hw as [e [Hef Hw]].
    apply IN_Sing_EQ in Hw.
    destruct (In_inv_pi2 _ _ Hef) as [a Hae].
    apply In_mk_sup_iff. exists a. rewrite mk_repr, Hw, Hae. reflexivity.
Qed.

(* Base case: on a couple, [projRec] is its base operation. *)
Lemma projRec_Couple :
  forall (base : ZFSet -> ZFSet) (x y : ZFSet),
    projRec base (⟨ x , y ⟩) = base (⟨ x , y ⟩).
Proof.
  intros base x y. rewrite projRec_unfold. unfold proj_step.
  assert (Hc : isCoupleb (⟨ x , y ⟩) = true)
    by (apply isCoupleb_true; exists x, y; reflexivity).
  rewrite Hc. reflexivity.
Qed.

(* Recursive case: off couples, [projRec] maps over the couple members. *)
Lemma projRec_rel :
  forall (base : ZFSet -> ZFSet) (f : ZFSet),
    ~ isCouple f ->
    projRec base f
      = (e ← couples f ;; {| ⟨ projRec base (pfst e) , projRec base (psnd e) ⟩ |}).
Proof.
  intros base f Hf. rewrite projRec_unfold. unfold proj_step.
  apply isCoupleb_false in Hf. rewrite Hf.
  apply (image_repr_eq_iUnion
             (fun e => ⟨ projRec base (pfst e) , projRec base (psnd e) ⟩)).
Qed.

(** ** [FST] and [SND]. *)

Definition FST : ZFSet -> ZFSet := projRec pfst.
Definition SND : ZFSet -> ZFSet := projRec psnd.

(* Base cases. *)
Lemma FST_Couple : forall x y : ZFSet, FST (⟨ x , y ⟩) = x.
Proof. intros x y. unfold FST. rewrite projRec_Couple. apply pfst_Couple. Qed.

Lemma SND_Couple : forall x y : ZFSet, SND (⟨ x , y ⟩) = y.
Proof. intros x y. unfold SND. rewrite projRec_Couple. apply psnd_Couple. Qed.

(* Relational unfolding (the recursive clause). *)
Lemma FST_rel : forall f : ZFSet,
  ~ isCouple f ->
  FST f = (e ← couples f ;; {| ⟨ FST (pfst e) , FST (psnd e) ⟩ |}).
Proof. intros f Hf. unfold FST. apply projRec_rel. exact Hf. Qed.

Lemma SND_rel : forall f : ZFSet,
  ~ isCouple f ->
  SND f = (e ← couples f ;; {| ⟨ SND (pfst e) , SND (psnd e) ⟩ |}).
Proof. intros f Hf. unfold SND. apply projRec_rel. exact Hf. Qed.

(* ================================================================== *)
(** ** [FST] / [SND] of a functional graph. *)
(* ================================================================== *)

(** A functional graph [{⟨a, g a⟩ : a ∈ S}] is a set, hence never a couple. *)
Lemma graph_not_couple : forall S g,
  ~ isCouple (iUnion S (fun a => {| ⟨ a, g a ⟩ |})).
Proof.
  intros S g Hc. apply isCouple_IsPair in Hc.
  pose proof (IsSet_iUnion S (fun a => {| ⟨ a, g a ⟩ |})) as Hs.
  revert Hc Hs. pattern (iUnion S (fun a => {| ⟨ a, g a ⟩ |})).
  apply ZFSet_ind1. intros e. rewrite IsPair_mk, IsSet_mk.
  destruct e; simpl; intros; contradiction.
Qed.

(** The couple members of a graph are all of it. *)
Lemma couples_graph : forall S g,
  couples (iUnion S (fun a => {| ⟨ a, g a ⟩ |})) = iUnion S (fun a => {| ⟨ a, g a ⟩ |}).
Proof.
  intros S g. apply set_ext.
  - unfold couples. apply Comp_Inc.
  - inc_def. intros e He. apply In_couples. split; [ exact He | ].
    apply iUnion_IN in He. destruct He as [a [_ He]]. apply IN_Sing_EQ in He.
    exists a, (g a). exact He.
Qed.

(** Its first projection [{⟨FST a, FST (g a)⟩ : a ∈ S}] is single-valued when
    [g] respects [FST] (so the value is determined by the key). *)
Lemma FST_graph_isFunction : forall S g,
  (forall a b, In a S -> In b S -> FST a = FST b -> FST (g a) = FST (g b)) ->
  isFunction (FST (iUnion S (fun a => {| ⟨ a, g a ⟩ |}))).
Proof.
  intros S g Hresp c d1 d2 H1 H2.
  rewrite (FST_rel _ (graph_not_couple S g)), couples_graph in H1.
  rewrite (FST_rel _ (graph_not_couple S g)), couples_graph in H2.
  apply iUnion_IN in H1. destruct H1 as [e1 [He1 H1]]. apply IN_Sing_EQ in H1.
  apply iUnion_IN in H2. destruct H2 as [e2 [He2 H2]]. apply IN_Sing_EQ in H2.
  apply iUnion_IN in He1. destruct He1 as [a1 [Ha1 He1]]. apply IN_Sing_EQ in He1. subst e1.
  apply iUnion_IN in He2. destruct He2 as [a2 [Ha2 He2]]. apply IN_Sing_EQ in He2. subst e2.
  rewrite pfst_Couple, psnd_Couple in H1. rewrite pfst_Couple, psnd_Couple in H2.
  pose proof (Couple_inj_left _ _ _ _ H1) as Hc1. pose proof (Couple_inj_right _ _ _ _ H1) as Hd1.
  pose proof (Couple_inj_left _ _ _ _ H2) as Hc2. pose proof (Couple_inj_right _ _ _ _ H2) as Hd2.
  assert (Heq : FST (g a1) = FST (g a2))
    by (apply Hresp; [ exact Ha1 | exact Ha2 | rewrite <- Hc1, <- Hc2; reflexivity ]).
  congruence.
Qed.

Lemma SND_graph_isFunction : forall S g,
  (forall a b, In a S -> In b S -> SND a = SND b -> SND (g a) = SND (g b)) ->
  isFunction (SND (iUnion S (fun a => {| ⟨ a, g a ⟩ |}))).
Proof.
  intros S g Hresp c d1 d2 H1 H2.
  rewrite (SND_rel _ (graph_not_couple S g)), couples_graph in H1.
  rewrite (SND_rel _ (graph_not_couple S g)), couples_graph in H2.
  apply iUnion_IN in H1. destruct H1 as [e1 [He1 H1]]. apply IN_Sing_EQ in H1.
  apply iUnion_IN in H2. destruct H2 as [e2 [He2 H2]]. apply IN_Sing_EQ in H2.
  apply iUnion_IN in He1. destruct He1 as [a1 [Ha1 He1]]. apply IN_Sing_EQ in He1. subst e1.
  apply iUnion_IN in He2. destruct He2 as [a2 [Ha2 He2]]. apply IN_Sing_EQ in He2. subst e2.
  rewrite pfst_Couple, psnd_Couple in H1. rewrite pfst_Couple, psnd_Couple in H2.
  pose proof (Couple_inj_left _ _ _ _ H1) as Hc1. pose proof (Couple_inj_right _ _ _ _ H1) as Hd1.
  pose proof (Couple_inj_left _ _ _ _ H2) as Hc2. pose proof (Couple_inj_right _ _ _ _ H2) as Hd2.
  assert (Heq : SND (g a1) = SND (g a2))
    by (apply Hresp; [ exact Ha1 | exact Ha2 | rewrite <- Hc1, <- Hc2; reflexivity ]).
  congruence.
Qed.

(** Diagonals [diag X = {⟨a,a⟩ : a ∈ X}] are the special case [g = id]. *)
Lemma diag_not_couple : forall X, ~ isCouple (diag X).
Proof. intro X. unfold diag. exact (graph_not_couple X (fun a => a)). Qed.

Lemma FST_diag_isFunction : forall X, isFunction (FST (diag X)).
Proof.
  intro X. unfold diag.
  apply (FST_graph_isFunction X (fun a => a)). intros a b _ _ H. exact H.
Qed.

Lemma SND_diag_isFunction : forall X, isFunction (SND (diag X)).
Proof.
  intro X. unfold diag.
  apply (SND_graph_isFunction X (fun a => a)). intros a b _ _ H. exact H.
Qed.

(* lib/Diagonal.v

   General-purpose lemmas about *diagonal* relations over [ZFSet]: sets of
   pairs all of the form ⟨v,v⟩.  These are pure [ZFSet] facts (no object
   language), factored out of [Timbda.TimSTLC]; the semantics-specific
   results connecting diagonality to a type interpretation live there. *)

Require Import ZFSetFacts.
Require Import ZFNotation.


(** From a diagonal pair [p = ⟨psnd p, psnd p⟩], the two projections
    coincide. *)
Lemma diag_eq p : p = ⟨ psnd p , psnd p ⟩ -> pfst p = psnd p.
Proof.
  intro H. transitivity (pfst ⟨ psnd p , psnd p ⟩).
  - f_equal. exact H.
  - apply pfst_Couple.
Qed.

(** On a graph [h ∈ Pi A B] whose domain [A] and every [B a] are
    diagonal, the two relations obtained by reading off ⟨psnd,pfst⟩ vs.
    ⟨pfst,psnd⟩ of each edge coincide. *)
Lemma sndRel_eq_thdRel (A : ZFSet) (B : ZFSet -> ZFSet) (h : ZFSet) :
  IsDiag A ->
  (forall a, a ∈ A -> IsDiag (B a)) ->
  h ∈ Pi A B ->
  iUnion_pat h (fun ab cd => {| ⟨ psnd ab , pfst cd ⟩ |})
  = iUnion_pat h (fun ab cd => {| ⟨ pfst ab , psnd cd ⟩ |}).
Proof.
  intros HA HB Hh.
  apply In_Pi_inv in Hh. destruct Hh as [Hsub _].
  unfold iUnion_pat. apply iUnion_ext_mem. intros q qIn.
  pose proof (Inc_IN _ _ _ Hsub qIn) as Hq.
  apply IN_Prod_EX in Hq. destruct Hq as [qa [qc [Hqa [Hqc Heq]]]].
  subst q. rewrite pfst_Couple, psnd_Couple.
  (* qa is diagonal: pfst qa = psnd qa *)
  pose proof (diag_eq qa (HA qa Hqa)) as Efa.
  (* qc lives in some B a', which is diagonal *)
  apply iUnion_IN in Hqc. destruct Hqc as [a' [Ha' Hqc]].
  pose proof (diag_eq qc (HB a' Ha' qc Hqc)) as Efc.
  rewrite Efa, Efc. reflexivity.
Qed.

(** On a diagonal relation, the [psnd] projection is injective (the pair
    is determined by it). *)
Lemma diag_psnd_inj (A : ZFSet) :
  IsDiag A ->
  forall ab ab', ab ∈ A -> ab' ∈ A -> psnd ab = psnd ab' -> ab = ab'.
Proof.
  intros HA ab ab' Hab Hab' He.
  rewrite (HA ab Hab), (HA ab' Hab'), He. reflexivity.
Qed.

(** ... and so is [pfst], since on a diagonal pair both projections
    coincide. *)
Lemma diag_pfst_inj (A : ZFSet) :
  IsDiag A ->
  forall ab ab', ab ∈ A -> ab' ∈ A -> pfst ab = pfst ab' -> ab = ab'.
Proof.
  intros HA ab ab' Hab Hab' He.
  apply (diag_psnd_inj A HA); auto.
  rewrite <- (diag_eq ab (HA ab Hab)), <- (diag_eq ab' (HA ab' Hab')).
  exact He.
Qed.

(* ================================================================== *)
(** * The diagonal constructor.

    [diag S] is the identity relation on [S], i.e. the diagonal
    [{⟨a,a⟩ : a ∈ S}].  Only the universe-free facts are here; the
    partial-identity universes built from [diag] belong to the universe
    layer. *)
(* ================================================================== *)


(** The range of a diagonal is its support set. *)
Lemma rng_diag S (HS : IsSet S) : rng (diag S) = S.
Proof.
  apply set_ext; [ inc_def | apply (Inc_intro _ _ HS) ]; intros b Hb.
  - apply rng_elim in Hb. destruct Hb as [a Hab].
    unfold diag in Hab. apply iUnion_IN in Hab. destruct Hab as [c [Hc Hab]].
    apply IN_Sing_EQ in Hab.
    pose proof (Couple_inj_right _ _ _ _ Hab) as Eb. rewrite Eb. exact Hc.
  - unfold diag. apply (rng_intro _ b b).
    apply IN_iUnion with (y := b); [ exact Hb | apply IN_Sing ].
Qed.

(** A diagonal is single-valued: every input is paired with itself only. *)
Lemma isFunction_diag : forall X, isFunction (diag X).
Proof.
  intros X. unfold isFunction. intros a b1 b2 H1 H2. unfold diag in H1, H2.
  apply iUnion_IN in H1. destruct H1 as [y [_ H1]].
  apply iUnion_IN in H2. destruct H2 as [z [_ H2]].
  apply IN_Sing_EQ in H1. apply IN_Sing_EQ in H2.
  pose proof (Couple_inj_left _ _ _ _ H1) as Ea1.
  pose proof (Couple_inj_right _ _ _ _ H1) as Eb1.
  pose proof (Couple_inj_left _ _ _ _ H2) as Ea2.
  pose proof (Couple_inj_right _ _ _ _ H2) as Eb2.
  congruence.
Qed.

(** Monotonicity of [diag]: it preserves [⊆]. *)
Lemma diag_mono S T : S ⊆ T -> diag S ⊆ diag T.
Proof.
  intros HS. inc_def. intros x Hx.
  unfold diag in Hx. apply iUnion_IN in Hx. destruct Hx as [a [Ha Hx]].
  apply IN_Sing_EQ in Hx. rewrite Hx.
  unfold diag. apply IN_iUnion with (y := a); [ exact (Inc_IN _ _ _ HS Ha) | apply IN_Sing ].
Qed.

(* ================================================================== *)
(** * Partial functions and partial identities.

    These are the set-theoretic ingredients of the [Timbda] type machinery:
    [pFun A B] is the partial functions from [A] to [B], and [pIdFun A] the
    partial *identity* functions on [A]. *)
(* ================================================================== *)

(** The partial functions from [A] to [B]: the single-valued
    ([isFunction]) subsets of the product [A × B]. *)

(** The partial *identity* functions on [A]: the subsets of the diagonal
    [diag A].  (A subset of the diagonal is automatically single-valued,
    so no separate [isFunction] side-condition is needed.) *)

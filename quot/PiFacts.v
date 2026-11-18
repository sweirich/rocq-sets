(* PiFacts.v: general ZFSet / Pi lemmas gathered from the timbda
   development (Timbda2, TimSTLC, Parametricity). *)

From Stdlib Require Import FunctionalExtensionality.
Require Import ZFNotation Diagonal ZFSetFacts Projections.

Open Scope zf_scope.

(* -- from Timbda2 -- *)
Definition is_diag (r : ZFSet) : Prop := forall a b, ⟨ a , b ⟩ ∈ r -> a = b.

(** A diagonal relation is single-valued (a function): both [b1] and [b2]
    equal the common source [a].  Used to discharge the [isFunction] filter
    that [eval_lam] / [eval_lamb] now place on the function value. *)
Lemma isFunction_of_diag : forall r : ZFSet, is_diag r -> isFunction r.
Proof.
  intros r Hd a b1 b2 H1 H2.
  pose proof (Hd a b1 H1) as E1. pose proof (Hd a b2 H2) as E2. congruence.
Qed.

(** A *constant* graph [{⟨k s, c⟩ : s ∈ A}] (every edge has target [c]) is
    single-valued. *)
Lemma isFunction_const_graph (A : ZFSet) (k : ZFSet -> ZFSet) (c : ZFSet) :
  isFunction (s ← A ;; {| ⟨ k s , c ⟩ |}).
Proof.
  intros a b1 b2 H1 H2.
  apply iUnion_IN in H1. destruct H1 as [s1 [_ H1]]. apply IN_Sing_EQ in H1.
  apply iUnion_IN in H2. destruct H2 as [s2 [_ H2]]. apply IN_Sing_EQ in H2.
  pose proof (Couple_inj_right _ _ _ _ H1) as E1.
  pose proof (Couple_inj_right _ _ _ _ H2) as E2. congruence.
Qed.

(** A graph [{⟨k s, v s⟩ : s ∈ A}] is single-valued whenever the key [k s]
    determines the value [v s]. *)
Lemma isFunction_graph (A : ZFSet) (k v : ZFSet -> ZFSet) :
  (forall s s', s ∈ A -> s' ∈ A -> k s = k s' -> v s = v s') ->
  isFunction (s ← A ;; {| ⟨ k s , v s ⟩ |}).
Proof.
  intros Hdet a b1 b2 H1 H2.
  apply iUnion_IN in H1. destruct H1 as [s1 [Hs1 H1]]. apply IN_Sing_EQ in H1.
  apply iUnion_IN in H2. destruct H2 as [s2 [Hs2 H2]]. apply IN_Sing_EQ in H2.
  pose proof (Couple_inj_left  _ _ _ _ H1) as A1.
  pose proof (Couple_inj_right _ _ _ _ H1) as B1.
  pose proof (Couple_inj_left  _ _ _ _ H2) as A2.
  pose proof (Couple_inj_right _ _ _ _ H2) as B2.
  assert (k s1 = k s2) by congruence.
  pose proof (Hdet s1 s2 Hs1 Hs2 H) as Hv. congruence.
Qed.

(* -- from TimSTLC -- *)
Lemma proj_isFunction (A : ZFSet) (B : ZFSet -> ZFSet) (h : ZFSet)
      (kf vf : ZFSet -> ZFSet) :
  (forall ab ab', ab ∈ A -> ab' ∈ A -> kf ab = kf ab' -> ab = ab') ->
  h ∈ Pi A B ->
  isFunction (iUnion_pat h (fun ab cd => {| ⟨ kf ab , vf cd ⟩ |})).
Proof.
  intros Hkf Hh a b1 b2 H1 H2.
  apply In_Pi_inv in Hh. destruct Hh as [Hsub [_ Hfn]].
  unfold iUnion_pat in H1, H2.
  apply iUnion_IN in H1. destruct H1 as [q1 [Hq1 He1]].
  apply iUnion_IN in H2. destruct H2 as [q2 [Hq2 He2]].
  apply IN_Sing_EQ in He1, He2.
  pose proof (Inc_IN _ _ _ Hsub Hq1) as Hp1.
  pose proof (Inc_IN _ _ _ Hsub Hq2) as Hp2.
  apply IN_Prod_EX in Hp1. destruct Hp1 as [qa1 [qc1 [Hqa1 [_ Eq1]]]].
  apply IN_Prod_EX in Hp2. destruct Hp2 as [qa2 [qc2 [Hqa2 [_ Eq2]]]].
  subst q1 q2. rewrite !pfst_Couple, !psnd_Couple in He1, He2.
  pose proof (Couple_inj_left _ _ _ _ He1) as Ea1.
  pose proof (Couple_inj_right _ _ _ _ He1) as Eb1.
  pose proof (Couple_inj_left _ _ _ _ He2) as Ea2.
  pose proof (Couple_inj_right _ _ _ _ He2) as Eb2.
  assert (Eqa : qa1 = qa2).
  { apply (Hkf qa1 qa2 Hqa1 Hqa2). rewrite <- Ea1, <- Ea2. reflexivity. }
  subst qa2.
  assert (Eqc : qc1 = qc2) by exact (Hfn qa1 qc1 qc2 Hq1 Hq2).
  subst qc2. rewrite Eb1, Eb2. reflexivity.
Qed.

(** The relational application packed into the [Eapp] arm: iterating a
    function [G] and keeping the diagonal of the output whenever the input
    matches [a1].  When [G] is a single-valued relation containing the
    edge [⟨a1,b0⟩], exactly that edge survives, leaving [{|⟨b0,b0⟩|}]. *)
Lemma app_iUnion_Sing (G a1 b0 : ZFSet) :
  isFunction G ->
  (forall q, q ∈ G -> q = ⟨ pfst q , psnd q ⟩) ->
  ⟨ a1 , b0 ⟩ ∈ G ->
  ('⟨ a , b ⟩ ← G ;; ⦃ _ ∈ {| ⟨ b , b ⟩ |} | a = a1 ⦄) = {| ⟨ b0 , b0 ⟩ |}.
Proof.
  intros HF Hrel Hedge. unfold iUnion_pat. apply set_ext.
  - apply iUnion_Inc. intros q Hq.
    inc_def. intros w Hw.
    pose proof (Inc_IN _ _ _ (Comp_Inc _ _) Hw) as HwS.
    apply In_Comp_P in Hw.
    apply IN_Sing_EQ in HwS. subst w.
    (* the kept edge has key [a1], so by functionality its value is [b0] *)
    pose proof (Hrel q Hq) as Hqc.
    assert (Hq' : ⟨ a1 , psnd q ⟩ ∈ G) by (rewrite <- Hw, <- Hqc; exact Hq).
    pose proof (HF a1 (psnd q) b0 Hq' Hedge) as Eb. rewrite Eb. apply IN_Sing.
  - apply Sing_Inc_IN.
    apply IN_iUnion with (y := ⟨ a1 , b0 ⟩); [ exact Hedge | ].
    rewrite pfst_Couple, psnd_Couple.
    apply In_P_Comp; [ apply IN_Sing | reflexivity ].
Qed.

(* -- from Parametricity -- *)
Lemma Eimg_Pi_Sing : forall x (B : ZFSet -> ZFSet), IsSet (B x) ->
  (f ← Pi (Sing x) B ;; rng f) = B x.
Proof.
  intros x B HB. apply set_ext; [ inc_def | apply (Inc_intro _ _ HB) ]; intros z Hz.
  - apply iUnion_IN in Hz. destruct Hz as [f [Hf Hz]].
    apply rng_elim in Hz. destruct Hz as [a Ha].
    destruct (In_Pi_inv _ _ _ Hf) as [Hsub _].
    pose proof (Inc_IN _ _ _ Hsub Ha) as Hap.
    apply Couple_Prod_IN in Hap. destruct Hap as [Hax _].
    apply IN_Sing_EQ in Hax. subst a.
    exact (Pi_edge_codomain _ _ _ _ _ Hf (IN_Sing x) Ha).
  - apply IN_iUnion with (y := (a ← Sing x ;; {| ⟨ a , z ⟩ |})).
    + apply (iUnion_graph_mem_pi (Sing x) B (fun _ => z)).
      intros a Ha. apply IN_Sing_EQ in Ha. subst a. exact Hz.
    + rewrite (iUnion_Sing_l x (fun a => {| ⟨ a , z ⟩ |}) (IsSet_Sing _)), rng_Sing_Couple. apply IN_Sing.
Qed.

(* [η] for [Pi]: a function equals the graph of its own application. *)
Lemma Pi_eta : forall E B g,
  g ∈ Pi E B -> g = (a ← E ;; {| ⟨ a , applyFun g a ⟩ |}).
Proof.
  intros E B g Hg. apply set_ext; [ apply (Inc_intro _ _ (Pi_IsSet _ _ _ Hg)) | inc_def ]; intros z Hz.
  - destruct (In_Pi_inv _ _ _ Hg) as [Hsub _].
    pose proof (Inc_IN _ _ _ Hsub Hz) as Hz'.
    apply IN_Prod_EX in Hz'. destruct Hz' as [a [b [Ha [_ Ezab]]]]. subst z.
    rewrite (pi_edge_value _ _ _ _ _ Hg Hz).
    apply IN_iUnion with (y := a); [ exact Ha | apply IN_Sing ].
  - apply iUnion_IN in Hz. destruct Hz as [a [Ha Hz]]. apply IN_Sing_EQ in Hz. subst z.
    exact (pi_value_edge _ _ _ _ Hg Ha).
Qed.

(* Reprojecting a function on the relabelled domain [{⟨x,a⟩ : a∈E}] is the
   graph of its application at [⟨x,·⟩]. *)
Lemma reproject_graph : forall x E (G : ZFSet -> ZFSet) h,
  h ∈ Pi (a ← E ;; {| ⟨ x , a ⟩ |}) G ->
  ('⟨ p, b ⟩ ← h ;; {| ⟨ psnd p, b ⟩ |})
  = (a ← E ;; {| ⟨ a , applyFun h ⟨ x , a ⟩ ⟩ |}).
Proof.
  intros x E G h Hh.
  destruct (In_Pi_inv _ _ _ Hh) as [Hsub _].
  apply set_ext; inc_def; intros z Hz.
  - unfold iUnion_pat in Hz. apply iUnion_IN in Hz. destruct Hz as [el [Hel Hz]].
    apply IN_Sing_EQ in Hz. subst z.
    pose proof (Inc_IN _ _ _ Hsub Hel) as Hel'.
    apply IN_Prod_EX in Hel'. destruct Hel' as [p [b [Hp [_ Eel]]]]. subst el.
    rewrite pfst_Couple, psnd_Couple.
    apply iUnion_IN in Hp. destruct Hp as [a [Ha Hp]]. apply IN_Sing_EQ in Hp. subst p.
    rewrite psnd_Couple.
    pose proof (pi_edge_value _ _ _ _ _ Hh Hel) as Eb. rewrite Eb.
    apply IN_iUnion with (y := a); [ exact Ha | apply IN_Sing ].
  - apply iUnion_IN in Hz. destruct Hz as [a [Ha Hz]]. apply IN_Sing_EQ in Hz. subst z.
    assert (Hxa : ⟨ x , a ⟩ ∈ (a0 ← E ;; {| ⟨ x , a0 ⟩ |}))
      by (apply IN_iUnion with (y := a); [ exact Ha | apply IN_Sing ]).
    pose proof (pi_value_edge _ _ _ _ Hh Hxa) as Hedge.
    unfold iUnion_pat. apply IN_iUnion with (y := ⟨ ⟨ x , a ⟩ , applyFun h ⟨ x , a ⟩ ⟩).
    + exact Hedge.
    + rewrite pfst_Couple, psnd_Couple, psnd_Couple. apply IN_Sing.
Qed.

Lemma reproject_Pi : forall x E (G : ZFSet -> ZFSet),
  (h ← Pi (a ← E ;; {| ⟨ x , a ⟩ |}) G
     ;; {| '⟨ p, b ⟩ ← h ;; {| ⟨ psnd p, b ⟩ |} |})
  = Pi E (fun a => G ⟨ x , a ⟩).
Proof.
  intros x E G. apply set_ext; inc_def; intros X HX.
  - apply iUnion_IN in HX. destruct HX as [h [Hh HX]]. apply IN_Sing_EQ in HX. subst X.
    rewrite (reproject_graph x E G h Hh).
    apply (iUnion_graph_mem_pi E (fun a => G ⟨ x , a ⟩)
             (fun a => applyFun h ⟨ x , a ⟩)).
    intros a Ha.
    assert (Hxa : ⟨ x , a ⟩ ∈ (a0 ← E ;; {| ⟨ x , a0 ⟩ |}))
      by (apply IN_iUnion with (y := a); [ exact Ha | apply IN_Sing ]).
    exact (applyFun_mem_of_pi _ G h ⟨ x , a ⟩ Hh Hxa).
  - (* given g, build its relabelling [h0] over the [⟨x,·⟩] domain *)
    pose (h0 := a ← E ;; {| ⟨ ⟨ x , a ⟩ , applyFun X a ⟩ |}).
    assert (Hh0 : h0 ∈ Pi (a ← E ;; {| ⟨ x , a ⟩ |}) G).
    { unfold Pi. apply In_P_Comp.
      - apply Inc_IN_Power; [ typeclasses eauto | ]. inc_def. intros z Hz.
        unfold h0 in Hz. apply iUnion_IN in Hz. destruct Hz as [a [Ha Hz]].
        apply IN_Sing_EQ in Hz. subst z.
        apply Couple_IN_Prod.
        + apply IN_iUnion with (y := a); [ exact Ha | apply IN_Sing ].
        + apply IN_iUnion with (y := ⟨ x , a ⟩).
          * apply IN_iUnion with (y := a); [ exact Ha | apply IN_Sing ].
          * exact (applyFun_mem_of_pi _ _ X a HX Ha).
      - split.
        + intros p Hp. apply iUnion_IN in Hp. destruct Hp as [a [Ha Ep]].
          apply IN_Sing_EQ in Ep. subst p.
          exists (applyFun X a). split.
          * exact (applyFun_mem_of_pi _ _ X a HX Ha).
          * unfold h0. apply IN_iUnion with (y := a); [ exact Ha | apply IN_Sing ].
        + intros p b1 b2 H1 H2.
          unfold h0 in H1, H2.
          apply iUnion_IN in H1. destruct H1 as [a1 [Ha1 E1]]. apply IN_Sing_EQ in E1.
          apply iUnion_IN in H2. destruct H2 as [a2 [Ha2 E2]]. apply IN_Sing_EQ in E2.
          pose proof (Couple_inj_left _ _ _ _ E1) as Ep1.
          pose proof (Couple_inj_right _ _ _ _ E1) as Eb1.
          pose proof (Couple_inj_left _ _ _ _ E2) as Ep2.
          pose proof (Couple_inj_right _ _ _ _ E2) as Eb2.
          subst b1 b2. rewrite Ep1 in Ep2.
          pose proof (Couple_inj_right _ _ _ _ Ep2) as Ea. rewrite Ea. reflexivity. }
    apply IN_iUnion with (y := h0); [ exact Hh0 | ].
    assert (Eapp : forall a, a ∈ E -> applyFun h0 ⟨ x , a ⟩ = applyFun X a).
    { intros a Ha.
      assert (Hxa : ⟨ x , a ⟩ ∈ (a0 ← E ;; {| ⟨ x , a0 ⟩ |}))
        by (apply IN_iUnion with (y := a); [ exact Ha | apply IN_Sing ]).
      pose proof (pi_value_edge _ _ _ _ Hh0 Hxa) as Hedge.
      unfold h0 in Hedge. apply iUnion_IN in Hedge. destruct Hedge as [a' [Ha' Eedge]].
      apply IN_Sing_EQ in Eedge.
      pose proof (Couple_inj_left _ _ _ _ Eedge) as Exa.
      pose proof (Couple_inj_right _ _ _ _ Exa) as Eaa. subst a'.
      pose proof (Couple_inj_right _ _ _ _ Eedge) as Ev. exact Ev. }
    assert (Hgoal : X = ('⟨ p, b ⟩ ← h0 ;; {| ⟨ psnd p, b ⟩ |})).
    { rewrite (reproject_graph x E G h0 Hh0).
      rewrite (Pi_eta E (fun a => G ⟨ x , a ⟩) X HX).
      apply (iUnion_ext_mem E (fun a => {| ⟨ a , applyFun X a ⟩ |})
               (fun a => {| ⟨ a , applyFun h0 ⟨ x , a ⟩ ⟩ |})).
      intros a Ha. rewrite (Eapp a Ha). reflexivity. }
    rewrite Hgoal. apply IN_Sing.
Qed.

Lemma Comp_iUnion_Sing (E : ZFSet) (g : ZFSet -> ZFSet) (P : ZFSet -> Prop) :
  (h ← E ;; ⦃ f ∈ {| g h |} | P f ⦄)
  = ⦃ x ∈ (h ← E ;; {| g h |}) | P x ⦄.
Proof.
  apply set_ext; inc_def; intros x Hx.
  - apply iUnion_IN in Hx. destruct Hx as [h [Hh Hx]].
    pose proof (In_Comp_P _ _ _ Hx) as HPx.
    apply (Inc_IN _ _ _ (Comp_Inc _ _)) in Hx. apply IN_Sing_EQ in Hx. subst x.
    apply In_P_Comp; [ apply IN_iUnion with (y := h); [ exact Hh | apply IN_Sing ] | exact HPx ].
  - pose proof (In_Comp_P _ _ _ Hx) as HPx.
    apply (Inc_IN _ _ _ (Comp_Inc _ _)) in Hx.
    apply iUnion_IN in Hx. destruct Hx as [h [Hh Hx]].
    apply IN_Sing_EQ in Hx. subst x.
    apply IN_iUnion with (y := h); [ exact Hh | ].
    apply In_P_Comp; [ apply IN_Sing | exact HPx ].
Qed.


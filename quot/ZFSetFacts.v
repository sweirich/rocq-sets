(** * ZFSetFacts.v — pure ZFSet theory built on the core interface.

    Every lemma below reasons at the [ZFSet] level through the abstract
    interface exported by [ZFSetCore.v], and *states its result in the
    [zf_scope] set notations* of [ZFNotation.v] ([∈], [⊆], [{|·|}],
    [⟨·,·⟩], [∩], [∪], [⋃], [∅], the [·←·;;·] iterators, …).  (Two helpers,
    [BinUnion_eq_Union_Paire] and [BinUnion_Vide_l/r], still touch the [mk]
    representation in their *proofs*; every other proof is
    representation-independent.)

    Contents: the [Pi] / [applyFun] theory, the pure smallness lemmas
    ([small_of_Inc], [BinUnion_small], [Prod_small]), the general-purpose
    facts (intersection, image/range, iterated unions, singleton
    products), and the [zf_reduce] step tactic shared by the three
    interpreters. *)

Require Import ZFSetCore.
Require Import ZFDefs.
Require Import ZFNotation.
From Stdlib Require Import Logic.Epsilon.
From Stdlib Require Import PeanoNat.
Require Import utils.axioms.

(* State and reason in the ZFSet-level notations ([zf_scope]); the
   Ens-level [ens_scope] (opened transitively by the core) is closed so
   the syntax is unambiguous. *)
Close Scope ens_scope.
Open Scope zf_scope.

(* ================================================================== *)
(* The derived set-formers of [ZFDefs] produce sets: instances of the
   sort class [IsSet], so that the sortedness premises of the core lemmas
   ([Inc_def], [Union_Sing], [Inc_IN_Power], …) resolve automatically. *)
(* ================================================================== *)

#[global] Instance IsSet_BinUnion (E E' : ZFSet) : IsSet (BinUnion E E').
Proof. unfold BinUnion. apply IsSet_Union. Qed.

#[global] Instance IsSet_BinInter (A B : ZFSet) : IsSet (BinInter A B).
Proof. unfold BinInter. apply IsSet_Comp. Qed.

#[global] Instance IsSet_iUnion_pat (E : ZFSet) (F : ZFSet -> ZFSet -> ZFSet) : IsSet (iUnion_pat E F).
Proof. unfold iUnion_pat. apply IsSet_iUnion. Qed.

#[global] Instance IsSet_iUnion_pat3 (E : ZFSet) (F : ZFSet -> ZFSet -> ZFSet -> ZFSet) : IsSet (iUnion_pat3 E F).
Proof. unfold iUnion_pat3. apply IsSet_iUnion. Qed.

#[global] Instance IsSet_dom (r : ZFSet) : IsSet (dom r).
Proof. unfold dom. apply IsSet_Comp. Qed.

#[global] Instance IsSet_rng (r : ZFSet) : IsSet (rng r).
Proof. unfold rng. apply IsSet_Comp. Qed.

#[global] Instance IsSet_image (r S : ZFSet) : IsSet (image r S).
Proof. unfold image. apply IsSet_Comp. Qed.

#[global] Instance IsSet_natId : IsSet natId.
Proof. unfold natId. apply IsSet_iUnion. Qed.

#[global] Instance IsSet_Pi (A : ZFSet) (B : ZFSet -> ZFSet) : IsSet (Pi A B).
Proof. unfold Pi. apply IsSet_Comp. Qed.

#[global] Instance IsSet_Sig (A : ZFSet) (B : ZFSet -> ZFSet) : IsSet (Sig A B).
Proof. unfold Sig. apply IsSet_iUnion. Qed.

#[global] Instance IsSet_ParPi (A : ZFSet) (B : ZFSet -> ZFSet) : IsSet (ParPi A B).
Proof. unfold ParPi. apply IsSet_Comp. Qed.

#[global] Instance IsSet_diag (S : ZFSet) : IsSet (diag S).
Proof. unfold diag. apply IsSet_iUnion. Qed.

#[global] Instance IsSet_pFun (A B : ZFSet) : IsSet (pFun A B).
Proof. unfold pFun. apply IsSet_Comp. Qed.

#[global] Instance IsSet_pIdFun (A : ZFSet) : IsSet (pIdFun A).
Proof. unfold pIdFun. apply IsSet_Power. Qed.

(** A member of a function space is a set. *)
Lemma Pi_IsSet : forall (A : ZFSet) (B : ZFSet -> ZFSet) (f : ZFSet), f ∈ Pi A B -> IsSet f.
Proof.
  intros A B f Hf. unfold Pi in Hf.
  apply (Inc_IN _ _ _ (Comp_Inc _ _)) in Hf. apply IN_Power_Inc in Hf.
  exact (Inc_IsSet _ _ Hf (IsSet_Prod _ _)).
Qed.

(* ================================================================== *)
(** * Function application: the edge lemma. *)
(* ================================================================== *)

(** [applyFun f v] is the value of the edge over [v] whenever [f] is
    single-valued there. *)
Lemma applyFun_edge : forall f v b : ZFSet,
  isFunction f -> In (Couple v b) f -> applyFun f v = b.
Proof.
  intros f v b Hf Hvb. unfold applyFun.
  apply (Hf v); [ | exact Hvb ].
  apply (epsilon_spec (inhabits Empty) (fun b' => In (Couple v b') f)).
  exists b. exact Hvb.
Qed.

Lemma theOf_Sing : forall b : ZFSet, theOf (Sing b) = b.
Proof.
  intro b. unfold theOf. apply IN_Sing_EQ.
  apply (epsilon_spec (inhabits Empty) (fun b' => In b' (Sing b))).
  exists b. apply IN_Sing.
Qed.

(* ================================================================== *)
(* Theory of the derived definitions now living in [zf/quot/ZFDefs.v]
   ([BinUnion], [is_subsingleton], [is_nonempty], [dom], [rng], [image],
   [proj1/2/3], [applyFun], [natId]), relocated here from [ZFSetCore.v]
   and reproved at the [ZFSet] level (elims fall out of [In_Comp_P];
   intros use [IN_iUnion] over the couple projections). *)
(* ================================================================== *)

(* ----- BinUnion ----- *)

Lemma BinUnion_mk e f : BinUnion (mk e) (mk f) = mk (EnsDefs.BinUnion e f).
Proof. unfold BinUnion. rewrite Paire_mk, Union_mk. reflexivity. Qed.

Lemma BinUnion_Vide_l : forall (E : ZFSet) (H : IsSet E), BinUnion Empty E = E.
Proof.
  intro E. pattern E; apply quot_ind. intros e H.
  rewrite IsSet_mk in H.
  unfold Empty. rewrite BinUnion_mk.
  apply mk_eq, EnsLib.BinUnion_Vide_l. exact H.
Qed.

Lemma BinUnion_Vide_r : forall (E : ZFSet) (H : IsSet E), BinUnion E Empty = E.
Proof.
  intro E. pattern E; apply quot_ind. intros e H.
  rewrite IsSet_mk in H.
  unfold Empty. rewrite BinUnion_mk.
  apply mk_eq, EnsLib.BinUnion_Vide_r. exact H.
Qed.

Lemma empty_union_empty : BinUnion Empty Empty = Empty.
Proof. apply (BinUnion_Vide_l Empty _). Qed.

Lemma IN_BinUnion_l :
  forall x E E' : ZFSet, In x E -> In x (BinUnion E E').
Proof.
  intros x E E' H. unfold BinUnion.
  apply (IN_Union _ E); [ apply IN_Paire_left | exact H ].
Qed.

Lemma IN_BinUnion_r :
  forall x E E' : ZFSet, In x E' -> In x (BinUnion E E').
Proof.
  intros x E E' H. unfold BinUnion.
  apply (IN_Union _ E'); [ apply IN_Paire_right | exact H ].
Qed.

Lemma BinUnion_IN :
  forall x E E' : ZFSet,
  In x (BinUnion E E') -> In x E \/ In x E'.
Proof.
  intros x E E'.
  pattern x; apply quot_ind. intros ex.
  pattern E; apply quot_ind. intros eE.
  pattern E'; apply quot_ind. intros eE'.
  rewrite BinUnion_mk.
  unfold mk. rewrite !In_mk. apply EnsLib.BinUnion_IN.
Qed.

(** The empty set is the bottom of the inclusion order. *)
Lemma Empty_Inc (X : ZFSet) : Empty ⊆ X.
Proof. inc_def; intros x Hx; destruct (not_In_Empty _ Hx). Qed.

(** Binary union is a commutative, associative, idempotent operation. *)
Lemma BinUnion_comm (A B : ZFSet) : A ∪ B = B ∪ A.
Proof.
  apply set_ext; inc_def; intros x Hx; apply BinUnion_IN in Hx;
    (destruct Hx as [H|H];
      [ apply IN_BinUnion_r; exact H | apply IN_BinUnion_l; exact H ]).
Qed.

Lemma BinUnion_assoc (A B C : ZFSet) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof.
  apply set_ext; inc_def; intros x Hx.
  - apply BinUnion_IN in Hx. destruct Hx as [H|H].
    + apply BinUnion_IN in H. destruct H as [H|H].
      * apply IN_BinUnion_l; exact H.
      * apply IN_BinUnion_r, IN_BinUnion_l; exact H.
    + apply IN_BinUnion_r, IN_BinUnion_r; exact H.
  - apply BinUnion_IN in Hx. destruct Hx as [H|H].
    + apply IN_BinUnion_l, IN_BinUnion_l; exact H.
    + apply BinUnion_IN in H. destruct H as [H|H].
      * apply IN_BinUnion_l, IN_BinUnion_r; exact H.
      * apply IN_BinUnion_r; exact H.
Qed.

Lemma BinUnion_idem (A : ZFSet) (HA : IsSet A) : A ∪ A = A.
Proof.
  apply set_ext; [ inc_def | apply (Inc_intro _ _ HA) ]; intros x Hx.
  - apply BinUnion_IN in Hx. destruct Hx; assumption.
  - apply IN_BinUnion_l; exact Hx.
Qed.

(* ----- subsingleton / nonempty ----- *)

Lemma Sing_is_subsingleton :
  forall a : ZFSet, is_subsingleton (Sing a).
Proof.
  intros a y z Hy Hz.
  rewrite (IN_Sing_EQ _ _ Hy), (IN_Sing_EQ _ _ Hz).
  reflexivity.
Qed.

Lemma is_nonempty_Sing : forall E : ZFSet, is_nonempty (Sing E).
Proof. intro E. exists E. apply IN_Sing. Qed.

Lemma not_nonempty_Vide : ~ is_nonempty Empty.
Proof.
  intros [y Hy].
  pattern y in Hy; revert Hy; pattern y; apply quot_ind.
  intros e HIN.
  change Empty with (mk zf.zfc.Axioms.Vide) in HIN.
  rewrite In_mk in HIN.
  elim (zf.zfc.Axioms.Vide_est_vide _ HIN).
Qed.

(* ----- domain / range / image ----- *)

Lemma IN_dom : forall a b f : ZFSet, In (Couple a b) f -> In a (dom f).
Proof.
  intros a b f H. unfold dom. apply In_P_Comp.
  2: { exists b. exact H. }
  apply IN_iUnion with (y := Couple a b); [ exact H | ].
  rewrite pfst_Couple. apply IN_Sing.
Qed.

Lemma dom_elim :
  forall f a : ZFSet, In a (dom f) -> exists b : ZFSet, In (Couple a b) f.
Proof. intros f a H. unfold dom in H. exact (In_Comp_P _ _ _ H). Qed.

Lemma rng_intro :
  forall r a b : ZFSet,
  In (Couple a b) r -> In b (rng r).
Proof.
  intros r a b H. unfold rng. apply In_P_Comp.
  2: { exists a. exact H. }
  apply IN_iUnion with (y := Couple a b); [ exact H | ].
  rewrite psnd_Couple. apply IN_Sing.
Qed.

Lemma rng_elim :
  forall r b : ZFSet,
  In b (rng r) -> exists a : ZFSet, In (Couple a b) r.
Proof. intros r b H. unfold rng in H. exact (In_Comp_P _ _ _ H). Qed.

(** The range of the empty relation is empty, and the diagonal of a non-set is
    empty. *)
Lemma rng_Empty : rng Empty = Empty.
Proof.
  apply all_empty_eq_Empty; [ typeclasses eauto | ].
  intros y Hy. apply rng_elim in Hy. destruct Hy as [a Ha]. exact (not_In_Empty _ Ha).
Qed.

Lemma diag_not_set : forall S : ZFSet, ~ IsSet S -> diag S = Empty.
Proof. intros S H. unfold diag. apply iUnion_not_set. exact H. Qed.

Lemma image_intro :
  forall r S b a : ZFSet,
  In a S ->
  In (Couple a b) r ->
  In b (image r S).
Proof.
  intros r S b a HaS Hab. unfold image. apply In_P_Comp.
  - exact (rng_intro r a b Hab).
  - exists a. split; assumption.
Qed.

Lemma image_elim :
  forall r S b : ZFSet,
  In b (image r S) ->
  exists a : ZFSet, In a S /\ In (Couple a b) r.
Proof. intros r S b H. unfold image in H. exact (In_Comp_P _ _ _ H). Qed.

Lemma image_Sing_Inc r a B :
  (forall b, In (Couple a b) r -> In b B) -> Inc (image r (Sing a)) B.
Proof.
  intro h. inc_def. intros b Hb.
  apply image_elim in Hb. destruct Hb as [a' [Ha' Hab]].
  apply IN_Sing_EQ in Ha'. subst a'. exact (h b Hab).
Qed.

(* ----- triple projections ----- *)

Lemma proj1_triple :
  forall a b c : ZFSet, proj1 (Couple a (Couple b c)) = a.
Proof. intros; apply pfst_Couple. Qed.

Lemma proj2_triple :
  forall a b c : ZFSet, proj2 (Couple a (Couple b c)) = b.
Proof.
  intros a b c. unfold proj2.
  rewrite psnd_Couple. apply pfst_Couple.
Qed.

Lemma proj3_triple :
  forall a b c : ZFSet, proj3 (Couple a (Couple b c)) = c.
Proof.
  intros a b c. unfold proj3.
  rewrite psnd_Couple. apply psnd_Couple.
Qed.

(* ----- the identity relation [natId] on [Omega] ----- *)

Lemma pair_self_mem_natId :
  forall n : nat, In (Couple (natZ n) (natZ n)) natId.
Proof.
  intro n. unfold natId.
  apply IN_iUnion with (y := natZ n);
    [ apply natZ_mem_omega | apply IN_Sing ].
Qed.

Lemma IN_natId_EXType :
  forall p : ZFSet,
  In p natId ->
  exists n : nat, p = Couple (natZ n) (natZ n).
Proof.
  intros p H. unfold natId in H.
  apply iUnion_IN in H. destruct H as [y [Hy Hp]].
  apply In_omega in Hy. destruct Hy as [n <-].
  apply IN_Sing_EQ in Hp. exists n. exact Hp.
Qed.

Lemma natId_pair_diagonal :
  forall a b : ZFSet, In (Couple a b) natId -> a = b.
Proof.
  intros a b H. apply IN_natId_EXType in H. destruct H as [n Hn].
  pose proof (Couple_inj_left _ _ _ _ Hn) as Ha.
  pose proof (Couple_inj_right _ _ _ _ Hn) as Hb.
  rewrite Ha, Hb. reflexivity.
Qed.

Lemma natId_diagonal :
  forall p : ZFSet, In p natId -> pfst p = psnd p.
Proof.
  intros p H. apply IN_natId_EXType in H. destruct H as [n Hn].
  rewrite Hn, pfst_Couple, psnd_Couple. reflexivity.
Qed.

Lemma rng_natId : rng natId = Omega.
Proof.
  eapply set_ext; inc_def.
  - intros x xIn.
    apply rng_elim in xIn. destruct xIn as [y xIn].
    apply IN_natId_EXType in xIn. destruct xIn as [n EQ].
    apply Couple_inj_right in EQ. rewrite EQ. eapply natZ_mem_omega.
  - intros x xIn.
    apply In_omega in xIn. destruct xIn as [n <-].
    eapply rng_intro. eapply pair_self_mem_natId.
Qed.

Lemma Sing_nat_Inc_Omega (n : nat) :
  Inc (Sing (natZ n)) (rng natId).
Proof.
  eapply Sing_Inc_IN.
  rewrite rng_natId.
  eapply natZ_mem_omega.
Qed.

(** The set-level natural addition [natZAdd] is commutative — it is
    defined as [Nat (natOfEns a + natOfEns b)], so this reduces to
    [Nat.add_comm]. *)
Lemma natZAdd_comm (a b : ZFSet) : (a + b)%zf = (b + a)%zf.
Proof.
  revert a b. apply ZFSet_ind2. intros ea eb.
  rewrite !natZAdd_mk. unfold EnsNat.natZAdd.
  f_equal. f_equal. apply Nat.add_comm.
Qed.

(* ----- dependent sum [Sig] ----- *)

Lemma Sig_intro A B a b : In a A -> In b (B a) -> In (Couple a b) (Sig A B).
Proof.
  intros Ha Hb. unfold Sig.
  apply IN_iUnion with (y := a); [ exact Ha | ].
  apply IN_iUnion with (y := b); [ exact Hb | apply IN_Sing ].
Qed.

Lemma Sig_elim A B p :
  In p (Sig A B) -> exists a b, In a A /\ In b (B a) /\ p = Couple a b.
Proof.
  unfold Sig. intro H. apply iUnion_IN in H. destruct H as [a [Ha H]].
  apply iUnion_IN in H. destruct H as [b [Hb H]]. apply IN_Sing_EQ in H.
  exists a, b. split; [ exact Ha | split; [ exact Hb | exact H ] ].
Qed.

(* ----- partial function space [ParPi] ----- *)

Lemma ParPi_sub : forall A B g,
  In g (ParPi A B) -> Inc g (Prod A (iUnion A B)).
Proof.
  intros A B g Hg. unfold ParPi in Hg.
  apply (Inc_IN _ _ _ (Comp_Inc _ _)) in Hg. apply IN_Power_Inc in Hg. exact Hg.
Qed.

(* ----- further facts relating the relational operations ----- *)

(** The identity relation on [ω] is the diagonal of [ω]. *)
Lemma natId_diag : natId = diag Omega.
Proof.
  apply set_ext; inc_def; intros z Hz.
  - apply IN_natId_EXType in Hz. destruct Hz as [n Hz]. subst z.
    unfold diag. apply IN_iUnion with (y := natZ n);
      [ apply natZ_mem_omega | apply IN_Sing ].
  - unfold diag in Hz. apply iUnion_IN in Hz. destruct Hz as [a [Ha Hz]].
    apply IN_Sing_EQ in Hz. subst z.
    destruct (In_omega a Ha) as [n Hn]. subst a. apply pair_self_mem_natId.
Qed.

(** Applying the diagonal of [D] to an in-domain point is the identity. *)
Lemma image_diag_app D v : In v D -> image (diag D) (Sing v) = Sing v.
Proof.
  intro Hv. apply set_ext; inc_def; intros z Hz.
  - apply image_elim in Hz. destruct Hz as [a [Ha Hcoup]].
    apply IN_Sing_EQ in Ha. subst a.
    unfold diag in Hcoup. apply iUnion_IN in Hcoup. destruct Hcoup as [w [Hw Hwz]].
    apply IN_Sing_EQ in Hwz.
    pose proof (Couple_inj_left _ _ _ _ Hwz) as E1.
    pose proof (Couple_inj_right _ _ _ _ Hwz) as E2.
    rewrite E2. rewrite <- E1. apply IN_Sing.
  - apply IN_Sing_EQ in Hz. subst z.
    apply image_intro with (a := v); [ apply IN_Sing | ].
    unfold diag. apply IN_iUnion with (y := v); [ exact Hv | apply IN_Sing ].
Qed.

(** The image of a singleton under a single-valued relation is a subsingleton. *)
Lemma image_Sing_subsingleton f v :
  isFunction f -> is_subsingleton (image f (Sing v)).
Proof.
  intros Hfun x x' Hx Hx'.
  apply image_elim in Hx. destruct Hx as [a [Ha Hax]].
  apply image_elim in Hx'. destruct Hx' as [a' [Ha' Hax']].
  apply IN_Sing_EQ in Ha; apply IN_Sing_EQ in Ha'. subst a a'.
  exact (Hfun v x x' Hax Hax').
Qed.

(* ===== Pi / applyFun theory ===== *)

(** Inversion: every [X ∈ Pi A B] is a subset of [A × ⋃B] that is
    total and functional. Packages the [Comp] / [Power] unfolding so
    callers don't have to repeat it. *)
Lemma In_Pi_inv :
  forall (A : ZFSet) (B : ZFSet -> ZFSet) (X : ZFSet),
  X ∈ Pi A B ->
  X ⊆ Prod A (iUnion A B) /\
  (forall a, a ∈ A -> exists b, b ∈ B a /\ ⟨ a , b ⟩ ∈ X) /\
  (forall a b1 b2, ⟨ a , b1 ⟩ ∈ X -> ⟨ a , b2 ⟩ ∈ X -> b1 = b2).
Proof.
  intros A B X HX.
  pose proof HX as HXP. unfold Pi in HXP.
  apply In_Comp_P in HXP. destruct HXP as [Htot Hfn].
  pose proof (Comp_Inc (Power (Prod A (iUnion A B)))
              (fun f =>
                (forall a, In a A -> exists b, In b (B a) /\ In (Couple a b) f)
                /\ (forall a b1 b2,
                      In (Couple a b1) f -> In (Couple a b2) f -> b1 = b2)))
    as Hsub.
  inc_elim Hsub.
  apply Hsub in HX. apply IN_Power_Inc in HX.
  split; [|split]; assumption.
Qed.

Lemma iUnion_graph_mem_pi :
  forall (A : ZFSet) (B : ZFSet -> ZFSet) (g : ZFSet -> ZFSet),
  (forall a : ZFSet, a ∈ A -> g a ∈ B a) ->
  (a ← A ;; {| ⟨ a , g a ⟩ |}) ∈ Pi A B.
Proof.
  intros A B g hg.
  unfold Pi. apply In_P_Comp.
  - apply Inc_IN_Power; [ typeclasses eauto | inc_def ]. intros x Hx.
    destruct (iUnion_IN _ _ _ Hx) as [a [HaA HxSing]].
    apply IN_Sing_EQ in HxSing. subst x.
    apply Couple_IN_Prod; [exact HaA|].
    apply IN_iUnion with a; [exact HaA | apply hg; exact HaA].
  - split.
    + intros a HaA. exists (g a). split.
      * apply hg; exact HaA.
      * apply IN_iUnion with a; [exact HaA | apply IN_Sing].
    + intros a b1 b2 H1 H2.
      destruct (iUnion_IN _ _ _ H1) as [a1 [_ HS1]].
      destruct (iUnion_IN _ _ _ H2) as [a2 [_ HS2]].
      apply IN_Sing_EQ in HS1, HS2.
      assert (Ea1 : a = a1) by exact (Couple_inj_left _ _ _ _ HS1).
      assert (Eb1 : b1 = g a1) by exact (Couple_inj_right _ _ _ _ HS1).
      assert (Ea2 : a = a2) by exact (Couple_inj_left _ _ _ _ HS2).
      assert (Eb2 : b2 = g a2) by exact (Couple_inj_right _ _ _ _ HS2).
      congruence.
Qed.

(** The singleton graph [{|⟨a,b⟩|}] is a member of any [Pi] over the
    singleton domain [{|a|}] whose codomain at [a] contains [b].
    Specializes [iUnion_graph_mem_pi] to a one-point domain. *)
Lemma Sing_Couple_mem_Pi a b C :
  b ∈ C a -> {| ⟨ a , b ⟩ |} ∈ Pi {| a |} C.
Proof.
  intro h.
  rewrite <- (iUnion_Sing_l a (fun a' => Sing (Couple a' b)) (IsSet_Sing _)).
  apply iUnion_graph_mem_pi with (g := fun _ => b).
  intros a' Ha'. apply IN_Sing_EQ in Ha'. subst a'. exact h.
Qed.

(** A [Pi] over a singleton domain and a constant singleton codomain
    is included in the singleton of its unique graph: every function in
    [Pi {|a|} (fun _ => {|b|})] is [{|⟨a,b⟩|}].  The [Inc]-level
    eliminator for this shape, so equality goals against it close by
    [set_ext] without element-chasing. *)
Lemma Pi_Sing_Sing_Inc a b :
  Pi {| a |} (fun _ => {| b |}) ⊆ {| {| ⟨ a , b ⟩ |} |}.
Proof.
  inc_def. intros X HX.
  apply In_Pi_inv in HX. destruct HX as [XPow [Htot _]].
  rewrite iUnion_Sing_l in XPow by typeclasses eauto. rewrite Prod_Sing_Sing in XPow.
  assert (HC : In (Couple a b) X).
  { destruct (Htot a (IN_Sing a)) as [b' [Hb' HC]].
    apply IN_Sing_EQ in Hb'. subst b'. exact HC. }
  assert (HX : X = Sing (Couple a b)).
  { apply set_ext; [exact XPow|].
    inc_def. intros x Hx. apply IN_Sing_EQ in Hx. subst x. exact HC. }
  subst X. apply IN_Sing.
Qed.

Lemma applyFun_mem_of_pi :
  forall (A : ZFSet) (B : ZFSet -> ZFSet) (f v : ZFSet),
  f ∈ Pi A B -> v ∈ A -> applyFun f v ∈ B v.
Proof.
  intros A B f v Hf Hv.
  unfold Pi in Hf. apply In_Comp_P in Hf.
  destruct Hf as [Htotal Hfn].
  destruct (Htotal v Hv) as [b [HbB Hbf]].
  rewrite (applyFun_edge f v b Hfn Hbf). exact HbB.
Qed.

(** The relational image of a function [f ∈ Pi A B] at an in-domain point
    [v] is the singleton of the applied value [{f v}].  This is what makes
    a *relational* application [image f {|v|}] agree with the functional
    [applyFun f v] on in-domain arguments (and yield [∅] off-domain). *)
Lemma image_Sing_of_pi :
  forall (A : ZFSet) (B : ZFSet -> ZFSet) (f v : ZFSet),
  f ∈ Pi A B -> v ∈ A -> image f {| v |} = {| applyFun f v |}.
Proof.
  intros A B f v Hf Hv.
  unfold Pi in Hf. apply In_Comp_P in Hf. destruct Hf as [Htotal Hfn].
  destruct (Htotal v Hv) as [b [HbB Hbf]].
  assert (Himg : image f (Sing v) = Sing b).
  { apply set_ext; inc_def; intros x Hx.
    - destruct (image_elim _ _ _ Hx) as [a [Ha Hax]].
      apply IN_Sing_EQ in Ha. subst a.
      specialize (Hfn v x b Hax Hbf). subst x. apply IN_Sing.
    - apply IN_Sing_EQ in Hx. subst x.
      apply image_intro with v; [apply IN_Sing | exact Hbf]. }
  rewrite Himg, (applyFun_edge f v b Hfn Hbf). reflexivity.
Qed.

(** Applying a λ-graph [{ ⟨a, g a⟩ | a ∈ A }] at an in-domain point [v]
    returns the value [g v].  This is what makes a functional-model [λ]
    (whose denotation is its graph) compute under application; used by the
    [lang/] interpreters' β-soundness. *)
Lemma applyFun_graph A (g : ZFSet -> ZFSet) v :
  v ∈ A -> applyFun (iUnion A (fun a => {| ⟨ a , g a ⟩ |})) v = g v.
Proof.
  intro Hv. apply applyFun_edge.
  - intros a b1 b2 H1 H2.
    apply iUnion_IN in H1. destruct H1 as [a1 [_ H1]]. apply IN_Sing_EQ in H1.
    apply iUnion_IN in H2. destruct H2 as [a2 [_ H2]]. apply IN_Sing_EQ in H2.
    pose proof (Couple_inj_left _ _ _ _ H1) as Ea1.
    pose proof (Couple_inj_right _ _ _ _ H1) as Eb1.
    pose proof (Couple_inj_left _ _ _ _ H2) as Ea2.
    pose proof (Couple_inj_right _ _ _ _ H2) as Eb2.
    subst a1 a2. rewrite Eb1, Eb2. reflexivity.
  - apply IN_iUnion with (y := v); [ exact Hv | apply IN_Sing ].
Qed.

(** In a function [f ∈ Pi A B], an edge [⟨v,w⟩] over an in-domain point
    [v] lands its target in [B v].  (The functional version of
    [applyFun_mem_of_pi], usable when one has the edge directly.) *)
Lemma Pi_edge_codomain :
  forall (A : ZFSet) (B : ZFSet -> ZFSet) (f v w : ZFSet),
  f ∈ Pi A B -> v ∈ A -> ⟨ v , w ⟩ ∈ f -> w ∈ B v.
Proof.
  intros A B f v w Hf Hv Hedge.
  unfold Pi in Hf. apply In_Comp_P in Hf. destruct Hf as [Htotal Hfn].
  destruct (Htotal v Hv) as [b [HbB Hbf]].
  specialize (Hfn v w b Hedge Hbf). subst w. exact HbB.
Qed.

(** In [f ∈ Pi A B], the edge over an in-domain point [a] is exactly
    [⟨a, f a⟩] — the graph contains the applied value (used to validate η). *)
Lemma pi_value_edge A B f a :
  f ∈ Pi A B -> a ∈ A -> ⟨ a , applyFun f a ⟩ ∈ f.
Proof.
  intros Hf Ha.
  destruct (In_Pi_inv A B f Hf) as [_ [Htot Hfn]].
  destruct (Htot a Ha) as [b [_ Hedge]].
  rewrite (applyFun_edge f a b Hfn Hedge). exact Hedge.
Qed.

(** Conversely, every edge's target in [f ∈ Pi A B] is the applied value. *)
Lemma pi_edge_value A B f a b :
  f ∈ Pi A B -> ⟨ a , b ⟩ ∈ f -> b = applyFun f a.
Proof.
  intros Hf Hedge.
  destruct (In_Pi_inv A B f Hf) as [_ [_ Hfn]].
  symmetry. exact (applyFun_edge f a b Hfn Hedge).
Qed.



(* ----- monotonicity of [Pi] in its codomain ----- *)

Lemma Pi_Inc_Codomain A C D :
  (forall x, x ∈ A -> C x ⊆ D x) ->
  Pi A C ⊆ Pi A D.
Proof.
  intros h1. inc_def. intros X XIn.
  pose proof (Pi_IsSet _ _ _ XIn) as HXS.
  apply In_Pi_inv in XIn.
  destruct XIn as [XIn [XdomB XisFun]].
  unfold Pi.
  eapply In_P_Comp.
  - apply Inc_IN_Power; [ typeclasses eauto | ].
    apply (Inc_intro _ _ HXS). intros x xIn.
    pose proof (Inc_elim _ _ XIn x xIn) as xIn'.
    apply IN_Prod_EX in xIn'. destruct xIn' as [b [c [bIn [cIn ->]]]].
    apply Couple_IN_Prod; [ exact bIn | ].
    apply iUnion_IN in cIn. destruct cIn as [a [aIn cIn]].
    apply IN_iUnion with a; [ exact aIn | ].
    exact (Inc_elim _ _ (h1 a aIn) c cIn).
  - split; [ | exact XisFun ].
    intros a aIn. destruct (XdomB a aIn) as [c [cIn pIn]].
    exists c. split; [ exact (Inc_elim _ _ (h1 a aIn) c cIn) | exact pIn ].
Qed.

(** A [Pi] depends on its codomain only at in-domain points, so pointwise
    equality of the codomain sets there suffices for equality of the whole [Pi].
    (Antisymmetric companion of [Pi_Inc_Codomain].) *)
Lemma Pi_ext A (C D : ZFSet -> ZFSet) :
  (forall a, a ∈ A -> C a = D a) -> Pi A C = Pi A D.
Proof.
  intro H. apply set_ext; apply Pi_Inc_Codomain; intros x Hx.
  - rewrite (H x Hx). apply Inc_refl.
  - rewrite (H x Hx). apply Inc_refl.
Qed.

(** Separating a singleton: if the predicate holds at [x] the comprehension is
    the whole singleton, otherwise it is empty.  (The shape relational [lang/SystemT]
    interpreters bottom out in for a [tif]/guard over a single value.) *)
Lemma Comp_Sing_in (x : ZFSet) (P : ZFSet -> Prop) :
  P x -> ⦃ y ∈ {| x |} | P y ⦄ = {| x |}.
Proof.
  intro HP. apply set_ext; inc_def; intros y Hy.
  - apply (Inc_IN _ _ _ (Comp_Inc _ _)) in Hy. exact Hy.
  - apply IN_Sing_EQ in Hy. subst y. apply In_P_Comp; [ apply IN_Sing | exact HP ].
Qed.

Lemma Comp_Sing_out (x : ZFSet) (P : ZFSet -> Prop) :
  ~ P x -> ⦃ y ∈ {| x |} | P y ⦄ = ∅.
Proof.
  intro HP. apply set_ext; inc_def; intros y Hy.
  - pose proof (In_Comp_P _ _ _ Hy) as HPy.
    apply (Inc_IN _ _ _ (Comp_Inc _ _)) in Hy. apply IN_Sing_EQ in Hy. subst y.
    destruct (HP HPy).
  - destruct (not_In_Empty _ Hy).
Qed.

(* ===== general-purpose facts ===== *)

(** Binary union is [⋃ {A, B}]. *)
Lemma BinUnion_eq_Union_Paire : forall A B : ZFSet,
  A ∪ B = ⋃ {| A ; B |}.
Proof.
  intros A B. pattern A; apply quot_ind; intros ea.
  pattern B; apply quot_ind; intros eb.
  rewrite BinUnion_mk, Paire_mk, Union_mk. reflexivity.
Qed.


(* The edge structure of a relation included in a product [A × ⋃B]: every
   member is a couple, and the components of each edge lie in the domain [A]
   and the codomain-union [⋃B] respectively. *)
Lemma sub_Prod_edges : forall A B g,
  g ⊆ Prod A (iUnion A B) ->
  (forall e, e ∈ g -> exists x y, e = ⟨ x , y ⟩) /\
  (forall x y, ⟨ x , y ⟩ ∈ g -> x ∈ A) /\
  (forall x y, ⟨ x , y ⟩ ∈ g -> y ∈ iUnion A B).
Proof.
  intros A B g Hsub. split; [|split].
  - intros e He. apply (Inc_IN _ _ _ Hsub) in He.
    apply IN_Prod_EX in He. destruct He as [a [b [_ [_ He]]]]. exists a, b. exact He.
  - intros x y Hxy. apply (Inc_IN _ _ _ Hsub) in Hxy. apply Couple_Prod_IN in Hxy. tauto.
  - intros x y Hxy. apply (Inc_IN _ _ _ Hsub) in Hxy. apply Couple_Prod_IN in Hxy. tauto.
Qed.


(** *** General-purpose lemmas collected from the Timbda / Lang
    developments.  These are pure [ZFSet] facts (binary intersection,
    image/range of concrete relations, iterated unions, and the
    singleton-product lemmas) with no dependence on any object language. *)

(** **** Binary intersection. *)

Lemma BinInter_Inc_l (A B : ZFSet) : A ∩ B ⊆ A.
Proof. unfold BinInter. apply Comp_Inc. Qed.

Lemma BinInter_Inc_r (A B : ZFSet) : A ∩ B ⊆ B.
Proof.
  inc_def. intros x Hx. unfold BinInter in Hx.
  apply In_Comp_P in Hx. exact Hx.
Qed.

Lemma Inc_BinInter (C A B : ZFSet) (HC : IsSet C) : C ⊆ A -> C ⊆ B -> C ⊆ A ∩ B.
Proof.
  intros H1 H2. apply (Inc_intro _ _ HC). intros x Hx. unfold BinInter.
  apply In_P_Comp.
  - exact (Inc_IN _ _ _ H1 Hx).
  - exact (Inc_IN _ _ _ H2 Hx).
Qed.

Lemma IN_BinInter (x A B : ZFSet) : x ∈ A -> x ∈ B -> x ∈ A ∩ B.
Proof. intros HA HB. unfold BinInter. apply In_P_Comp; assumption. Qed.

Lemma BinInter_IN_l (x A B : ZFSet) : x ∈ A ∩ B -> x ∈ A.
Proof. intro H. exact (Inc_IN _ _ _ (Comp_Inc _ _) H). Qed.

Lemma BinInter_IN_r (x A B : ZFSet) : x ∈ A ∩ B -> x ∈ B.
Proof. intro H. unfold BinInter in H. apply In_Comp_P in H. exact H. Qed.

(** Intersection of a singleton with itself / with a distinct singleton —
    the two shapes produced when [Eequal] is applied to constants. *)
Lemma BinInter_Sing_same : forall a : ZFSet, {| a |} ∩ {| a |} = {| a |}.
Proof.
  intro a. apply set_ext; [ apply BinInter_Inc_l | apply Inc_BinInter; [ typeclasses eauto | apply Inc_refl | apply Inc_refl ] ].
Qed.

Lemma BinInter_Sing_diff :
  forall a b : ZFSet, a <> b -> {| a |} ∩ {| b |} = ∅.
Proof.
  intros a b Hab. apply set_ext; inc_def; intros x Hx.
  - pose proof (BinInter_IN_l _ _ _ Hx) as Ha.
    pose proof (BinInter_IN_r _ _ _ Hx) as Hb.
    apply IN_Sing_EQ in Ha, Hb. subst a. exfalso. apply Hab. exact Hb.
  - destruct (not_In_Empty _ Hx).
Qed.

(** Binary intersection is commutative, associative and idempotent, and
    the empty set is an annihilator. *)
Lemma BinInter_comm (A B : ZFSet) : A ∩ B = B ∩ A.
Proof.
  apply set_ext; inc_def; intros x Hx;
    (apply IN_BinInter;
      [ apply (BinInter_IN_r _ _ _ Hx) | apply (BinInter_IN_l _ _ _ Hx) ]).
Qed.

Lemma BinInter_assoc (A B C : ZFSet) : (A ∩ B) ∩ C = A ∩ (B ∩ C).
Proof.
  apply set_ext; inc_def; intros x Hx.
  - pose proof (BinInter_IN_l _ _ _ Hx) as HAB.
    pose proof (BinInter_IN_r _ _ _ Hx) as HC.
    apply IN_BinInter.
    + apply (BinInter_IN_l _ _ _ HAB).
    + apply IN_BinInter; [ apply (BinInter_IN_r _ _ _ HAB) | exact HC ].
  - pose proof (BinInter_IN_l _ _ _ Hx) as HA.
    pose proof (BinInter_IN_r _ _ _ Hx) as HBC.
    apply IN_BinInter.
    + apply IN_BinInter; [ exact HA | apply (BinInter_IN_l _ _ _ HBC) ].
    + apply (BinInter_IN_r _ _ _ HBC).
Qed.

Lemma BinInter_idem (A : ZFSet) (HA : IsSet A) : A ∩ A = A.
Proof.
  apply set_ext; [ inc_def | apply (Inc_intro _ _ HA) ]; intros x Hx.
  - apply (BinInter_IN_l _ _ _ Hx).
  - apply IN_BinInter; exact Hx.
Qed.

Lemma BinInter_Empty_l (B : ZFSet) : Empty ∩ B = Empty.
Proof.
  apply set_ext; inc_def; intros x Hx.
  - apply (BinInter_IN_l _ _ _ Hx).
  - destruct (not_In_Empty _ Hx).
Qed.

Lemma BinInter_Empty_r (A : ZFSet) : A ∩ Empty = Empty.
Proof.
  apply set_ext; inc_def; intros x Hx.
  - apply (BinInter_IN_r _ _ _ Hx).
  - destruct (not_In_Empty _ Hx).
Qed.

(** Intersection distributes over union. *)
Lemma BinInter_BinUnion_distr_r (A B C : ZFSet) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Proof.
  apply set_ext; inc_def; intros x Hx.
  - pose proof (BinInter_IN_l _ _ _ Hx) as HA.
    pose proof (BinInter_IN_r _ _ _ Hx) as HBC.
    apply BinUnion_IN in HBC. destruct HBC as [HB|HC].
    + apply IN_BinUnion_l, IN_BinInter; assumption.
    + apply IN_BinUnion_r, IN_BinInter; assumption.
  - apply BinUnion_IN in Hx. destruct Hx as [H|H].
    + apply IN_BinInter;
        [ apply (BinInter_IN_l _ _ _ H)
        | apply IN_BinUnion_l; apply (BinInter_IN_r _ _ _ H) ].
    + apply IN_BinInter;
        [ apply (BinInter_IN_l _ _ _ H)
        | apply IN_BinUnion_r; apply (BinInter_IN_r _ _ _ H) ].
Qed.

(** **** Image and range of concrete relations. *)

(** The image of the empty graph is empty. *)
Lemma image_Vide_l (X : ZFSet) : image ∅ X = ∅.
Proof.
  apply set_ext; inc_def; intros y Hy.
  - apply image_elim in Hy. destruct Hy as [a [_ Hab]].
    destruct (not_In_Empty _ Hab).
  - destruct (not_In_Empty _ Hy).
Qed.

(** A one-edge graph applied (relationally) to its key yields the value. *)
Lemma image_Sing_Couple (a b : ZFSet) :
  image {| ⟨ a , b ⟩ |} {| a |} = {| b |}.
Proof.
  apply set_ext; inc_def; intros y Hy.
  - apply image_elim in Hy. destruct Hy as [a' [Ha' Hab]].
    apply IN_Sing_EQ in Ha'. subst a'.
    apply IN_Sing_EQ in Hab. apply Couple_inj_right in Hab. subst y. apply IN_Sing.
  - apply IN_Sing_EQ in Hy. subst y. apply image_intro with a; apply IN_Sing.
Qed.

(** The image of a union of graphs is the union of the images. *)
Lemma image_BinUnion (R S X : ZFSet) :
  image (R ∪ S) X = image R X ∪ image S X.
Proof.
  apply set_ext; inc_def; intros y Hy.
  - apply image_elim in Hy. destruct Hy as [a [HaX Hab]].
    apply BinUnion_IN in Hab. destruct Hab as [Hab | Hab].
    + apply IN_BinUnion_l. apply image_intro with a; assumption.
    + apply IN_BinUnion_r. apply image_intro with a; assumption.
  - apply BinUnion_IN in Hy. destruct Hy as [Hy | Hy].
    + apply image_elim in Hy. destruct Hy as [a [HaX Hab]].
      apply image_intro with a; [ exact HaX | apply IN_BinUnion_l; exact Hab ].
    + apply image_elim in Hy. destruct Hy as [a [HaX Hab]].
      apply image_intro with a; [ exact HaX | apply IN_BinUnion_r; exact Hab ].
Qed.

(** The range of a one-edge graph. *)
Lemma rng_Sing_Couple (a b : ZFSet) : rng {| ⟨ a , b ⟩ |} = {| b |}.
Proof.
  apply set_ext; inc_def; intros y Hy.
  - apply rng_elim in Hy. destruct Hy as [a' Hab].
    apply IN_Sing_EQ in Hab. apply Couple_inj_right in Hab. subst y. apply IN_Sing.
  - apply IN_Sing_EQ in Hy. subst y. apply rng_intro with a. apply IN_Sing.
Qed.

(** **** Iterated unions. *)

(** Subset rule for a double iterated union of singletons: the union is
    included in [T] when [g y z ∈ T] for every pair of elements. *)
Lemma iUnion2_Sing_Inc
  (A B : ZFSet) (g : ZFSet -> ZFSet -> ZFSet) (T : ZFSet) :
  (forall y z, y ∈ A -> z ∈ B -> g y z ∈ T) ->
  (a ← A ;; b ← B ;; {| g a b |}) ⊆ T.
Proof.
  intro h. apply iUnion_Inc. intros y yIn.
  apply iUnion_Inc. intros z zIn.
  apply Sing_Inc_IN. now apply h.
Qed.

(** A union is monotone in its index set. *)
Lemma iUnion_Inc_index (E1 E2 : ZFSet) (F : ZFSet -> ZFSet) :
  E1 ⊆ E2 -> iUnion E1 F ⊆ iUnion E2 F.
Proof.
  intro h. inc_def. intros x xIn.
  apply iUnion_IN in xIn. destruct xIn as [y [yIn xFy]].
  apply IN_iUnion with y; [ exact (Inc_IN _ _ _ h yIn) | exact xFy ].
Qed.

(** A union is unchanged when its body is replaced by a pointwise-equal
    body on the members of the index set. *)
Lemma iUnion_ext_mem (E : ZFSet) (F G : ZFSet -> ZFSet) :
  (forall y, y ∈ E -> F y = G y) -> iUnion E F = iUnion E G.
Proof.
  intro h. apply set_ext; inc_def; intros x xIn;
    apply iUnion_IN in xIn; destruct xIn as [y [yIn xFy]];
    apply IN_iUnion with y; auto.
  - rewrite <- (h y yIn). exact xFy.
  - rewrite (h y yIn). exact xFy.
Qed.

(** A union splits along a union in its index set. *)
Lemma iUnion_BinUnion_index (A B : ZFSet) (F : ZFSet -> ZFSet) :
  iUnion (A ∪ B) F = iUnion A F ∪ iUnion B F.
Proof.
  apply set_ext; inc_def; intros x Hx.
  - apply iUnion_IN in Hx. destruct Hx as [y [Hy Hx]].
    apply BinUnion_IN in Hy. destruct Hy as [Hy|Hy].
    + apply IN_BinUnion_l. apply (IN_iUnion _ _ y); assumption.
    + apply IN_BinUnion_r. apply (IN_iUnion _ _ y); assumption.
  - apply BinUnion_IN in Hx. destruct Hx as [Hx|Hx].
    + apply iUnion_IN in Hx. destruct Hx as [y [Hy Hx]].
      apply (IN_iUnion _ _ y); [ apply IN_BinUnion_l; exact Hy | exact Hx ].
    + apply iUnion_IN in Hx. destruct Hx as [y [Hy Hx]].
      apply (IN_iUnion _ _ y); [ apply IN_BinUnion_r; exact Hy | exact Hx ].
Qed.

(** A union of a family that is empty on every point of its index is
    empty. *)
Lemma iUnion_Empty_pointwise (E : ZFSet) (F : ZFSet -> ZFSet) :
  (forall y, In y E -> F y = Empty) -> iUnion E F = Empty.
Proof.
  intro H. apply set_ext.
  - apply iUnion_Inc. intros y Hy. rewrite (H y Hy). apply Inc_refl.
  - apply Empty_Inc.
Qed.

(** **** Singleton products.

    A [Pi] whose codomain is a singleton at every point is itself a singleton: the
    unique inhabitant is the graph of the choice function [g]. *)
Lemma Pi_Sing (A : ZFSet) (B : ZFSet -> ZFSet) (g : ZFSet -> ZFSet) :
  (forall a, a ∈ A -> B a = {| g a |}) ->
  Pi A B = {| a ← A ;; {| ⟨ a , g a ⟩ |} |}.
Proof.
  intro hB.
  assert (hg : forall a, In a A -> In (g a) (B a)).
  { intros a Ha. rewrite (hB a Ha). apply IN_Sing. }
  apply set_ext.
  - inc_def. intros f Hf.
    assert (Ef : f = iUnion A (fun a => Sing (Couple a (g a)))).
    { pose proof (Pi_IsSet _ _ _ Hf) as HfS.
      apply In_Pi_inv in Hf. destruct Hf as [Hsub [Htot Hfun]].
      apply set_ext.
      - apply (Inc_intro _ _ HfS). intros p Hp.
        pose proof (Inc_IN _ _ _ Hsub Hp) as Hp'.
        apply IN_Prod_EX in Hp'. destruct Hp' as [a [b [Ha [_ Ep]]]].
        subst p.
        destruct (Htot a Ha) as [b' [Hb' Hcoup]].
        rewrite (hB a Ha) in Hb'. apply IN_Sing_EQ in Hb'. subst b'.
        pose proof (Hfun a b (g a) Hp Hcoup) as Eb. subst b.
        apply IN_iUnion with a; [exact Ha | apply IN_Sing].
      - inc_def. intros p Hp.
        apply iUnion_IN in Hp. destruct Hp as [a [Ha HpS]].
        apply IN_Sing_EQ in HpS. subst p.
        destruct (Htot a Ha) as [b' [Hb' Hcoup]].
        rewrite (hB a Ha) in Hb'. apply IN_Sing_EQ in Hb'. subst b'.
        exact Hcoup. }
    rewrite Ef. apply IN_Sing.
  - apply Sing_Inc_IN. apply iUnion_graph_mem_pi. exact hg.
Qed.

(** Existential form: a [Pi] whose codomain is a singleton at every point
    is a singleton (Hilbert choice picks the witness at each point). *)
Lemma Pi_Sing_ex (A : ZFSet) (B : ZFSet -> ZFSet) :
  (forall a, a ∈ A -> exists b, B a = {| b |}) ->
  exists f, Pi A B = {| f |}.
Proof.
  intro h.
  pose (g := fun a => epsilon (inhabits Empty) (fun b => B a = Sing b)).
  exists (iUnion A (fun a => Sing (Couple a (g a)))).
  apply Pi_Sing. intros a Ha.
  unfold g. apply epsilon_spec. apply h. exact Ha.
Qed.


(* ===== Reduction lemmas and the [zf_reduce] tactic =====

   These are the computation rules an interpreter's evaluator bottoms out
   in: iterating over a singleton (in single / pair / triple form),
   integer addition, and the reflexive-unification intersection.  They are
   collected here, with the [zf_reduce] tactic that applies them, so the
   three interpreters share one normalisation engine instead of each
   re-deriving it. *)

(** Iterate a pair-pattern union over a single pair. *)
Lemma iUnion_pat_Sing_Couple :
  forall (a b : ZFSet) (F : ZFSet -> ZFSet -> ZFSet) (H : IsSet (F a b)),
  iUnion_pat {| ⟨ a , b ⟩ |} F = F a b.
Proof.
  intros a b F H. unfold iUnion_pat.
  rewrite (iUnion_Sing_l (Couple a b) (fun p => F (pfst p) (psnd p))).
  - cbv beta. rewrite pfst_Couple, psnd_Couple. reflexivity.
  - cbv beta. rewrite pfst_Couple, psnd_Couple. exact H.
Qed.

(** Iterate a triple-pattern union over a single triple. *)
Lemma iUnion_pat3_Sing :
  forall (r a b : ZFSet) (F : ZFSet -> ZFSet -> ZFSet -> ZFSet) (H : IsSet (F r a b)),
  iUnion_pat3 {| ⟨ r , a , b ⟩ |} F = F r a b.
Proof.
  intros r a b F H. unfold iUnion_pat3.
  rewrite (iUnion_Sing_l (Couple r (Couple a b)) (fun t => F (proj1 t) (proj2 t) (proj3 t))).
  - cbv beta. rewrite proj1_triple, proj2_triple, proj3_triple. reflexivity.
  - cbv beta. rewrite proj1_triple, proj2_triple, proj3_triple. exact H.
Qed.

(** Distinct diagonal pairs / triples — used to show a clashing
    unification denotes [∅] in the pair / triple semantics. *)
Lemma Couple_diag_neq : forall a b : ZFSet, a <> b -> ⟨ a , a ⟩ <> ⟨ b , b ⟩.
Proof. intros a b Hab H. apply Hab. exact (Couple_inj_left _ _ _ _ H). Qed.

Lemma Triple_snd_neq :
  forall env a b : ZFSet, a <> b -> ⟨ env , a , a ⟩ <> ⟨ env , b , b ⟩.
Proof.
  intros env a b Hab H. apply Hab.
  apply Couple_inj_right in H. exact (Couple_inj_left _ _ _ _ H).
Qed.

(** [zf_reduce] normalises a denotation that bottoms out in singleton
    iterations: it discharges single / pair / triple unions over
    singletons, integer additions, the reflexive intersection, and the
    image / range reductions, then renormalises nat additions.  An
    interpreter's step tactic is just [cbn [eval]; zf_reduce; try
    reflexivity] (see [Timbda0.step_eval], [Timbda1.step1],
    [Timbda2.step3]). *)
Ltac zf_reduce :=
  repeat (first
    [ rewrite iUnion_Sing_l by typeclasses eauto
    | rewrite iUnion_pat_Sing_Couple by typeclasses eauto
    | rewrite iUnion_pat3_Sing by typeclasses eauto
    | rewrite iUnion_Vide
    | rewrite BinUnion_Vide_l by typeclasses eauto
    | rewrite BinUnion_Vide_r by typeclasses eauto
    | rewrite natZAdd_natZ
    | rewrite BinInter_Sing_same
    | rewrite image_Vide_l
    | rewrite image_Sing_Couple
    | rewrite image_BinUnion
    | rewrite rng_Sing_Couple
    | rewrite rng_natId
    | rewrite Union_Sing by typeclasses eauto ]; cbn [Nat.add]).

(* Applying a [Pi] to a singleton at which the codomain is a singleton
   (moved here from timbda/Timbda0.v). *)
Lemma app_pi_sing :
  forall (A : ZFSet) (B g : ZFSet -> ZFSet) (v0 w : ZFSet),
  In v0 A ->
  (forall a, In a A -> In (g a) (B a)) ->
  B v0 = Sing w ->
  ( f ← Pi A B ;; v ← Sing v0 ;; image f (Sing v) ) = Sing w.
Proof.
  intros A B g v0 w Hv0 Hg HB.
  assert (Himg : forall f, In f (Pi A B) ->
                 (v ← Sing v0 ;; image f (Sing v)) = Sing w).
  { intros f Hf. rewrite iUnion_Sing_l by typeclasses eauto.
    rewrite (image_Sing_of_pi A B f v0 Hf Hv0).
    pose proof (applyFun_mem_of_pi A B f v0 Hf Hv0) as Hm.
    rewrite HB in Hm. apply IN_Sing_EQ in Hm. rewrite Hm. reflexivity. }
  pose proof (iUnion_graph_mem_pi A B g Hg) as Hwit.
  apply set_ext.
  - apply iUnion_Inc. intros f Hf. rewrite (Himg f Hf). apply Inc_refl.
  - apply Sing_Inc_IN. eapply IN_iUnion.
    + exact Hwit.
    + rewrite (Himg _ Hwit). apply IN_Sing.
Qed.

(* [Comp]-of-singleton when the predicate holds (moved/dedup'd from timbda). *)
Lemma Comp_Sing_true (p : ZFSet) (P : ZFSet -> Prop) :
  P p -> Comp {| p |} P = {| p |}.
Proof.
  intro HP. apply set_ext.
  - apply Comp_Inc.
  - apply Sing_Inc_IN. apply In_P_Comp; [ apply IN_Sing | exact HP ].
Qed.


(** **** Decoding numerals: [natZto] and case analysis over [ω].

    [natZto] decodes a [ZFSet] back to a Rocq [nat] (via the chosen
    representative and [EnsNat.natOfEns]); it is total and agrees with the
    intended value on the numerals [natZ k] ([natZto_natZ]).  [setNatCase v b cf]
    is *case analysis* over [ω]: the zero branch [b] when [v] decodes to [0], and
    [cf (natZ m)] when [v] decodes to [S m].  (The recursive variant is
    [lang/CC/set_model.v]'s [setNatRec]; the models in [lang/PLC/set_model.v] /
    [lang/CC/set_model.v] and the [LambdaSet] PLC embedding all read [Nat]'s
    eliminator through these.) *)

Definition natZto (X : ZFSet) : nat := EnsNat.natOfEns (repr X).

Lemma natZto_natZ : forall k, natZto (natZ k) = k.
Proof.
  intro k. unfold natZto, natZ.
  rewrite (EnsNat.natOfEns_sound (repr (mk (EnsDefs.natZ k))) (EnsDefs.natZ k)).
  - unfold EnsDefs.natZ. apply EnsNat.natOfEns_Nat.
  - apply mk_inj. rewrite mk_repr. reflexivity.
Qed.

Definition setNatCase (v b : ZFSet) (cf : ZFSet -> ZFSet) : ZFSet :=
  match natZto v with O => b | S m => cf (natZ m) end.

Lemma setNatCase_zero b cf : setNatCase (natZ 0) b cf = b.
Proof. unfold setNatCase. rewrite natZto_natZ. reflexivity. Qed.

Lemma setNatCase_succ k b cf : setNatCase (natZ (S k)) b cf = cf (natZ k).
Proof. unfold setNatCase. rewrite natZto_natZ. reflexivity. Qed.

(* ================================================================== *)
(** * Member-wise forms of the [iUnion] laws.

    [iUnion_Sing_l] needs [F E] to be a set ([iUnion] always returns a
    set).  Stated member-wise the law holds for every sort of [F E], which is
    what a rewrite under an outer [iUnion] needs. *)
(* ================================================================== *)

Lemma iUnion_Sing_l_mem : forall (E : ZFSet) (F : ZFSet -> ZFSet) (z : ZFSet),
  In z (iUnion (Sing E) F) = In z (F E).
Proof.
  intros E F z. apply prop_ext. split.
  - intro Hz. apply iUnion_IN in Hz. destruct Hz as [x [Hx Hz]].
    apply IN_Sing_EQ in Hx. subst x. exact Hz.
  - intro Hz. apply (IN_iUnion _ _ E); [ apply IN_Sing | exact Hz ].
Qed.

(** Extensionality of [iUnion] up to the members of the sets [F x]. *)
Lemma iUnion_ext_memwise : forall (E : ZFSet) (F G : ZFSet -> ZFSet),
  (forall x, In x E -> forall z, In z (F x) <-> In z (G x)) ->
  iUnion E F = iUnion E G.
Proof.
  intros E F G H. apply set_ext; inc_def; intros z Hz;
    apply iUnion_IN in Hz; destruct Hz as [x [Hx Hz]];
    apply (IN_iUnion _ _ x); try exact Hx; apply (H x Hx); exact Hz.
Qed.

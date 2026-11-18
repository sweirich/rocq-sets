(* EnsLib.v: Setoid instances and derived lemmas for the [Ens]-level
   operations of [EnsDefs.v], over the sorted [Ens] (atoms, couples, sets)
   of [zf/zfc/Sets.v].

   Where a law reads a value off the members of a set ("the union of a
   singleton is its element", "the union over [E] of the singletons is
   [E]"), it holds only for a *set* and now carries an [is_set] premise:
   a set-former always produces a set, and an atom or couple is equal to
   no set. *)

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.
Require Import Omega.
Require Import EnsNotation.

From Stdlib Require Import Setoid Morphisms PropExtensionality.

(* Universe polymorphic, like the [zfc] core: [IN]/[EQ] carry floating
   universes now, so lemmas that take them in hypothesis position (e.g.
   [iUnion_IN]) must be polymorphic too, otherwise their rigid universes
   fail to unify with a caller's fresh ones. *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** The set-formers of [EnsDefs] produce sets. *)

Lemma iUnion_is_set : forall (E : Ens) (F : Ens -> Ens), is_set (iUnion E F).
Proof. intros E F. destruct E; exact I. Qed.

Lemma BinUnion_is_set : forall E E' : Ens, is_set (E ∪ E').
Proof. intros; exact I. Qed.

Lemma dom_is_set : forall r : Ens, is_set (dom r).
Proof. intro r. unfold dom. apply Comp_is_set. Qed.

Lemma rng_is_set : forall r : Ens, is_set (rng r).
Proof. intro r. unfold rng. apply Comp_is_set. Qed.

Lemma image_is_set : forall r S : Ens, is_set (image r S).
Proof. intros r S. unfold image. apply Comp_is_set. Qed.

(** EQ as a setoid equivalence + Proper instances for the standard
    operations, so that [setoid_rewrite] can drive rewrites under [≃]. ***)

#[global] Instance EQ_Equivalence : Equivalence EQ.
Proof.
  constructor.
  - exact EQ_refl.
  - exact EQ_sym.
  - intros x y z; apply EQ_tran.
Defined.

#[global] Instance Sing_Proper : Proper (EQ ==> EQ) Sing.
Proof. intros x y H; exact (Sing_sound _ _ H). Qed.

#[global] Instance Paire_Proper : Proper (EQ ==> EQ ==> EQ) Paire.
Proof.
  intros a a' Ha b b' Hb.
  apply EQ_tran with (Paire a b').
  - apply Paire_sound_right; exact Hb.
  - apply Paire_sound_left; exact Ha.
Qed.

#[global] Instance Couple_Proper : Proper (EQ ==> EQ ==> EQ) Couple.
Proof. intros a a' Ha b b' Hb. apply pair_sound; assumption. Qed.

Lemma Prod_sound :
  forall E E' F F' : Ens,
  EQ E F -> EQ E' F' -> EQ (Prod E E') (Prod F F').
Proof.
  intros E E' F F' HE HE'.
  apply EQ_ext; [ apply Prod_is_set | apply Prod_is_set | ].
  intro x; split; intro Hx.
  - destruct (IN_Prod_EXType _ _ _ Hx) as [A [B HAB]].
    assert (HpEE : IN (Couple A B) (Prod E E'))
      by (apply IN_sound_left with x;
          [apply EQ_sym; exact HAB | exact Hx]).
    destruct (Couple_Prod_IN _ _ _ _ HpEE) as [HA HB].
    apply IN_sound_left with (Couple A B); [exact HAB |].
    apply Couple_IN_Prod.
    + apply IN_sound_right with E; assumption.
    + apply IN_sound_right with E'; assumption.
  - destruct (IN_Prod_EXType _ _ _ Hx) as [A [B HAB]].
    assert (HpFF : IN (Couple A B) (Prod F F'))
      by (apply IN_sound_left with x;
          [apply EQ_sym; exact HAB | exact Hx]).
    destruct (Couple_Prod_IN _ _ _ _ HpFF) as [HA HB].
    apply IN_sound_left with (Couple A B); [exact HAB |].
    apply Couple_IN_Prod.
    + apply IN_sound_right with F; [apply EQ_sym; exact HE | exact HA].
    + apply IN_sound_right with F'; [apply EQ_sym; exact HE' | exact HB].
Qed.

#[global] Instance Prod_Proper : Proper (EQ ==> EQ ==> EQ) Prod.
Proof. intros E E' HE F F' HF; apply Prod_sound; assumption. Qed.

#[global] Instance Power_Proper : Proper (EQ ==> EQ) Power.
Proof. intros E E' H; exact (Power_sound _ _ H). Qed.

#[global] Instance Union_Proper : Proper (EQ ==> EQ) Union.
Proof. intros E E' H; exact (Union_sound _ _ H). Qed.

#[global] Instance BinUnion_Proper : Proper (EQ ==> EQ ==> EQ) BinUnion.
Proof.
  intros a a' Ha b b' Hb. unfold BinUnion.
  apply Union_sound. apply Paire_Proper; assumption.
Qed.

(** Pointwise [Proper] instances for [IN] and [INC]. *)

#[global] Instance IN_Proper_left {e} :
  Proper (EQ ==> eq) (fun x : Ens => IN x e).
Proof.
  intros E E' H. apply propositional_extensionality.
  split; eapply IN_sound_left; [exact H | apply EQ_sym; exact H].
Qed.

#[global] Instance IN_Proper_right {x} : Proper (EQ ==> eq) (IN x).
Proof.
  intros E E' H. apply propositional_extensionality.
  split; eapply IN_sound_right; [exact H | apply EQ_sym; exact H].
Qed.

#[global] Instance INC_Proper_left {e} :
  Proper (EQ ==> eq) (fun x : Ens => INC x e).
Proof.
  intros E E' H. apply propositional_extensionality.
  split; intro HINC.
  - apply INC_sound_left with E; assumption.
  - apply INC_sound_left with E'; [ apply EQ_sym; exact H | exact HINC ].
Qed.

#[global] Instance INC_Proper_right {x} : Proper (EQ ==> eq) (INC x).
Proof.
  intros E E' H. apply propositional_extensionality.
  split; intro HINC.
  - apply INC_sound_right with E; assumption.
  - apply INC_sound_right with E'; [ apply EQ_sym; exact H | exact HINC ].
Qed.

(** [is_set] respects [≃] in both directions. *)
Lemma is_set_iff : forall E E' : Ens, E ≃ E' -> (is_set E <-> is_set E').
Proof.
  intros E E' H; split; intro Hs.
  - apply EQ_is_set with E; assumption.
  - apply EQ_is_set with E'; [ apply EQ_sym | ]; assumption.
Qed.


(** Reusable lemmas about Union and Comp ***)

(** The union of a singleton is its element — when that element is a set.
    (For an atom or couple [E], [⋃ {| E |}] is the empty set.) *)
Lemma Union_Sing : forall E : Ens, is_set E -> ⋃ {| E |} ≃ E.
Proof.
  intros E Hs. apply EQ_ext; [ apply Union_is_set | exact Hs | ].
  intro x; split; intro Hx.
  - destruct (Union_IN _ _ Hx) as [y [Hy Hxy]].
    apply IN_sound_right with y; [apply IN_Sing_EQ|]; assumption.
  - apply IN_Union with E; [apply IN_Sing|]; assumption.
Qed.

Lemma Comp_sound_left :
  forall (E E' : Ens) (P : Ens -> Prop),
  (forall x y, P x -> x ≃ y -> P y) ->
  E ≃ E' -> Comp E P ≃ Comp E' P.
Proof.
  intros E E' P HP HE.
  apply EQ_ext; [ apply Comp_is_set | apply Comp_is_set | ].
  intro x; split; intro Hx.
  - assert (HxE : x ∈ E) by (exact (INC_elim _ _ (Comp_INC E P) x Hx)).
    assert (HPx : P x) by (apply IN_Comp_P with E; assumption).
    apply IN_P_Comp; [assumption | apply IN_sound_right with E | ]; assumption.
  - assert (HxE' : x ∈ E') by (exact (INC_elim _ _ (Comp_INC E' P) x Hx)).
    assert (HPx : P x) by (apply IN_Comp_P with E'; assumption).
    apply IN_P_Comp; [assumption | apply IN_sound_right with E';
      [apply EQ_sym | ] | ]; assumption.
Qed.


(** Simplification lemmas for iUnion

  Intro needs F extensionally sound (EQ-respecting) since elements of E are
  only EQ-witnessed by the Aczel index; elim does not. ***)

Theorem IN_iUnion :
  forall (E : Ens) (F : Ens -> Ens) (y x : Ens),
  (forall u v : Ens, u ≃ v -> F u ≃ F v) ->
  y ∈ E -> x ∈ F y -> x ∈ (z ← E ;; F z).
Proof.
  intros E F y x Fsnd Hy Hx.
  destruct E as [n | a b | IE fE]; simpl in Hy; try contradiction.
  destruct Hy as [a Ha].
  change (iUnion (sup IE fE) F)
    with (Union (sup IE (fun a' => F (fE a')))).
  apply IN_Union with (F (fE a)).
  - exists a; apply EQ_refl.
  - apply IN_sound_right with (F y).
    + apply Fsnd; exact Ha.
    + exact Hx.
Qed.

Theorem iUnion_IN :
  forall (E : Ens) (F : Ens -> Ens) (x : Ens),
   x ∈ (z ← E ;; F z)  ->
  EXType _ (fun y : Ens => y ∈ E /\ x ∈ F y).
Proof.
  intros E F x H.
  destruct E as [n | a b | IE fE].
  - destruct H as [c _]; destruct c.
  - destruct H as [c _]; destruct c.
  - change (iUnion (sup IE fE) F)
      with (Union (sup IE (fun a' => F (fE a')))) in H.
    destruct (Union_IN _ _ H) as [E1 [HE1 Hx]].
    destruct HE1 as [a Ha].
    exists (fE a); split.
    + exists a; apply EQ_refl.
    + apply IN_sound_right with E1; assumption.
Qed.

(** Iterating over a singleton is the body at its element — when the body
    is a set there. *)
Lemma iUnion_Sing_l E F :
  is_set (F E) -> x ← {| E |} ;; F x ≃ F E.
Proof.
  intro Hs. apply EQ_ext; [ apply iUnion_is_set | exact Hs | ].
  intro x; split; intro Hx.
  - destruct (iUnion_IN _ _ _ Hx) as [y [Hy Hxy]].
    apply IN_Sing_EQ in Hy.
    unfold iUnion, Sing, Paire in Hx.
    destruct (Union_IN _ _ Hx) as [z [[b Hb] Hxz]].
    destruct b; cbn in Hb; apply IN_sound_right with z; assumption.
  - unfold iUnion, Sing, Paire.
    apply IN_Union with (F E).
    + exists true; cbn; apply EQ_refl.
    + exact Hx.
Qed.

(** The union of the singletons of the members of a set is the set. *)
Lemma iUnion_Sing_r E :
  is_set E -> x ← E ;; {| x |} ≃ E.
Proof.
  intro Hs. apply EQ_ext; [ apply iUnion_is_set | exact Hs | ].
  intro x; split; intro Hx.
  - destruct (iUnion_IN _ _ _ Hx) as [y [HyE HxSy]].
    apply IN_Sing_EQ in HxSy.
    apply IN_sound_left with y; [apply EQ_sym; exact HxSy | exact HyE].
  - apply IN_iUnion with (y := x).
    + intros u v Huv; apply Sing_sound; exact Huv.
    + exact Hx.
    + apply IN_Sing.
Qed.

(** Soundness of iUnion in its index argument. ***)

Lemma iUnion_sound_l :
  forall (E E' : Ens) (F : Ens -> Ens),
  (forall u v : Ens, u ≃ v -> F u ≃ F v) ->
  E ≃ E' ->
  iUnion E F ≃ iUnion E' F.
Proof.
  intros E E' F HF HEE.
  apply EQ_ext; [ apply iUnion_is_set | apply iUnion_is_set | ].
  intro x; split; intro Hx.
  - destruct (iUnion_IN _ _ _ Hx) as [y [HyE Hxy]].
    apply IN_iUnion with y; auto.
    apply IN_sound_right with E; assumption.
  - destruct (iUnion_IN _ _ _ Hx) as [y [HyE' Hxy]].
    apply IN_iUnion with y; auto.
    apply IN_sound_right with E'; [apply EQ_sym|]; assumption.
Qed.

Lemma iUnion_assoc E F G
  (HF : forall u v : Ens, u ≃ v -> F u ≃ F v)
  (HG : forall u v : Ens, u ≃ v -> G u ≃ G v) :
  y ← (x ← E ;; F x) ;; G y ≃  x ← E ;; y ← F x ;; G y.
Proof.
  apply EQ_ext; [ apply iUnion_is_set | apply iUnion_is_set | ].
  intro z; split; intro Hz.
  - destruct (iUnion_IN _ _ _ Hz) as [y [HyU HzGy]].
    destruct (iUnion_IN _ _ _ HyU) as [x [HxE HyFx]].
    apply IN_iUnion with (y := x).
    + intros u v Huv. apply iUnion_sound_l; [exact HG | exact (HF _ _ Huv)].
    + exact HxE.
    + apply IN_iUnion with (y := y); [exact HG | exact HyFx | exact HzGy].
  - destruct (iUnion_IN _ _ _ Hz) as [x [HxE Hzx]].
    destruct (iUnion_IN _ _ _ Hzx) as [y [HyFx HzGy]].
    apply IN_iUnion with (y := y).
    + exact HG.
    + apply IN_iUnion with (y := x); [exact HF | exact HxE | exact HyFx].
    + exact HzGy.
Qed.

(** [iUnion] as a setoid morphism in both arguments. ***)

#[global] Instance iUnion_Proper :
  Proper (EQ ==> (EQ ==> EQ) ==> EQ) iUnion.
Proof.
  intros E E' HEE F G HFG.
  assert (HFsnd : forall u v, u ≃ v -> F u ≃ F v).
  { intros u v Huv.
    apply EQ_tran with (G v); [apply HFG; exact Huv|].
    apply EQ_sym; apply HFG; apply EQ_refl. }
  assert (HGsnd : forall u v, u ≃ v -> G u ≃ G v).
  { intros u v Huv.
    apply EQ_tran with (F u);
      [apply EQ_sym; apply HFG; apply EQ_refl | apply HFG; exact Huv]. }
  apply EQ_ext; [ apply iUnion_is_set | apply iUnion_is_set | ].
  intro x; split; intro Hx.
  - destruct (iUnion_IN _ _ _ Hx) as [y [HyE Hxy]].
    apply IN_iUnion with y; auto.
    + apply IN_sound_right with E; assumption.
    + apply IN_sound_right with (F y); [apply HFG; apply EQ_refl | exact Hxy].
  - destruct (iUnion_IN _ _ _ Hx) as [y [HyE' Hxy]].
    apply IN_iUnion with y; auto.
    + apply IN_sound_right with E'; [apply EQ_sym|]; assumption.
    + apply IN_sound_right with (G y);
        [apply EQ_sym; apply HFG; apply EQ_refl | exact Hxy].
Qed.


Lemma Sing_is_subsingleton : forall a : Ens, is_subsingleton {| a |}.
Proof.
  intros a y z Hy Hz.
  apply EQ_tran with a.
  apply IN_Sing_EQ; assumption.
  apply EQ_sym; apply IN_Sing_EQ; assumption.
Qed.


(** pfst / psnd soundness and projection equations ***)

Lemma is_subsingleton_sound :
  forall x y : Ens, x ≃ y -> is_subsingleton x -> is_subsingleton y.
Proof.
  intros x y Hxy Hx u v Hu Hv.
  apply Hx;
    (apply IN_sound_right with y; [apply EQ_sym|]; assumption).
Qed.

Lemma is_nonempty_Sing : forall E : Ens, is_nonempty {| E |}.
Proof. intro E; exists E; apply IN_Sing. Qed.

Lemma not_nonempty_Vide : ~ is_nonempty ∅.
Proof. intros [y Hy]; elim (Vide_est_vide _ Hy). Qed.

Lemma is_nonempty_sound :
  forall x y : Ens, x ≃ y -> is_nonempty x -> is_nonempty y.
Proof.
  intros x y Hxy [u Hu]; exists u.
  apply IN_sound_right with x; assumption.
Qed.

Lemma pfst_sound : forall x y : Ens, x ≃ y -> pfst x ≃ pfst y.
Proof.
  intros x y Hxy.
  destruct x as [n | a b | A f]; destruct y as [m | c d | B g]; simpl in Hxy;
    try contradiction; cbn [pfst]; try apply EQ_refl.
  destruct Hxy as [H _]; exact H.
Qed.

Lemma psnd_sound : forall x y : Ens, x ≃ y -> psnd x ≃ psnd y.
Proof.
  intros x y Hxy.
  destruct x as [n | a b | A f]; destruct y as [m | c d | B g]; simpl in Hxy;
    try contradiction; cbn [psnd]; try apply EQ_refl.
  destruct Hxy as [_ H]; exact H.
Qed.

#[global] Instance pfst_Proper : Proper (EQ ==> EQ) pfst.
Proof. intros x y H; exact (pfst_sound _ _ H). Qed.

#[global] Instance psnd_Proper : Proper (EQ ==> EQ) psnd.
Proof. intros x y H; exact (psnd_sound _ _ H). Qed.

Theorem pfst_Couple : forall a b : Ens, pfst ⟨ a , b ⟩ ≃ a.
Proof. intros a b. apply EQ_refl. Qed.

Theorem psnd_Couple : forall a b : Ens, psnd ⟨ a , b ⟩ ≃ b.
Proof. intros a b. apply EQ_refl. Qed.

Theorem proj1_triple : forall a b c : Ens, proj1 ⟨ a , b , c ⟩ ≃ a.
Proof. intros; unfold proj1; apply pfst_Couple. Qed.

Theorem proj2_triple : forall a b c : Ens, proj2 ⟨ a , b , c ⟩ ≃ b.
Proof.
  intros; unfold proj2.
  apply EQ_tran with (pfst (Couple b c)).
  - apply pfst_sound; apply psnd_Couple.
  - apply pfst_Couple.
Qed.

Theorem proj3_triple : forall a b c : Ens, proj3 ⟨ a , b , c ⟩ ≃ c.
Proof.
  intros; unfold proj3.
  apply EQ_tran with (psnd (Couple b c)).
  - apply psnd_sound; apply psnd_Couple.
  - apply psnd_Couple.
Qed.



(* Every element of natId is EQ to a diagonal pair of encoded naturals. *)
Lemma IN_natId_EXType :
  forall p : Ens, p ∈ natId ->
  EXType _ (fun n : nat => p ≃ ⟨ Nat n , Nat n ⟩).
Proof.
  intros p Hp; unfold natId in Hp.
  destruct (iUnion_IN _ _ _ Hp) as [n [Hn Hpn]].
  destruct (IN_EXType _ _ Hn) as [k Hk]; simpl in Hk.
  exists k.
  apply EQ_tran with (⟨ n , n ⟩).
  - apply IN_Sing_EQ; exact Hpn.
  - apply EQ_tran with (⟨ Nat k , n ⟩).
    + apply Couple_sound_left; exact Hk.
    + apply Couple_sound_right; exact Hk.
Qed.

(* A Couple in natId is a diagonal pair. *)
Lemma natId_pair_diagonal :
  forall a b : Ens, ⟨ a , b ⟩ ∈ natId -> a ≃ b.
Proof.
  intros a b H.
  destruct (IN_natId_EXType _ H) as [k Hk].
  apply EQ_tran with (Nat k).
  - exact (Couple_inj_left _ _ _ _ Hk).
  - apply EQ_sym; exact (Couple_inj_right _ _ _ _ Hk).
Qed.

(* For elements of natId, the two projections coincide. *)
Lemma natId_diagonal :
  forall p : Ens, p ∈ natId -> pfst p ≃ psnd p.
Proof.
  intros p Hp.
  destruct (IN_natId_EXType p Hp) as [n Heq].
  apply EQ_tran with (Nat n).
  - apply EQ_tran with (pfst ⟨ Nat n , Nat n ⟩).
    + apply pfst_sound; exact Heq.
    + apply pfst_Couple.
  - apply EQ_sym; apply EQ_tran with (psnd ⟨ Nat n , Nat n ⟩).
    + apply psnd_sound; exact Heq.
    + apply psnd_Couple.
Qed.


(** dom / rng / image: soundness, introduction and elimination.

   The ambient sets are the replacements [⋃_{p∈r} {pfst p}] and
   [⋃_{p∈r} {psnd p}]; the bodies respect [≃] through [pfst_sound] /
   [psnd_sound]. *)

Lemma Sing_pfst_sound : forall u v : Ens, u ≃ v -> {| pfst u |} ≃ {| pfst v |}.
Proof. intros u v H. apply Sing_sound. apply pfst_sound. exact H. Qed.

Lemma Sing_psnd_sound : forall u v : Ens, u ≃ v -> {| psnd u |} ≃ {| psnd v |}.
Proof. intros u v H. apply Sing_sound. apply psnd_sound. exact H. Qed.

Lemma dom_sound :
  forall r r' : Ens, r ≃ r' -> dom r ≃ dom r'.
Proof.
  assert (Hpred : forall R w1 w2 : Ens,
    (exists b, ⟨ w1 , b ⟩ ∈ R) -> w1 ≃ w2 -> (exists b, ⟨ w2 , b ⟩ ∈ R)).
  { intros R w1 w2 [b Hb] Hw12; exists b.
    apply IN_sound_left with (⟨ w1 , b ⟩);
      [apply Couple_sound_left; exact Hw12 | exact Hb]. }
  assert (Hdir : forall s s' : Ens, s ≃ s' -> INC (dom s) (dom s')).
  { intros s s' Hs. apply INC_intro; [ apply dom_is_set | ].
    intros a Ha; unfold dom in *.
    apply IN_P_Comp; [ apply Hpred | | ].
    - apply IN_sound_right with (iUnion s (fun p => {| pfst p |}));
        [ apply iUnion_sound_l; [ exact Sing_pfst_sound | exact Hs ]
        | exact (INC_elim _ _ (Comp_INC _ _) _ Ha) ].
    - destruct (IN_Comp_P _ _ _ (Hpred s) Ha) as [b Hb].
      exists b; apply IN_sound_right with s; [ exact Hs | exact Hb ]. }
  intros r r' Hr; apply INC_EQ;
    [ apply Hdir; exact Hr | apply Hdir; apply EQ_sym; exact Hr ].
Qed.

Lemma rng_sound :
  forall r r' : Ens, r ≃ r' -> rng r ≃ rng r'.
Proof.
  assert (Hpred : forall R w1 w2 : Ens,
    (exists a, ⟨ a , w1 ⟩ ∈ R) -> w1 ≃ w2 -> (exists a, ⟨ a , w2 ⟩ ∈ R)).
  { intros R w1 w2 [a Ha] Hw12; exists a.
    apply IN_sound_left with (⟨ a , w1 ⟩);
      [apply Couple_sound_right; exact Hw12 | exact Ha]. }
  assert (Hdir : forall s s' : Ens, s ≃ s' -> INC (rng s) (rng s')).
  { intros s s' Hs. apply INC_intro; [ apply rng_is_set | ].
    intros b Hb; unfold rng in *.
    apply IN_P_Comp; [ apply Hpred | | ].
    - apply IN_sound_right with (iUnion s (fun p => {| psnd p |}));
        [ apply iUnion_sound_l; [ exact Sing_psnd_sound | exact Hs ]
        | exact (INC_elim _ _ (Comp_INC _ _) _ Hb) ].
    - destruct (IN_Comp_P _ _ _ (Hpred s) Hb) as [a Ha].
      exists a; apply IN_sound_right with s; [ exact Hs | exact Ha ]. }
  intros r r' Hr; apply INC_EQ;
    [ apply Hdir; exact Hr | apply Hdir; apply EQ_sym; exact Hr ].
Qed.

#[global] Instance dom_Proper : Proper (EQ ==> EQ) dom.
Proof. intros r r' H; apply dom_sound; exact H. Qed.

#[global] Instance rng_Proper : Proper (EQ ==> EQ) rng.
Proof. intros r r' H; apply rng_sound; exact H. Qed.

Lemma image_sound :
  forall r r' S S' : Ens,
  r ≃ r' -> S ≃ S' -> image r S ≃ image r' S'.
Proof.
  assert (Hpred : forall R Sx w1 w2 : Ens,
    (exists a, a ∈ Sx /\ ⟨ a , w1 ⟩ ∈ R) -> w1 ≃ w2 ->
    (exists a, a ∈ Sx /\ ⟨ a , w2 ⟩ ∈ R)).
  { intros R Sx w1 w2 [a [HaS Ha]] Hw12; exists a; split; [exact HaS|].
    apply IN_sound_left with (⟨ a , w1 ⟩);
      [apply Couple_sound_right; exact Hw12 | exact Ha]. }
  assert (Hdir : forall r r' S S' : Ens,
    r ≃ r' -> S ≃ S' -> INC (image r S) (image r' S')).
  { intros s s' T T' Hs HT. apply INC_intro; [ apply image_is_set | ].
    intros b Hb; unfold image in *.
    apply IN_P_Comp; [ apply Hpred | | ].
    - apply IN_sound_right with (rng s);
        [ apply rng_sound; exact Hs | exact (INC_elim _ _ (Comp_INC _ _) _ Hb) ].
    - destruct (IN_Comp_P _ _ _ (Hpred s T) Hb) as [a [HaT Ha]].
      exists a; split.
      + apply IN_sound_right with T; [ exact HT | exact HaT ].
      + apply IN_sound_right with s; [ exact Hs | exact Ha ]. }
  intros r r' S S' Hr HS; apply INC_EQ;
    [ apply Hdir; assumption | apply Hdir; apply EQ_sym; assumption ].
Qed.

#[global] Instance image_Proper : Proper (EQ ==> EQ ==> EQ) image.
Proof. intros r r' Hr S S' HS; apply image_sound; assumption. Qed.

Lemma dom_intro :
  forall (r a b : Ens), ⟨ a , b ⟩ ∈ r -> a ∈ dom r.
Proof.
  intros r a b Hab.
  unfold dom.
  apply IN_P_Comp; [ | | exists b; exact Hab ].
  - intros w1 w2 [b' Hb'] Hw12.
    exists b'.
    apply IN_sound_left with (⟨ w1 , b' ⟩); [|exact Hb'].
    apply Couple_sound_left; exact Hw12.
  - apply IN_iUnion with (y := ⟨ a , b ⟩); [ exact Sing_pfst_sound | exact Hab | ].
    apply IN_Sing.
Qed.

Lemma dom_elim :
  forall (r a : Ens),
  a ∈ dom r -> exists b : Ens, ⟨ a , b ⟩ ∈ r.
Proof.
  intros r a H.
  apply IN_Comp_P
    with (E := iUnion r (fun p => {| pfst p |}))
         (P := fun a' => exists b : Ens, ⟨ a' , b ⟩ ∈ r);
    [|exact H].
  intros w1 w2 [b Hab] Hw12.
  exists b; apply IN_sound_left with (⟨ w1 , b ⟩); [|exact Hab].
  apply Couple_sound_left; exact Hw12.
Qed.

Lemma rng_intro :
  forall (r a b : Ens), ⟨ a , b ⟩ ∈ r -> b ∈ rng r.
Proof.
  intros r a b Hab.
  unfold rng.
  apply IN_P_Comp; [ | | exists a; exact Hab ].
  - intros w1 w2 [a' Ha'b'] Hw12.
    exists a'.
    apply IN_sound_left with (⟨ a' , w1 ⟩); [|exact Ha'b'].
    apply Couple_sound_right; exact Hw12.
  - apply IN_iUnion with (y := ⟨ a , b ⟩); [ exact Sing_psnd_sound | exact Hab | ].
    apply IN_Sing.
Qed.

Lemma rng_elim :
  forall (r b : Ens),
  b ∈ rng r -> exists a : Ens, ⟨ a , b ⟩ ∈ r.
Proof.
  intros r b H.
  apply IN_Comp_P
    with (E := iUnion r (fun p => {| psnd p |}))
         (P := fun b' => exists a : Ens, ⟨ a , b' ⟩ ∈ r);
    [|exact H].
  intros w1 w2 [a Hab] Hw12.
  exists a; apply IN_sound_left with (⟨ a , w1 ⟩); [|exact Hab].
  apply Couple_sound_right; exact Hw12.
Qed.

Lemma image_intro :
  forall (r S b a : Ens),
  a ∈ S ->
  ⟨ a , b ⟩ ∈ r ->
  b ∈ image r S.
Proof.
  intros r S b a Ha Hab.
  unfold image.
  apply IN_P_Comp;
    [|apply rng_intro with a; exact Hab|exists a; split; assumption].
  intros w1 w2 [a' [Ha'S Ha'b']] Hw12.
  exists a'; split; [exact Ha'S|].
  apply IN_sound_left with (⟨ a' , w1 ⟩); [|exact Ha'b'].
  apply Couple_sound_right; exact Hw12.
Qed.

Lemma image_elim :
  forall (r S b : Ens),
  b ∈ image r S ->
  exists a : Ens, a ∈ S /\ ⟨ a , b ⟩ ∈ r.
Proof.
  intros r S b H.
  apply IN_Comp_P
    with (E := rng r)
         (P := fun b' => exists a : Ens, a ∈ S /\ ⟨ a , b' ⟩ ∈ r);
    [|exact H].
  intros w1 w2 [a [HaS Hab]] Hw12.
  exists a; split; [exact HaS|].
  apply IN_sound_left with (⟨ a , w1 ⟩); [|exact Hab].
  apply Couple_sound_right; exact Hw12.
Qed.

(** Simplification lemmas for BinUnion ***)

Theorem IN_BinUnion_l : forall x E E' : Ens, x ∈ E -> x ∈ E ∪ E'.
Proof.
  intros x E E' Hx; unfold BinUnion.
  apply IN_Union with E; [ apply IN_Paire_left | exact Hx ].
Qed.

Theorem IN_BinUnion_r : forall x E E' : Ens, x ∈ E' -> x ∈ E ∪ E'.
Proof.
  intros x E E' Hx; unfold BinUnion.
  apply IN_Union with E'; [ apply IN_Paire_right | exact Hx ].
Qed.

Theorem BinUnion_IN :
  forall x E E' : Ens, x ∈ E ∪ E' -> x ∈ E \/ x ∈ E'.
Proof.
  intros x E E' H; unfold BinUnion in H.
  destruct (Union_IN _ _ H) as [y [Hy Hxy]].
  destruct (Paire_IN _ _ _ Hy) as [Heq | Heq].
  - left;  apply IN_sound_right with y; assumption.
  - right; apply IN_sound_right with y; assumption.
Qed.


Theorem BinUnion_Vide_l : forall E : Ens, is_set E -> ∅ ∪ E ≃ E.
Proof.
  intros E Hs; apply EQ_ext; [ apply BinUnion_is_set | exact Hs | ].
  intro x; split; intro Hx.
  - destruct (BinUnion_IN _ _ _ Hx) as [Hv | He].
    + elim (Vide_est_vide _ Hv).
    + exact He.
  - apply IN_BinUnion_r; exact Hx.
Qed.

Theorem BinUnion_Vide_r : forall E : Ens, is_set E -> E ∪ ∅ ≃ E.
Proof.
  intros E Hs; apply EQ_ext; [ apply BinUnion_is_set | exact Hs | ].
  intro x; split; intro Hx.
  - destruct (BinUnion_IN _ _ _ Hx) as [He | Hv].
    + exact He.
    + elim (Vide_est_vide _ Hv).
  - apply IN_BinUnion_l; exact Hx.
Qed.


Theorem iUnion_Vide : forall F : Ens -> Ens, x ← ∅ ;; F x  ≃ ∅.
Proof.
  intro F; apply EQ_ext; [ apply iUnion_is_set | exact I | ].
  intro x; split; intro Hx.
  - apply iUnion_IN in Hx.
    destruct Hx as [y [Hy _]]; elim (Vide_est_vide _ Hy).
  - elim (Vide_est_vide _ Hx).
Qed.

Theorem empty_union_empty : ∅ ∪ ∅ ≃ ∅.
Proof. apply BinUnion_Vide_l. exact I. Qed.

Lemma iUnion_graph_mem_pi {A : Ens} {B : Ens -> Ens}
    (g : Ens -> Ens) (hg_sound : forall a a', a ≃ a' -> g a ≃ g a')
    (hg : forall a, a ∈ A -> g a ∈ B a) :
    (iUnion A (fun v => {| ⟨v, g v⟩ |})) ∈ Pi A B.
Proof.
  (* The graph's body function respects ≃ (needed by [IN_iUnion]). *)
  assert (Fsnd : forall u v : Ens, u ≃ v -> {| ⟨ u , g u ⟩ |} ≃ {| ⟨ v , g v ⟩ |}).
  { intros u v Huv; apply Sing_sound.
    apply EQ_tran with (⟨ v , g u ⟩).
    - apply Couple_sound_left; exact Huv.
    - apply Couple_sound_right; apply hg_sound; exact Huv. }
  unfold Pi.
  apply IN_P_Comp.
  - (* The Pi predicate respects ≃ on the graph. *)
    intros w1 w2 [Htot Hfun] Hw12; split.
    + intros a Ha. destruct (Htot a Ha) as [b [Hb Hab]].
      exists b; split; [exact Hb | apply IN_sound_right with w1; assumption].
    + intros a b1 b2 H1 H2. apply (Hfun a b1 b2);
        apply IN_sound_right with w2; auto with zfc.
  - (* The graph is a subset of [Prod A (⋃B)], hence in its power-set.
       Work with A's underlying elements so [g (fA k) ∈ B (fA k)] lands
       in [iUnion A B] without needing [B] to respect ≃. *)
    apply INC_IN_Power; [ apply Prod_is_set | ].
    apply INC_intro; [ apply iUnion_is_set | ].
    intros x Hx.
    destruct A as [n | a b | IA fA];
      [ destruct Hx as [c _]; destruct c | destruct Hx as [c _]; destruct c | ].
    change (iUnion (sup IA fA) (fun v => {| ⟨ v , g v ⟩ |}))
      with (Union (sup IA (fun k => {| ⟨ fA k , g (fA k) ⟩ |}))) in Hx.
    destruct (Union_IN _ _ Hx) as [E1 [HE1 HxE1]].
    destruct HE1 as [k Hk].
    assert (Hxsing : x ∈ {| ⟨ fA k , g (fA k) ⟩ |})
      by (apply IN_sound_right with E1; assumption).
    assert (Hxeq : x ≃ ⟨ fA k , g (fA k) ⟩) by (apply IN_Sing_EQ; exact Hxsing).
    apply IN_sound_left with (⟨ fA k , g (fA k) ⟩); [apply EQ_sym; exact Hxeq|].
    apply Couple_IN_Prod.
    + exists k; apply EQ_refl.
    + change (iUnion (sup IA fA) B)
        with (Union (sup IA (fun j => B (fA j)))).
      apply IN_Union with (B (fA k)).
      * exists k; apply EQ_refl.
      * apply hg. exists k; apply EQ_refl.
  - (* Totality and functionality of the graph. *)
    split.
    + intros a Ha. exists (g a); split; [apply hg; exact Ha|].
      apply IN_iUnion with (y := a); [exact Fsnd | exact Ha | apply IN_Sing].
    + intros a b1 b2 H1 H2.
      apply iUnion_IN in H1; destruct H1 as [y1 [Hy1 Hxy1]].
      apply iUnion_IN in H2; destruct H2 as [y2 [Hy2 Hxy2]].
      assert (HC1 : ⟨ a , b1 ⟩ ≃ ⟨ y1 , g y1 ⟩) by (apply IN_Sing_EQ; exact Hxy1).
      assert (HC2 : ⟨ a , b2 ⟩ ≃ ⟨ y2 , g y2 ⟩) by (apply IN_Sing_EQ; exact Hxy2).
      apply EQ_tran with (g y1); [exact (Couple_inj_right _ _ _ _ HC1)|].
      apply EQ_tran with (g y2);
        [| apply EQ_sym; exact (Couple_inj_right _ _ _ _ HC2)].
      apply hg_sound.
      apply EQ_tran with a;
        [ apply EQ_sym; exact (Couple_inj_left _ _ _ _ HC1)
        | exact (Couple_inj_left _ _ _ _ HC2) ].
Qed.

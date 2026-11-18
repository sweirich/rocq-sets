(** * Axioms: the axioms of the development *)

Require Export basics.

(* Prefer the type-theoretic notations ([A * B] is the product type). *)
#[global] Open Scope type_scope.

(** Instead of working with explicit setoids, we use them implicitly by working
  with (a mock-up) observational equality, which gives us an internal language
  for setoids. This is achieved by the axioms below. *)

(** ** Propositional extensionality *)
From Stdlib Require Export PropExtensionalityFacts.

Axiom prop_ext : forall {P Q : Prop}, P <-> Q -> P = Q.

(** ** Proof irrelevance *)
(** Ideally, we'd be using SProp here instead, but for the time being this shall be
  good enough. *)
From Stdlib Require Export ProofIrrelevanceFacts.

(** Propositional proof irrelevance is a consequence of propositional extensionality,
  so we do not need to postulate it explicitly. *)

Module PropExtProofIrr : ProofIrrelevance.

  Definition proof_irrelevance {P:Prop} (p q : P) : p = q.
  Proof.
    assert (P = True) as e.
    {
      apply prop_ext.
      now split.
    }
    revert p q.
    subst P.
    now intros [] [].
  Qed.

End PropExtProofIrr.

Export PropExtProofIrr.

Instance Prop_ProofIrrel (P : Prop) : ProofIrrel P.
Proof.
  intros p q. apply proof_irrelevance.
Qed.

(** ** Function extensionality *)
(** Corresponds to the definition of function setoids. *)
From Stdlib Require Export FunctionalExtensionality.

(** ** More extensionality *)

Lemma exist_ext {A B} (p q : {x : A | B x}) :
  proj1_sig p = proj1_sig q -> p = q.
Proof.
  intros e.
  destruct p as [? b], q as [? b'] ; cbn in *.
  assert (b' = transport _ e b) as -> by apply proof_irrelevance.
  destruct e ; cbn.
  reflexivity.
Qed.

Instance ProofIrrel_prod T (P : T -> Type) `{forall (x : T), ProofIrrel (P x)} : ProofIrrel (forall x : T, P x).
Proof.
  intros f g. apply functional_extensionality_dep. intro x. apply proof_irrel.
Qed.

(** ** Quotients *)

(** The axiomatization of quotient types below is due to Meven Lennon-Bertrand. *)

From Stdlib Require Import Relation_Definitions Relations RelationClasses RelationPairs Equivalence Morphisms.

(** *** Basic quotient axioms *)

(** The quotient type *)
Axiom quot : forall {T : Type} (R : relation T) `{! Equivalence R}, Type.

(** The quotient element constructor *)
Axiom to_quot : forall {T : Type} {R : relation T} `{! Equivalence R}, T -> quot R.

(** The quotient path constructor *)
Axiom quot_ext : forall {T : Type} {R : relation T} `{! Equivalence R} (t t' : T),
  R t t' -> to_quot t = to_quot t'.

(** Quotient effectivity axiom *)
Axiom quot_eq : forall {T : Type} {R : relation T} `{! Equivalence R} (t t' : T),
  to_quot t = to_quot t' -> R t t'.

(** Induction for quotients *)
Axiom quot_rect : forall {T : Type} {R : relation T} `{! Equivalence R},
  forall (P : quot R -> Type)
  (f : forall (t : T), P (to_quot t)),
  (forall (x y :T) (e : R x y), (quot_ext _ _ e) # (f x) = f y :> P (to_quot y)) ->
  forall u : quot R, P u.

(** Propositional computation rule *)
Axiom quot_rect_eq : forall {T : Type} {R : relation T} `{! Equivalence R},
  forall (P : quot R -> Type)
  (f : forall (t : T), P (to_quot t))
  (r : forall (x y :T) (e : R x y), (quot_ext _ _ e) # (f x) = f y :> P (to_quot y))
  (x : T),
  quot_rect P f r (to_quot x) = f x.

(** *** Quotient derived functions *)

Program Definition quot_rec {T : Type} {R : relation T} `{! Equivalence R} {P : Type}
  (f : T -> P)
  `{p : Proper _ (R ==> eq)%signature f} :
  quot R -> P :=
  quot_rect (fun _ => P) f _.
Next Obligation.
  intros. rewrite transport_const. apply p. assumption.
Qed.

Lemma quot_rec_eq {T : Type} {R : relation T} `{! Equivalence R} {P : Type}
  (f : T -> P)
  `{! Proper (R ==> eq) f}
  (t : T) : quot_rec f (to_quot t) = f t.
Proof.
  unfold quot_rec. now rewrite quot_rect_eq.
Qed.

Program Definition quot_rect_irr {T : Type} {R : relation T} `{! Equivalence R}
  (P : quot R -> Type)
  (f : forall (t : T), P (to_quot t))
  `{p : forall (t : T), ProofIrrel (P (to_quot t))} :
  forall u : quot R, P u :=
    quot_rect P f _.
Next Obligation.
  apply p.
Qed.

Definition quot_ind {T : Type} {R : relation T} `{! Equivalence R}
  (P : quot R -> Prop)
  (f : forall (t : T), P (to_quot t)) :
  forall u : quot R, P u :=
    quot_rect_irr P f.

Instance to_quot_proper
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  (f : A -> B)
  `{e : Proper _ (RA ==> RB) f} :
  Proper (RA ==> eq) (fun x => to_quot (f x)).
Proof.
  intros x y h.
  now apply quot_ext, e.
Qed.

Definition quot_map
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  (f : A -> B)
  `{e : Proper _ (RA ==> RB) f}
  : quot RA -> quot RB :=
  quot_rec (fun x => to_quot (f x)).

Lemma quot_map_eq
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  (f : A -> B)
  `{e : Proper _ (RA ==> RB) f}
  (a : A)
  : quot_map f (to_quot a) = to_quot (f a).
Proof.
  unfold quot_map. now rewrite quot_rec_eq.
Qed.

Instance PER_Equivalence {A} {RA : relation A} `{! PER RA} :
  @Equivalence {a : A | Proper RA a} (RA @@ (@proj1_sig A (Proper RA))).
Proof.
  unfold RelCompFun, Proper.
  split ; red.
  - apply proj2_sig.
  - intros.
    now symmetry.
  - intros x y z H1 H2.
    etransitivity; eassumption.
Qed.

Existing Instance respectful_per.

Program Definition quot_map2
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  {C : Type} {RC : relation C} `{! Equivalence RC}
  (f : A -> B -> C)
  `{e : Proper _ (RA ==> RB ==> RC) f}
  (a : quot RA) (b : quot RB) : quot RC :=
  quot_rec (fun a' => quot_rec (fun b' => to_quot (f a' b')) (p := _) b)
    (p := _) a.
Next Obligation.
  intros.
  unfold Proper, respectful.
  intros.
  now apply quot_ext, e.
Qed.
Next Obligation.
  intros.
  unfold Proper, respectful.
  intros.
  pattern b ; apply quot_ind ; intros b'.
  rewrite !quot_rec_eq.
  now apply quot_ext, e.
Qed.

Lemma quot_map2_eq
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  {C : Type} {RC : relation C} `{! Equivalence RC}
  (f : A -> B -> C)
  `{e : Proper _ (RA ==> RB ==> RC) f}
  : forall a b, quot_map2 f (to_quot a) (to_quot b) = to_quot (f a b).
Proof.
  intros.
  unfold quot_map2.
  now rewrite !quot_rec_eq.
Qed.
(** * domains.basics: basic definitions *)
From Stdlib Require Import Morphisms Relations RelationClasses.
Require Import tactics.


(** ** Equalities *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y
  := match p with eq_refl => u end.

Arguments transport {A}%_type_scope P%_function_scope {x y} p u : simpl nomatch.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression. *)
Notation "p # u" := (transport _ p u) (at level 55, u at next level, only parsing).

Lemma transport_const {A B} {x y : A} {e : x = y} (b : B) :
  transport (fun _ => B) e b = b.
Proof.
  destruct e ; reflexivity.
Qed.

(*
(** ** Lemmas for working with [iffT] *)
Lemma arrowTE: CMorphisms.Proper (iffT ==> iffT ==> iffT) arrow.
Proof. move=>A A' e B B' f; split; move=>p a; apply f, p, e, a. Defined.

Definition allT {A} (f: A -> Type) := forall a, f a.
Definition pointwise_crelation {A B} (R: crelation B): crelation (A -> B) := fun f g => forall a, R (f a) (g a).
Lemma allTE {A}: CMorphisms.Proper (@pointwise_crelation A _ iffT ==> iffT) allT.
Proof. move=>f g fg; split; move=>Hf x; apply fg, Hf. Defined.
Lemma allTE' {A B} (f: A -> Type) (g: B -> Type):
  iffT A B -> (forall a b, iffT (f a) (g b)) -> iffT (allT f) (allT g).
Proof. move=>ab fg; split; move=>H x; unshelve eapply fg, H; apply ab, x. Qed.

Lemma sigTE {A}: CMorphisms.Proper (pointwise_crelation iffT ==> iffT) (@sigT A).
Proof. move=>f g fg; split; move=>[x H]; exists x; apply fg, H. Defined.
Lemma sigTE' {A B} (f: A -> Type) (g: B -> Type):
  iffT A B -> (forall a b, iffT (f a) (g b)) -> iffT (sigT f) (sigT g).
Proof. move=>ab fg; split; move=>[x H]; (unshelve eexists; [apply ab, x|eapply fg, H]). Qed.

Lemma iffT_hyp {A A' B}: (iffT A A') -> (A' -> B) -> A -> B.
Proof. move=>[+ _]; auto. Qed.
*)

(** ** H-propositions *)

Class ProofIrrel (T : Type) := proof_irrel : forall x y : T, x = y.
Global Hint Mode ProofIrrel ! : typeclass_instances.

(** Option *)

Definition option_bind {A B} (f : A -> option B) : option A -> option B :=
  fun x =>
  match x with
  | None => None
  | Some a => f a
  end.

(** Unit *)

Lemma unit_ext (x y : unit) : x = y.
Proof (match x, y with | tt, tt => eq_refl end).

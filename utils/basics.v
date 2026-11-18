(** * Basics: definitions used by the axioms in [axioms.v] *)

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

(** ** H-propositions *)

Class ProofIrrel (T : Type) := proof_irrel : forall x y : T, x = y.
Global Hint Mode ProofIrrel ! : typeclass_instances.

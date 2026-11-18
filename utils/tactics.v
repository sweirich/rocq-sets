(** * Domains.Tactics: utility tactics *)

(** ** Hints *)

(** Solves the following issue: [Hint Extern]'s patterns only match syntactically:
  contrarily to the standard [Instances] it does not try to reduce at all before
  matching. *)
Hint Extern 500 => (progress (cbn beta delta zeta iota)) : typeclass_instances.

#[global]Hint Unfold notT: core.
#[global] Hint Resolve eq_refl eq_sym : core.
#[global] Hint Constructors and : core. 
#[global]Hint Extern 10 =>
  match goal with
    | H : False |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : ~ _ |- False => apply H
  end : core.

(** ** Automation *)

#[global] Ltac easy ::= solve [eauto 3 with core relations].

#[global] Ltac Tauto.intuition_solver ::= auto.

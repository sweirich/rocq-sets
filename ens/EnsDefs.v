(* EnsDefs.v: Aczel-style set-theoretic operations on Ens that
   aren't part of the base zfc library. Notation-free; see
   EnsNotation.v for ens_scope syntax. *)

Require Import Sets.
Require Import Axioms.
Require Import Cartesian.
Require Import Omega.

(* [Ens] is now universe polymorphic (so [Hierarchy.v] can reuse it for
   the "small sets").  This quotient/library layer, however, only ever
   works at a single universe.  We pin [Ens] to one shared monomorphic
   universe [ulib] for the whole [lib]/[timbda] development so that every
   occurrence lands in the same universe — in particular the invariant
   positions ([exists a : Ens, …], [eq] on [Ens]) that cumulativity alone
   cannot reconcile.  The notation is re-exported through [EnsNotation]. *)
Monomorphic Universe ulib.
Notation Ens := Ens@{ulib}.



(** Indexed union: iUnion E F = ∪_{x ∈ E} F(x), using the Aczel
    decomposition of [E] directly. *)

Definition iUnion (E : Ens) (F : Ens -> Ens) : Ens :=
  match E with
  | sup IE fE => Union (sup IE (fun a => F (fE a)))
  | _ => Vide
  end.


(** Binary union: BinUnion E E' = ⋃ {E, E'}. *)

Definition BinUnion (E E' : Ens) : Ens := Union (Paire E E').

(** Binary intersection: A ∩ B = { x ∈ A | x ∈ B }. *)

Definition BinInter (A B : Ens) : Ens := Comp A (fun x => IN x B).

(** Dependent product of sets: [Pi A B] is the set of total functional
    graphs [f] from [A] into [⋃B] with [f(a) ∈ B(a)] for every [a ∈ A].

    Built ZF-style: separate the power-set of [A × ⋃B] down to subsets
    that are total ([forall a ∈ A, exists b ∈ B a, ⟨a,b⟩ ∈ f]) and
    functional ([⟨a,b1⟩, ⟨a,b2⟩ ∈ f ⇒ b1 ≃ b2]). *)

Definition Pi (A : Ens) (B : Ens -> Ens) : Ens :=
  Comp (Power (Prod A (iUnion A B)))
       (fun f =>
          (forall a, IN a A ->
              exists b, IN b (B a) /\ IN (Couple a b) f)
          /\ (forall a b1 b2,
                IN (Couple a b1) f -> IN (Couple a b2) f -> EQ b1 b2)).


(** Projections of the primitive couple [pair a b] (the [Couple] of
    [Cartesian.v]).  Off a couple they return the empty set. *)

Definition is_subsingleton (x : Ens) : Prop :=
  forall y z : Ens, IN y x -> IN z x -> EQ y z.

Definition is_nonempty (x : Ens) : Prop :=
  exists y : Ens, IN y x.

Definition pfst (p : Ens) : Ens :=
  match p with pair a _ => a | _ => Vide end.

Definition psnd (p : Ens) : Ens :=
  match p with pair _ b => b | _ => Vide end.


(** Pair-pattern variant of [iUnion]: bind the [pfst] / [psnd] of
    the iterated element. *)

Definition iUnion_pat (E : Ens) (F : Ens -> Ens -> Ens) : Ens :=
  iUnion E (fun p => F (pfst p) (psnd p)).


(** Triple projections: [⟨ a , b , c ⟩ = ⟨ a , ⟨ b , c ⟩ ⟩]. *)

Definition proj1 (t : Ens) : Ens := pfst t.
Definition proj2 (t : Ens) : Ens := pfst (psnd t).
Definition proj3 (t : Ens) : Ens := psnd (psnd t).


(** Relational domain, range, image.

    A relation [r] is a set of ordered pairs. The domain is the set
    of first components, the range is the set of second components,
    and the image of [S] under [r] is [{ b | ∃ a ∈ S, ⟨a,b⟩ ∈ r }].
    A couple is memberless, so its components are not reached by
    [Union]; the ambient set is instead the replacement
    [⋃_{p ∈ r} {pfst p}] / [⋃_{p ∈ r} {psnd p}], and the [Comp]
    predicate does the real work. *)

Definition dom (r : Ens) : Ens :=
  Comp (iUnion r (fun p => Sing (pfst p)))
       (fun a => exists b : Ens, IN (Couple a b) r).

Definition rng (r : Ens) : Ens :=
  Comp (iUnion r (fun p => Sing (psnd p)))
       (fun b => exists a : Ens, IN (Couple a b) r).

Definition image (r S : Ens) : Ens :=
  Comp (rng r)
       (fun b => exists a : Ens,
                   IN a S /\ IN (Couple a b) r).


(** Naturals.

    [natZ n] is [Nat n] (defined in Omega.v); [natSet] is [Omega]
    (already a notation [ω] in Notation.v). *)

Definition natZ (n : nat) : Ens := Nat n.


(** Identity relation on ω: [natId = { ⟨a,a⟩ | a ∈ ω }]. *)

Definition natId : Ens := iUnion Omega (fun n => Sing (Couple n n)).

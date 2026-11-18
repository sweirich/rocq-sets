(* zf/quot/ZFDefs.v

   Definitions of the set-theoretic *structures* used throughout the
   development, expressed purely in terms of [ZFSet] and the core operations
   lifted from [EnsDefs] (re-exported here through [ZFSetCore]):

     [Empty]  [Omega]  [Sing]  [Paire]  [Couple]  [Union]
     [In]  [Inc]  [Comp]  [iUnion]  [Power]  [Prod]  [pfst]  [psnd]
     [isFunction]  [Pi]  [dom]  [rng]  [image]  [applyFun]  ...

   This file collects *only* definitions — no lemmas.  Besides the core
   operations (available via the export of [ZFSetCore]), it gathers the
   derived structures that are otherwise scattered across the development:

     - [Sig]                  (dependent sum;     see [Lang.PredF])
     - [ParPi]                (partial functions; see [Timbda.Parametricity])
     - [IsDiag] [diag]                            (see [lib.Diagonal])
     - [pFun] [pIdFun]                            (see [lib.Diagonal])

   so the families of operations can be read in one place. *)

Require Export ZFSetCore.
From Stdlib Require Import Logic.Epsilon.

(* This file is deliberately notation-free: every definition is written
   directly with the core [ZFSet] operations ([Sing], [Couple], [iUnion],
   [Comp], [Power], [Prod], [In], [Inc], ...) rather than the [ZFNotation]
   surface syntax.  For readability, the [ZFNotation] form of each body is
   shown in a [notation:] comment immediately above the definition. *)

(* ================================================================== *)
(** * Function predicate. *)
(* ================================================================== *)

(** [isFunction f]: the relation [f] is single-valued — each input is
    paired with at most one output.  This is the functional clause of the
    [Pi] comprehension, named as a standalone predicate so that (e.g.) the
    [Elam] arm of [eval] can separate the function values it builds. *)
Definition isFunction (f : ZFSet) : Prop :=
  forall a b1 b2, In (Couple a b1) f -> In (Couple a b2) f -> b1 = b2.

(* ================================================================== *)
(** * Total function space. *)
(* ================================================================== *)

(** [Pi A B] is the set of total functional graphs [f] from [A] into
    [⋃B] with [f a ∈ B a].  Built ZF-style: separate the power set of
    [A × ⋃B] down to the subsets that are total and functional.
    Equality on [ZFSet] is Leibniz [=], so the functionality clause is
    just [b1 = b2].  (The functional clause is spelled out with the core
    operations rather than [isFunction], so the [ZFSetFacts] proofs may
    destruct it directly.) *)
(* notation:  Π[ a ∈ A ] B a *)
Definition Pi (A : ZFSet) (B : ZFSet -> ZFSet) : ZFSet :=
  Comp (Power (Prod A (iUnion A B)))
       (fun f =>
          (forall a, In a A -> exists b, In b (B a) /\ In (Couple a b) f)
          /\ (forall a b1 b2,
                In (Couple a b1) f -> In (Couple a b2) f -> b1 = b2)).

(* TODO: use set=theoretic function for B, don't have to pass in 
   set for A? *)
(*
Definition Pi' (AB : ZFSet) : ZFSet := 
    Comp (Power AB)
         (fun ab => ab = ⟨a,b⟩  ) *)

(* ================================================================== *)
(** * Subsingleton / nonempty predicates. *)
(* ================================================================== *)

(** [X] is a *subsingleton* when all its members are equal. *)
(* notation:  forall y z, y ∈ X -> z ∈ X -> y = z *)
Definition is_subsingleton (X : ZFSet) : Prop :=
  forall y z : ZFSet, In y X -> In z X -> y = z.

(** [X] is *nonempty* when it has a member. *)
(* notation:  exists y, y ∈ X *)
Definition is_nonempty (X : ZFSet) : Prop :=
  exists y : ZFSet, In y X.

(* ================================================================== *)
(** * Binary union and intersection. *)
(* ================================================================== *)

(** Binary union [E ∪ E' = ⋃ {E, E'}]. *)
(* notation:  Union {| E ; E' |} *)
Definition BinUnion (E E' : ZFSet) : ZFSet := Union (Paire E E').

(** Binary intersection [A ∩ B = { x ∈ A | x ∈ B }]. *)
(* notation:  ⦃ x ∈ A | x ∈ B ⦄ *)
Definition BinInter (A B : ZFSet) : ZFSet :=
  Comp A (fun x => In x B).

(* ================================================================== *)
(** * Couple-pattern unions and triple projections. *)
(* ================================================================== *)

(** Pair-pattern variant of [iUnion]: bind [pfst] / [psnd] of each
    iterated element.  ([pfst]/[psnd] are the projections of the primitive
    couple, lifted in [ZFSetCore].) *)
(* notation:  p ← E ;; F (pfst p) (psnd p) *)
Definition iUnion_pat
  (E : ZFSet) (F : ZFSet -> ZFSet -> ZFSet) : ZFSet :=
  iUnion E (fun p => F (pfst p) (psnd p)).

(** Triple projections: [⟨ a , b , c ⟩ = ⟨ a , ⟨ b , c ⟩ ⟩]. *)
(* notation:  pfst t  /  pfst (psnd t)  /  psnd (psnd t) *)
Definition proj1 (t : ZFSet) : ZFSet := pfst t.
Definition proj2 (t : ZFSet) : ZFSet := pfst (psnd t).
Definition proj3 (t : ZFSet) : ZFSet := psnd (psnd t).

(** Triple-pattern variant of [iUnion]: bind [proj1] / [proj2] / [proj3]
    of each iterated element. *)
(* notation:  t ← E ;; F (proj1 t) (proj2 t) (proj3 t) *)
Definition iUnion_pat3
  (E : ZFSet) (F : ZFSet -> ZFSet -> ZFSet -> ZFSet) : ZFSet :=
  iUnion E (fun t => F (proj1 t) (proj2 t) (proj3 t)).

(* ================================================================== *)
(** * Relational domain, range, image. *)
(* ================================================================== *)

(** A relation [r] is a set of ordered pairs.  [dom r] collects the
    first components, [rng r] the second, and [image r S] the second
    components of pairs whose first component lies in [S].  A couple is
    memberless, so its components are not reached by [Union]; the ambient
    set is the replacement [⋃_{p ∈ r} {pfst p}] (resp. [{psnd p}]), and the
    [Comp] predicate does the real work. *)
(* notation:  ⦃ a ∈ (p ← r ;; {| pfst p |}) | exists b, ⟨ a , b ⟩ ∈ r ⦄ *)
Definition dom (r : ZFSet) : ZFSet :=
  Comp (iUnion r (fun p => Sing (pfst p)))
       (fun a => exists b : ZFSet, In (Couple a b) r).

(* notation:  ⦃ b ∈ (p ← r ;; {| psnd p |}) | exists a, ⟨ a , b ⟩ ∈ r ⦄ *)
Definition rng (r : ZFSet) : ZFSet :=
  Comp (iUnion r (fun p => Sing (psnd p)))
       (fun b => exists a : ZFSet, In (Couple a b) r).

(* notation:  ⦃ b ∈ rng r | exists a, a ∈ S /\ ⟨ a , b ⟩ ∈ r ⦄ *)
Definition image (r S : ZFSet) : ZFSet :=
  Comp (rng r)
       (fun b => exists a : ZFSet, In a S /\ In (Couple a b) r).

(** The unique member of a singleton, by Hilbert choice: [theOf {| b |} = b].
    (Formerly [Union {| b |}], which is wrong for an atom or couple [b]:
    the union of a singleton is a *set*.) *)
Definition theOf (S : ZFSet) : ZFSet := epsilon (inhabits Empty) (fun b => In b S).

(** Set-theoretic function application: [applyFun f v] is the [b] with
    [⟨v,b⟩ ∈ f], chosen by Hilbert's [epsilon].  When [f] is functional and
    [v ∈ dom f] this is the unique output ([applyFun_edge]). *)
(* notation:  epsilon (fun b => ⟨ v , b ⟩ ∈ f) *)
Definition applyFun (f v : ZFSet) : ZFSet :=
  epsilon (inhabits Empty) (fun b => In (Couple v b) f).

(* ================================================================== *)
(** * Identity relation on the naturals. *)
(* ================================================================== *)

(** [natId = { ⟨a,a⟩ | a ∈ ω }], the identity relation on [Omega]. *)
(* notation:  n ← Omega ;; {| ⟨ n , n ⟩ |} *)
Definition natId : ZFSet := iUnion Omega (fun n => Sing (Couple n n)).

(* ================================================================== *)
(** * Dependent sum. *)
(* ================================================================== *)

(** The dependent sum [Σ_{a ∈ A} B a], realised as the set of couples
    [⟨a, b⟩] with [a ∈ A] and [b ∈ B a].  This is the denotation of an
    existential: a witness paired with a value of the instantiated body. *)
(* notation:  a ← A ;; b ← B a ;; {| ⟨ a , b ⟩ |} *)
Definition Sig (A : ZFSet) (B : ZFSet -> ZFSet) : ZFSet :=
  iUnion A (fun a => iUnion (B a) (fun b => Sing (Couple a b))).

(* ================================================================== *)
(** * Partial functions (the predicative function space). *)
(* ================================================================== *)

(** [ParPi A B]: the *partial* functions from [A] to [B] — the
    single-valued subsets of the product [A × ⋃_{a∈A} B a].  Unlike [Pi],
    the totality requirement is dropped. *)
(* notation:  ⦃ f ∈ Power (Prod A (a ← A ;; B a)) | isFunction f ⦄ *)
Definition ParPi (A : ZFSet) (B : ZFSet -> ZFSet) : ZFSet :=
  Comp (Power (Prod A (iUnion A B))) isFunction.

(* ================================================================== *)
(** * Diagonal relations and the partial-identity type universe. *)
(* ================================================================== *)

(** A relation [R] is *diagonal* when every element is its own diagonal
    pair ⟨psnd p, psnd p⟩. *)
(* notation:  forall p, p ∈ R -> p = ⟨ psnd p , psnd p ⟩ *)
Definition IsDiag (R : ZFSet) : Prop :=
  forall p, In p R -> p = Couple (psnd p) (psnd p).

(** The diagonal of a set [S]: the identity relation [{⟨a,a⟩ : a ∈ S}]. *)
(* notation:  a ← S ;; {| ⟨ a , a ⟩ |} *)
Definition diag (S : ZFSet) : ZFSet := iUnion S (fun a => Sing (Couple a a)).

(** The partial functions from [A] to [B]: the single-valued
    ([isFunction]) subsets of the product [A × B]. *)
(* notation:  ⦃ G ∈ Power (Prod A B) | isFunction G ⦄ *)
Definition pFun (A B : ZFSet) : ZFSet :=
  Comp (Power (Prod A B)) (fun G => isFunction G).

(** The partial *identity* functions on [A]: the subsets of the diagonal
    [diag A].  (A subset of the diagonal is automatically single-valued.) *)
(* notation:  Power (diag A)  (no special syntax) *)
Definition pIdFun (A : ZFSet) : ZFSet := Power (diag A).


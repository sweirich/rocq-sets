(** * ZFSets.v — umbrella for the quotient set theory.

    The [zf] library is built in layers:

      - [zf/quot/ZFSetCore.v] — the quotient construction and the
        *Ens-lifted* interface (definitions and lemmas proved by descending
        to the underlying [Ens] representation; the only layer that unfolds
        [mk]);

      - [zf/quot/ZFSetFacts.v] — the *pure* ZFSet theory, reasoning only
        through the core interface, plus the [zf_reduce] step-tactic
        infrastructure;

      - [zf/quot/ZFDefs.v], [ZFNotation.v] — derived-structure definitions
        and notation;

      - [zf/quot/{Diagonal,Projections,PiFacts}.v] — further derived
        constructions (diagonals, projections, Π-facts).

    This file is the *single* module that code outside [zf] should import:
    [Require Import ZFSets] re-exports the whole public surface, so
    downstream files never need to name the individual submodules.

    (The internal [zf/quot] files must NOT import this umbrella — that would
    cycle, since [ZFSets] re-exports them; they import [ZFSetFacts] and the
    lower layers directly.)

    One layer is deliberately left out: [zf/quot/Universes.v], the universe
    tower [U0 ∈ U1] and its closure theory.  It sits *above* this umbrella
    (it imports it), so requiring [ZFSets] gives the set theory without
    committing to a universe; a file that wants [U0] / [smallId] / [U1] adds

        Require Import Universes.

    which is what [lib/universe.v]'s witness [LambdaSetBig] does.  Code
    written against the [UNIVERSE] / [UNIVERSE1] signatures never needs it. *)

Require Export ZFSetCore.
Require Export ZFDefs.
Require Export ZFNotation.
Require Export ZFSetFacts.
Require Export Foundation.
Require Export Diagonal.
Require Export Projections.
Require Export PiFacts.

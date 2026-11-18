# rocq-sets

A Rocq library of ZF-style set theory, built as a quotient of Aczel's
type-theoretic encoding of sets. It provides a type `ZFSet` whose equality is
Rocq's ordinary (Leibniz) `=`, the usual set-formers and their laws, a theory
of functions as sets of pairs, and a tower of Grothendieck universes
`U0 ∈ U1` for interpreting types as sets.

## Values: sets, atoms and pairs

The underlying representation is the `Ens` type of
[`sweirich/zfc`](https://github.com/sweirich/zfc), a fork of Benjamin Werner's
ZFC development included here as the `zfc/` submodule. Besides sets, `Ens` has
two other kinds of values:

- **atoms** `atom n` for natural numbers, and
- **primitive pairs** `pair a b`.

Neither has members, and values of different kinds are never equal. So
numerals are not sets (and in particular not functions), and the components of
a pair are read off directly instead of being decoded from a set encoding. See
the fork's `ATOMS_AND_PAIRS.md` for details.

## Layers

| Directory | Contents |
|---|---|
| `zfc/` | (submodule) `Ens`, extensional equality `EQ`, membership `IN`, and the basic set-formers: empty set, pairing, union, separation, power set, products, `Omega`; the small-sets hierarchy in `Hierarchy.v`. |
| `utils/` | The axioms the library uses (see below); `utils/axioms.v` is the entry point. |
| `ens/` | Further operations on `Ens`: binary union and intersection, indexed union, the dependent function space `Pi`, domain and range, pair projections, natural numbers; their setoid instances and laws. |
| `quot/` | The quotient `ZFSet := Ens / EQ` and the theory built on it. |

Within `quot/`:

- `ZFSetCore.v` defines `ZFSet` and lifts each `Ens` operation to it. It is
  the only file that works with the representation directly.
- `ZFSetFacts.v` develops the theory abstractly, through the interface of
  `ZFSetCore.v`: functions (`Pi`, `applyFun`), images and ranges, iterated
  unions, smallness lemmas, and the `zf_reduce` tactic.
- `ZFDefs.v` and `ZFNotation.v` collect the derived definitions and the
  `zf_scope` notations (`∈`, `⊆`, `⟨a, b⟩`, `{| a |}`, `⦃ x ∈ E | P ⦄`, `∪`,
  `∩`, `x ← E ;; F`, …).
- `Foundation.v`: membership (together with "is a component of a pair") is
  well-founded, so no value contains itself.
- `Projections.v`: `FST`/`SND` on sets of pairs, defined by well-founded
  recursion.
- `Diagonal.v`, `PiFacts.v`: lemmas about diagonal relations and function
  graphs.
- `Universes.v`: the Grothendieck universes `U0 ∈ U1` and the lemmas that each
  is closed under the set-formers.

## Using the library

The logical name of the library is `zf`.

```coq
Require Import zf.ZFSets.            (* the set theory: re-exports quot/ *)
Require Import zf.quot.Universes.    (* the universes U0 and U1 (not re-exported) *)
```

## Axioms

Besides the Rocq kernel, the library uses:

- propositional extensionality and function extensionality,
- quotient types, postulated in `utils/axioms.v` (an axiomatization due to
  Meven Lennon-Bertrand),
- Hilbert's epsilon (`Stdlib.Logic.Epsilon`), used to pick a representative
  of a `ZFSet` (`repr`) and in a few definitions such as `applyFun`.
  Together with the extensionality axioms it implies excluded middle, so
  the development is classical, though no proof uses excluded middle
  directly.

The `zfc/` core itself uses no axioms.

## Building

Requirements: Rocq 9.0 and `rocq-stdlib`.

```sh
git clone --recurse-submodules https://github.com/sweirich/rocq-sets
cd rocq-sets
make
```

For an existing clone, run `git submodule update --init` first.

## Installing with opam

The library is packaged as `rocq-sets` (`rocq-sets.opam`). It is not in an
opam repository; install it by pinning the git repository:

```sh
opam pin add rocq-sets git+https://github.com/sweirich/rocq-sets.git
```

or, from a local clone (with the `zfc` submodule checked out),

```sh
opam pin add rocq-sets .
```

This installs the library under the logical name `zf` in Rocq's
`user-contrib`, so a project can `Require Import zf.ZFSets` without a
`-R`/`-Q` flag for it. `make install` does the same without opam.

## License

MIT (see `LICENSE`), with two exceptions:

- `zfc/` (the submodule) is LGPL-2.1 or later, like the original ZFC
  contribution.
- `utils/` is adapted from code by Meven Lennon-Bertrand in the
  [`domains`](https://github.com/sweirich/domains) development and is
  distributed under that project's BSD-3-Clause license (see
  `utils/LICENSE`).

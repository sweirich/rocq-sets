# Use of AI in this library

This library was developed by Stephanie Weirich in 2026 with Claude, an AI
model by Anthropic, used through Claude Code. The work was directed by the
author. Claude wrote most of the Rocq code and comments.

## What was AI-assisted

- **`ens/`, `quot/` and `ZFSets.v`.** The library was developed as part of a
  larger project (a set-theoretic semantics for a functional logic language)
  and extracted from it for this repository. In that project's history, from
  2026-06-22 to 2026-11-16, 33 of the 36 commits that touched these files
  record a Claude model as co-author: Claude Opus 4.8, Claude Opus 5,
  Claude Opus 5.5, Claude Fable 5.1 and Claude Fable 5.2. The first of these
  commits imported the files from an earlier repository, whose history is not
  included here.
- **The `zfc/` submodule.** See `AI_USE.md` in
  [`sweirich/zfc`](https://github.com/sweirich/zfc).
- **This repository's structure and documentation:** extracting the library,
  `README.md` and this file were done with Claude Opus 5.5 (2026-11-18).

## Code from elsewhere

- **`utils/`** is adapted from the `theories/utils` directory of the
  [`domains`](https://github.com/sweirich/domains) development, trimmed to
  what this library needs. It was written by Meven Lennon-Bertrand, not as
  part of this work.

## Checking

Every proof is checked by Rocq. The library postulates quotient types and uses
propositional extensionality, function extensionality and Hilbert's epsilon
(see `README.md`). No lemma is admitted. Since Rocq checks the proofs, they do
not depend on trusting the AI. What does depend on review is that the
definitions and the statements of the theorems say what is intended.

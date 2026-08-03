# Potkin 3

`potkin3` is the Lean 4 foundation for Potkin. Milestones P3-0 and P3-1 deliberately
contain a small, proof-producing vertical slice rather than a port of the
whole Racket workbench or the whole `nonmonlogics` development.

The three related repositories have different jobs:

- **`potkin3`** is the clean Lean development. It defines the language,
  nonempty whole-hypersequent boundaries, fully instantiated local
  occurrences, arbitrary material bases, finite equipped presentations,
  checked derivations, and an occurrence-decorated open CK carrier. Its P3-0
  example is anonymous and has only nullary, unary, and binary occurrences.
- **`potkin`** is the executable Racket research workbench and the operational
  reference at commit
  `c0f74a38cb06e088936b7cc0440621b364349b2e`. It remains the reference for the
  larger context, cut-witness, Hopf-algebra, revision, repair, recurrence, and
  reporting APIs. `potkin3` does not modify or wrap it.
- **`nonmonlogics`** is the earlier verified Lean research development and the
  proof-engineering reference at commit
  `713a809b14ccae5baeaa3d64e0d0ccec21085534`. P3-0 reuses and generalises
  selected declaration shapes and proof patterns, but does not import that
  repository as a dependency.

The Lean toolchain is `leanprover/lean4:v4.29.0-rc1`; Mathlib is pinned to
`378b908c009ef82cf9584cba7447c44a5a89e58a`, matching the source development.

## What P3-1 verifies

The library implements the following route:

```text
finite equipped presentation
  -> anonymous raw candidate
  -> checked complete derivation
  -> occurrence-decorated open CK tree
  -> arbitrary-depth finite prefix-free CK cut
  -> lexicographic address-indexed detached tuple and forest image
  -> retained typed punctures
  -> distinguished typed filling that leaves old punctures alone
  -> exact reconstruction
  -> realised-open detached/remainder closure
```

In particular, the declarations prove that:

- checking resolves every node ID through one finite registry and checks exact
  arity and every ordered whole-hypersequent premise boundary;
- checked constructors are private, so fixtures and clients obtain checked
  derivations only from successful executable checking;
- supplied incidence profiles enumerate each exact component multiset and
  retain separate local slots for equal displayed occurrences;
- a checked root conclusion is its type index;
- every recursive cut address exists, is nonroot and ordinary, and distinct
  sites are genuinely prefix-incomparable;
- each selected puncture requires exactly the boundary of its corresponding
  detached root;
- a computationally new puncture occurs exactly at one selected site, while
  every old puncture outside the detached regions remains at its old address;
- filling the retained component with the address-aligned detached family
  reconstructs the source tree;
- degree partitions between the retained remainder and every addressed
  detached occurrence;
- the constructor-recursive cut enumerator is sound, complete for intrinsic
  witnesses, and duplicate-free as a structural witness list;
- every independent finite valid nonroot vertex antichain constructs a cut
  with exactly that address finset and occurs in the enumeration;
- exact-presentation local admission is hereditary to detached factors and
  retained open remainders;
- a `BaseHom` maps equipped presentations and checked derivations while
  realization, and therefore decoration erasure, is unchanged;
- flattening root components can identify a connected proof of `S | T` with
  the forest of separate `S` and `T` proofs, while the block-root projection
  distinguishes them by connected-factor cardinality.

The P3-0 fixture is in `Potkin/Examples/Anonymous.lean`; the P3-1 running-tree,
open-source, invalid-address, and duplicate-occurrence fixtures are in
`Potkin/Examples/RecursiveCut.lean`. They test the generic representation and
are not a featured logic or calculus.

## Build

From the repository root:

```text
lake build
```

The aggregate import is `Potkin.lean`. The intended audit also searches the
new source for `sorry`, `admit`, custom axioms, `unsafe`, and accidental
`native_decide`; P3-0 and P3-1 are designed to require none of them.

## Scope boundary

P3-1 does **not** claim a full CK coproduct, coefficient collection,
coassociativity, counit, antipode, tensor algebra, constructor deletion,
revision calculus, automatic repair, protected defects, recurrence, focusing,
proof search, GL/Oudom/pre-Lie structure, Sandqvist IPL, normalization, cut
elimination, proof quotients, or parity with either source repository.

`RootCut` remains the P3-0 immediate-root API. `CKCut` is the separate P3-1
recursive occurrence-witness layer and includes the empty cut, but introduces
no linear combinations, tensor endpoints, or coproduct. See
`SEMANTIC_CONTRACT.md` for the conventions fixed for those later layers and
`MIGRATION_LEDGER.md` for declaration-level provenance.

The current dependent representation does not yet prove that equality of two
address finsets forces structural equality of transported `CKCutPlan` values.
Accordingly, duplicate-freedom is claimed for intrinsic witnesses, not for the
enumeration after forgetting each witness to only its address list.

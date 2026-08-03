# Potkin 3

`potkin3` is the Lean 4 foundation for Potkin. Milestone P3-0 deliberately
contains a small, proof-producing vertical slice rather than a port of the
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

## What P3-0 verifies

The library implements the following route:

```text
finite equipped presentation
  -> anonymous raw candidate
  -> checked complete derivation
  -> occurrence-decorated open CK tree
  -> one nonempty two-site proper root cut
  -> site-indexed detached tuple and commutative forest image
  -> retained typed punctures
  -> typed filling
  -> exact reconstruction
```

In particular, the declarations prove that:

- checking resolves every node ID through one finite registry and checks exact
  arity and every ordered whole-hypersequent premise boundary;
- checked constructors are private, so fixtures and clients obtain checked
  derivations only from successful executable checking;
- supplied incidence profiles enumerate each exact component multiset and
  retain separate local slots for equal displayed occurrences;
- a checked root conclusion is its type index;
- the two binary cut addresses exist, are nonroot, and are genuinely
  prefix-incomparable;
- each selected puncture requires exactly the boundary of its corresponding
  detached root;
- filling the retained component with the address-aligned detached family
  reconstructs the source tree;
- a `BaseHom` maps equipped presentations and checked derivations while
  realization, and therefore decoration erasure, is unchanged;
- flattening root components can identify a connected proof of `S | T` with
  the forest of separate `S` and `T` proofs, while the block-root projection
  distinguishes them by connected-factor cardinality.

The executable fixture is in `Potkin/Examples/Anonymous.lean`. It is a test of
the generic representation, not a featured logic or calculus.

## Build

From the repository root:

```text
lake build
```

The aggregate import is `Potkin.lean`. The intended audit also searches the
new source for `sorry`, `admit`, custom axioms, and `unsafe`; P3-0 is designed
to require none of them.

## Scope boundary

P3-0 does **not** claim a full CK coproduct, coefficient collection,
coassociativity, counit, antipode, tensor algebra, constructor deletion,
revision calculus, automatic repair, protected defects, recurrence, focusing,
proof search, GL/Oudom/pre-Lie structure, Sandqvist IPL, normalization, cut
elimination, proof quotients, or parity with either source repository.

The cut implementation is intentionally restricted to nonempty selections of
ordinary immediate children of one positive root. Recursive prefix-free cuts
at arbitrary depth belong to a later milestone. See `SEMANTIC_CONTRACT.md` for
the conventions already fixed for those later layers and `MIGRATION_LEDGER.md`
for declaration-level provenance.

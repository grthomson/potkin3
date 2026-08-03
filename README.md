# Potkin 3

`potkin3` is the Lean 4 foundation for Potkin. Milestones P3-0 through P3-2 deliberately
contain a small, proof-producing vertical slice rather than a port of the
whole Racket workbench or the whole `nonmonlogics` development.

This commit completes P3-2 Phases A--C and the strict independent-insertion
part of Phase D. Its nested-cut layer is intentionally partial: actual
transported-region/factor equivalence, sequential-root equality, genuine
two-stage filling from the final root, and iterated finite-schedule coherence
remain documented proof obligations.

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

## What P3-2 verifies

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
  -> arbitrary admitted filling and typed puncture insertion
  -> source-addressed two-stage cut transport and ranked hierarchy data
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
- a material base is indexed by the exact fully instantiated occurrence, so
  positive arity is allowed and equal boundaries do not alias different
  constructor IDs; the selected primitive formula fragment is explicit;
- `ExtensionalCKCut` is structurally equivalent to `ValidAddressCut`, has a
  canonical compiled recursive plan, duplicate-free public enumeration, and
  unique address-list validation;
- arbitrary boundary-compatible fillers preserve the source root and local
  admission, prefix their internal puncture addresses, preserve unrelated old
  punctures, and preserve completeness when source and fillers are complete;
- insertions at two prefix-incomparable typed punctures commute as literal
  decorated trees;
- two disjoint cuts are noncrossing exactly when their comparable cross-pairs
  do not exhibit both strict-prefix orientations; transport splits the second
  cut between the retained remainder and exact detached factors while keeping
  source and relative addresses;
- a globally ranked finite cut hierarchy has a canonical source frontier;
  separately, generic ordered address-segment append is independent of binary
  parenthesisation;
- flattening root components can identify a connected proof of `S | T` with
  the forest of separate `S` and `T` proofs, while the block-root projection
  distinguishes them by connected-factor cardinality.

The P3-0 fixture is in `Potkin/Examples/Anonymous.lean`; the P3-1 running-tree,
open-source, invalid-address, and duplicate-occurrence fixtures are in
`Potkin/Examples/RecursiveCut.lean`. P3-2 adds the exact material fixture in
`Potkin/Examples/MaterialBase.lean` and filling/coherence fixtures in
`Potkin/Examples/Coherence.lean`. They test the generic representation and are
not a featured logic or calculus.

## Build

From the repository root:

```text
lake build
```

The aggregate import is `Potkin.lean`. The intended audit also searches the
new source for `sorry`, `admit`, custom axioms, `unsafe`, and accidental
`native_decide`; P3-0 through P3-2 require none of them.

## Scope boundary

P3-2 does **not** claim a linear CK coproduct, coefficient collection,
coassociativity, counit, antipode, tensor algebra, constructor deletion,
revision calculus, automatic repair, protected defects, recurrence, focusing,
proof search, GL/Oudom/pre-Lie structure, Sandqvist IPL, normalization, cut
elimination, proof quotients, or parity with either source repository.

`RootCut` remains the P3-0 immediate-root API. The constructor-recursive
`CKCut` remains the internal compiled witness, while `ExtensionalCKCut` /
`ValidAddressCut` is the P3-2 public cut identity. Empty cuts are retained, but
no linear combinations, tensor endpoints, or coproduct are introduced. See
`SEMANTIC_CONTRACT.md` for the conventions fixed for those later layers and
`MIGRATION_LEDGER.md` for declaration-level provenance.

Direct equality of arbitrary legacy dependent `CKCutPlan` values remains an
awkward eliminator problem. P3-2 resolves identity at the correct public
level: one valid address antichain is one `ExtensionalCKCut`; compilation to a
plan is canonical, and the public enumeration deduplicates on this structural
address carrier before proving exact-once occurrence.

The Phase-D proof boundary is explicit. `ExactTwoStageRemainderCoherence`
names, but does not prove, literal equality of both sequential retained roots
with the canonical union-frontier remainder. The proved result gives exact
source/relative transport, a unique retained-or-detached destination for each
occurrence, common untyped interface presence at each canonical frontier
address, and separate local reconstruction laws. The source-occurrence
equivalence is only a label-preserving `Sum` swap of the two address families,
not an equality of actual transported detached trees. A ranked hierarchy
constructs a canonical frontier; the parenthesisation theorem separately
proves generic list-append associativity for supplied address segments and
does not connect a bracketing to hierarchy levels or an iterated cut schedule.
Those stronger claims still need a constructor-recursive remainder-composition
theorem.

Likewise, `sourceRegion_swap` is symmetry of a source-address classifier, not
identity of actual transported region components or maps, and its proof does
not use the noncrossing certificate. The current reconstruction laws rebuild
the retained and inside pieces separately and then refill the original
first-stage cut; they do not yet compose filling from the further-cut final
root. `noMixedOrientation` therefore currently supports rejection and the
rank-cycle diagnosis, not a full two-cut coherence theorem.

There is a separate dependent-provenance boundary for base transport. The
presentation and realised-component packages have identity/composition `HEq`
laws, and checked transport has exact identity/composition action on the full
occurrence-decorated realization. A direct `HEq` between transported and
source `CheckedDerivation` proof terms is not claimed: constructor congruence
still requires explicit casts across the presentation index.

## Manuscript correction exposed by P3-2

The two-cut noncrossing formula must explicitly include disjointness. For a
finite hierarchy, pairwise noncrossing alone is insufficient: the three
address families

```text
A = {(1,1), (3)}
B = {(1),   (2,1)}
C = {(2),   (3,1)}
```

force `A` below `B`, `B` below `C`, and `C` below `A`. P3-2 therefore defines
a hierarchy with one global rank respected by every comparable cross-pair.
This is the exact extra hypothesis used by its finite parenthesisation result.

# Potkin paper theorem ledger

This ledger compares the current Lean declarations with the labelled claims in
manuscript v56. It records theorem strength, hypotheses, and equality level; it
does not promote a fixture, an address calculation, or an unbuilt module to a
universal theorem.

Status vocabulary:

- **exact**: the stated manuscript-level mathematical content is proved for the
  represented carrier;
- **strengthened**: Lean proves the claim with more explicit provenance or a
  stronger equality;
- **partial**: some mathematical content is proved, but a named part of the
  manuscript statement is still absent;
- **pending**: no current built declaration proves the universal statement;
- **standard/address-only**: a supporting equality is proved, but it is not the
  theorem-level result with which it must not be confused.

## Equality and carrier boundary

The Lean carrier uses structural proof-presentation equality. A `CKTree` keeps
the exact occurrence decoration, ordered children, whole boundaries, instance
data, and supplied incidence. `CKComponent` and `CKForest` equality therefore
keep decorated trees and factor multiplicity; no quotient by proof equations or
commuting conversions is used.

`CheckedDerivation P G` is indexed by its presentation. A persistent base
inclusion produces a term under `P.mapBase f`, so this ledger does **not** claim
raw `CheckedDerivation` equality across base change. The stable comparison is
`CheckedDerivation.realize_mapBase`, equality of decorated `CKTree`
realizations, together with the equalities of `RealizedOpenComponent` packages
listed below. Coherent reindexing of equal displayed component occurrences is
also not implemented; their separate local indices are retained instead.

## Foundational manuscript definitions

| Manuscript item | Lean declarations | Status | Exact boundary |
|---|---|---|---|
| `def:concrete-occurrence`, Concrete rule occurrence | `OccurrenceKind`, `OccurrenceShape`, `LocalOccurrence`, `ComponentProfile`, `ComponentIncidence` in `Potkin/Occurrence.lean` | **partial/strengthened** | Constructor ID, kind, ordered whole-boundary premises, conclusion, instance data, and optional supplied component incidence are immutable data. Unknown incidence is distinct from known empty incidence. A dedicated formula-occurrence action and coherent component reindexing remain outside the formal interface. |
| `def:material-equipped`, Material base and equipped calculus | `PrimitiveFragment`, exact-occurrence `MaterialBase.Member`, `BaseHom`, `ProofTheory.Admits`, and `EquippedPresentation` | **strengthened** | Membership is indexed by the whole `LocalOccurrence`, so equal input/output profiles with different IDs do not alias. Positive arity is allowed. `BaseHom` transports membership evidence for the same occurrence; it has no operation that can rename, revise, delete, or substitute an occurrence. |
| `def:proof-tree`, Proof tree and puncture | `CheckedDerivation`, `CKTree`, `CKTree.PunctureAt`, `CKTree.IsComplete`, and realization | **partial/strengthened** | Checked proofs are calculus-relative and complete; open decorated trees have typed vacant slots, not vertices. Addresses are exact ordered premise paths. Lean deliberately uses strict presentation equality rather than the manuscript's stated isomorphism/reindexing quotient. |
| `def:filling`, Filling | `CKCut.fill`, `CKTree.PunctureAt.insert`, and `RealizedOpenComponent.fillOfCut` in `Potkin/GeneralFilling.lean` | **partial** | Cut-site-indexed and one-hole typed filling are exact, including admitted open fillers. The manuscript's global set-valued Cartesian product `Fill(R)` over every puncture of an arbitrary context is not packaged as a separate object. |
| `prop:context-composition-associativity` | `PunctureAt.insert_replacement`, `insertIncomparable_commutes`, and the two-stage `composedFilling` | **partial** | Prefix transport and the independent two-hole interchange are structural equalities, and the canonical two-stage composition reconstructs exactly. A single general simultaneous-context associativity theorem for arbitrary nested families is not yet packaged. |
| `def:linked-cut`, Address-indexed cut witness | `ValidAddressCut`, `ExtensionalCKCut`, `validAddressEquiv`, `toCut`, `detachedTuple`, and `remainder` | **strengthened** | A public cut is exactly one finite prefix-free nonroot address set. Compilation to the recursive plan is canonical. Public enumeration is duplicate-free and exact-once (`enumerate_nodup`, `count_enumerate_eq_one`), and validation is sound and unique. The addressed tuple is retained before forest projection. |

## `thm:linked-factorisation` clause ledger

### Clause (i): distinguished reconstruction — exact

`CKCut.fill_detached_reconstructs` and `CKCut.fill_originalDetached` prove
literal decorated-tree equality

```text
cut.fill cut.plan.detached = source
```

for every intrinsic cut. This is constructor-recursive reconstruction, not
finite agreement.

### Clause (ii): arbitrary compatible filling — strengthened

The following declarations in `Potkin/GeneralFilling.lean` establish the
calculus-relative result for arbitrary site-indexed open replacements:

- `CKCut.fill_rootBoundary` and `CKCut.fill_isOrdinary`;
- `CKCut.fill_locallyAdmitted` and `CKCut.fill_isComplete`;
- `CKCut.fill_fillerPuncture_prefixed` and
  `CKCut.fill_oldPuncture_preserved`;
- the exhaustive formula `CKCut.fill_punctureAt_iff`;
- `CheckedDerivation.fill_realize_isComplete` and
  `CheckedDerivation.fill_realize_locallyAdmitted`;
- `RealizedOpenComponent.fillOfCut_mapBase`.

The old-or-prefixed-new puncture formula is stronger than root and
completeness preservation alone. It also makes explicit that old punctures
inside a replaced region are removed, while unrelated old punctures remain.

### Clause (iii): exact two-stage coherence — strengthened

The Lean hypothesis is a `CanonicalTwoStageWitness first second`, whose
`Noncrossing` field requires both disjoint selected address sets and absence of
oppositely oriented strict-prefix pairs. The canonical combined cut is the
source-nearest frontier of the union. It is the literal union only when every
cross-pair is incomparable.

The proof is organized around source-address transport and constructor
decomposition:

- `CutAddressDestination.unique`, `CutTransport.canonical`,
  `transport_partition_unique`, `retainedAfter`, and `insideAfter` give the
  exclusive retained-or-detached destination and its source/relative address
  equation;
- `CanonicalThreeRegionDecomposition`, `middleTuple`, and `lowerTuple` retain
  the actual occurrence identities before forest collection;
- `firstToSecondMiddleEquiv` and `firstToSecondLowerEquiv`, with
  `firstToSecondMiddleEquiv_component` and
  `firstToSecondLowerEquiv_component`, give explicit schedule bijections and
  equality of the corresponding decorated components;
- `firstScheduleMiddleForest_eq_canonical`,
  `secondScheduleMiddleForest_eq_canonical`,
  `firstScheduleLowerForest_eq_canonical`, and
  `secondScheduleLowerForest_eq_canonical` derive multiplicity-preserving
  forest equality from those occurrence bijections;
- `firstThenSecondRoot_eq_pruneCombined`,
  `secondThenFirstRoot_eq_pruneCombined`, and
  `finalRoot_eq_pruneCombined` reduce both constructor-recursive schedules to
  the same occurrence-preserving source pruning;
- `exactTwoStageRemainderCoherence` proves literal equality of both sequential
  decorated roots with the canonical frontier root;
- `scheduleRegionData_cohere` proves equality of the actual ordered
  lower/middle/root basis triple, and `exactTwoStageRegionCoherence` packages
  component equality, root equality, basis equality, and reconstruction;
- `CanonicalThreeRegionDecomposition.composedFilling_reconstructs` fills the
  lower factors into the actual punctured middle factors and then fills those
  factors into the final root, reconstructing the exact source tree.

At the realized level,
`RealizedOpenComponent.canonicalTwoStageRoot_mapBase`,
`canonicalTwoStageMiddle_mapBase`, `canonicalTwoStageLower_mapBase`, and
`canonicalTwoStageComposedFilling_mapBase` show compatibility with persistent
base inclusion. These are realized-package or decorated-tree equalities. They
are not a claim of raw `CheckedDerivation` equality across presentations.

### Clause (iv): finite schedules — pending

`RankedCutHierarchy` states the corrected global hypothesis: cuts at distinct
levels are disjoint, and strict containment points from a lower rank to a
higher rank. `pair_noncrossing`, `finalCut`, and `finalRoot` provide pairwise
and canonical-frontier infrastructure.

`AddressBracketing.compose_independent_of_parenthesization` and
`RankedCutHierarchy.evaluate_independent_of_parenthesization` are explicitly
**address-only**. They prove associativity of list-prefix composition while
holding the source-canonical root fixed. They do not construct finite
transported cut schedules, finite region bijections, or iterated staged
fillings. Consequently manuscript clause (iv) remains pending.

The documented three-family cycle in `HierarchyGapFixture` is a genuine gap
in the manuscript's pairwise formulation: pairwise noncrossing alone can force
a strict orientation cycle. A global rank (or equivalently an acyclic
orientation plus a chosen topological order) is required.

## Corollaries adjacent to factorisation

| Manuscript item | Current theorem-level result | Status | Remaining boundary |
|---|---|---|---|
| `cor:strict-refinement-interchange` | `CKTree.PunctureAt.insertIncomparable_commutes`; `insertIncomparable_replacementPunctures_prefixed` | **exact for the core equality** | The two insertion orders are literally the same decorated tree, and inner puncture addresses are prefixed by the original incomparable addresses. The corollary's further claims about all cut witnesses, collected coproduct equality, and arbitrary finite adjacent-exchange schedules are not yet proved. |
| `cor:profiled-factorisation` | extensional cut identity, addressed `detachedTuple`, exact reconstruction | **partial** | The forward data and inverse reconstruction exist, but the manuscript's labelled `Mark ≃ Ctx+ × ∏ Prf` bijection is not packaged as a single Lean equivalence. |

## Exact material-base occurrence support

These declarations are new semantic infrastructure rather than a claim that
the later linear manuscript theorems have already been proved.

| Result | Lean declarations | Status and meaning |
|---|---|---|
| Exact base member | `MaterialBase.ExactOccurrence`, `ExactOccurrence.map`, `map_occurrence`, `map_injective` | **exact**. The occurrence itself is unchanged by `BaseHom`; only its membership proof is transported. Different exact occurrences cannot alias under this transport. |
| Proof-relevant use | `CKTree.MaterialUse`, `CKChildren.MaterialUse`, `sourceAddress`, `exactOccurrence`, `occurrenceId`, `siteBoundary` | **exact**. The witness is indexed by one decorated tree and retains its path and whole exact base occurrence. Interfaces contribute no use. |
| Recursive extraction | `CKTree.materialUseList`, `CKChildren.materialUseList`, `materialUseList_ordinary_material`, `materialUseList_ordinary_nonmaterial` | **exact**. A material node contributes once, and every ordered premise is traversed. Logical or structural nodes contribute no entry but do not stop recursion. Repeated uses remain repeated list entries. |
| Address-forgetting multiplicity | `materialUseSummary`, `materialProfile` and the checked/realized wrappers | **exact**. The summary retains address and ID; the `Multiset` profile forgets addresses only after retaining exact occurrence multiplicity. |
| Persistent inclusion | `sourceAddress_mapBase`, `exactOccurrence_mapBase`, `materialUseList_mapBase`, `materialProfile_mapBase` | **exact**. Addresses are fixed and the multiplicity profile is the pushforward along identity-on-occurrences membership transport. This proves no harmony, conservativity, or substitution principle by itself. |
| Wholly material regions | `CKTree.AllVerticesMaterial`, `maximalMaterialAddresses`, `maximalMaterialCut_validAddresses`, and `maximalMaterialPlan_detached_allVerticesMaterial` | **exact with the root exception stated**. A whole material tree returns only `[]`, proved not to be a nonroot CK cut. For a non-pure ordinary source, the recursive plan is a public valid cut with exactly the maximal-region address finset, and every detached region is wholly material. |
| Stratified pure-region coverage | `CKTree.MaterialDownwardClosed` and `CKTree.MaterialUse.coveredByMaximalMaterialRegion_of_downwardClosed` | **exact under the explicit hypothesis**. If materiality is downward closed through every ordered premise, every proof-relevant base use lies below a maximal wholly material root. No unconditional coverage claim is made. |
| Forward dependent-use classification | `MaterialSupportCut.lean`: `CKCut.partitionFilledMaterialUse`, `ValidAddressCut.partitionFilledMaterialUse` | **partial**. Every filled proof-relevant use is classified as retained or as a site-indexed filler use. No inverse classifier or `Equiv` of dependent `MaterialUse` witnesses is proved. |
| Filling/substitution law | `MaterialSupportListLaws.lean`: `fillerAddressedMaterialOccurrences_eq_orderedSites`, `fill_addressedMaterialOccurrences_perm`, `fill_materialProfile_eq_remainder_add_fillers` | **exact at projected addressed-occurrence level**. Constructor recursion gives a universal `List.Perm` of `(source address, ExactOccurrence)` values; every filler address is prefixed by its exact cut site and the profile sum follows by forgetting addresses. This is stronger than count agreement but is not a witness-index `Equiv`. |
| CK-cut partition of material uses | `MaterialSupportListLaws.lean`: `ValidAddressCut.source_addressedMaterialOccurrences_perm_remainder_append_detached`, `ValidAddressCut.source_materialProfile_eq_remainder_add_detached` | **exact at projected addressed-occurrence level**. The public extensional cut partitions the source list into the actual remainder and its address-aligned detached family, preserving exact occurrence identity and multiplicity. |
| Compatibility with exact two-stage coherence | `MaterialSupportListLaws.lean`: `source_addressedMaterialOccurrences_perm_root_middle_lower`, `source_materialProfile_eq_root_add_middle_add_lower`, `exactTwoStageMaterialPartitionCoherence` | **exact for the canonical projected partition**. The combined frontier is recursively refined into actual root, middle, and lower support and coupled to equality of the two decorated Stage-A schedule-region data. A schedule-specific dependent-use commuting `Equiv` remains unproved. |

Primitive-boundary eligibility and proof occurrence support are distinct.
`PrimitiveFragment` constrains the formula boundaries of a base member;
`MaterialUse` records where that exact admitted inference occurs in one proof
presentation. Neither says that the occurrence is semantically necessary.

Likewise, a wholly material subtree is not the general notion of base
dependence. For interleaved positive-arity bases, a material occurrence may
have a logical node below or above it. The concrete counterexample exhibits
that failure, while the universal coverage theorem assumes the explicit
`MaterialDownwardClosed` stratification hypothesis.

## Later manuscript labels

| Manuscript item | Status in the present non-linear milestone |
|---|---|
| `prop:final-rule-extraction` | **pending** as a paper-facing recursive frame equivalence. The constructor-indexed proof grammar supplies ingredients, not the named theorem. |
| `thm:cut-flags` | **pending/out of scope**. No linear cut-flag or iterated coproduct theorem is claimed. |
| `prop:base-extension` | **partial**. Exact occurrence preservation and checked/realized transport are proved by `BaseHom` and `mapBase`; the algebra/coalgebra extension statement awaits the linear carrier. |
| `def:base-conservativity` | **pending/out of scope**. Occurrence-support preservation is not conservativity. |
| `thm:base-hopf-functor` | **pending/out of scope**. There is no Hopf algebra or categorical base-change layer in this milestone. |
| `cor:proof-fibre-parametricity` | **pending/out of scope**. No fibrewise Hopf statement follows from realization transport alone. |
| `thm:connected-factorised` | **pending/out of scope**. No formal sums, tensor products, coproduct, counit, or antipode are introduced. |

The exact two-stage theorem and the built projected material filling/cut
partition laws are prerequisites for linearisation. The remaining
proof-relevant inverse and schedule-specific commuting diagram are not
silently supplied by them. Finite agreement, address associativity, or
equality of collected multiplicities must not be cited as proofs of universal
occurrence-level statements.

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

## CK revival continuation milestone — 12 October 2026

Current report: [context-revival-hopf.md](../reports/2026-10-12/context-revival-hopf.md).
HEAD `93b4a9abce87692ac32665132144ba1cd602808c`; work uncommitted.

| Result | Status and scope |
| --- | --- |
| Type-valued open continuation kernel | **MECHANIZED** in `Potkin/Research/OpenCertificateKernel.lean`; existing native trees, physical leaves, absolute addresses, inherited scopes, fixed finite palette and indexed ghost owner choices. |
| Closed existence and exact counting | **MECHANIZED**: `closed_nonempty_iff` and `closedCountEquiv : ClosedKernel … ≃ Fin (certificateCount …)` under exact local admission. The old Prop relation records existence, not multiplicity. |
| Complete-source cut-created holes | **MECHANIZED** in `CutHoleAdapter.lean`; native hole/site equivalence, boundary/address alignment and literal refill. Arbitrary open filling retains inherited holes through `filledLeafEquiv`. |
| Universal certificate cut gluing | **MECHANIZED** in `CertificateCutGluing.lean`; complete source, native full branch cuts, scope-dependent aligned factor callbacks, and both actual inverse maps. Empty/public root-excluding cuts and separate whole-branch selection remain distinct. |
| Scoped contextual certificate replacement | **MECHANIZED**; pointwise equivalences at the same physical interface/address/scope transport whole-context certificate witnesses. Not C1, ordinary LJ equivalence or full-LQ adequacy. |
| Native inside-factor flag geometry | **MECHANIZED** in `CutCertificateFlags.lean`; actual installed cut equivalence, native site dependent-sum bijection, exact addresses/factors and intermediate remainder filling. Not certificate-map coherence. |
| Cooperative pp/pq/qp/qq gluing example | **MECHANIZED instantiated consequence** in `CertificateGluingExamples.lean`; shared-scope compatibility and failure of independent closed-factor grounding. Not the proof of universal gluing. |
| Two-stage hierarchical context witness coherence | **MECHANIZED** in `CertificateNestedGluing.lean`; independently recursive restriction and both actual map diagrams. Open-filler naturality also verified in `CertificateContinuationComposition.lean`. |
| Actual native one-shot versus nested cut coherence | **MECHANIZED** in `CertificateFlagGluing.lean`: actual restriction and inverse gluing maps, with native callback matching proved through refill injectivity. Complete first sources and full lower cuts inside first detached factors; arbitrary noncrossing schedules remain unclaimed. |
| Conditioned dependent piece count | **MECHANIZED**: `piecesCountEquiv` in `CertificateCutGluing.lean`, giving piece witnesses equivalent to `Fin certificateCount` under source admission. Shared-scope Sigma/product witnesses, not independent closed-factor counts. |
| Signed finite-sum L/A/e/K laws | **MECHANIZED** in `ContextCutAction.lean`: actual choice splicing, δG=Lδ+A, L/A composition, eδ=id, eL=Ge, eA=0, K=L+Ae, δG=Kδ and K composition on arbitrary signed extraction records. No H-linearity or Hopf-morphism claim. |

Accepted headline axiom closures contain only `propext`, `Quot.sound` and,
where needed, `Classical.choice`. Failed checks' `sorryAx` placeholder output
is not accepted. No full build or full test suite was run. The report gives
commands, durations, dependency-repair costs, independent review and exact gates.

The exact two-stage theorem and the built projected material filling/cut
partition laws are prerequisites for linearisation. The remaining
proof-relevant inverse and schedule-specific commuting diagram are not
silently supplied by them. Finite agreement, address associativity, or
equality of collected multiplicities must not be cited as proofs of universal
occurrence-level statements.

## CK contraction postponement additive milestone 13 October 2026

Report: [contraction-postponement.md](../reports/2026-10-13/contraction-postponement.md).
HEAD remains `93b4a9abce87692ac32665132144ba1cd602808c`; uncommitted.

| Result | Status and exact scope |
| --- | --- |
| Complete native public quotation | **MECHANIZED** in `Potkin/CompleteQuotation.lean`: complete `LocallyAdmittedTree P` sources quote through the existing checker and realize literally unchanged. No private checked constructor or unfilled-Box proof. |
| Canonical Plan, termination and threshold | **MECHANIZED** in `ContractionPlans.lean`; all ordered children, arbitrary bounded states and universal quota threshold. |
| Attained Bellman and secondary optimum | **MECHANIZED** in `ContractionPlans.lean`; node minimum and lexicographic secondary minimum only in the fixed opaque-donor Plan language. Selection is noncomputable, not an executable optimized search. |
| Exact multiset boundary substitutions and script costs | **MECHANIZED** in `ContractionBoundaries.lean`: literal continuation/premise boundaries, donor inclusion, prescribed EW count and terminal EC count, preserving aliases and multiplicity. |
| Native proof-producing interpretation and checked output | **MECHANIZED** in `ContractionPostponement.lean`, conditional on the explicit admitted rule/EW/EC interface and finite registration of reached occurrences. `compile_realize` proves literal realization; exact node costs, completeness and occurrence-predicate avoidance are proved. |
| Actual HLJ+com/external EW/EC instantiation | **OPEN**. Source audit finds no installed schema. The interface is a required input, not an admission theorem. Paper 29/35 and 7401/84105 numbers are not a registered native fixture. |
| Universal physical CK observation and contextual action | **MECHANIZED** in `ContractionCutObservation.lean`: arbitrary commutative-semiring native witness sum, exact physical total, one-hole affine filling and total dominance, and the explicit scalar K adapter on the image of delta. |
| Integrated native compiler cut objective | **MECHANIZED** in `ContractionCompilerCuts.lean`: stop/continue/final EC recurrences, checked-output adapter, and node-first/full-physical-cut-count-second optimum among fixed opaque-donor Plan outputs. |
| Instantiated finite-coefficient/ coefficientwise comparison | **OPEN**. Exact Polynomial cache gate: `Mathlib.Data.Finset.Powerset.olean`; alternate existing MonoidAlgebra import gate: `Mathlib.Data.Finsupp.Basic.olean`. Scalar agreement is not a coefficientwise theorem. |

The required non-EC condition applies to the continuing rule as well as donors
and EW. Final logical-Cut freedom additionally needs the supplied EC family to
avoid the exact logical-Cut predicate. No positive CK defect, tensor/remainder
equality, independent copied certificates, or global logical-proof optimum is
asserted. Existing scoped gluing and signed K laws are reused, not re-verified.

## Interface-aware iterated CK decomposition — 13 October 2026

Report: [iterated-ck-decomposition.md](../reports/2026-10-13/iterated-ck-decomposition.md).
HEAD remains `93b4a9abce87692ac32665132144ba1cd602808c`; all changes uncommitted.

| Result | Status and exact scope |
| --- | --- |
| Full physical two-stage extraction equivalence | **MECHANIZED** in `RemainderExtractionFlags.lean`: `BranchInside tree ≃ BranchRemainder tree`, including extraction of the first open remainder, empty/separate whole endpoints, both inverse maps and arbitrary native open trees. Not merely the older inside-factor theorem. |
| Ordered three-output preservation and reconstruction | **MECHANIZED**: `branchFlag_outputs`, `toRemainderBranch_intermediate`, `inside_refill`, `remainder_refill`; literal typed final root, addressed lower/middle packets and physical multiplicity retained. Intermediate filling is not the final remainder. |
| Full addressed and collected finite extraction sums | **MECHANIZED** in `IteratedExtractionSums.lean`: arbitrary additive weights on the complete packet triple, signed addressed equality and explicit native commutative projection. No scalar-count surrogate. |
| Open-source scoped cut gluing | **MECHANIZED** in `OpenCutCertificateGluing.lean`: inherited callbacks remain distinct from cut-created callbacks, no fabricated completeness, actual scopes/addresses and both serial inverse maps. |
| Actual inside-versus-remainder certificate diagrams | **MECHANIZED** in `IteratedCutCertificates.lean`: independently constructor-defined piece reassociation and `restriction_branch` / `gluing_branch` actual map equalities. Scope is the existing right-ghost kernel; not all-system legality. |
| Independent Sys(com) dependency/interface agreement | **MECHANIZED** in `DependencyInterface.lean`: exact local shape/incidence checking plus independent designated-bottom/parameter/branch legality; exported pending demands characterize piece legality under external/internal owner freshness. |
| Checked positive/negative replacement and staged reuse | **MECHANIZED instantiated application** in `DependencyInterfaceExamples.lean`: genuine finite source-fragment stock, same-boundary wrong-pack rejection, compatible IW/IC interior update, native proper `[0]` cut, literal retained remainder and both staged checked reconstructions. The universal interface theorem is used. |
| Arbitrary open dependency-piece replacement | **OPEN**: a requirements-only interface omits internal grants needed by future inherited-hole fillings. Preserve grant signatures or prove callback compatibility; the complete grant-free factor application does not establish that stronger contract. |
| Ordinary forest coalgebra/coaction | **OPEN**: raw CKForest already permits ordinary open factors, but no installed `Delta_H`/forest-product adapter is supplied. Typed two-stage extraction and its finite-sum laws are proved; K remains a context action. |
| Full 2-system/hypersequent embedding and analyticity | **OPEN**, outside this finite faithful Sys(com) validation fragment; exact source ownership/erasure, all rule schemas/side conditions and adequate interface composition remain obligations. |

Six final targeted module checks passed with headline closures containing only
`propext`, `Quot.sound`, and where required `Classical.choice`. No `sorryAx`,
custom axiom, full build or finite-test substitution was accepted. The dated
report records exact commands, durations, bounded startup diagnoses, concrete
fixes, independent review and D1–D6. The contraction milestone remains intact.

## Open discharge replacement — 14 October 2026

Report: [open-discharge-replacement.md](../reports/2026-10-14/open-discharge-replacement.md).
HEAD remains `93b4a9abce87692ac32665132144ba1cd602808c`; all changes uncommitted.

| Result | Status and exact scope |
| --- | --- |
| Independent annotated discharge semantics | **MECHANIZED** in `OpenDischarge.lean`: actual-tree designated UID/parameters/ordered-branch legality, independent exact local rule checking, and universal typed `exact_fill`. Scope is identity/IW/IC/implication-right plus Sys(com), not full LJ erasure/decorability. |
| Open-source native factor-to-hole adapter | **MECHANIZED** in `OpenCutAssignments.lean`: inherited interfaces remain distinct from cut-created ones, exact native Box retained, literal source refill without a fabricated completeness assumption. |
| Type-valued native scoped cut certificates | **MECHANIZED** in `OpenDischargeCertificates.lean`: physical owner positions and scopes, `cutEquiv`/`branchEquiv`, native factor callbacks, and serial remainder restriction/gluing inverse laws. No independent closed-factor-count product. |
| Independent legality/certificate agreement and cut gluing | **MECHANIZED** in `OpenDischargeAgreement.lean`: `closed_kernel_iff_legal`, `closed_legality_cut_gluing`, and public `proper_cut_legality_gluing`, with explicit exact-local, unique-owner, and complete-source hypotheses. |
| Native simultaneous-filling scope partition | **MECHANIZED** in `OpenDischargeComposition.lean`: field laws and `native_scope_partition` cover hidden/sibling/descendant owners, wrong parameters/branches, persistent input failures and genuine external demands. Declaration freshness does not forbid valid cross-piece references. |
| Exact entire compact-summary composition | **MECHANIZED** in `OpenDischargeCompositionLaws.lean`: unconditional all-address `exposure_fill`, `ok_fill`, `directSummary_fill`, and `composeSummary_realizable_assoc` with native physical reindexing. No valid-input/freshness/completeness hypotheses and no deduplication. Final check 110.341 s, standard clean closures. |
| Generic fixed-owner replacement | **MECHANIZED** in `NativeDischargeReplacement.lean`: literal finite-summary equality supplies its canonical physical-hole correspondence and implies independent correctness preservation/reflection under arbitrary matching future fillings and all native typed exterior contexts. Transported finite interfaces additionally permit moved physical holes. No success/freshness restriction on arbitrary fillers; registry admission remains separate. |
| Actual implication-right/system-bottom permutation | **MECHANIZED** in `DischargePermutation.lean`: the existing theorem is now derived from generic fixed-ID replacement, including arbitrary future native/checked fillers AND typed exterior contexts. Exact immutable ten-instance registry and nonvacuous Phi={p}, Psi={q} application retained; admission is not inferred from summaries. Final check 125.911 s. Not all LJ rule schemas. |
| New Sys(com) two-stage witness diagram | **MECHANIZED**: corrected `DischargeCutFlags.lean` passes with actual constructor-defined restriction/gluing commuting diagrams under native flag reindexing. Final check 176.532 s; closures `[propext, Quot.sound]`. |
| Full summary evaluation joined to witness coherence | **MECHANIZED** in `DischargeSummaryCutEvaluation.lean`: actual native remainder/factor folds, inside-versus-serial all-field equality, addressed ordered packets and literal remainder, and the actual restriction/gluing diagrams. Joint piece certificate interpretation explicitly requires exact-local/unique/complete sources. Final check 106.325 s, standard clean closures. |
| Independent selected source formula/rule interpretation | **MECHANIZED** in `D3SourceEncoding.lean`: actual implication constructor image, arbitrary formula/multiset schemes, local exactness soundness/reflection, physical hole boundary/address/order and literal filling/puncture-insertion commutation. Final check 59.410 s. Canonical supplied incidence concerns components, not individual formula-occurrence movement. |
| Pending assignments and fixed-reference source replacement | **MECHANIZED** in `D3DischargeGrouping.lean` (70.890 s) and `D3SourceAdequacy.lean` (72.941 s): inverse pending-schedule/eligible-assignment maps, naming recovery, source annotation correctness iff native Legal, source fillings AND source exteriors. Ordinal physical occurrences preserve multiplicities; closed interpretation separately requires completeness. Recursive source-constructor erasure/decoration remains OPEN. |
| Schema-general and source-encoded implication application | **MECHANIZED** in `D3SchemaPermutation.lean` (58.993 s), `D3SourcePermutation.lean` (69.456 s), and `D3SourceCK.source_implication_replacement`: arbitrary schema parameters, owner fixed, actual source implication, generic replacement applied rather than reproved. Any-registry checked corollary assumes the exact shell descriptors are admitted together with donors/exterior. The old ten-instance fixture remains unchanged. |
| Common finite source admission and exact extension | **MECHANIZED with explicit hypotheses** in `D3RegistryAdmission.lean` (50.055 s) and `D3SourceAdmission.lean` (44.771 s): finite family admission under `ConsistentKeys`, exact old lookup preservation, public checker lifting with literal realization, local schema admission from source validity. Unconditional fresh-key allocation and logical conservativity are not claimed. |
| Source interpretation of native staged CK certificates | **MECHANIZED** in `D3SourceCK.lean` (76.328 s): both stagings evaluate the independent chosen-reference source condition; source correctness supplies exact-local/unique premises for jointly scoped piece certificates when complete. Actual restriction/gluing maps and addressed ordered packets/literal remainder are coherent. Not a bijection of all possible source groupings or coproduct invariance across permutation. |
| Scoped permutation/cut application | **SOURCE-PRESENT / NOT RECHECKED** in `DischargeCertificatePermutation.lean`; no completion claim. |
| Executable cache/refinement, optional cost formula, full LJ embedding | **OPEN / NOT PURSUED**, as detailed in the report. |

The continuation completed all four requested fixed-owner proof targets. Seven
final targeted continuation module checks passed, with headline closures
containing only `propext`, `Quot.sound`, and where needed `Classical.choice`.
The report records exact commands, durations, concrete elaboration fixes,
independent review, the global owner-renaming correction, D1–D6, and remaining
downstream obligations. Generic correctness is not claimed to supply registry
admission, arbitrary renaming, generic certificate-type equality, or full tensor
invariance. No full build, finite-test proof substitute, commit, or push was made.
The earlier recovery-only report is retained as labelled history beneath the
completed continuation.

The maintained research status entry is **D3-A** in
[ledger_current.md](../D3_Research_Ledger_Evidence/ledger_current.md), updated in
place. Its full source-adequacy target remains partial: recursive source grouping
and closed erasure/decoration, finer formula-occurrence action, and unconditional
consistent key allocation remain explicit gates. The D3 continuation in the same
dated report records eight successful final checks with standard clean closures;
these extend the application scope of the existing fixed-owner/CK results rather
than claim new abstract identities or a new logical permutation.

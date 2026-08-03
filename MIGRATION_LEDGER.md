# Potkin P3-0/P3-1/P3-2 migration ledger

This ledger records declaration-level provenance. The source repositories were
read-only references; `potkin3` has no source-level dependency on either one.

- `nonmonlogics` source commit:
  `713a809b14ccae5baeaa3d64e0d0ccec21085534`
- `potkin` source commit:
  `c0f74a38cb06e088936b7cc0440621b364349b2e`
- Mathlib revision:
  `378b908c009ef82cf9584cba7447c44a5a89e58a`

Every record below has an explicit commit field. `N` denotes the exact
`nonmonlogics` commit `713a809b14ccae5baeaa3d64e0d0ccec21085534`; `R`
denotes the exact `potkin` commit
`c0f74a38cb06e088936b7cc0440621b364349b2e`.

Status vocabulary:

- **copied**: definition transferred without a material representation change;
- **generalised**: the source declaration was retained in a more general or
  more precise indexed form;
- **reproved**: the mathematical statement was proved again for the new
  representation;
- **replaced**: the source role is served by a deliberately different
  foundation or executable representation;
- **consulted**: source proof structure informed the design, but the named
  source theorem was not migrated as a destination theorem.

No P3-0 declaration is a blind textual copy. “Copied” is therefore not used
below.

## Language and boundary declarations

| Source | Commit | Path | Source declaration | Destination | Status | Migration note |
|---|---|---|---|---|---|---|
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `FormulaSignature` | `Potkin/Language.lean`: `Signature` | generalised | Retains atoms and arity-indexed operation symbols under the `Potkin` namespace. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `FormulaSignature.Formula`, `Formula.app₀`, `app₁`, `app₂` | `Potkin/Language.lean`: `Formula`, `app0`, `app1`, `app2` | generalised | Keeps the free arity-indexed syntax and ordered `Fin n` arguments; names are ASCII. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `Sequent` | `Potkin/Boundary.lean`: `Context`, `Sequent` | generalised | Makes the multiset context alias explicit and retains two-sided multiset boundaries. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/HypersequentCore.lean` | `SequentHypersequent` | `Potkin/Boundary.lean`: `Hypersequent` | replaced | The older alias permits the empty multiset; P3-0 uses a proof-carrying nonempty multiset of sequents as every local boundary. |

## Occurrences, bases, and presentations

| Source | Commit | Path | Source declaration | Destination | Status | Migration note |
|---|---|---|---|---|---|---|
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `RuleInstance` | `Potkin/Occurrence.lean`: `OccurrenceShape` | generalised | Premises and conclusion are upgraded from sequents to whole nonempty hypersequents. |
| `potkin` | R | `potkin/kernel/calculus.rkt` | `concrete-occurrence`, `make-concrete-occurrence`, `occurrence-arity` | `Potkin/Occurrence.lean`: `OccurrenceKind`, `OccurrenceShape`, `LocalOccurrence`, `LocalOccurrence.arity` | replaced | The Lean structure makes the exact shape and optional incidence dependent immutable data. |
| `potkin` | R | `potkin/kernel/calculus.rkt` | component-incidence fields of `concrete-occurrence` | `Potkin/Occurrence.lean`: `ComponentProfile`, `OccurrenceProfiles`, `ComponentEdge`, `ComponentIncidence` | generalised | A supplied ordered profile is proved to enumerate each exact component multiset; `Fin` endpoints then retain duplicate local occurrences, while `Option` preserves unknown versus known empty. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `PrimitiveBase` | `Potkin/ProofTheory.lean`: `PrimitiveFragment`, `MaterialBase` | replaced | P3-2 restores an explicitly chosen primitive fragment but indexes membership by the exact fully instantiated occurrence, allowing positive arity and adding no closure laws. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `RuleSystem`, `ProofTheory` | `Potkin/ProofTheory.lean`: `RuleSystem`, `ProofTheory`, `ProofTheory.Admits` | generalised | Separates logical and structural occurrence admission, retains nullary logical initials, and gives material admission exact occurrence membership at arbitrary finite arity. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCRealizedSectorTransport.lean` | `PreservesBase`, `mapProofTree` | `Potkin/ProofTheory.lean`: `BaseHom`; `Potkin/Checked.lean`: `CheckedDerivation.mapBase` | generalised | Specialises transport to a proof-preserving material-base map while keeping fixed rules, initials, registry occurrences, and whole boundaries. |
| `potkin` | R | `potkin/kernel/calculus.rkt` | `equipped-calculus`, `make-equipped-calculus`, `calculus-lookup` | `Potkin/Presentation.lean`: `EquippedPresentation`, `LookupResult`, `lookup` | replaced | A finite registry list carries unique-ID and admission proofs; executable lookup returns exact membership and ID evidence. |
| `potkin` | R | `potkin/kernel/calculus.rkt` | immutable registry preservation under compatible addition | `Potkin/Presentation.lean`: `EquippedPresentation.mapBase`, `mapBase_registry` | replaced | P3-0 maps only base evidence and keeps the registry definitionally unchanged; deletion and revision are not represented. |

## Checked and CK carriers

| Source | Commit | Path | Source declaration | Destination | Status | Migration note |
|---|---|---|---|---|---|---|
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `ProofTheory.ProofTree`, `CompleteTree` | `Potkin/Checked.lean`: `CheckedDerivation`, `CheckedChildren` | generalised | Indexing is by whole hypersequent, exact presentation, and the complete ordered premise-boundary list. |
| `potkin` | R | `potkin/kernel/calculus.rkt` and `potkin/kernel/context.rkt` | raw/checking boundary embodied by occurrence lookup, `complete-proof?`, `term-admitted-by?` | `Potkin/Checked.lean`: `RawDerivation`, `CheckError`, `EquippedPresentation.check`, `checkAt` | replaced | Anonymous raw punctures make no boundary claim; private checked constructors are exposed only through executable checking, including an exact-root wrapper. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `TypedCKTree`, `TypedCKTree.interface`, `ordinary` | `Potkin/CKTree.lean`: `OpenTree`, `OpenChildren`, `CKTree`, `CKChildren` | generalised | Separates boundary-generic open combinatorics from its whole-hypersequent occurrence-decorated specialization. |
| `nonmonlogics` | N | `nonmonlogic/JLC_RULE_DECORATED_CARRIER_BLOCKER.md` | Architecture A recommendation | `Potkin/CKTree.lean`: parameterised occurrence-decorated carrier | replaced | P3-0 adopts the clean-carrier direction rather than aliasing the old coarse marked tree. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `ProofTree.toTypedCKTree` | `Potkin/Checked.lean`: `CheckedDerivation.realize`, `realize_isOrdinary` | generalised | Realization now preserves IDs, kinds, instance data, incidence, whole boundaries, and premise order. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCTwoCarrierRealization.lean` | `eraseRuleTree` comparison discipline | `Potkin/CKTree.lean`: `CKTree.Bare`, `CKTree.erase` | replaced | Erasure is explicit and intentionally loses decoration while retaining boundary-labelled ordered shape. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCRealizedSectorTransport.lean` | `toTypedCKTree_mapProofTree` | `Potkin/Checked.lean`: `realize_mapBase`, `erase_realize_mapBase` | reproved | The realization square commutes for the new proof-preserving base map and decorated target. |

## Cut, filling, and root projection

| Source | Commit | Path | Source declaration | Destination | Status | Migration note |
|---|---|---|---|---|---|---|
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCScopedRootExposure.lean` | `TypedRootConstruction`, `immediateRootCut` | `Potkin/RootCut.lean`: `RootConstruction`, `RootCut`, `RootCut.address` | generalised | Uses decorated whole-hypersequent nodes and a nonempty finite selection of ordinary immediate child roots. |
| `potkin` | R | `potkin/kernel/cut.rkt` | `validate-ck-cut`, `prefix-conflict`, `cut-witness` | `Potkin/RootCut.lean`: `VertexAt`, `AddressPrefix`, `PrefixIncomparable`, `RootCut` | generalised | P3-0 proves the witness conditions for immediate-root selections only; recursive arbitrary-depth validation is deferred. |
| `potkin` | R | `potkin/kernel/cut.rkt` | `detached-entry`, `make-cut-witness` | `Potkin/RootCut.lean`: `RootCut.Site`, `detached`, `detachedForest`, `retained` | generalised | The dependent site family is retained before its commutative multiset image. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCScopedRootExposure.lean` | `retainedSlot`, `retainedTree`, `selectedPremiseForest` | `Potkin/RootCut.lean`: `retainedChild`, `retained`, `detachedForest` | generalised | Selected ordinary children become typed interfaces; the original decorated positive root is retained. |
| `potkin` | R | `potkin/kernel/context.rkt` | `puncture-requirement`, `complete-fill` | `Potkin/RootCut.lean`: `requirement`, `fill`, `retainedChild_at_site` | generalised | Filling is a total dependent operation on an exact site-indexed filler family, not a search. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCTwoCarrierRealization.lean` | `selectedImmediate_typedMatching`, `selectedImmediate_filling_reconstructs` | `Potkin/RootCut.lean`: `puncture_matches_detached`, `fill_detached_reconstructs` | reproved | Matching packages the retained interface with its aligned detached root, and exact reconstruction is re-established for decorated whole-hypersequent trees. |
| `potkin` | R | `potkin/kernel/cut.rkt` | `reconstruct-cut-witness`, `cut-witness-reconstructs?` | `Potkin/RootCut.lean`: `fill_detached_reconstructs` | reproved | The result is universal for every P3-0 `RootCut`, not a bounded fixture agreement. |
| `potkin` | R | `potkin/kernel/cut.rkt` | `forest-block-root-profile`, `forest-flattened-root` | `Potkin/RootProjection.lean`: `blockRoots`, `flattenedRoots` | replaced | Lean separates whole connected blocks from a flattened nonempty whole boundary; the empty forest yields `none`. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCScopedRootExposure.lean` | `forestRootProjection`, `literalHypersequent` | `Potkin/RootProjection.lean`: `flattenedRoots` | generalised | The projection acts on occurrence-decorated components whose root boundary is already a whole hypersequent. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCRootProjectionSplitting.lean` | root projection/cardinality separation pattern | `Potkin/RootProjection.lean`: `block_connected_pair_ne_separate` | reproved | A cardinality proof distinguishes one connected block from two forest factors. |

## Anonymous executable witness

| Source | Commit | Path | Source declaration | Destination | Status | Migration note |
|---|---|---|---|---|---|---|
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCTwoCarrierRealization.lean` | selected immediate binary exposure examples | `Potkin/Examples/Anonymous.lean`: `binaryConstruction`, `binaryCut` and its theorem package | replaced | Uses no featured connective or calculus; both binary premise slots form one nontrivial proper prefix-free cut. |
| `potkin` | R | `potkin/kernel/calculus.rkt`, `context.rkt`, `cut.rkt` | executable nullary/unary/binary checking and witness flow | `Potkin/Examples/Anonymous.lean`: `rawBinary_checks`, `rawUnary_checks`, `binaryCut_reconstructs` | reproved | Exact reduction establishes the checker results; universal library theorems establish address, typing, and reconstruction properties. |

## Consulted but intentionally not migrated in P3-0

The following source modules informed terminology or future constraints but
have no claimed P3-0 destination declaration:

- `Nonmonlogics/JLCOpenRootCocycle.lean`: recursive proper-cut enumeration and
  coproduct support;
- `Nonmonlogics/JLCConcreteCKHopfInstance.lean`: concrete bialgebra packaging;
- `Nonmonlogics/JLCTypedCKConcreteCoassoc.lean`: two-stage cut bijections and
  coassociativity;
- `Nonmonlogics/JLCTypedCKConnectedAntipode.lean`: vertex grading and recursive
  antipode;
- `Nonmonlogics/JLCTwoCarrierRealization.lean`: featured MILL calculations
  beyond the generic realization/filling patterns listed above;
- `Nonmonlogics/JLCRealizedSectorTransport.lean`: general signature
  relabelling and realized-forest transport beyond material-base maps;
- `potkin/analysis/cocycle.rkt`: pointed coactions, grafting cocycles,
  protected defects, and residue laws.

These are deferred, not silently assumed.

## P3-1 recursive cut, open-sector, and enumeration additions

P3-1 continues to use source commits `N` and `R` defined above. The entries
below record only the new declaration-level work; no source repository file
was copied or modified.

| Source | Commit | Path | Source declaration | Destination | Status | Migration note |
|---|---|---|---|---|---|---|
| `potkin` | R | `potkin/kernel/address.rkt` | `address<?`, address prefixing/conversion, `vertex-at-address` | `Potkin/CKCut.lean`: address append/prefix laws, recursive `address_vertexAt`; `Potkin/CKCutEnumeration.lean`: positive validation | generalised | Retains Lean’s zero-based internal paths and proves compatibility with positive one-based interchange paths; interfaces remain addressable holes but are never vertices. |
| `potkin` | R | `potkin/kernel/cut.rkt` | `validate-ck-cut`, prefix-conflict validation | `Potkin/CKCut.lean`: `CKCutPlan`, `CKChildCuts`, `CKBranchCut`; `Potkin/CKCutEnumeration.lean`: canonical validators; `Potkin/CKCutValidity.lean`: `ValidAddressCut`, external witness construction | replaced | Invalid root, interface, duplicate, and ancestor/descendant selections are unrepresentable by the structural branch decomposition. Requests are lexicographically canonicalised without deduplication before witness lookup, matching the Racket order convention. |
| `potkin` | R | `potkin/kernel/cut.rkt` | `make-cut-witness`, addressed `detached-entry`, retained remainder | `Potkin/CKCut.lean`: `CKCut`, `CKCutEntry`, `detachedTuple`, `remainder`, `detachedForest` | generalised | The dependent recursive site family and lexicographic tuple remain primary before the commutative forest image. Equal trees at different addresses remain different entries. |
| `potkin` | R | `potkin/kernel/context.rkt`, `potkin/kernel/cut.rkt` | `puncture-requirement`, `context-insert`, `reconstruct-cut-witness` | `Potkin/CKCut.lean`: `siteBoundary`, `fill`, `remainder_interfaceAt_site`, `fill_detached_reconstructs`; `Potkin/CKCutPuncture.lean`: `requirement`, `selectedPuncture_matches_detachedRoot`, exact new/old interface laws | reproved | Filling is distinguished by new-site identity and therefore leaves pre-existing interfaces alone. Exact reconstruction is structural equality. |
| `potkin` | R | `potkin/kernel/cut.rkt` | recursive `all-ck-cuts` branch enumeration | `Potkin/CKCutEnumeration.lean`: recursive plan/child/branch enumerators, intrinsic completeness and no-duplicate theorems; `Potkin/CKCutValidity.lean`: external finite-antichain completeness | generalised | Uses the explicit none/whole/below constructor decomposition and ordered Cartesian child product, not subset filtering or result-level deduplication. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCOpenRootCocycle.lean` | `OpenCutResult`, `ChildCutResult`, `combineChildCuts`, `childCutChoices`, `treeNonTotalCuts` | `Potkin/CKCut.lean`; `Potkin/CKCutEnumeration.lean` | generalised | Reuses the constructor-recursive independent-child proof pattern while adding occurrence addresses, exact tuple identity, old/new interfaces, and duplicate-free enumeration absent from the source result carrier. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCTwoCarrierRealization.lean` | `fillInterfaces`, `selectedImmediate_typedMatching`, `selectedImmediate_filling_reconstructs` | `Potkin/CKCut.lean`: distinguished recursive filling and reconstruction | generalised | The source fills interfaces by type and proves an immediate case; P3-1 fills only cut-created sites and reproves the theorem at arbitrary depth for already-open sources. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCHoleRelabellingAndFilling.lean` | hole-bijection, staged-filling, and disjoint-filling proof patterns | `Potkin/CKCut.lean`: site-indexed address-aligned fill | consulted | Informed the separation of old vacancies from cut-created sites, but no general hole reindexing, staged-fill, disjoint-fill, or nested-coherence theorem is migrated in P3-1. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCIteratedTelescopeCapstone.lean` | old/fresh `Sum` hole discipline, `fillInsideOut` | `Potkin/CKCut.lean`: recursive-sum `Site`, new-site fill; `Potkin/CKCutPuncture.lean`: `newHoleAt_iff_selectedSite`, old-interface preservation | generalised | Keeps old interfaces outside the new-site index and uses recursive sums for fresh selected occurrences; address provenance replaces name-wide refinement. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCTypedCKConnectedAntipode.lean` | `ordinaryNodeCount`, cut degree-split lemmas | `Potkin/CKCut.lean`: `CKTree.degree`, `degree_partition` | reproved | Interfaces have degree zero; the theorem sums the degrees of the aligned detached occurrences before any algebraic grading or antipode packaging. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/JLCRealizedSectorTransport.lean` | `RealizedComponent`, `mapProofTree`, `realizedComponent_map` | `Potkin/RealizedSector.lean`: `LocallyAdmittedTree`, `RealizedOpenComponent`, `mapBase`; `Potkin/RealizedCut.lean`: cut closure | replaced | The source predicate is the range of complete proof erasure. P3-1 instead defines a genuine exact-registry admitted open sector, allowing typed interfaces and proving detached/remainder closure. |

## Recorded P3-1 source mismatch

Manuscript v56 and Racket both allow positive-arity material occurrences.
P3-0’s `ProofTheory.Admits.material` requires a nullary occurrence, and P3-1
does not alter that foundation. The open-sector and heredity theorems are
therefore intentionally scoped to the exact current `EquippedPresentation`;
they must not be cited as a proof of the broader manuscript material carrier.

## Recorded P3-1 representation gap

`CKCutValidity` constructs an intrinsic recursive cut from every independent
finite valid address antichain and proves exact address-finset preservation.
The converse structural-injectivity proof is not present: dependent
elimination stalls when two occurrence constructors expose equality first at
their `shape.conclusion` projections. Thus intrinsic witness enumeration is
proved duplicate-free, but P3-1 does not claim `CKCut ≃ ValidAddressCut` or a
Nodup theorem after forgetting witnesses to address lists. This is a formal
representation/elimination gap, not evidence of two mathematical cuts with
the same address set, and no quotient is added to bypass it.

## P3-2 corrections and coherence additions

P3-2 closes both recorded P3-1 representation mismatches at the public API
level and migrates the manuscript's filling/coherence clauses. Source commits
remain `N` and `R`; the manuscript source is v56.

| Source | Commit | Path | Source declaration | Destination | Status | Migration note |
|---|---|---|---|---|---|---|
| manuscript v56 | v56 | Definition `Material base and the equipped calculus` | tagged primitive-boundary material occurrences and persistent inclusion | `Potkin/ProofTheory.lean`: `PrimitiveFragment`, exact-occurrence `MaterialBase.Member`, `BaseHom` | replaced | Membership is indexed by the whole occurrence and proves material kind plus primitive boundaries; arbitrary positive arity is admitted. A hom has no occurrence map, so it preserves exact old IDs, shapes, instance data, and incidence. |
| `potkin` | R | `potkin/kernel/calculus.rkt` | positive-arity material occurrences and exact registry occurrence identity | `Potkin/Examples/MaterialBase.lean` | reproved | A unary material operation checks successfully; a same-profile twin ID remains separately includable, extension preserves only the explicit old member, and no Weakening, contraction, Cut, or substitution closure is generated. |
| manuscript v56 | v56 | Definition `Address-indexed cut witness` | finite nonroot address antichain as cut identity | `Potkin/CKCutValidity.lean`: `ExtensionalCKCut`, `validAddressEquiv`, public enumeration and validation | replaced | The public cut is structurally equivalent to `ValidAddressCut` and canonically compiles to the legacy recursive plan. Public enumeration is Nodup and exact-once after structural address deduplication; no quotient is introduced. |
| `potkin` | R | `potkin/kernel/context.rkt`, `cut.rkt` | general context insertion, filling, puncture requirements | `Potkin/GeneralFilling.lean`: `PunctureAt`, `IsComplete`, exact general-fill puncture formula | generalised | Proves root, local-admission, old-hole, filler-prefix, completeness, distinguished-reconstruction, and base-transport laws for arbitrary compatible replacements. |
| `nonmonlogics` | N | `Nonmonlogics/JLCHoleRelabellingAndFilling.lean`, `JLCIteratedTelescopeCapstone.lean` | disjoint filling, prefix relabelling, staged reconstruction patterns | `Potkin/GeneralFilling.lean`: typed insertion and strict interchange | reproved | Constructor recursion fixes old occurrence decorations, prefixes replacement addresses, transports an incomparable old puncture literally, and proves structural interchange. |
| manuscript v56 | v56 | Theorem `Puncture factorisation and nested coherence`, clauses (iii)-(iv) | noncrossing cuts and finite hierarchy | `Potkin/NestedCoherence.lean`: `Noncrossing`, `CutTransport`, `CanonicalTwoStageWitness`, `RankedCutHierarchy`, `ExactTwoStageRemainderCoherence` | partial/generalised | Retains source and relative addresses, proves a unique retained-or-detached destination, a `Sum` swap of source-address identities, common frontier-interface presence, and separate local reconstruction laws. A ranked hierarchy determines a canonical frontier; the only parenthesisation result is generic address-list append associativity. Actual region/factor correspondence, composed filling from the further-cut root, literal equality of sequential remainders, and coherence of iterated cut schedules remain explicit targets. |
| manuscript v56 | v56 | Corollary `Strict interchange of independent refinements` | two incomparable puncture insertions | `Potkin/GeneralFilling.lean`: `insertIncomparable_commutes` | reproved | Equality is literal decorated-tree equality, not a quotient or commuting conversion; internal addresses are prefixed by their exact old puncture addresses. |

## Manuscript correction exposed by P3-2

The displayed v56 two-cut predicate must explicitly require disjoint address
sets; otherwise the same address may occur in both cuts and cannot be
transported after becoming a puncture. Clause (iv) also needs more than
pairwise noncrossing. The formal fixture uses
`A={(1,1),(3)}`, `B={(1),(2,1)}`, and `C={(2),(3,1)}`: each pair is
noncrossing, but their orientations force `A < B < C < A`.

Exact proposed wording: “A finite noncrossing hierarchy is a finite family of
pairwise disjoint address cuts equipped with a global rank such that, whenever
selected addresses from two levels are comparable, strict containment points
from the lower rank to the higher rank.” Equivalently, require the induced
level-orientation graph to be acyclic and choose a topological order. For two
entirely incomparable cuts, retain their source labels (or an explicit
tie-break) rather than claiming a canonical lower/middle label swap.

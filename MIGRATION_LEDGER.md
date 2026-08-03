# P3-0 migration ledger

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
  foundation or executable representation.

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
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `PrimitiveBase` | `Potkin/ProofTheory.lean`: `MaterialBase` | replaced | Removes the fixed primitive-fragment side condition and uses an arbitrary proof-relevant whole-boundary evidence family. No closure laws are added. |
| `nonmonlogics` | N | `nonmonlogic/Nonmonlogics/LanguageSignature.lean` | `RuleSystem`, `ProofTheory` | `Potkin/ProofTheory.lean`: `RuleSystem`, `ProofTheory`, `ProofTheory.Admits` | generalised | Separates logical and structural occurrence admission, retains initials, and gives material admission an explicit nullary evidence branch. |
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

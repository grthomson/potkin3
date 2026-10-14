# Native sparse-material-record audit

10 October 2026. Repository baseline: `93b4a9abce87692ac32665132144ba1cd602808c`.
The existing `AGENTS.MD` change and the supplied research folders are preserved.
No branch, commit, Racket change, Python prototype, or full build was made.

## 1. Contribution and verification status

`Potkin/MaterialDegree.lean` supplies constructor-recursive proofs that the
existing maximal-material plan maximizes detached positive vertex degree, and
that every tie has exactly the same native address cut. The public result is
`ExtensionalCKCut.unique_materialDegree_maximizer`. Its source is an ordinary,
non-pure native tree; eligible cuts have wholly material detached factors.
The empty degree-zero case is included. A pure whole tree instead needs the
separate whole endpoint: this contribution never fabricates a root cut.

`Potkin/Examples/MaterialRecordObstruction.lean` checks two raw derivations in
one exact equipped registry and proves a focused collection obstruction.
Swapping distinct same-boundary material grounds gives the same maximal
commutative forest and literal boundary-only remainder, but different ordered
detached tuples and sources. Both native fills reconstruct their own source.
This is a greatest-term ambiguity, NOT equality of the full coactions.

The native degree theorem and the alignment/reconstruction example are now
**MECHANIZED**. The degree statement and dependent-elimination correction were
independently source-reviewed. The full sparse-record theorem is NOT thereby
mechanized. The new sources contain no `sorry`, `admit`, or custom axioms.

Targeted verification commands, from the POTKIN3 root:

```powershell
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\MaterialDegree.olean .\Potkin\MaterialDegree.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\Examples\MaterialRecordObstruction.olean .\Potkin\Examples\MaterialRecordObstruction.lean
```

The initial degree attempt was stopped at approximately 62 seconds under the
old hard-timeout policy. The user then explicitly authorized the longer
monitored policy. The authorized retry showed increasing Lake CPU activity,
then a Lean child checking the actual module. It completed in 319.06 seconds
with exit 1 and a concrete nested-dependent-pattern error, rather than a
silent environment failure. The attempted five-minute stop found that the
process had already exited; its final buffered diagnostics supplied the error.
A single startup diagnostic using the toolchain's absolute `lean.exe --version`
returned exit 0 in 0.36 seconds (Lean 4.29.0-rc1).

After replacing the nested `.descend (.ordinary ...)` pattern with
`.descend cut` followed by `cases cut`, the degree command passed in **63.10
seconds**, exit 0. The fixture command passed in **69.97 seconds**, exit 0.
Those runs used an automatic five-minute process-chain limit and CPU
checkpoints. No unchanged failed command was repeatedly restarted.

`#print axioms` ran for `CKCutPlan.materialDegree_optimal`,
`CKCut.materialDegree_le_and_eq_addresses`,
`ExtensionalCKCut.unique_materialDegree_maximizer`,
`Examples.MaterialRecordObstruction.greatest_term_loses_alignment`, and
`Examples.MaterialRecordObstruction.native_refills`. Every successful result
listed exactly `propext`, `Classical.choice`, and `Quot.sound`: no `sorryAx`
or custom axioms occur in those theorem dependency closures. The earlier
failed run's `sorryAx` output was an error placeholder and is superseded by
the successful corrected compilation. No full build, test suite, dependency
installation, umbrella import change, commit, or push was performed.

## 2. Correspondence to the proposed theorem

The supplied `mixed_2026_10_10/mixed_theory.md` sections 1–3 and 8, and
`continuation_2026_10_10/bridge_completion.md` sections 2, 3 and 6, require
persistent named origin seams and physically indexed material coefficients.
Those names share a factor-to-hole correspondence and are rigid under the
ordinary quotient. Under this hypothesis the swapped-ground example does
NOT refute the paper: the jointly named coefficient/remainder data differ.
Which coordinate differs depends on the consistent choice of origin names.

The native degree proof establishes one genuine combinatorial ingredient of
the reverse direction, not `K(t)=K(u) ↔ (id ⊗ q)ρ(t)=(id ⊗ q)ρ(u)` itself.
Its recurrence is:

- A positive pure branch is best detached whole. Every descent retains its
  positive root, so degree partition gives a strict loss of at least one.
- An impure branch cannot be detached by a pure-factor cut; recurse below it.
- Independent ordered premises add their optima. Equality of the sum forces
  equality at each premise, hence the same exact address support.
- Interfaces contribute zero vertices and cannot be detached.

The paper's shell need not be literally logical-only: it retains impure
primitive applications outside islands. `MaterialDownwardClosed` is NOT an
extra hypothesis of the paper theorem. In the native result,
`AllVerticesMaterial` tests material kind. Interpreting this as exact selected
base membership requires local admission in the fixed corresponding theory;
it does not implement an arbitrary narrower selector inside another base.

## 3. Reused native results and exact missing bridge

| Data | Existing source | Scope |
| --- | --- | --- |
| Exact occurrences and admission | `Occurrence`, `ProofTheory`, `Presentation`, `Checked` | Whole hypersequent boundaries, ordered premises, supplied incidence, exact registry provenance |
| Typed positive trees and forests | `CKTree` | Premises ordered; `CKForest = Multiset CKComponent` commutative, with multiplicity |
| Actual cuts | `CKCut`, `CKCutValidity` | Prefix-free nonroot addresses, dependent sites, ordered detached tuple, public extensional identity |
| Remainder and refill | `CKCut`, `CKCutPuncture`, `RealizedCut` | Typed punctures, selected-site matching, literal reconstruction and admission heredity |
| Degree and maximal regions | `CKCut`, `MaterialSupport`, `MaterialRegions` | Degree partition, existing maximal plan, purity, explicit whole-root exception |
| Material partition under filling/opening | `MaterialSupportCut`, `MaterialSupportListLaws` | Addressed occurrences and multiplicities, not a linear material coaction |
| Two-stage opening | `NestedCoherence`, `RealizedNestedCoherence` | Actual decorated-tree/component equivalences, not an instantiated tensor coalgebra |

`LocalOccurrence.id` identifies an exact registered instance, which may be
used more than once. Physical uses have addresses. `detachedTuple` retains
these; `detachedForest` forgets the source-address association.
`CKTree.interface G` retains the complete boundary `G`, but no persistent
material-origin name. A zero-vertex interface is not a positive generator,
and the forest unit is not a typed whole-proof vacancy.

There is no native ordinary mixed logical quotient, formal linear material
coaction, or instantiated CK coalgebra coassociativity declaration in this
baseline. No parallel replacement carrier has been introduced here.

## 4. Reverse, forward, linear and hereditary obligations

The greatest cut is unique WITHIN one source. This alone does not recover
alignment ACROSS sources after collection. Faithful recovery additionally
needs persistent physical origins shared by coefficients and inherited/new
holes, exact complete interfaces, quotient rigidity, once-use of each seam,
and equivariant well-typed hole-to-token relabelling. Degree zero must retain
all inherited holes in the empty term; it does not mean no material vertex
occurs in an impure host. Pure hosts require a separately named whole endpoint.

For the forward direction, record equality must independently induce a
bijection of ALL actual material cuts, including internal nonprimitive cuts,
with exact forests and corresponding complete residual shell classes.
Typed open-shell congruence under partial island opening/filling is needed.
Defining record equality by this desired conclusion would be circular.

The paper supplies a legitimate triangular linear argument CONDITIONAL on
distinct records having distinct reconstructing greatest-degree tensor basis
terms: choose maximal degree in a finite linear relation, eliminate its
coefficients using those distinct terms, then descend. Basis injectivity
alone is insufficient. The degree lemma does not establish the required
across-record greatest-term injectivity.

Residual-record heredity likewise requires the all-cut matching and named
seams. Native exact two-stage region coherence supplies tree-level ingredients
but must not be presented as the missing linear coassociativity theorem.
The full sparse equivalence, linear-kernel equality, descended comodule and
arbitrary nested flags are **OPEN in POTKIN3**, not contradicted by this fixture.

## 5. Finite-mode audit

The supplied finite-mode proof explicitly uses raw decomposition BEFORE
logical normalization, atomic-output selected rules, closed atomic origin
holes, linear capture-avoiding jointly resource-disjoint substitution, and
rigid probe namespaces. Compound fillers need no extra Boolean purity mode
under THESE assumptions: their raw logical boundary blocks a spanning pure
cone. Tensor principal reduction before extraction changes this observation
and can create a new composite; that is a different operation.

Free Ref substitution and whole-origin-hole filling are different operations.
The latter may enlarge or split the retained material templates. Both need
native admission and complete interfaces, not displayed-succedent equality.
Formal nullary probes are not conservative or automatically admitted in a
fixed/nonmonotone base. Jointly admitted complete-judgment witnesses and the
fresh unary separating context are required for completeness/maximality;
unrestricted formal equality is only sufficient in a restricted actual base.
The entire correlated mode tuple must remain one basis label: separately
linearized coordinates can lose correlation by cancellation.

No contradiction was found under the papers' stated restrictions. Their
finite-mode theorem is NOT instantiated or mechanized here. Exact next
dependencies are the named-seam sparse theorem, rigid mixed open equality,
checked simultaneous substitution/refill, admitted fresh extension witnesses,
all-cut factor/residual heredity, and the composite cut-expansion bijection.

## 6. Mathematical application and next obligation

A faithful sparse/signature theorem would support replacement preserving
actual intact composite modules, their complete residual operations and
subsequent declared extraction/refill histories. No runtime deadlock freedom,
memory safety or general behavioral equivalence follows without an adequate
operational interpretation.

Replacing a nullary probe by a composite proof is not a Hopf morphism: the
composite has additional internal cuts. The required Faà di Bruno bijection
partitions actual expanded cuts into old nonprobe antichains and independent
inner cuts in UNSWALLOWED fillers; old selected ancestors carry whole expanded
payloads and suppress their inner choices. Existing filling and two-stage
cut coherence are ingredients, not this whole-composite cut bijection.

The continuation below supplies raw origin-enriched reconstruction. Rigid
open-shell quotient equality and all-cut correspondence remain separate gates.

## 7. Origin-enriched native reconstruction continuation

### Minimum data and validity conditions

`Potkin/OriginCuts.lean` defines `CKTree.OriginNames Origin` and
`CKChildren.OriginNames Origin` by recursion over the EXISTING native trees.
An interface has one name; an ordinary vertex has one name and annotations
for its existing ordered children. `OriginTree` and `OriginComponent` are
dependent annotation wrappers, not a second proof syntax. Components retain
the original complete hypersequent boundary, exact occurrence, supplied
incidence, native subtree and positivity proof. No whole source, cut witness,
reconstruction theorem or desired equivalence is stored in the extracted
remainder or coefficient packets.

`OriginForest` is a COMMUTATIVE `Multiset OriginComponent`. The extraction
implementation traverses native sites before collection. The decoder does
NOT receive that traversal order, a source address, source, cut, or tuple.
It receives only the collected enriched forest and enriched remainder,
looks up factors by root origin, checks the complete boundary, and fills the
corresponding native interface. It does not recursively fill an inserted
factor: its inherited holes are retained as payload, not opened a second time.

The stated validity condition is extraction from a native cut of a source
whose `originList` is `Nodup`, including ALL ordinary vertices and inherited
interfaces. This is an independent freshness condition, not a reconstruction
witness. `originFactors_typedMatching` proves matching complete-boundary and
origin keys. `originRoots_nodup` and `remainder_holeOrigins_nodup` give unique
factor roots and unique vacancy origins, hence once-only matching on this
extraction image. The total mathematical decoder is NOT a validator for
arbitrary input pairs: it can ignore unused factors or leave an unmatched or
wrong-boundary hole unchanged. No arbitrary-input validation theorem is claimed.

Origins are generic immutable birth identifiers supplied by the caller.
Distinct physical uses of the same `LocalOccurrence.id` receive distinct
names. Source birth addresses can initialize names in a scoped namespace;
no automatic initializer or copy-renaming algorithm is claimed. Current
addresses may change when rerooting. Opening restricts existing annotations,
and a new vacancy receives precisely the opened root's old name, rather than
its new current address. Native ordered premise positions never change.

### Exact collected-data theorem

With the usual implicit signature, instance-data, origin, boundary and native
source parameters, the public statement is:

```lean
theorem CKCut.decode_collected (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) :
    OriginTree.decode (cut.originForest names) (cut.enrichedRemainder names).native
      (cut.enrichedRemainder names).names =
        (⟨tree, names⟩ : OriginTree sigma InstanceData Origin G)
```

The source is on the conclusion's right side, NOT an input to `decode`.
`CKCut.collected_injective` then proves that two fresh sources with equal
enriched remainders and equal collected enriched forests are equal as raw
annotated native trees. Equality is structural; it is not defined by all cuts.
The constructor proof separates the forests of disjoint ordered premises by
fresh origin keys, preserves untouched interfaces, and performs a typed root
lookup at actual detached branches.

`CKCut.enrichedRemainder_forget` projects literally to the native remainder.
`CKCut.originForest_forget` projects to the EXISTING `detachedForest`, and
`originForest_card` retains multiplicity. `originFactors_forget` gives the
stronger native site-order compatibility before collection. These laws do
not change the native commutative forest product or recover order from it.

`CKTree.decode_maximalMaterialCut` specializes the general theorem using the
already mechanized maximum, for ordinary non-pure hosts. It does not require
`MaterialDownwardClosed`. `AllVerticesMaterial` remains a kind predicate, not
an arbitrary exact-base selector. `decode_collected_locallyAdmitted` in
`OriginCutCoherence.lean` explicitly preserves admission to the SAME equipped
presentation, given native source admission. Wrappers and decoder results
are ambient native trees, not a way around the private checked-node checker.

Empty cuts are included. The plan-level interface case retains a zero-vertex
source and its inherited name with an empty forest. Pure whole hosts have
`OriginTree.decode_wholeOpening`: one positive packet and its named typed
vacancy reconstruct the source. This is a separate module-opening law, NOT
a public root cut, forest unit, or instantiated algebraic `t tensor 1` theorem.

### Focused swapped-ground regression

`Potkin/Examples/OriginCuts.lean` reuses the two already checked derivations
and their maximal native cuts, without adding a finite-enumeration programme.
The forgotten greatest terms remain equal. With names fixed at physical
source slots, the enriched remainders remain equal but the enriched forests
differ; `enriched_forests_differ` follows from the general collected
injectivity theorem and existing source inequality. `decodeAB` and `decodeBA`
recover the respective annotated sources. Under another consistent policy
that follows each primitive payload's name through the swap, the named
remainders instead differ. The pair is distinguished in either policy.

The existing duplicate-ground source supplies one further tiny regression:
two uses of the SAME exact registered ground retain root names `{1, 2}` and
forest cardinality 2. No theorem about all cuts or full coactions is inferred
from these examples.

### Nested opening: exact present scope

`Potkin/OriginCutCoherence.lean` restricts names through actual native
dependent sites (`originDetached`). `originDetached_sublist` proves that each
restriction preserves original names and freshness. New relative-cut
vacancies inherit the corresponding actual opened roots via
`originRemainder`; inherited interfaces keep their old names.

For any outer native cut and a family of native inner cuts on its actual
detached components, `CKCut.stagedOriginForest` computes each inner
collected-data decoder first, then collects the reconstructed middle packets.
`stagedOriginForest_eq` and `decode_twoStage` prove that lower-then-middle-then-
root reconstruction equals direct extraction/refill, including all annotations.
The grouping uses the existing native relative-cut family; lower and middle
layers are not flattened into a new carrier.

`CanonicalThreeRegionDecomposition.originDecode_forget` specializes this to
the existing canonical noncrossing decomposition. Its final native output
equals the EXISTING `composedFilling`, by that native reconstruction theorem.
This is a final-output projection. It does NOT lift the full
`exactTwoStageRegionCoherence` package to origin-decorated alternative
schedule triples, componentwise origin bijections or coefficient multisets.
That stronger enriched schedule comparison remains OPEN. No linear
coassociativity, tensor coalgebra or descended comodule is claimed.

### Precise remaining logical-quotient bridge

Raw annotated reconstruction is not quotient reconstruction. The next bridge
requires independently stated properties, not a sparse-injectivity assumption:

1. An actual ordinary open logical equivalence preserving complete interfaces,
   exact admission, hole multiplicity and declared port/resource discipline.
2. Rigidity, or explicit capture-avoiding equivariance, for primitive physical
   origins and named material seams. Logical administrative vertex names may
   be coherently eliminated by logical equations; raw all-vertex names must
   not simply be imposed as rigid invariants of beta/eta reduction.
3. Well-typed hole-to-token relabelling at the COMPLETE boundary, in a shared
   origin namespace with exact once-use matching and consistent token labels.
4. Compatibility of this relabelling with EVERY declared logical equation,
   so it descends to classes rather than just raw syntax.
5. Congruence of those classes under well-typed partial island opening and
   filling, with coherent transport of old and newly exposed seams.

The general native theorem permits whole hypersequent boundaries. The paper's
closed-atomic material-hole restriction remains an additional application
hypothesis; it does not follow automatically from native typing. Exact selected
base membership requires the relevant theory/admission, not just material kind.

Even after that bridge, the forward all-cut correspondence and the triangular
linear independence step remain obligations. Full sparse-record equivalence,
its linear-kernel consequence, the finite-mode theorem and descended comodule
remain OPEN. The original swapped fixture refutes forgetting the seam matching,
not the paper's appropriately origin-enriched formulation.

### Verification and independent review

The raw general reconstruction, forgetting, freshness and typed-matching laws,
maximal specialization, staged reconstruction and final native projection are
now **MECHANIZED**. The two swapped-source regressions and repeated-use
multiplicity statements are also Lean-checked particular results, not finite
evidence offered as proof of the general statements.

Exact targeted commands, from the POTKIN3 root:

```powershell
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\OriginCuts.olean .\Potkin\OriginCuts.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\Examples\OriginCuts.olean .\Potkin\Examples\OriginCuts.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\OriginCutCoherence.olean .\Potkin\OriginCutCoherence.lean
```

| Module | Successful duration | Result |
| --- | ---: | --- |
| `OriginCuts.lean` | 64.16 seconds | Exit 0 |
| `Examples/OriginCuts.lean` | 63.55 seconds | Exit 0 |
| `OriginCutCoherence.lean` | 57.41 seconds | Exit 0 |

Four earlier core checks returned exit 1 in 94.45, 58.29, 83.70 and 87.82
seconds. The repairs concerned syntax/name resolution, dependent annotation
constructors and unfolding native recursive `Site` before a list-map law.
Three earlier staged checks returned exit 1 in 63.06, 47.42 and 49.42 seconds;
their concrete errors were dependent site-pattern elaboration, a native
namespace/projection rewrite and inconsistent match arity. Every rerun followed
a relevant source correction. No passing module was rerun unchanged. Runs
were monitored with a five-minute bound; 60-second checkpoints recorded live
Lean process CPU activity, not an assumed silent hang.

`#print axioms` ran for the following successful central declarations:

- `CKCut.decode_collected`, `CKCut.collected_injective`,
  `CKTree.decode_maximalMaterialCut`;
- `CKCut.originForest_forget`, `CKCut.originRoots_nodup`,
  `CKCut.remainder_holeOrigins_nodup`, `CKCut.originFactors_typedMatching`;
- `Examples.OriginCuts.enriched_forests_differ`, `decodeAB`, `decodeBA`;
- `CKCut.decode_twoStage`, `CKCut.decode_collected_locallyAdmitted`, and
  `CanonicalTwoStageWitness.CanonicalThreeRegionDecomposition.originDecode_forget`.

The successful dependency lists contain only `propext`, `Quot.sound` and,
where lookup is used, `Classical.choice`. No `sorryAx` or custom axioms occur
in those closures. A focused source search of the three new modules found no
`sorry`, `admit` or `axiom` declarations. Failed-run placeholder outputs are
superseded by the successful checks; they were never accepted as results.

The independent static reviewer found no circularity or serious mathematical
defect. It specifically confirmed that the decoder is not secretly given the
source, that forest collection remains commutative, and that staged
reconstruction must not be reported as enriched schedule-triple coherence.

No Racket command, broad tests, full build, dependency installation, umbrella
import change, existing degree-module recheck, commit or push was performed.
HEAD remains `93b4a9abce87692ac32665132144ba1cd602808c`; the existing
`AGENTS.MD` change remains 17 insertions and was not edited or staged. All
contributions and supplied research folders remain uncommitted.

## 8. Central endpoint correction and actual composite cut expansion

### Main result: ordinary CK needs an endpoint correction

**MECHANIZED — countertheorem, not a completed pointed sparse-record theorem.**

`Potkin/AtomicIdentityFragment.lean` specifies an infinite fragment of the
EXISTING native `CKTree`: two exact atomic material grounds, a two-premise
material occurrence, atomic identity, and atomic Gentzen Cut against identity.
Their complete boundaries and supplied component incidence are literal data
in one five-occurrence equipped presentation. `ClosedFragment` is a predicate
on native trees, not another proof syntax. It permits arbitrary material
branching/depth and identity-Cut detours, including inherited typed holes. It
does not claim full MILL, tensor/implication normalization, arbitrary Cut
continuations or general commuting conversions.

Logical equality is independently generated by the genuine right
identity-Cut equation and native ordered context congruence. The module proves
`logicalEq_iff_observe_eq`, named typed-filling congruence, origin-relabelling
congruence, and observer equivariance. Material origins, premise order and
typed holes are retained; administrative Cut/identity origins may disappear.
No equality is defined through the material observation.

`Potkin/SparseMaterialObservation.lean` defines `record` independently as the
commutative forest of FULL origin-enriched maximal material islands plus the
independently observed, typed maximal-opening shell. It stores neither a
source field nor a reconstruction witness. In a pure whole host the full
source is necessarily its one material island, not an extra hidden payload.

`standardObservation` is a finite multiset of monomials. It enumerates public
`ExtensionalCKCut` nonroot antichains once, including the empty cut, filters
actual pure detached forests and retains multiplicities after collection.
The whole contribution is added separately, with no root `CKCut` witness.
The monomial right coordinate is `some` of an existing typed observed
remainder, or `none` for the algebraic unit. This is an endpoint tag, not a
new proof, cut, context or forest carrier. The finite positive sum is not an
asserted implementation of linear coaction/coassociativity laws.

The exact checked, fresh example is `leaf = g₀` and
`detour = Cut(g₀, Ax)`. The complete island packet and named hole are the same,
so `record leaf = record detour`. But the ordinary whole endpoint is different:

```text
standardObservation(g₀)             = 1 ⊗ q(g₀) + g₀ ⊗ 1
standardObservation(Cut(g₀, Ax))     = 1 ⊗ q(g₀) + g₀ ⊗ Box₀
```

This displayed calculation explains the obstruction at paper level. Lean
proves inequality using the universal right-unit coordinate, not by assuming
these lists of terms agree with a finite oracle. `right_unit_mem_iff` and
`observed_equality_preserves_root_purity` establish that the separately
projected unit detects root purity on positive ordinary sources. The general
`pure_identity_detour_countertheorem` applies to arbitrary positive pure
composites, not just this ground. Its admitted specialization restricts both
trees to the SAME exact presentation. The positive-arity composite family and
`logical_equality_not_material_observation` prevent treating ordinary logical
equality alone as a valid CK-sensitive module-reuse criterion.

On arbitrary ambient `CKTree` values, `AllVerticesMaterial`/`PureDetached` are
kind predicates. Exact selected-base interpretation is asserted only on the
admitted fixed fragment: its only material occurrences are precisely the
three selected base members. The raw structural generalization does not
silently certify unregistered trees.

The native `detourIslandCut` selects internal address `[0]` (premise 1; Racket
address `[1]`). Its exact ordered tuple is the single FULL `g₀` component,
its typed remainder is the punctured Cut/identity shell, and observing that
shell gives `Box₀`. `detourIslandCut_refill` reconstructs the actual checked
detour. `detourIslandCut_origin_refill` reconstructs its full origin annotation
from the collected forest and named remainder under proven freshness.

**Correction propagated to the paper/application contract.** The ordinary
native CK endpoint is `t ⊗ 1`. The paper's complete named-hole whole opening
instead uses a typed endpoint such as `t ⊗ Box_t`. These cannot be silently
identified. Thus unrefined `K`-completeness is FALSE for the ordinary endpoint
contract. This does NOT refute the origin-faithful POINTED paper theorem.
Root-purity refinement is necessary for the ordinary positive-source contract;
its sufficiency is not established. Bare inherited whole holes are degree-zero
and have no positive whole contribution: the fragment separately mechanizes
that raw purity is not observable by this argument there. `record_inherited_hole`
gives their exact empty-island/named-hole record.

### Actual outer/inner expansion and a typed module consequence

**MECHANIZED — all intrinsic native cut witnesses, not only fixtures.**

`Potkin/CompositeCutExpansion.lean` treats a native installation cut's
remainder as a finite typed multi-site template. Fillers have the exact
site-indexed whole boundaries. `ExpansionChoices` is a recursive product/sum
of EXISTING native payload cuts and old-node choices, not another cut carrier.
At an old ordinary branch it chooses an old ancestor or recurses. Selecting
an ancestor suppresses EVERY independent inner choice below it. At an opened
installation site it chooses a native branch cut of the FULL composite filler,
including detachment of that filler root inside the surrounding host.

`CKCutPlan.compositeCutEquiv` and `CKCut.installedCutEquiv` give both inverse
maps for every actual intrinsic proper/empty cut of the filled proof.
`installed_outer_inner_injective` strengthens uniqueness: the actual native
outer cut and the site-indexed optional inner cuts determine the entire cut;
there is no extra hidden choice information. The old ancestor's factor is the
whole expanded subtree, possibly enclosing several modules, not a product of
their leaf inventories. `oldAncestor_suppresses`, `oldAncestor_fullFactor` and
`wholePayload_factor` give exact constructor statements.

Independent constructor recurrences assemble full factor lists and complete
typed remainders without calling the expansion map. The accepted
`expand_originFactors`, `expand_originRemainder` and `expanded_originObservation`
identify them with actual native extraction, before commutative collection.
Ordered component multiplicity, complete interfaces and supplied origins are
preserved. `expanded_locallyAdmitted` proves admission of the completed fill,
remainder and detached factors under the SAME presentation, assuming admission
of the source and every exact typed filler.

The substantive module consequence is `decode_expansion_twoStage`, together
with `expansion_stagedForest`: arbitrary further native extractions inside
the ACTUAL expanded composite factors reassemble those full factors first;
their collected origin forest and independently assembled residual then
reconstruct the complete installed proof. This retains full composite-module
identity which a primitive inventory loses. It connects the expansion to the
previously accepted `CKCut.decode_twoStage`, not merely to an unexpanded tree
filling law. Global freshness of the FILLED origin list is explicit and is
not inferred from individual filler freshness.

Scope limits: installation templates are remainders of native installation
cuts, with unchanged unrelated inherited holes and a retained host root.
The bijection is at the intrinsic `CKCutPlan`/`CKCut` witness level, not a new
equivalence of deduplicated public address-cut enumeration. The latter needs
an address-injectivity or representative-independence bridge. Native local
admission is not itself a new checker-quotation/completeness theorem; claiming
a checked COMPLETE installation additionally requires the native completeness
and exact-admission premises. No material projection, linear coaction identity,
Hopf morphism, or equality of alternative enriched schedule triples is inferred
from these structural expansion/reconstruction laws. The witness-free global
whole endpoint remains separate.

### Remaining central claims

**OPEN:** the complete origin-faithful POINTED `K ↔ (id ⊗ q)ρ` theorem, or a
sufficient purity-refined theorem with ordinary whole endpoints. In either
case the forward direction still needs quotient-compatible matching of ALL
eligible public cuts across equal records, and the reverse direction must
connect native maximal degree uniqueness to the actual quotient monomials.
`Potkin/SparseTopTerm.lean` mechanizes recovery of a unique greatest term and
its multiplicity from equal finite multisets; it is SUPPORTING mathematics,
not an instantiated sparse-record theorem or a linear-kernel theorem.

**OPEN:** full mixed-calculus equality/transport, mode completeness, arbitrary
future-base extension universality, typed installation linear coaction laws,
and universal Faà di Bruno/flag interchange. No finite fixtures are promoted
to proofs of these statements.

### Exact verification and independent review

All commands below ran from the POTKIN3 root, monitored under the explicitly
authorized longer policy. No full build, Racket/Python enumeration, test suite,
dependency installation, branch, commit or push was performed.

```powershell
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\SparseTopTerm.olean .\Potkin\SparseTopTerm.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\AtomicIdentityFragment.olean .\Potkin\AtomicIdentityFragment.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\CompositeCutExpansion.olean .\Potkin\CompositeCutExpansion.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\SparseMaterialObservation.olean .\Potkin\SparseMaterialObservation.lean
```

| Final accepted module | Duration | Result |
| --- | ---: | --- |
| `SparseTopTerm` | 47.42 seconds | Exit 0 |
| `AtomicIdentityFragment` | 50.04 seconds | Exit 0 |
| `CompositeCutExpansion` | 90.34 seconds | Exit 0 |
| `SparseMaterialObservation` | 48.11 seconds | Exit 0; unused-simp-argument warnings only |

The greatest-term module's first check failed in 43.57 seconds due to a missing
existing Mathlib count import. Six logical-fragment checks failed in 49.23,
53.50, 52.74, 47.53, 48.95 and 58.65 seconds while repairing dependent native
tuple projections/normalization elaboration. Four initial expansion checks
failed in 83.88, 75.45, 66.53 and 66.54 seconds due to universe/dependent-index
elaboration; repaired intermediate versions passed in 81.59 and 74.54 seconds.
The final strengthening added uniqueness in terms of outer/inner native data.
Every rerun followed a concrete source correction or theorem addition.
Passing versions were not rerun unchanged. The central countertheorem passed
its first command; cosmetic simp warnings were not used to justify another run.

`#print axioms` inspected the successful dependency closures of the logical
equality, filling/renaming, inherited-hole obstruction, central endpoint
countertheorems, greatest-term recovery, full expansion bijections,
outer/inner uniqueness, exact factor/remainder observations, admission and
staged decoder laws. They contain only `propext`, `Quot.sound` and, where
noncomputable observation/decoding is used, `Classical.choice`. No `sorryAx`
or custom axioms occur. A focused source search of the four new modules
found no `sorry`, `admit` or `axiom` declarations. Failed-run placeholder
outputs were not accepted as results.

Independent static review accepted the endpoint countertheorem and the full
cut expansion/application definitions. It independently confirmed the
standard-versus-pointed distinction, the positive-source restriction, exact
base scope, intrinsic/public-cut distinction and explicit filled-origin
freshness hypothesis. Reviewer agreement is not substituted for the kernel
checks above.

HEAD remains `93b4a9abce87692ac32665132144ba1cd602808c`. The existing
`AGENTS.MD` modification remains 17 insertions, untouched and unstaged. This
pass adds the four Lean modules and appends only this audit section; the
previous contributions/research folders and unrelated changes are preserved.
Everything remains uncommitted.

## 9. Exact MATERIAL coefficient composition and intact availability (2026-10-10)

**MECHANIZED:** the intrinsic/public physical-cut bridge, independent finite
choice sum, post-installation exact-base eligibility, complete coefficient
identity, pointed endpoint formula, restricted inherited-cut transport, and
actual staged availability. These are constructor proofs and finite-bijection
proofs, not agreement with an enumerated fixture. Section 8's pending
intrinsic/public bridge and material-projection gates are now closed in the
precise finite-sum sense below. Its algebraic and sparse-record gates remain.

### The coefficient theorem

Use the existing native installation `I : CKCut tree`, its typed payload
family `f`, source annotation `n`, and actual payload annotations `nf`.
`fillOriginNames` preserves retained origins and installs the supplied
physical origins; it does not manufacture global freshness.

`MaterialObservations.cutSum B t ordinary names` is the finite multiset

\[
  \mathcal M_B(t)=\sum_{c\text{ public nonroot cut of }t}
    [\operatorname{DetachedInBase}_B(c)]\,
    [\,(F_c^{\mathrm{origin}},R_c^{\mathrm{typed,origin}})\,].
\]

The empty cut is included; the witness-free whole endpoint is not. The
native forest is commutative. The cut's ordered sites and full detached
list are retained before this collection. Equal output monomials are
collected with natural-number multiplicity, never deduplicated.

The independently computed RHS traverses the installation constructors:
ordered child products; actual native branch cuts inside unswallowed
payloads; and an ancestor-selection choice that swallows all its payloads.
The latter contributes the FULL connected filled factor, not an inventory
of primitive vertices. Its eligibility is tested after installation.

Exact accepted declaration in `Potkin/MaterialComposition.lean:75`
(ambient variables `sigma`, `InstanceData`, `Origin`, `pi`, `G`, `tree`):

```lean
theorem material_cutSum_composition (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    cutSum B (installation.fill fillers) (installation.fill_isOrdinary fillers)
      (installation.plan.fillOriginNames fillers names innerNames) =
        expansionSum B installation fillers names innerNames
```

This is equality of FINITE COEFFICIENT SUMS on full native factor/state
basis elements. `installed_coefficient_eq` at line 279 proves equality of
the exact `.count operation` coefficients, including any collisions.
Applying any specified observer to the residuals preserves the equality
by multiset map; this does not supply observer congruence or sparse
completeness. `CKCut.publicEnumerate_filter_bind_expandedChoices` also
allows arbitrary multiset-valued continuations of the ACTUAL expanded
cuts, before collection, preserving their resulting multiplicities.

Why physical cuts are counted once:

- `IntrinsicCutIdentity.lean` proves native plan, child and branch cut
  injectivity from their address finsets. `ExtensionalCKCut.compiled_ofCKCut`
  and `CKCut.extensionalEquiv` make native compilation and public projection
  genuine inverses. Proof fields do not add cut representations.
- `CutExpansionSums.lean` independently constructs
  `CKCutPlan.enumerateExpansionChoices` and proves completeness and `Nodup`.
  It NEVER enumerates cuts of the completed proof on this construction path.
- `CKCut.installedPublicCutEquiv` identifies public completed cuts with
  exactly these choices. `publicEnumerate_perm_expandedChoices` is list
  permutation, and `publicEnumerate_eq_expandedChoices` is exact multiset
  equality. Enumeration order need not coincide; native slot and detached
  tuple order are unchanged.

### Exact eligibility, not an inventory approximation

`CKTree.AllVerticesInBase B` tests exact local-occurrence membership, retaining
the occurrence's complete boundary, supplied incidence and instance data.
Interfaces contribute `True`, not fake vertices or material generators.
`FilledInBase` and `EligibleExpansion` are independent native constructor
recurrences. `CKCutPlan.expanded_eligible_iff` proves

```lean
(installation.expandCut fillers choices).DetachedInBase B ↔
  installation.EligibleExpansion B fillers choices
```

For a selected retained ancestor, the precise completion criterion is
the retained skeleton plus EVERY complete filler below it. The deleted old
probe bodies need not have been material. Exact accepted declaration in
`Potkin/MaterialInstallation.lean:357`:

```lean
theorem CKBranchCut.spanning_available_iff (B : MaterialBase sigma InstanceData pi)
    (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (installation : CKChildCuts children)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) :
    (CKBranchCut.descend (.ordinary o children installation)).EligibleExpansion B
      fillers (.inl PUnit.unit) ↔
      (CKTree.ordinary o installation.remainder).AllVerticesInBase B ∧
        (∀ site, (fillers site).AllVerticesInBase B)
```

Consequently a retained nonmaterial vertex blocks that spanning operation;
a nonmaterial vertex removed WITHIN a replaced region does not. Inherited
holes impose no vertex-membership condition but remain in the complete
factor/state. A pure payload admits all its native inner cuts. An impure
payload blocks enclosing selections but may still have eligible INTERNAL
cuts; it is not globally discarded from the choice sum.

These ambient-tree identities alone are not proof evidence. The accepted
`admitted_material_composition` in `MaterialComposition.lean:260` explicitly
fixes one `T`, one `P : EquippedPresentation T`, the exact base `T.base`,
native source admission and admission of EVERY filler. It concludes native
admission of the installed proof, the coefficient identity, and agreement
of every choice's exact-base eligibility with the native material-kind
cut predicate. The bridge is
`CKCutPlan.detachedInBase_iff_material_of_admitted` and native admission
inversion, not a rule-name match. Local admission is still distinct from
hole-free checked-derivation completeness. The concrete application below
has literal successful native checker quotations in the SAME registry.

### Endpoints: pointed states versus ordinary coefficients

`MaterialObservations.pointedSum` is `cutSum + pointedWhole`. The separately
labelled whole opening exists iff the FULL installed tree is in `B`; it
returns its full positive packet and the named typed vacancy at its root.
`pointedStateSum` of a typed vacancy is only `1 tensor THAT vacancy`.
`pointed_sum_composition` in `MaterialComposition.lean:114` proves exactly

```lean
pointedSum B (installation.fill fillers) (installation.fill_isOrdinary fillers)
  (installation.plan.fillOriginNames fillers names innerNames) =
expansionSum B installation fillers names innerNames +
  expansionWhole B installation fillers names innerNames
```

`expansionWhole` tests the independent `FilledInBase` recurrence and is
NOT an element of the cut-choice enumeration. The host root is retained
and is never a selectable proper-cut address.

`MaterialObservations.coefficientCutSum` is a SEPARATE finite observation
on a positive native origin component, including positive OPEN components.
For proper/empty cuts its right coordinate is the singleton component of
the actual positive remainder; its whole coordinate is the EMPTY right
forest. Thus its nonroot terms are the positive-component rendering of
`cutSum`, while its whole summand has a different endpoint convention.
The pointed whole typed Box is not that empty forest, and no Box-to-unit
identification, erasure quotient or Hopf morphism is used.

**Exact algebraic gap:** these definitions do not yet instantiate a linear
coefficient Hopf algebra or a pointed comodule. An actual coaction claim
still needs the chosen linearizations and multiplicative coefficient
coproduct, counit, and coassociativity with the stated typed whole-opening
convention, including whole-enabled flag endpoints. No such law follows
merely from the raw multiset identity or decoder. These claims are **OPEN**.

### Intact operations and staged availability

`Available` observes a full forest PLUS typed origin-enriched root remainder,
not merely factor counts. The following exact accepted declaration is at
`Potkin/MaterialComposition.lean:169`:

```lean
theorem installed_operation_available_iff (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (operation : Operation sigma InstanceData Origin G) :
    Available B (installation.fill fillers)
      (installation.plan.fillOriginNames fillers names innerNames) operation ↔
    ∃ choice : installation.plan.ExpansionChoices fillers,
      installation.plan.EligibleExpansion B fillers choice ∧
        expansionTerm installation fillers choice names innerNames = operation
```

`coefficient_pos_iff_available` links this predicate to a strictly positive
coefficient. With global filled-origin freshness, `available_decodes`
reconstructs the entire source from this actual complete operation. Here
"complete operation" means FULL residual/interface data, not a hole-free
remainder; open middle operations are intentional.

The staged observation uses native inner families indexed by the physical
outer cut sites. It records THREE full coordinates: lower factor forest,
positive OPEN middle residual forest, and typed root remainder. Exact
accepted declaration in `Potkin/MaterialComposition.lean:230`:

```lean
theorem staged_available_composition_iff (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (operation : TwoStageOperation sigma InstanceData Origin G) :
    StagedAvailable B (installation.fill fillers)
      (installation.plan.fillOriginNames fillers names innerNames) operation ↔
    ∃ choice : installation.plan.ExpansionChoices fillers,
      installation.plan.EligibleExpansion B fillers choice ∧
      ∃ inner : (site : (installation.expandedCut fillers choice).Site) →
          CKCut ((installation.expandedCut fillers choice).plan.detached site),
        stagedTerm (installation.expandedCut fillers choice)
          (installation.plan.fillOriginNames fillers names innerNames) inner = operation
```

This is availability under installation followed by ACTUAL further extraction
inside full composite coefficients, not merely "refill returns the tree".
`pure_outer_all_stages`, supported by exact-base detached/remainder heredity,
proves all such inner cuts eligible and their middle components pure. It
covers subsequent proper/empty cuts, NOT their separately projected whole
openings. The previous `decode_expansion_twoStage` supplies full-packet
reassembly under global freshness; it is not promoted to a linear
coassociativity or alternative enriched-schedule theorem.

### Aligned inherited transport and gain/loss

`MaterialInheritedCuts.lean` uses ONLY existing native cuts and choices.
`CKCut.InheritedDomain I oldFillers oldCut` checks the old cut's unique
decomposition: at each declared installation site it may select the payload
root or leave the payload untouched by an empty descent; proper selections
inside that payload are excluded. Retained ancestor selections suppress all
interior choices. This domain is conservative: the exclusion applies even
if a declared site's old/new fillers happen to be equal.

`CKCut.transportInherited` takes that explicit domain proof and positive
replacement payloads and returns an existing public cut of the new fill.
`transportInherited_addresses`, `transportInherited_injective` and
`transportInherited_reconstructs` prove unchanged addresses, no physical-cut
collisions, and native ordered refill. The original uninstalled proof is
the special old filling `I.plan.detached`, via native reconstruction.
No old internal address is fabricated after deleting its region.

This transport aligns ADDRESS witnesses, not their full old/new packets.
Exact origins and full factor bodies may change. It does not preserve
material eligibility unconditionally. `spanning_replacement_gain` and
`spanning_replacement_loss` give both statuses at the SAME retained old
ancestor. Thus neither a positive full tensor defect nor unrestricted
eligibility preservation is asserted.

### Checked application: completion of an intact binary module

The five-occurrence `AtomicIdentityFragment.presentation` is unchanged.
Source and target are genuine native checker realizations in that one
registry:

\[
 \mathrm{Cut}(\mathrm{binary}(\mathrm{Cut}(g_0,\mathrm{Ax}),g_1),\mathrm{Ax})
 \quad\longrightarrow\quad
 \mathrm{Cut}(\mathrm{binary}(g_0,g_1),\mathrm{Ax}).
\]

Two physical installation sites are `[0,0]` and `[0,1]`. The first deleted
region was impure. Pure fillers create the eligible spanning cut `[0]`,
which detaches the WHOLE `binary(g₀,g₁)` with origin 0 and leaves the exact
`Cut(Box₀,Ax)` root operation (outer origins 5 and 6). The reverse replacement
loses that spanning eligibility. The partial inherited transport returns
the SAME public `[0]` witness, while the full factor changes and becomes
eligible: new eligibility is not confused with a newly created address.

Further proper extraction `[0]` WITHIN the detached binary exposes `g₀`
with origin 1, retains `binary(Box₁,g₁)` (origins 0 and 2) as the full open
middle component, and leaves `Cut(Box₀,Ax)` as root state. This actual
lower/middle/root operation specializes staged availability composition.
Global origin freshness and native refill are explicit.

`Examples/MaterialInstallation.lean` verifies the literal checker successes,
fillings, full factors/remainders, eligibility gain and reverse loss, and
the actual subsequent internal extraction. `Examples/MaterialComposition.lean`
connects these to positive coefficient, exact installed sum, actual staged
availability, and the inherited witness. Cross-state absence of these RAW
complete operations is proved by exact decoding and source/target degrees
7 versus 5, not by a failed finite membership test. It is not a claim about
their logically quotiented observations or a universal normalization theorem.

### Necessary research-note corrections and live targets

1. The former intrinsic/public multiplicity gap is closed; do not count
   redundant intrinsic witnesses or deduplicate observed monomials.
2. Replace "old pure factor" eligibility with retained exact-base skeleton
   PLUS full post-installation fillers. Keep internal cuts of impure fillers.
3. A primitive probe cannot be sent to a composite coefficient by a presumed
   Hopf morphism: its new internal cuts occur in this actual expansion sum.
   The Faà di Bruno interpretation is the full outer/compatible-inner
   substitution formula, not primitive inventory substitution.
4. Inherited comparisons require the stated partial address transport.
   Distinguish changed coefficients, newly eligible inherited addresses,
   and genuinely internal payload cuts. Arbitrary replacement can also lose
   eligibility. No unaligned positive defect is claimed.
5. Preserve the permanent ordinary-endpoint countertheorem from section 8.
   Purity refinement is necessary in its stated positive-source setting,
   not known sufficient. The origin-faithful POINTED sparse-record theorem,
   full logical-quotient completeness, and finite-mode universality remain
   **OPEN**; none is assumed here.
6. Full Hopf/comodule laws, whole-enabled universal flag interchange and
   consistency of arbitrary successive replacement schedules remain
   **OPEN**. The proved staged result is installation followed by actual
   proper/empty nested extraction, with all three operation coordinates.

### Targeted verification and independent review

All targeted commands use the POTKIN3 root and the explicitly authorized
monitored policy. No full build, test suite, Racket/Python enumeration,
dependency installation, branch, commit or push was performed.

```powershell
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\IntrinsicCutIdentity.olean .\Potkin\IntrinsicCutIdentity.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\CutExpansionSums.olean .\Potkin\CutExpansionSums.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\MaterialInstallation.olean .\Potkin\MaterialInstallation.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\MaterialInheritedCuts.olean .\Potkin\MaterialInheritedCuts.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\MaterialObservations.olean .\Potkin\MaterialObservations.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\MaterialComposition.olean .\Potkin\MaterialComposition.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\Examples\MaterialInstallation.olean .\Potkin\Examples\MaterialInstallation.lean
& 'C:\Users\gavin\.elan\bin\lake.exe' env lean -o .\.lake\build\lib\lean\Potkin\Examples\MaterialComposition.olean .\Potkin\Examples\MaterialComposition.lean
```

| Accepted module | Final duration | Result |
| --- | ---: | --- |
| `IntrinsicCutIdentity` | 53.79 s | Exit 0 |
| `CutExpansionSums` | 92.14 s | Exit 0 |
| `MaterialInstallation` | 59.97 s | Exit 0 |
| `MaterialInheritedCuts` | 65.09 s | Exit 0 |
| `MaterialObservations` | 72.28 s | Exit 0 |
| `MaterialComposition` | 47.15 s | Exit 0 |
| `Examples/MaterialInstallation` | 94.80 s | Exit 0 |
| `Examples/MaterialComposition` | 48.29 s | Exit 0 |

Relevant failed checks before accepted repairs: identity 57.28 s; sums
61.32 s; material installation 110.11 and 68.51 s; inherited transport
72.98 s; observations 76.72 s; composition 58.03, 56.56 and 56.22 s;
integrated application 161.58 and 51.28 s.
Failures involved dependent-index elaboration, explicit types/decidable
predicates, or syntax; no mathematical hypothesis was dropped. Every
rerun followed a concrete source repair. Passing sources were not rerun
unchanged. At 60-second checkpoints the monitors confirmed owned Lean
processes accumulating CPU; no command exceeded the five-minute policy.
The first integrated application check reached a unification heartbeat
limit while mismatched equality instances caused unnecessary unfolding.
The repair pinned the coefficient definitions and applied the accepted
membership/count and multiset-identity theorems, without evaluating cut
enumeration. The remaining dependent proof rewrite was repaired locally.

Successful central `#print axioms` closures contain only `propext`,
`Quot.sound` and, for classical finite observations/decoding, `Classical.choice`.
No `sorryAx` or custom axiom occurs in those successful closures. A focused
source search of the eight task modules found no `sorry`, `admit` or `axiom`
declaration. Failed-check placeholder closures were not accepted.

Separate agents developed the public coefficient bridge and the material
eligibility/application. Independent adversarial review accepted the raw
coefficient/staged statements and checked the endpoint, multiplicity,
admission, freshness and conservative inherited-domain qualifications.
Static reviewer agreement does not substitute for kernel checking.
The final integrated example's eight printed closures also contain only
the three standard axioms above. In particular both raw absence proofs,
positive coefficient, installed sum, staged application and inherited
exact witness were accepted together in the final exit-0 command.

HEAD remains `93b4a9abce87692ac32665132144ba1cd602808c`; `AGENTS.MD` remains
the existing untouched 17-insertion unstaged change. Prior uncommitted work
and research folders are preserved. This pass adds only the eight native
Lean theorem/application modules above and this directly relevant audit
section. Everything remains uncommitted.

## 10. Native typed inverse cuts (11–12 October 2026)

This pass implements M1 of the supplied inverse-cut task, not the entire
M1–M4 programme. It adds no alternative proof, cut, forest or context syntax.
HEAD remains `93b4a9abce87692ac32665132144ba1cd602808c`. The pre-existing
uncommitted files/research folders and `AGENTS.MD`'s 17 added lines are preserved.
There are no commits or pushes.

### Universal native result

`Potkin/AllHoleFilling.lean` defines a canonical `CKTree.LeafOccurrence` index,
its full native boundary, address and premise-recursive traversal, and
`CKTree.fillAssignment`. This adapter is independent of cut construction;
its interface clause invokes native `PunctureAt.root.insert` and its ordinary
clause retains the entire exact `LocalOccurrence` and ordered children.
Filling is injective for a fixed literal remainder. Admission is proved by
mutual constructor recursion in one fixed equipped presentation.

`Potkin/InverseCutGeometry.lean` proves native typed-puncture coverage, unique
physical leaf addresses, and complete duplicate-free traversal. Puncture
proof evidence is not part of leaf identity. Internal addresses are zero-based;
the existing Racket address conversion is unchanged.

`Potkin/InverseCut.lean` establishes the genuine equivalence

```lean
CKTree.leafAssignmentCutEquiv (R : CKTree sigma InstanceData G) :
  R.LeafAssignment ≃ R.CutAssembly
```

Here `R.LeafAssignment` is
`(h : R.LeafOccurrence) → CKTree sigma InstanceData (R.leafBoundary h)`,
and `R.CutAssembly` is the dependent pair
`(T : CKTree sigma InstanceData G) × {c : CKBranchCut T // c.remainder = R}`.
These are families/predicates over EXISTING native syntax, not another carrier.
The forward map fills independently then constructs an actual native cut.
The reverse map supplies the full detached tree at cut-created holes and the
unchanged typed interface at inherited holes. `allHole_reconstruction` uses
the independent adapter. Both inverse laws are proved, with dependent
transports justified by literal remainder equality. Fixed source plus literal
remainder determines a unique cut (`CKCut.eq_of_remainder_eq`); factor VALUES
plus remainder do not determine a varying source.

For positive R, `assignmentProperCut` and `assignmentPublicCut` expose existing
`CKCut` and `ExtensionalCKCut`. `assignmentProperCut_detachedTuple` identifies
the FULL native `CKCutEntry` list with positive providers in leaf order,
including exact addresses, boundaries and entire possibly-open trees.
`inverse_assignment_tuple` gives the reverse addressed classification;
`assignment_no_positive_tuple` proves all-interface assignments have no
positive selected entries. Native distinguished refill is also proved.
No order is reconstructed from a multiset. Only the existing `detachedForest`
projection forgets address matching and order, retaining multiplicity.

Endpoints reuse the existing `CKBranchCut`: descent on a positive source is
the native proper/empty case; detach is positive whole extraction to the typed
root interface; an interface has only identity descent with no positive factor.
Whole extraction is neither a fabricated ordinary CK root cut nor T tensor 1.

`admittedLeafAssignmentCutEquiv` assumes R locally admitted in ONE fixed P and
restricts all providers to P; it is not automatic from raw typed syntax.
`materialLeafAssignmentCutEquiv` uses exact `AllVerticesInBase B`, not rule kinds
or names. It allows pure OPEN providers and unchanged interfaces, and imposes
no material-purity assumption on the retained R. Admission and material purity
remain distinct predicates. Native whole HG boundaries are multisets; exact
local incidence records stay in the retained rule occurrences. No stronger
globally indexed incidence payload on an interface is claimed.

### Verification and status

The following targeted checks run from the POTKIN3 root. Successful checks
are Lean kernel checks of universal theorems, not agreement of finite n cases.
No full build, test suite, Racket, Python campaign or new cut-enumeration
campaign was run. Existing native fixture witness constants were reused.

The initial `lake env lean -o .\.lake\build\lib\lean\Potkin\AllHoleFilling.olean
.\Potkin\AllHoleFilling.lean` reached Lean elaboration but timed out after
303.63 s. One targeted process/toolchain diagnostic found no surviving owned
process or produced olean; subsequent commands bypassed launcher setup using
the unchanged toolchain binary below and the existing package search paths.

```powershell
$inversePackagePaths = @(Get-ChildItem -LiteralPath '.lake\packages' -Directory |
  ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' })
$env:LEAN_PATH = ((@((Join-Path (Get-Location).Path '.lake\build\lib\lean')) +
  $inversePackagePaths) -join ';')
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\build\lib\lean\Potkin\AllHoleFilling.olean .\Potkin\AllHoleFilling.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\build\lib\lean\Potkin\InverseCutGeometry.olean .\Potkin\InverseCutGeometry.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\build\lib\lean\Potkin\InverseCut.olean .\Potkin\InverseCut.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\build\lib\lean\Potkin\Examples\InverseCut.olean .\Potkin\Examples\InverseCut.lean
```

Actual execution set `LEAN_PATH` in each monitored child process rather than
changing the parent environment. Sixty-second checkpoints confirmed owned Lean
CPU progress. Each rerun followed a concrete proof/elaboration repair.

| Module | Final elapsed time | Result |
| --- | ---: | --- |
| AllHoleFilling | 65.31 s | Exit 0 |
| InverseCutGeometry | 53.09 s | Exit 0 |
| InverseCut | 85.08 s | Exit 0 |
| Examples/InverseCut | 90.16 s | Exit 0 |

Earlier concrete failed proof checks took 115.14 and 69.85 s (all-hole),
74.02 s (geometry), and 80.29, 96.15 and 83.73 s (inverse module). The first
example-module check took 86.05 s and failed on constructor elaboration,
missing decidable membership instances and an omitted theorem signature;
these were repaired with exact constructors and registry-membership proofs.
Repairs addressed dependent pattern elaboration, exact typed projections,
Sum-index transparency and tuple-entry annotation. No mathematical assumption
was weakened. Successful sources were not rechecked unchanged. The inverse
module has one harmless unused-binder warning.

The successful headline closures are:

- `fillAssignment_injective`, `fillAssignment_locallyAdmitted`,
  `leafAddress_injective`, `PunctureAt.exists_leafOccurrence`,
  `allHole_reconstruction`, `assignmentProperCut_detachedTuple`:
  `[propext, Quot.sound]`.
- `CKCut.eq_of_remainder_eq`, `leafAssignmentCutEquiv`,
  `inverse_assignment_tuple`, `admittedLeafAssignmentCutEquiv`,
  `materialLeafAssignmentCutEquiv`:
  `[propext, Classical.choice, Quot.sound]`.

A focused source search of the four new modules found no sorry, admit, custom
axiom, unsafe cast or native_decide. Two independent read-only reviewers found
the maps noncircular and the endpoint, material and admission qualifications
sound. Reviewer agreement is not a substitute for the kernel checks above.

The example module represents acceptance fixtures (a)–(i): unchanged interface;
nullary empty/whole separation; positive unary OPEN provider; left-only/right-only
singleton-value ambiguity; two equal physical uses; the existing AB/BA theorem;
ancestor masking in the actual RecursiveCut host and a composite provider host;
provably unequal native boundaries preventing the required assignment typing;
admitted logical impurity versus exact pure OPEN/interface eligibility.
These fixtures do not establish the universal equivalence.
Its four printed example closures (`left_right_ambiguity`,
`equal_provider_uses`, `native_refills`, `exact_material_rejects_impure`)
contain only `[propext, Quot.sound]`. The complete module compiles without
errors or warnings. Examples are supplementary kernel-checked concrete facts,
not the argument for arbitrary trees.

| Milestone | Status | Exact remaining obligation |
| --- | --- | --- |
| M1 universal native inverse cuts | MECHANIZED; complete | None within the stated M1 native contract |
| M2 ordered coefficient/coaction staging | OPEN | Full addressed ordered cut-flag bijection, including endpoint cases, BEFORE coassociativity/counit/WP laws |
| M3 effective residual saturation | CONDITIONAL / not implemented | Native M2 bridge and finite exact sorted registry hypotheses |
| M4 independent logical observation | CONDITIONAL / not implemented | M3 and independent normalization/derivation bridge |

Reused anchors: `GeneralFilling` (typed native insertion), `CKCut` and
`CKCutPuncture` (full witness geometry), `IntrinsicCutIdentity` (address
extensionality), `RealizedCut` (admission heredity), `MaterialInstallation`
(exact base predicate), `CompositeCutExpansion` (actual installed-cut bijection
and ancestor masking), and native `Examples/RecursiveCut`,
`Examples/MaterialRecordObstruction`, `AtomicIdentityFragment`.
The existing composite-cut bijection handles installation and masking; existing
`exactTwoStageRegionCoherence` handles its specified original-tree schedules
with commutative forests. Neither is the missing full ordered coefficient
cut-flag bijection. No public Hopf/comodule, normalization or finite residual
theorem is claimed from M1. The next smallest obligation is that addressed flag
bijection, preserving both ordered factor lists and all three pointed endpoints.

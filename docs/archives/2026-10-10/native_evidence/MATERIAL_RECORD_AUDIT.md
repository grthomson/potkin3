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
NOT refute the paper: the named residual shells differ.

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

The next mathematical gate is a faithful native specification of persistent
origin signatures and rigid open-shell equality, with a proved greatest-term
decoder and all-cut correspondence. The current contribution isolates degree
optimality without asserting those unformalized contracts or changing carriers.

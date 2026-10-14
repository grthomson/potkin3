# Native CK/mathlib exploration — 12 October 2026

## Scope and provenance

POTKIN3 HEAD at entry: `93b4a9abce87692ac32665132144ba1cd602808c`.
Lean: `leanprover/lean4:v4.29.0-rc1`. Pinned and installed mathlib HEAD:
`378b908c009ef82cf9584cba7447c44a5a89e58a`.
Only additive exploration files were edited. Existing uncommitted work,
including AGENTS.MD, was preserved. No commits, network services, package
installation, full builds, test suites, or finite cut-enumeration experiments.

This is not a claim that the entire project/paper is implemented. The native
installed-composite cut bijection already exists; it is reused, not proposed
as a missing theorem. The missing general ordered iterated cut-flag law is
different from that bijection and from the existing restricted two-stage law.

The checked sector needs an explicit guard: CKTree itself is not indexed by
an equipped presentation. CheckedDerivation P and LocallyAdmittedTree P
provide that guard. Complete HG boundaries are nonempty multisets of sequents;
ordered component profiles and incidence belong to exact LocalOccurrence
decorations, not to an additional global indexed payload on Box. Every native
bridge keeps those decorations and ordered premise slots. An interface is a
typed vacancy, not a positive factor or the empty forest.

## Triage of all six directions

| Direction | Decision and actual result | Exact limit |
|---|---|---|
| A: geometry | Selected. Native public cuts equivalent to eligible finite mathlib antichains; restriction, unique selected ancestor and disjoint cones. | Antichain alone does not certify positivity, nonroot status or vertex existence. |
| B: residual contracts | Selected. Independently defined admitted native cut relation; Post/Box Galois connection, arbitrary intersections, feasibility and inverse orientation. | No coefficient-convolution weakest-precondition staging law without a full addressed cut-flag bridge. |
| C: linearization | Selected. Native multiplicity-preserving count functions and installed-cut coefficient reindexing. Finsupp/tensor APIs were attempted but blocked by incomplete cached dependencies. | No free-module or tensor comparison is claimed verified. |
| D: substitution | Triage only; existing dependent LeafAssignment/filling/reconstruction audited. | Need dependent flattening of filled holes, boundary transport and address/order laws for staged substitution. No ordinary Monad Type instance claimed. |
| E: fixed points | Pinned lfp/map_lfp source audited; native least-reach adapter attempted then removed after a cached Set-lattice dependency gate. | No provider/observer replacement saturation, executable recognizer or finite exact abstraction. |
| F: Hopf/convolution | Triage only; genuine coalgebra convolution APIs identified. | Those APIs assume coalgebra/bialgebra/Hopf laws. They do not establish native flag coherence, normalization congruence, or connectedness of an interface-rich carrier. |

## A — faithful cut geometry

Native goal: reason about selected regions without erasing physical addresses
or introducing another recursive cut syntax.

Pinned import: `Mathlib.Order.Antichain`.
Exact relevant source declarations (`Mathlib/Order/Antichain.lean:40–65`),
with `{α : Type*} {r : α → α → Prop} {s t : Set α}`:

```lean
def IsAntichain (r : α → α → Prop) (s : Set α) : Prop := s.Pairwise rᶜ
protected theorem subset (hs : IsAntichain r s) (h : t ⊆ s) : IsAntichain r t
protected theorem eq (hs : IsAntichain r s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (h : r a b) : a = b
protected theorem eq' (hs : IsAntichain r s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (h : r b a) : a = b
```

Lean's pinned `Init/Data/List/Sublist.lean:893` supplies:

```lean
List.prefix_or_prefix_of_prefix
  (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁
```

Native `AddressPrefix p q := p <+: q` points ancestor-to-descendant. No
lexicographic List order is silently substituted for this relation.

BRIDGE: `CutGeometry.lean` defines `EligibleAntichains tree` as a subtype of
existing address finsets requiring source positivity, existing nonroot vertices,
and IsAntichain. `validCutAntichainEquiv` and `cutAntichainEquiv` use native
validation and the existing public-cut equivalence. Their round trip is equality
of the entire compiled native witness, not just its forest value.

CONSEQUENCES: `restrictNativeCut`, `selected_ancestor_unique`, and
`selected_descendant_cones_disjoint`. Plain meaning: restricting any proper/empty
cut gives another native cut; a physical vertex belongs beneath at most one
selected ancestor; detached regions of different selected addresses are disjoint.
These quantify over arbitrary native sources/cuts, not bounded fixtures.

Meaning audit: an existing admitted two-hole source retains distinct [0]/[1]
provider occurrences. Singleton root {[]} is an antichain but cannot be a cut.
A bare interface has no ordinary cut even though the empty set is an antichain.
No information is lost in the Equiv; projecting its result to a commutative
forest would still discard order/address information.

## B — native residual contracts

Native goal: a real universal remainder contract with admission, coefficient
eligibility, constructive witnesses and explicit infeasible cases.

`ResidualContracts.lean` independently defines:

```lean
NativeResidual P A source remainder :=
  LocallyAdmittedTree P source ∧
  ∃ cut : CKCut source, A cut.detachedForest ∧ cut.remainder = remainder
```

This is source→remainder, with the same exact output HG. The existing native cut
keeps ordered tuple, incidence, addresses and refill matching. Its coefficient
predicate A observes the commutative forest only. An arbitrary exact material
profile B may instantiate A via AllVerticesInBase; no arbitrary B is cast into
T.base, and kind-purity is not used in place of exact membership. Only the
existing admitted-sector theorem for B=T.base justifies that special equivalence.

Pinned imports: `Mathlib.Order.GaloisConnection.Basic`,
`Mathlib.Order.FixedPoints`. The complete-lattice candidate, with a Galois connection gc between
`l : α → β` and `u : β → α`, is (`GaloisConnection/Basic.lean:129`):

```lean
theorem GaloisConnection.u_iInf {f : ι → β} : u (iInf f) = ⨅ i, u (f i)
```

The available weaker lattice API actually used is (`Basic.lean:108`)
`theorem u_inf (gc : GaloisConnection l u) : u (b₁ ⊓ b₂) = u b₁ ⊓ u b₂`.
The Set CompleteLattice import encountered missing transitive compiled modules.
Rather than extend dependency rebuilding, the native arbitrary-intersection
law is proved directly via Set.iInter, alongside the library binary-inf law.

`OrderHom` on a complete lattice supplies (`FixedPoints.lean:49,58,71`):

```lean
def OrderHom.lfp : (α →o α) →o α
theorem OrderHom.lfp_le {a : α} (h : f a ≤ a) : f.lfp ≤ a
theorem OrderHom.map_lfp : f f.lfp = f.lfp
```

REUSE: relation-image/universal-preimage adjunction and binary-inf library law.
BRIDGE: `nativeResidual_galois` instantiates it with the independently defined
native relation, not an assumed coherence field.
CONSEQUENCES: `nativeResidual_witness` gives admitted remainder/providers and
native refill; `nativeBox_iInter` preserves arbitrary intersections;
`nativeBox_antitone_coefficient` states the correct polarity when eligibility
broadens. The converse relation, not an accidental reversal of quantifiers,
defines inverse-source Post/Box. `nativeBox_empty_iff` identifies vacuity exactly.

Meaning audit: the actual checked ground proof has a feasible empty native cut.
Whole extraction has a separate native pointed witness but is not an ordinary
residual; ordinary cuts retain the root. Interfaces and unadmitted sources can
meet Box vacuously, so a usable guarantee must also establish NativeFeasible.

E candidate (removed, not a compiled result): the least fixed point of
`states ↦ seed ∪ NativePost P A states` would describe forward cut-residual
reachability. It is not provider/observer replacement saturation or an executable
algorithm. Its complete Set-lattice prerequisites were blocked by the next
missing compiled dependency; no native lfp result is claimed. A finite exact
registry already has finite concrete registered boundaries, but arbitrary
admitted provider trees and A still require an exact finite *joint* observation
abstraction, constructor transitions, source guards and witness reconstruction.
Independent projections may invent provider/observer pairs. This mathematical
bridge remains BLOCKED even if the cached import issue is repaired; neither lfp
existence nor a height bound supplies it.

## C — native coefficients; blocked tensor comparison

Native goal: move existing universal cut reindexing into library linear algebra
without collapsing occurrence multiplicities or assuming a coalgebra.

Final imports are only the already-available native modules CutExpansionSums,
InverseCut and Examples.InverseCut. The attempted
`Mathlib.LinearAlgebra.DirectSum.Finsupp` and narrower
`Mathlib.LinearAlgebra.Finsupp.Defs` have incomplete cached dependencies.

`Mathlib.Data.Finsupp.Multiset` contains the intended `Multiset.toFinsupp` API,
but its compiled module is absent here. Its underlying Finsupp constructor is
source-present (`Data/Finsupp/Defs.lean:88`), but that compiled module is also
absent, so the following library bridge was NOT implemented in the final module:

```lean
structure Finsupp (α : Type*) (M : Type*) [Zero M] where
  support : Finset α
  toFun : α → M
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0
```

The final native fallback is `linearize bag : Basis → ℕ`, defined by bag.count.
`linearize_add` and `linearize_support_finite` prove exact
count/add/finite-support laws (the latter gives an explicit Finset witness). The support is exactly bag.toFinset; values
retain bag.count, not deduplicated membership. `List.count_map_of_injective`
and the native public enumeration count theorem establish the individual
coefficient consequence. This scalar query is not silently an asserted Finsupp,
free-module or tensor carrier.

Exact pinned tensor declaration (`DirectSum/Finsupp.lean:300`, under
`(R ι κ : Type*) [CommSemiring R]`):

```lean
def finsuppTensorFinsupp' :
  (ι →₀ R) ⊗[R] (κ →₀ R) ≃ₗ[R] ι × κ →₀ R
theorem finsuppTensorFinsupp'_symm_single_mul (i : ι × κ) (r₁ r₂ : R) :
  (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i (r₁ * r₂)) =
    Finsupp.single i.1 r₁ ⊗ₜ[R] Finsupp.single i.2 r₂
```

BRIDGE: `CutBasis G := CKForest σ D × CKTree σ D G` uses existing carriers;
`cutCoefficients` is a Nat count function on that existing basis. `installed_coefficients` derives from the
existing `installedPublicCutEquiv` and universal Multiset enumeration equality;
`installed_filtered_continuation` also permits exact eligibility and multiset
continuations. Constructor choices retain ancestral masking; this is not a
finite agreement between two enumerators. The attempted `cutTensorComparison`
and `installed_tensor` were removed from the final compiling module after the
next cached dependency gate. The source API above is exact, but its application
here remains BLOCKED / NOT RECHECKED. Pair-indexed Finsupp equality is not claimed
as a proved tensor equality.

CONSEQUENCE: for ONE fixed complete decorated source and its FULL LITERAL typed
remainder, `cutBasis_injective` and `coefficient_at_native_cut` show each cut's
basis coefficient is exactly 1. This uses the existing inverse-cut remainder
injectivity theorem. It does not reconstruct an unknown source from coefficient
values. Equal factors *inside* one forest still have multiplicity 2; a repeated
native witness family separately has coefficient 2. Source-family aggregation,
observed/quotiented remainders and further projections can collide.

Controlled generalization: `changeCoefficients` postcomposes the count function
with an additive map ℕ→+R and `[AddMonoid R]`, not necessarily a ring.
`∀ n, map n = 0 ↔ n = 0` is proved sufficient for support preservation.
The zero additive map erases a native family of coefficient 2; it is NOT a
unital semiring map. The stronger unital-ring ZMod 2 cancellation probe and
Finsupp.mapRange bridge were removed after the import gate. Characteristic-two
cancellation remains a paper counterexample, not a mechanized theorem here.
No unconditional coefficient-ring support theorem is claimed. This controlled
extension proves a scalar support statement, not a module comparison.

Information lost: forest coordinate is already commutative; literal remainder
retains ordered attachments. The refinement excludes the global whole endpoint;
right coordinate is a positive open typed tree, never silently the forest unit.
It is coaction-shaped, not yet a coalgebra A→A⊗A or full coassociativity theorem.

Used count APIs are exact pinned mathlib declarations, under DecidableEq α:

```lean
-- Data/Multiset/Filter.lean:338
theorem count_map_eq_count' [DecidableEq β] (f : α → β) (s : Multiset α)
    (hf : Function.Injective f) (x : α) : (s.map f).count (f x) = s.count x
-- Data/Multiset/Count.lean:127
theorem coe_count (a : α) (l : List α) : count a (ofList l) = l.count a
-- checked by the final probe's #check
Multiset.count_add (a : α) (s t : Multiset α) :
  Multiset.count a (s + t) = Multiset.count a s + Multiset.count a t
```

## Integration and adversarial audit

`Integration.lean` proves `nativeResidual_unique_witness` and
`nativeResidual_coefficient`: a feasible residual with fixed source/literal
remainder has a unique actual native witness, coefficient 1 and native refill.
It does not choose an address from a collected coefficient.

Two existing failure cases are kept live, not explained away:

1. `varying_source_ambiguity`: equal-boundary left-only/right-only provider
   insertions have the same full forest and literal remainder, but different
   sources and physical addresses [0]/[1]. This does not contradict fixed-source
   injectivity. Both are admitted under the same exact registry.
2. `admitted_identity_cut_obstruction`: for arbitrary admitted positive pure
   proofs in the actual atomic identity/Cut fragment, the checked logical detour
   preserves the island record but changes the ordinary material observation.
   The existing checked ground fixture is a concrete instance. Normalization
   equality is not material-coaction equality.

The geometry reviewer independently inspected the linearization and integration
claims statically: fixed-source guard, exact count multiplicities, actual native
installation bijection and zero-reflection condition. The original proposed
tensor adapter was also statically reviewed, then removed because its imports
could not be checked within the bounded dependency policy. No substantive defect
identified in the inspected proof statements. Review is not execution evidence.

## D/F rejected abstractions and gates

Pinned `Mathlib.Data.PFunctor.Univariate.Basic` defines
`PFunctor` with `A : Type` and `B : A → Type`; `P.Obj α := Σ a, P.B a → α`.
`Mathlib.Data.PFunctor.Multivariate.Basic` has `MvPFunctor n` with
`B : A → TypeVec n`. Neither directly supplies the native dependent output
boundary, exact per-premise HG and same-P admission. Sigma-packaging types does
not prove compatibility or lawfulness. Ordinary Monad Type is the wrong direct
kind. Indexed/relative substitution remains OPEN; see recommendation 2.
Analytic differentiation and univariate power-series composition are not a
bridge to typed punctures or a Faà di Bruno theorem.

Pinned `Mathlib.RingTheory.Coalgebra.Convolution` is genuine coalgebra convolution
of linear maps, unlike Dirichlet convolution. Its data-only operation
(`Convolution.lean:58`, in namespace LinearMap under the supplied module,
non-unital algebra and CoalgebraStruct assumptions) is exactly:

```lean
lemma convMul_def (f g : WithConv (C →ₗ[R] A)) :
    f * g = toConv (mul' R A ∘ₗ map f.ofConv g.ofConv ∘ₗ comul)
```

The associative instance `convNonUnitalSemiring` at :124 requires Coalgebra,
not merely CoalgebraStruct. Thus a data-only convolution operation does not
automatically carry an associativity or inverse theorem. `Coalgebra.Basic:81` assumes
coassociativity/counits; `HopfAlgebra.Basic:60` assumes a bialgebra and antipode
equations. These classes cannot manufacture the missing native ordered flag law.
No applicable graded-coalgebra/Hopf recursive-antipode API was found in the
targeted inspected modules; this is a scoped search result, not a library-wide
nonexistence theorem. Native degree partitions alone do not prove connectedness
when distinct typed interfaces are treated as degree-zero objects. No claim that
the positive-forest sector admits no connected grading is made. No Hopf instance,
Grossman–Larson replacement, antipode-as-normalizer, or cross-calculus safety
transfer was introduced.

## Ranked next three theorem targets

1. **Full native ordered cut-flag bijection, including endpoints.** Match two
   successive cuts with coefficient-factor refinements and compatible opposite
   schedules, preserving addresses, ordered middle/lower packets, typed
   remainders and matching. Burden: high dependent constructor induction and
   genuine endpoint cases; existing installedCutEquiv is an ingredient, not
   the result. Payoff: justified native coassociativity/coaction and staged
   coefficient-convolution residual law. CK is essential: generic relational
   composition cannot prove this combinatorial cut law.
2. **Lawful native staged all-hole filling.** Prove
   `(R.fillAssignment f).LeafOccurrence ≃ Σ h, (f h).LeafOccurrence`, preserving
   dependent leafBoundary, ordered traversal and
   `filledAddress = R.leafAddress h ++ (f h).leafAddress inner`; transport the
   inner assignments and prove one-shot = two-stage filling, plus identity.
   Burden: medium mutual recursion and dependent Sum/Sigma transports; admission
   then follows from existing same-P filling. Payoff: checked compositional
   provider replacement. Filling alone is not specifically CK; the CK payoff is
   transporting installed addressed cuts/masking through that lawful staging.
3. **Finite exact inverse-cut fibre for fixed literal remainder and forest.**
   For an ordinary R and hR : R.IsOrdinary, prove
   `Finite {f : R.LeafAssignment // (R.assignmentProperCut hR f).detachedForest = F}`
   using the existing inverse-cut equivalence, finite holes, factor membership
   and exact multiplicity matching; then expose a witness-reconstructing
   enumeration with decidable source/profile guards. Burden: medium finite
   dependent-family restriction, including interface providers and duplicate
   factors. Payoff: exact feasibility/violating-source search for this fixed
   fibre, not arbitrary finite provider/observer saturation. Native CK matching
   is essential; matching displayed boundaries or factor values alone admits
   the left/right ambiguity. This target is a universal finiteness theorem,
   not testing finitely many small proof heights.

## Actual compilation commands and results

All commands below ran from
`C:\Users\gavin\Desktop\coding2023\lean_projects\potkin3`.
The child LEAN_PATH contained that repository's `.lake\build\lib\lean` and
the existing package build directories, separated by semicolons. Lean was
invoked directly, not through lake env. Each monitored command had a 300-second
cap and a 60-second CPU/process checkpoint. None reached the cap. Generated
output was confined to existing `.lake` build directories.

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\build\lib\lean\Potkin\Exploration\CutGeometry.olean .\Potkin\Exploration\CutGeometry.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\build\lib\lean\Potkin\Exploration\ResidualContracts.olean .\Potkin\Exploration\ResidualContracts.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\build\lib\lean\Potkin\Exploration\CutLinearization.olean .\Potkin\Exploration\CutLinearization.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\build\lib\lean\Potkin\Exploration\Integration.olean .\Potkin\Exploration\Integration.lean
```

| Target | Final result | Elapsed seconds | Earlier attempts and concrete changes |
|---|---|---:|---|
| CutGeometry | exit 0 | 80.37 | 98.70 s, exit 1: replace instance-sensitive `rw [Set.disjoint_left]` by explicit `.mpr`. |
| ResidualContracts | exit 0 | 44.55 | 74.55 s: missing Set complete-lattice instance/union orientation; 20.58/22.74 s: cached Bool.Set gate; 21.05 s: next Nat.Set gate. Removed native lfp adapter/unavailable import. 71.54 s: previous source snapshot's Set.iInter `change`; final snapshot uses Set.mem_iInter. |
| CutLinearization | exit 0 | 44.96 | 7.18 s: missing Finsupp.Multiset; 19.39 s: Bool.Set; 21.24 s: Nat.Set; 19.58 s: Int.Cast.Defs. Removed unavailable library bridge, kept native scalar counts. 65.55 s: concrete coercion/support/count proof errors; 43.46 s: remaining whole-basis equality-decider mismatch. Explicit classical basis decider fixes it. |
| Integration | exit 0 | 41.57 | First run; no corrections. |

One shared missing dependency, containing only three pinned Bool/Set lemmas,
was compiled once, exit 0 in 40.15 seconds:

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .\.lake\packages\mathlib\.lake\build\lib\lean\Mathlib\Data\Bool\Set.olean .\.lake\packages\mathlib\Mathlib\Data\Bool\Set.lean
```

On encountering the next missing dependency, the rebuild chain was stopped.
No dependency sources, revisions or installations changed. No unchanged
successful command was rerun. Every rerun followed a source/import fix or the
named dependency repair. Failed-compilation `sorryAx` recovery artifacts were
not accepted as theorem evidence; the final successful closures supersede them.

Progress examples: geometry Lean CPU 34.63 s at elapsed 60.99 s, contracts
43.45 s at 60.56 s, native coefficient check 64.86 s at 62.2 s. These establish
active Lean work, not a numerical performance comparison. Runs had different
imports/proofs and concurrent workloads; no cold/warm speedup is inferred.

## Tactic laboratory: six real goals

| Actual obligation | Explicit mathematical dependency | Observed automation / failure |
|---|---|---|
| Cut Equiv round-trip addresses | Equiv inverse law on the complete native cut | simp? suggested `simp only [Equiv.symm_apply_apply]`. Routine bookkeeping. |
| Selected address is nonroot | Native validation's address_nonroot field | exact? suggested `exact cut.validAddressCut.address_nonroot member`. Routine lookup, not a new geometry theorem. |
| Interface meets Box vacuously | Interface admits no ordinary cut | simp? suggested `simp only [nativeBox_interface]`. Must still require feasibility. |
| Arbitrary native Box intersections | Universal quantifier rearrangement, Set.mem_iInter | exact? found `nativeBox_iInter P A contracts`. An attempted definitional change failed; Set membership is not plain forall by definitional reduction. |
| Native installed-cut coefficient identity | Actual installedPublicCutEquiv and universal multiset reindexing | `fail_if_success rfl` confirmed the law is not definitional; exact? found `installed_coefficients installation fillers`. Search reused the proved bridge, did not invent it. |
| Additive finite-count observation | Multiset.count_add and function extensionality | ext/simp? suggested `simp only [linearize, Multiset.count_add, Pi.add_apply, Nat.add_left_cancel_iff]`. Routine scalar bookkeeping. |

Central proofs keep explicit dependencies. A further useful engineering failure
was `change` between generic-classical and concrete-product equality deciders:
their counts agree propositionally, but are not definitionally identical. A
local explicit whole-basis decider resolved it. No global simp rules, rewrite
loops or broad tactic rule sets were added. No unsupported fun_prop call or
unrelated arithmetic/algebra benchmark was performed.

## Final status and trust

All four new Lean modules compiled. Geometry/contract bridges and the scalar
coefficient consequences are MECHANIZED universal results. Their actual
admitted/checked examples and endpoint failures are kernel-proved fixed native
examples, not evidence establishing universal results by finite agreement.
Generic relational adjunction/composition and scalar support lemmas are
MECHANIZED generic infrastructure, separately from their native adapters.

Successful #print axioms closures:

| Headlines | Exact axiom set |
|---|---|
| validCutAntichainEquiv, cutAntichainEquiv, restrictNativeCut | propext, Quot.sound |
| selected_ancestor_unique, selected_descendant_cones_disjoint | propext, Classical.choice, Quot.sound |
| nativeResidual_witness, nativeBox_iInter, nativeBox_empty_iff, whole_extraction_endpoint_failure | propext, Quot.sound |
| nativeResidual_galois, nativeBox_inter, nativeInverseResidual_galois | propext, Classical.choice, Quot.sound |
| cutBasis_injective, coefficient_at_native_cut, installed_coefficients, installed_filtered_continuation, linearize_support_finite, duplicate_native_family_erased_zero_map, equal_detached_factor_multiplicity | propext, Classical.choice, Quot.sound |
| changeCoefficients_support | propext, Quot.sound |
| nativeResidual_unique_witness, nativeResidual_coefficient, admitted_identity_cut_obstruction | propext, Classical.choice, Quot.sound |
| varying_source_ambiguity | propext, Quot.sound |

No headline closure contains sorryAx, custom axioms or execution-only proof
axioms. Classical.choice and quotient/proposition extensionality are explicit
standard Lean/mathlib assumptions. The coefficient functions are noncomputable
scalar observations; no efficient extracted query implementation is claimed.

Finsupp/tensor adapters, the native complete-Set lfp adapter and ZMod experiment:
BLOCKED / NOT RECHECKED, removed from the final Lean modules. Exact source APIs
remain in this ledger, not hidden as compiled sketches. Indexed substitution
lawfulness, full ordered cut flags, executable exact joint recognizers and a
native Hopf/translation interface remain OPEN. No finite test suite was run;
there is no bounded-fixture theorem claim. All changes remain uncommitted.

Final read-only checks: `git rev-parse HEAD` still reports
`93b4a9abce87692ac32665132144ba1cd602808c`; `git status --short
--untracked-files=normal` retains the pre-existing AGENTS.MD modification and
adds the untracked Potkin/Exploration directory. No other tracked change was
introduced. A targeted `rg` search of the four new Lean sources for sorry,
admit, custom axiom declarations and unsafe found no matches (exit 1 means
no matches). Existing imported dependencies were not broadly rebuilt or tested.

Status distinction: the algebraic characteristic-two support counterexample is
PROVED at paper level, not mechanized by this probe. The universal native laws
listed above are MECHANIZED with their explicit guards. Fixed admitted examples
are separately identified, not promoted into universal theorems. No larger
CODE-CHECKED/BOUNDED-EVIDENCE campaign was performed. The three recommendation
targets are OPEN proposals, not new theorem claims.

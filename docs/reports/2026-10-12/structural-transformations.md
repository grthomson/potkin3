# CK under a genuine Cut/contraction step — 12 October 2026

## Result and scope

The selected experiment is an actual Gentzen Cut reduction across **internal
antecedent contraction**, with two physical copies of a premise derivation and a
subsequent contraction of its antecedent. It is not external contraction,
Communication, a critical pair, or a general normalization theorem.

The independent question is preservation of a declared restricted-rule fragment,
including a restriction on permissible Gentzen Cut formulas. Its decisive payoff
test is negative: exact all-rule occurrence inventory already determines this
question, even after copying. Equal-inventory payloads cannot separate its target
outcomes. The native CK expansion is strictly richer, but is not needed for this
observer. This is a specified-application no-go, not CK indispensability or a claim
that inventories determine addressed cuts and remainders.

The additive sources are:

- [StructuralReduction.lean](../../../Potkin/Research/StructuralReduction.lean):
  actual rules, immutable registry, exact logical step, arbitrary admitted and
  already-checked payload bridges, and closed native-checker examples.
- [StructuralCutExpansion.lean](../../../Potkin/Research/StructuralCutExpansion.lean):
  source/reduct installations, independent physical copy choices, ancestor
  masking, native refill, exact finite-sum specialization and material barriers.
- [StructuralObservation.lean](../../../Potkin/Research/StructuralObservation.lean):
  independently declared observer, exact inventory factorization, no separator,
  local fixed-rule obligations and native typed-context propagation.

Final compilation results and axiom closures are recorded in the verification
section below. Source statements alone are not mechanized claims.

## Selection before the CK theorem

| Candidate and user | Independent question and baseline | Forgotten information; payoff test |
| --- | --- | --- |
| Cut over contraction; proof-fragment checker | Does the reduct remain in a declared allowed-rule/Cut-formula fragment? Baseline: syntax-directed rule admission and exact occurrence inventory. | Inventory forgets addresses, order and incidence attachments between vertices, retaining full local decorations and multiplicity. CK would help only if a target distinction survived equal inventory. Universal factorization rules that out. **Selected negative result.** |
| Same reduction; resource accountant | A fixed additive weight per rule occurrence. Baseline: inventory and copy count. | Tree placement is forgotten. The reduct cost is twice the P cost plus Q and fixed-rule costs. Without an independent nonlinear execution semantics, this supplies no CK payoff. **Rejected without further development.** |
| One Communication/2-system translation; modular proof translator | Do opaque replacements preserve discharge legality of the translated system? Baseline: the source paper's structured derivations and applicability conditions. | Local rule inventories forget top/bottom grouping and discharge paths. Potentially a real distinction, but the native discharge-validity/translation bridge is missing. **Specific paper probe; not an implemented alternative calculus.** |

## Exact logical reduction

The atomic signature is the existing anonymous native signature, with pairwise
distinct atoms `d`, `a`, `c`. Formula contexts are multisets; each displayed
sequent below is the sole component of a nonempty whole hypersequent. The
registered instances have ordered premises and supplied component profiles.

Independently of CK, the standard single-succedent rules are

```text
Gentzen Cut:   Δ ⇒ A      Γ,A ⇒ C          IC: Γ,A,A ⇒ C
              -------------------             ---------
                   Δ,Γ ⇒ C                     Γ,A ⇒ C
```

The exact experiment fixes `Δ={d}`, `Γ=∅`, `A=a`, `C=c`:

```text
P : d ⇒ a                    Q : a,a ⇒ c

source = Cut(P, IC_a(Q))                : d ⇒ c
inner  = Cut(P_right, Q)                : d,a ⇒ c
outer  = Cut(P_left, inner)             : d,d ⇒ c
target = IC_d(outer)                    : d ⇒ c
```

The two a-assumptions of Q are discharged sequentially by the two uses of P;
multiset exchange permits the remaining a to stand beside d. The final IC_d
contracts the two copies of P's antecedent. There are no eigenconditions or
passive hypersequent components in this singleton fragment. The linear control
is `Cut(P, Id_a) → P : d ⇒ a`, which removes the source root rather than retaining
it through an installation.

This is independently justified by the displayed derivation substitution, not
by a rule-name match. `exact_gentzen_instances`, `exact_contraction_instances`
and `atoms_distinct` express its exact boundary checks. Incidence has one edge
from each ordered premise component to the sole conclusion component; it is
**not** interpreted as formula-occurrence routing. The routing above is the
separate logical schema. Native multiset formulas do not invent global indexed
formula ports.

The finite registry contains eleven exact occurrences: four explicitly declared
material provider/module operations, identity, four Cut instances, and IC_a/IC_d.
The material binary provider is not contraction. Its stock allows arbitrarily
deep P payloads; all four registered Cuts are at a. These added providers are
axiomatic module stock, not claims that their boundaries are intuitionistic
tautologies. No general Cut elimination theorem for arbitrary additional axioms
follows. The complete admitted Q stock is the specified ground provider; the
arbitrary native-tree expansion is broader, but its logical interpretation is
restricted to admitted payloads in this registry.

Admission and completeness are separate. The bridge quantifies over arbitrary
native admitted payloads of the required boundaries, and has corollaries for
arbitrary existing `CheckedDerivation presentation` payloads. Their realizations
provide admission/completeness; no private checked constructor or inverse
ambient-to-checker conversion is used. Closed examples enter through `checkAt`.

## Exact native expansion and physical copying

The source and reduct have **different** retained native skeletons. The source
installation addresses are `[0]`, `[1,0]`; the reduct installation addresses are
`[0,0]`, `[0,1,0]`, `[0,1,1]`. The first two reduct sites have the same whole
boundary but are distinct physical uses of the logical P port. Filling the three
sites with `left`, `right`, Q gives the independently specified reduct literally;
the actual logical reduction is its diagonal `left=right=P`. Boundary transports
at those slots are definitional, not provenance casts.

For any payload T write `B(T)=CKBranchCut T`. This includes native descent and,
only for a positive T, whole **branch** detachment to a typed vacancy. It is not
the algebraic global whole endpoint. The constructor classification is

```text
CKCut(target(left,right,Q)) ≃
    1 + B(left) × (1 + B(right) × B(Q)).
```

The first summand selects the outer Cut at `[0]` and masks both P copies and Q.
The inner singleton selects the inner Cut at `[0,1]`, masking right and Q while
allowing arbitrary left choices. The product case permits independent arbitrary
internal/whole/empty branch choices in both physical copies and Q. It is not a
Boolean copy-selection approximation. The unique all-empty combination remains
the empty cut; `[]` is never selected. A surrounding ordinary native context adds
exterior and enclosing-ancestor cases by the existing installation recursion.
That classification does not supply an equality between source and target
observations.

`physicalCutEquiv` proves both inverse laws; `independent_choices_injective`
retains the full product before collection. Native cut witnesses keep their
complete address-aligned detached tuples and typed remainders, and native refill
returns the literal reduct. Copy-separated origin annotations are applied before
any name-sharing observation. Forgetting the copy tag is an explicit later
projection, not an inverse reconstruction from a commutative forest. Every birth
in one copy is disjoint from every birth in the other; freshness within the
original supplied naming is not assumed. The Q namespace remains separate even
when an original P name equals an original Q name.

The finite-sum identity is a direct specialization of the existing
`material_cutSum_composition` and public filtered/bind reindexing **after** the
new logical-to-native filling bridge. Its RHS enumerates installation choices,
not completed reduct cuts, and retains natural multiplicities under arbitrary
multiset-valued observations. `pointed_sum_composition` remains the existing
separate whole-opening law. This is a finite witness/sum result, not a tensor
comparison, instantiated Hopf algebra, coaction law or substitution morphism.

There is an important exact obstruction to the requested spanning examples:
the enclosing Cut roots are logical, so no exact material base can admit them.
The target root is structural IC_d and the source root is logical Cut. Therefore
making the payloads pure cannot activate an enclosing material cut through this
redex, or its whole material opening. `outer_enclosing_ineligible`,
`inner_enclosing_ineligible` and `material_cut_coverage` isolate this barrier.
Eligible target choices are exactly independently eligible payload choices.
The existing post-installation spanning theorem still permits gain **and** loss
in other admissible material skeletons or inside changed payloads; that is not
permission to manufacture a spanning gain through a logical root here.

## Independent consequence, sufficiency and local criterion

Define `RulesAllowed allow T` recursively: a typed vacancy is accepted; an
ordinary vertex is accepted exactly when its full occurrence satisfies `allow`
and every ordered child is accepted. This definition precedes any CK sum.
Define the cheap summary S(T) as the multiset of **all exact local occurrences**.
It retains full native registered occurrence values, including their supplied
incidence; it forgets physical addresses, origin names and attachments between
vertices, not multiplicity or local decorations.
This is stronger than native `materialProfile`, which omits logical and
structural vertices and therefore cannot by itself answer Cut restrictions.

Constructor induction proves

```text
RulesAllowed allow T ↔ ∀ o ∈ S(T), allow o.
S(source) = [Cut_source, IC_a] + S(P) + S(Q).
S(target) = [IC_d, Cut_outer, Cut_inner] + S(P) + S(P) + S(Q).
```

Thus this independently selected query factors through S in both the linear and
copying fragments. There is no equal-S payload separator in the genuine target
context; no S+ is needed to restore its precision. In fact the **support** of S
already suffices: repeating a permission test does not change its truth. A
competent typed zipper/DAG checker can cache each payload's rule-permission result
once and check the fixed reduct rules, without unfolding either copy or carrying
cut witnesses. The CK expansion still records independent internal selections,
masking and typed remainders, but those data do not improve this query.

The specialized Cut-formula observer is even weaker: every registered Cut uses
a, and source/target acceptance collapses to permission for a. This finite-stock
collapse is a mechanized statement about this exact registry, not a general
analytic-fragment theorem. Separately, a **PAPER PROOF** gives the same no-go for
the standard schematic Cut-over-IC step: both sides satisfy the Cut-formula test
exactly when `Allowed(A) ∧ Fragment(P) ∧ Fragment(Q)`, provided the subsequent
antecedent contractions are permitted. Copying P and repeating Cut at the same
A cannot add a new forbidden formula. For a multiformula antecedent Δ, the
required final contractions must each be available; this condition is not
silently generalized from the single-d experiment.

For an arbitrary allowed-rule predicate, uniform source-to-target preservation
has exactly three new fixed-rule obligations: permit IC_d, the outer Cut and the
inner Cut. Necessity uses actual admitted allowed ground payloads and permission
for the old fixed rules; sufficiency works for arbitrary admitted P,Q. Nonvacuity
is explicit. This is a finite local criterion for this observer, not an assumed
global compatibility field.

Independent all-hole constructor recursion proves

```text
Allowed(M[f]) ↔ Allowed(M) ∧ ∀ physical hole h, Allowed(f(h)).
```

Consequently the local obligations propagate through arbitrary admitted typed
contexts and independent allowed fillings. When the skeleton and every filler
are independently locally admitted in the same exact registry, admission of the
filled trees follows the existing filling theorem. Neither `RulesAllowed` nor
displayed boundary coincidence establishes registry admission.
The linear identity step only deletes fixed rule occurrences. These statements
are one-step contextual preservation, not confluence, path independence,
normalization termination, or CK/coideal compatibility.

For full CK observations a selected address is exterior, in a payload copy,
at a fixed redex vertex, or at an enclosing ancestor. Prefix-freeness suppresses
inner choices under selected ancestors; incomparable cases can coexist. The
explicit reduct equivalence handles the local cases, and installed-cut recursion
handles a surrounding context. Matching full observations needs addressed branch
endpoints, typed matching, correlations and post-installation eligibility;
copy-label partitions alone do not suffice. No general finite local CK-quotient
criterion or sequence coherence has been established.

## One permitted alternative probe

Ciabattoni–Genco's Example 3.2 translates Communication into two top rules,
`Φ,Γ₁⇒Π₁ / Ψ,Γ₁⇒Π₁` and `Ψ,Γ₂⇒Π₂ / Φ,Γ₂⇒Π₂`, above a common bottom
with equal end-sequents. Their Definition 2.1 constrains top applications to
the appropriate bottom branch and shared parameters. Theorem 4.5 reconstructs
these groups from structured hypersequent derivations. Its proof handles duplicated
context components with dummy bottom rules and separates mixed groups; Lemma 4.6
uses external weakening and contraction to obtain the required structured form.
The standing hypotheses include externally shared contexts and one active
premise component, apart from EC. These assumptions are not available merely
from a weakening-free local registry. See the
[primary paper, §§2–4](https://arxiv.org/pdf/1805.04852).

Auditor inference: registering those top/bottom shapes locally would not certify
their nonlocal discharge conditions. POTKIN3's local checker currently has no
proved bridge for this particular global judgment or its translation. A standalone
registered top rule could pass local checking without its prescribed bottom.
Thus no surrogate 2-system or second native calculus was constructed, and no
implementation-independent invariant or translation/Hopf morphism is claimed.
The specific alternative remains **BLOCKED: missing mathematical bridge**, not
disproved mathematics or an olean issue.

## Old obstructions and unchanged limits

| Old obstruction | This experiment's repair or unchanged limit |
| --- | --- |
| Identity/Cut observations disagree; typed vacancy differs from coefficient unit | Unchanged. The linear root-deletion control is not an ordinary-cut equality. Whole branch/pointed opening and algebraic whole endpoint stay distinct. |
| Fixed source + literal remainder determines a cut, but factors + remainder do not determine a varying source | Unchanged. Every expansion retains actual witness, assignment and address matching. |
| Repeated-name filling defeated a naive CK-stable core | Physical copies are separated before a name projection. This repairs indexing only; no shared-name quotient/stability theorem follows. |
| Premise-saturated restriction failed coassociativity | Full native CK cuts retained; material selection is an observation, not a replacement lawful carrier. |
| Eligibility can gain or lose at inherited addresses | Existing theorem retained. Transport stays partial; no unaligned positive defect. Logical redex roots here impose a proved purity barrier. |
| Registry membership, kind and exact material membership differ | All three remain separate. Checked examples use one immutable presentation. |
| Boundary interfaces have no stronger global formula ports | Exact whole hypersequents and native local incidence only. Formula routing specified independently. |
| Ordered premises do not imply noncommutative forest product | Existing commutative forest unchanged; ordered native witnesses precede collection. |
| Coefficient rings can cancel positive multiplicities | Finite multisets/Nat multiplicities only; no support theorem for arbitrary rings. |
| Full Hopf/comodule laws and general quotient remain open | No antipode, Grossman–Larson replacement, tensor/coaction law or critical-pair claim. |

## Provenance and verification

Entry HEAD: `93b4a9abce87692ac32665132144ba1cd602808c`.
Toolchain: `leanprover/lean4:v4.29.0-rc1`.
Pinned **and installed** mathlib: `378b908c009ef82cf9584cba7447c44a5a89e58a`.
Applicable sources were `AGENTS.MD`, `SEMANTIC_CONTRACT.md`, current native
modules, the [material audit](native-material-record-audit.md) and
[Mathlib ledger](mathlib-exploration.md). The requested old
`Potkin/Exploration/LEDGER.md` was read at its new Mathlib-ledger path, following
the preceding documentation cleanup; no historical reset was performed.

Entry tracked changes were `AGENTS.MD` and `README.md` modified, and the moved
root `ARCHITECTURE.md`, `MIGRATION_LEDGER.md`, `PAPER_THEOREM_LEDGER.md` reported
deleted by unstaged Git status. Their content already exists under `docs/`.
Entry untracked paths from `git status --short --untracked-files=normal` were:

```text
Potkin/AllHoleFilling.lean
Potkin/AtomicIdentityFragment.lean
Potkin/CompositeCutExpansion.lean
Potkin/CutExpansionSums.lean
Potkin/Examples/InverseCut.lean
Potkin/Examples/MaterialComposition.lean
Potkin/Examples/MaterialInstallation.lean
Potkin/Examples/MaterialRecordObstruction.lean
Potkin/Examples/OriginCuts.lean
Potkin/Exploration/
Potkin/IntrinsicCutIdentity.lean
Potkin/InverseCut.lean
Potkin/InverseCutGeometry.lean
Potkin/MaterialComposition.lean
Potkin/MaterialDegree.lean
Potkin/MaterialInheritedCuts.lean
Potkin/MaterialInstallation.lean
Potkin/MaterialObservations.lean
Potkin/OriginCutCoherence.lean
Potkin/OriginCuts.lean
Potkin/SparseMaterialObservation.lean
Potkin/SparseTopTerm.lean
docs/
```

All remain preserved. Only the three additive research modules, this note and
its documentation-index link belong to this task. No dependencies, existing
proof modules, AGENTS.MD, commits, branches or pushes are changed.

The current branch remains `main`, with the same HEAD. A final SHA-256 comparison
found all 59 previously protected native/policy/build files unchanged, including
the existing AGENTS.MD and README edits. The relocation records and archives were
not rewritten. All task changes remain uncommitted.

The targeted children used the pinned executable below, from the POTKIN3 root.
Their scoped `LEAN_PATH` contained `.lake/build/lib/lean` and the existing
`.lake/packages/*/.lake/build/lib/lean` directories; no package was installed or
rebuilt. These are the exact executable and argument sequences, not a whole
project build:

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/StructuralReduction.olean Potkin/Research/StructuralReduction.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/StructuralCutExpansion.olean Potkin/Research/StructuralCutExpansion.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/StructuralObservation.olean Potkin/Research/StructuralObservation.lean
```

| Module | Attempts in seconds and results | Final status |
| --- | --- | --- |
| StructuralReduction | 341.790 terminated; 62.395 exit 1; 91.587 exit 0 | Compiled; `.olean` produced. |
| StructuralCutExpansion | 131.007 exit 1; 76.894 exit 1; 133.778 exit 1; 54.354 exit 0 | Compiled; `.olean` produced. |
| StructuralObservation | 77.156 exit 1; 72.639 exit 1; 63.982 exit 0 | Compiled; `.olean` produced. |

The first silent logical-module run exceeded the intended 300-second cap before
termination; its actual 341.790-second duration is not concealed. It produced no
proof evidence. One targeted diagnosis then ran the same pinned `lean.exe
--stdin` with exactly

```lean
import Potkin.AllHoleFilling
import Potkin.Examples.Anonymous
```

It exited 0 after **62.670 seconds**, demonstrating successful cached imports,
not diagnosing the exact cause of the earlier stall. Subsequent failed module
runs exposed concrete elaboration/proof errors and were rerun only after relevant
fixes. The final Cut-expansion correction resolved a pair-injection elaboration
issue; the subsequent whole-module run passed. All further runs used monitored 300-second
caps with CPU/memory checkpoints at 60 seconds. No unchanged failure was rerun.

`#print axioms` is part of each targeted module invocation, not a separate test
campaign. Successful logical-module headline closures contain only `propext` and
`Quot.sound`; the two closed-checker reduction examples additionally use
`Classical.choice`. All 17 observer-module headline closures are exactly
`[propext, Quot.sound]`. All 16 Cut-expansion headline closures contain exactly
`[propext, Quot.sound]`, with `Classical.choice` additionally on
`reduct_material_expansion`, `physically_named_reduct_material_expansion` and
`reduct_exact_observation_expansion`. None of the successful headline closures
contains `sorryAx` or a custom axiom. Recovery `sorryAx` printed during rejected
earlier declarations is excluded from all proof claims. Four harmless PUnit
variable-name linter warnings remain in the expansion module.

The focused source check

```powershell
rg -n '\b(sorry|admit|unsafe)\b|^\s*(axiom|opaque)\b' Potkin/Research/StructuralReduction.lean Potkin/Research/StructuralObservation.lean Potkin/Research/StructuralCutExpansion.lean
```

returned exit 1 with no matches. No authored placeholder, custom axiom or unsafe
cast was found. Dependency axiom evidence comes from the successful headline
closures, not this text search. No full build, Lake dependency run, Racket test,
bounded enumeration campaign, benchmark or full suite was run.

Three agents independently covered logical elaboration, physical expansion and
the adversarial observer/local criterion. Meaning reviews checked admission,
nonvacuity, endpoint distinctions, masking and the strongest inventory baseline.
They caught and corrected an accidental P/Q name-space conflation and the
incorrect suggestion that filling supplies its own admission premises. The
primary-paper probe was read by the integrating agent; the reviewer accepted its
limited inference, not an independent re-verification of that paper.

| Headline | Status and exact limit |
| --- | --- |
| Exact Gentzen/IC instance shapes and arbitrary checked-payload admission/completeness bridge | **MECHANIZED UNIVERSAL**, in the finite exact registry; not general logical adequacy. |
| Closed native checker examples and linear root-deletion control | **MECHANIZED EXAMPLE**, not proof by finite agreement. |
| Physical-cut equivalence, copying and exact material expansion | **MECHANIZED UNIVERSAL** over arbitrary native payloads; logical admission restricted to the exact registry. Existing composition theorem reused, not reproved. |
| Left-only, right-only, simultaneous-copy and enclosing-cut addressed/refill regressions | **MECHANIZED EXAMPLE**, by literal native constructors; no finite enumeration used as a universal proof. |
| Independent exact-inventory factorization and no separator after actual duplication | **MECHANIZED UNIVERSAL**; the support-only corollary is an immediate **PAPER PROOF**. |
| Nonvacuous three-rule criterion and one-step arbitrary native typed-context propagation | **MECHANIZED UNIVERSAL** for the rule-permission observer, not CK/coideal compatibility. |
| Schematic Cut-formula preservation with required final contractions | **PAPER PROOF**; its finite-stock instance and collapse are **MECHANIZED UNIVERSAL**. |
| General contextual CK compatibility, path independence and Hopf packaging | **OPEN**, not assumed or claimed. |
| Native Sys(com) discharge-validity/translation bridge | **BLOCKED mathematically** at the specified global judgment; not a disproved translation. |

Relative to earlier POTKIN3 work, the new application bridges a genuinely logical
duplication step to native independent installations and proves that the selected
verification observer needs no CK enrichment. Existing cut/composition theorems
remain existing results. Generic inventory/filling lemmas are infrastructure;
they are not advertised as the missing positive CK application. No literature
novelty, new CK-dependent safety guarantee or general normalization result follows.

## The one next theorem

For the single `Sys(com)` implementation above, prove an exact native boundary
summary of pending top-rule/discharge obligations sufficient for opaque module
replacement, together with its cut-decomposition propagation law. The independent
question is discharge legality, not absence of a bad CK coefficient. The current
inventory no-go makes another additive rule-count observer unjustified; the
specific translation instead has genuinely nonlocal grouping obligations.
Whether an exact finite summary suffices remains **CONJECTURE**, not a structure
field to assume or a promise of a general logical quotient.

# Interface-aware iterated CK decomposition — 13 October 2026

## Outcome

Work starts at HEAD `93b4a9abce87692ac32665132144ba1cd602808c`, branch `main`.
All additions remain uncommitted. Protected files, the existing dirty document
moves, AGENTS.MD, README and the contraction compiler were preserved. No full
build, test suite, finite-cut enumeration campaign or dependency installation
was run.

All six additive modules passed targeted Lean checks. Newly **MECHANIZED** are
the full native physical flag equivalence, its ordered three-output and finite-
sum laws, open-source certificate gluing, actual restriction/gluing diagrams,
independent dependency/interface agreement and a checked staged replacement.
This concerns full native extraction, not another scalar Q result. The corrected
target is typed two-stage extraction coherence and its certificate-map lift;
an ordinary Hopf coaction is not silently asserted. Scope limitations below
remain explicit.

## Actual algebraic types and closure

The existing declarations are:

```lean
structure CKComponent (sigma : Signature) (InstanceData : Type) where
  boundary : Hypersequent sigma
  tree : CKTree sigma InstanceData boundary
  ordinary : tree.IsOrdinary

abbrev CKForest sigma InstanceData := Multiset (CKComponent sigma InstanceData)
abbrev ExtractionBasis G := CKForest sigma InstanceData × CKTree sigma InstanceData G
abbrev ExtractionRecords G := FreeAbelianGroup (ExtractionBasis G)
abbrev States G := FreeAbelianGroup (CKTree sigma InstanceData G)

def delta : States G →+ ExtractionRecords G :=
  FreeAbelianGroup.lift fun tree => ∑ cut : CKBranchCut tree,
    FreeAbelianGroup.of (branchForest cut, cut.remainder)
```

Universe/index parameters above are suppressed for readability, not additional
hypotheses. See `Potkin/CKTree.lean` and `Research/ContextCutAction.lean` for the
native declarations.

The coefficient forest contains positive **open** decorated trees: `ordinary`
is not `IsComplete`, local admission, or a checked-proof certificate. Thus it
already accommodates factors containing typed holes. The raw-carrier closure
issue does **not** require a new forest carrier.

There is no installed `Delta_H` in the inspected native algebra. `delta` lands
in a free additive pair-basis, not a Lean tensor-product declaration. Existing
`e_delta` is an empty-coefficient extraction law and `K_compose` a context-action
law; neither supplies the missing forest coproduct or its product compatibility.

The smallest obstruction to **restricting coefficients to complete checked
proofs** is a two-vertex unary proof `r(g)`: detach `g`, leaving `r(Box)`, and
then select the whole positive remainder. That new factor is open. If both cuts
must be proper nonroot cuts, use `r(u(g))`, first selecting `g`, then `u(Box)`.
This is a structural obstruction to that narrower sector, not a counterexample
to the actual raw CKForest or to a correctly constructed typed coaction.

We establish the corresponding typed extraction theorem instead of describing
an undefined `(Delta_H ⊗ id) delta` as already proved. A positive middle fragment
is collected as a coefficient; a typed middle Box has no positive coefficient
component. This is an explicit projection, never equality of Box with a proof
unit. The final typed remainder is retained literally.

## Universal physical flag theorem

`Potkin/Research/RemainderExtractionFlags.lean` defines the two spaces independently:

```lean
BranchInside tree :=
  Σ upper : CKBranchCut tree,
    (site : upper.Site) → CKBranchCut (upper.detached site)

BranchRemainder tree :=
  Σ lower : CKBranchCut tree, CKBranchCut lower.remainder

branchFlagEquiv tree : BranchInside tree ≃ BranchRemainder tree
```

There is no vague schedule predicate. Each constituent cut is intrinsically
admissible; its selected positions are prefix-free. Comparable original
positions may be selected at different stages. Both spaces include legitimate
empty choices and the separate positive whole-branch endpoint. Interfaces
cannot be detached. Selecting a whole factor at both levels legitimately has
no positive middle factor, while the typed intermediate Box remains in the
witness.

`toRemainderBranch` and `fromRemainderBranch` are constructor-recursive maps with
both inverse laws. Root selection followed by proper descent becomes lower
extraction followed by whole selection of its ordinary remainder. Root selection
followed by whole selection becomes whole extraction followed by the unique
empty Box cut. Ordinary descent recurses through every ordered premise.

`branchFlag_outputs` equates the actual three-output data: the lower addressed
ordered packet, the middle addressed ordered packet and the final typed
remainder. Addresses prefix/shift according to the native premise positions;
entries retain whole boundaries, literal decorated factors and multiplicity.
`toRemainderBranch_intermediate` separately identifies the intermediate lower
remainder with filling the upper remainder by inner remainders. That intermediate
tree must not be confused with the final root. `inside_refill` and
`remainder_refill` reconstruct the original tree through the native fillings.
These statements quantify over arbitrary native open trees and full branch
cuts, without a completeness assumption or finite fixture bound.

`IteratedExtractionSums.extraction_sum` derives equality for **arbitrary additive
weights on the full ordered triple**, using the physical equivalence. Its
`addressed_coherence` is equality of signed addressed extraction records;
`collected_coherence` follows only after an explicit map to the unchanged
commutative forests. `collectPacket_append` proves that packet concatenation
projects to forest juxtaposition. It is not external Mix, filling, or a proof of
independent legality. These equalities are not scalar-count tests.

For any `AddCommMonoid R` and `weight : PacketBasis G → R`, the exact equation is

```lean
(∑ flag : BranchInside tree, weight (insideOutput flag)) =
  ∑ flag : BranchRemainder tree, weight (remainderOutput flag)
```

Here `PacketBasis G` is the two addressed packet lists and a native `CKTree G`,
not just their cardinalities. No completeness, local admission or palette
hypothesis is required for this structural equation.

## Open certificate interpretation and actual map coherence

`OpenCutCertificateGluing.branchEquiv` extends the existing shared-scope bridge
to arbitrary **open** sources:

```lean
Kernel tree provider actual inherited ≃
  Kernel cut.remainder (branchProvider cut provider) actual inherited
```

Inherited interfaces retain their original provider. A cut-created interface
evaluates its actual detached subtree with the unchanged absolute address and
inherited owner scope. Its root processes its conclusion exactly once, not at
the vacant slot. `remainderStagesEquiv` consequently interprets a second cut of
the first open remainder, with both inverse laws. No false completeness evidence
identifies inherited holes with selected sites.

`IteratedCutCertificates` independently constructs the inside-factor
interpretation and the constructor reassociation of its piece types.
`restriction_branch` proves that reassociation of the actual inside restriction
equals the actual remainder-stage restriction. `gluing_branch` proves the
inverse diagram. Reassociation is not defined by conjugating global gluing.
Shared owner colours, indexed equal-colour ancestor choices, checkpoints,
ordered premise witnesses and inherited physical callbacks remain intact.

Writing `r := toRemainderBranch upper inner`, the restriction equation is

```lean
reassociateBranch upper inner provider actual inherited
  (insideBranchEquiv upper inner provider actual inherited witness) =
  remainderStagesEquiv r.1 r.2 provider actual inherited witness
```

Its arguments are arbitrary native full branch cuts `upper`, full cuts `inner`
of their actual detached factors, an arbitrary open provider, an absolute
starting address, an inherited owner scope and a witness of that source kernel.
The inverse equation compares the actual gluing functions on reassociated
pieces. Neither theorem replaces witness equality by existence or counts.

These certificate statements concern the existing finite-palette right-ghost
kernel. Its previously verified admitted-source agreement is reused. The maps
are universal on that syntax, but intended logical grounding still needs the
existing local-admission hypotheses. They are not generic legality theorems for
every rule system and are not a claim that legal scoped proofs form a Hopf
subalgebra.

## Genuine Sys(com) dependency validation and staged reuse

The source fragment is Ciabattoni–Genco, Definition 2.1 and Example 3.2 of
[arXiv:1805.04852v1](https://arxiv.org/abs/1805.04852v1). Its two opposite top
substitutions share exact antecedent parameters Phi/Psi. The binary bottom has
two ordered premises with the same ordinary sequent as its conclusion. No
hypersequent-to-2-system adequacy theorem is inferred.

`DependencyInterface` defines local exact-boundary/incidence checking separately
from independent global legality. Each physical top is required to resolve to
its designated bottom instance, with the same parameter pack and correct
ordered-branch ancestry. The finite interface exports only outstanding top
requirements: exact top/owner IDs, parameter pack, role and physical addresses.
Internally discharged demands and ordinary interior nodes are forgotten. There
are no eigenvariables in this fragment; external/internal owner non-aliasing is
an explicit freshness hypothesis where needed.

`legality_interface_iff` and `native_legality_interface_iff` prove agreement with
independent legality; `interface_replacement` and `native_replacement` transport
piece legality against fixed external grants. These statements do not encode
legality as a field or store the entire source proof in the interface.

The native agreement conclusion, under `Fresh (events tree address) external`,
is exactly

```lean
Legal tree address external ↔ ExactTree tree ∧
  InteriorLegal (events tree address) ∧ InterfaceLegal (events tree address) external
```

Replacement additionally assumes equal exported interfaces, freshness for both
pieces, exact local checking and interior legality of the new piece, and legality
of the old piece. Same boundary alone is deliberately insufficient.

The exact eight-occurrence native stock uses `Phi={p}`, `Psi={q}`, genuine
identity/IW/IC interiors and the stated source top/bottom instances, with common
boundary `{q,p} => {p}`. Physical tops at `[0]` and `[1,0,0]` discharge at `[]`.
A CK frontier separates
a top from its bottom. A locally checked same-boundary replacement with a
different parameter pack is globally rejected. A compatible replacement inserts
an IW/IC interior roundtrip while retaining the same exported requirement. This
demonstrates forgetting actual interior detail, not just renaming a schematic
binary rule.

The staged application uses that complete, grant-free replaced factor, not the
parameterized contraction compiler whose concrete HG admission remains absent.
One bracketing selects the whole positive proof and then its proper [0] factor;
the other first selects that factor and then the whole punctured remainder.
The physical flag theorem compares the lower factor, the middle decorated
punctured proof and final typed Box; native refill recovers the same checked
replacement result. Ordinary local checker admission and independent dependency
legality are separate certificates.

**Important interface limit:** a requirements-only interface is not sufficient
for arbitrary open-piece replacement. Two same-boundary open bottoms may have
no outstanding requirements but different grant packs/IDs; a top subsequently
filled into a hole can depend on precisely the old grant. General opaque open
replacement must preserve grant signatures or impose callback-compatibility
hypotheses. The proved fixed-external-grant theorem and supplied complete,
grant-free detached-factor application do not have this defect.

Recovering the full source 2-system formalism would require all ordered top/bottom
schemas and shared substitutions, a proved erasure/decoration correspondence for
designated ownership, the source's complete branch/discharge conditions, and
freshness/side-condition transport for any added logical rules. Arbitrary open
piece gluing additionally needs the grant-export/callback condition above. Full
hypersequent embedding and analyticity require independent theorems; repeated
tops in this represented fragment do not establish arbitrary dependency-level
adequacy. These are **OPEN**, not hidden consequences of the fixture.

The checking operation enabled here is scoped staged reassembly: unchanged
external grants and discharged context obligations may be retained when the
proved interface conditions hold. The replacement's local admission, interior
legality and interface matching must still be checked, followed by native
refill/quotation. Changes inside the replacement can create additional CK cuts;
the theorem does not retain its old complete cut cache. No runtime saving,
semantic equivalence, normalization, resource safety or deadlock claim is made.

## CK contribution, open work and D1–D6

CK supplies the two independent physical flag spaces, their multiplicity-
preserving reassociation, full ordered extraction packets and literal typed
reconstruction. Shared-scope semantics supplies the dependent witness-map lift.
Forest multiplication is only the declared commutative coefficient projection;
it does not discharge obligations across factors.

The most concrete next algebraic target is a forest-valued `Delta_H`, its
multiplicative compatibility and a proved adapter from the current pair/triple
bases to the intended tensor expression. The present universal flag and
finite-sum theorems are prerequisites; an ordinary coaction, Hopf subalgebra,
antipode inversion, Faà di Bruno law and material coaction compatibility remain
unclaimed. More than two extraction stages require their own coherence result.

| Programme | Advance and exact remaining obligation |
| --- | --- |
| D1 relative Cut | Later success test; no logical Cut elimination or analytic adequacy follows from extraction. |
| D2 copying | Physical addresses/multiplicity survive restaging; arbitrary fresh copying and scope-origin transport remain separate. |
| D3 admission | The actual finite Sys(com) fragment is locally checked; the contraction compiler's general HG rule interface remains a supplied obligation. |
| D4 decomposition | Full remainder-stage versus inside-factor extraction and actual certificate-map reassociation are the central new targets; not scalar optimization. |
| D5 reuse | Complete dependency-factor replacement and two-stage reconstruction are certified under the stated interface; unrestricted open grant-export replacement remains open. |
| D6 calculus comparison | Raw native geometry is generic; revival and Sys(com) certificates retain their distinct decoration/calculus parameters. No silent comparison or cross-snapshot cast. |

## Targeted verification and independent review

Checks use the pinned Lean executable, existing project/package caches in
`LEAN_PATH`, async drainage of both output streams, progress reports and an
actual-child 300-second bound. Timed-out children were killed and joined.
No policy file was edited. The current prompt authorizes adequate targeted
timeouts; a timeout was not classified as a mathematical failure.

Exact final child commands from POTKIN3 (the monitoring wrapper supplies the
existing project/package `LEAN_PATH` and the bound):

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/RemainderExtractionFlags.olean Potkin/Research/RemainderExtractionFlags.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/OpenCutCertificateGluing.olean Potkin/Research/OpenCutCertificateGluing.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/IteratedExtractionSums.olean Potkin/Research/IteratedExtractionSums.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/IteratedCutCertificates.olean Potkin/Research/IteratedCutCertificates.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/DependencyInterface.olean Potkin/Research/DependencyInterface.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/DependencyInterfaceExamples.olean Potkin/Research/DependencyInterfaceExamples.lean
```

| Module | Final seconds | Result and accepted headline closures |
| --- | ---: | --- |
| OpenCutCertificateGluing | 38.492 | PASS; branch/staged equivalences and both inverses: `[propext, Classical.choice, Quot.sound]`. |
| DependencyInterface | 62.730 | PASS; agreement/replacement: `[propext, Classical.choice, Quot.sound]`; native refill: `[propext, Quot.sound]`. |
| RemainderExtractionFlags | 71.615 | PASS; physical equivalence, ordered outputs, intermediate remainder and both refill headlines: `[propext, Quot.sound]`. |
| IteratedExtractionSums | 60.160 | PASS; full sum/addressed/collected coherence: `[propext, Classical.choice, Quot.sound]`; packet-product projection: `[propext, Quot.sound]`. |
| IteratedCutCertificates | 149.834 | PASS; inside/reassociated equivalences and actual restriction/gluing diagrams: `[propext, Classical.choice, Quot.sound]`. |
| DependencyInterfaceExamples | 65.688 | PASS; all twelve checked-rule, legality, negative, refill and staged-workflow headlines contain only `propext`, `Quot.sound` and where needed `Classical.choice`. |

The initial concurrently running checks hit their 300-second bounds with
increasing CPU/memory and no error output. One targeted import diagnostic per
affected workstream isolated startup/import cost: root CertificateCutGluing
import passed in 67.439 seconds; geometry ContextCutAction/CompositeCutExpansion
imports in 71.723 seconds; dependency CKCut import in 51.831 seconds. Necessary
imports were narrowed, and subsequent targeted runs resumed normal progress.
Root's first child was killed after 301.381 seconds; its first completed source
check took 51.338 seconds and exposed one inconsistent provider match arity,
fixed before the successful final check. Failed-run placeholder axiom closures
are never accepted.

Geometry's first child was killed after 301.836 seconds, before any diagnostic
output. Its observable CPU/memory growth did not identify the exact phase;
startup/resource contention was an inference tested by the import-only probe.
Subsequent concrete-fix checks took 104.182, 92.843, 71.556 and 58.288 seconds,
resolving dependent inverse-law reductions, explicit source indices and ordered
packet map normalization. No extra research scope was added to make them pass.

Dependency's initial heavy-import check was terminated after 300.780 seconds.
The revised core passed after narrowing to its directly required CKCut import.
Example checks of 42.469 and 76.583 seconds exposed concrete incidence-bound,
list-membership and dependent Site/Sum pattern errors, fixed before the accepted
65.688-second check. Its accepted `replacement_workflow` depends on the universal
interface replacement theorem and verified native flag geometry, not enumeration.

The finite-sum first check took 70.048 seconds: a missing Sigma Fintype instance
was replaced by the explicit finite dependent-pair construction using already
imported APIs, without another import/cache campaign. The certificate first
check took 123.183 seconds: two full-endpoint callback reductions and a ghost
arity dependent elimination were fixed by small transparent root/ghost helper
lemmas. No statements or admissibility conditions were weakened. Both corrected
sources then passed as recorded above. Harmless unused-variable/simp warnings
were not grounds for another run.

The three diagnostic commands used that same pinned executable with `--stdin`.
Their exact input was respectively `import Potkin.Research.CertificateCutGluing`
followed by `#check Potkin.Research.CertificateCutGluing.cutGluingEquiv`;
`import Potkin.Research.ContextCutAction` and `import Potkin.CompositeCutExpansion`
followed by `#check Nat`; and `import Potkin.CKCut` followed by `#check Nat`.

Three independent agents covered geometry, dependency interfaces and adversarial
review. Review confirmed raw forest closure, demanded the final/intermediate
remainder distinction and actual restriction-map diagrams, and identified the
missing grant-export condition for arbitrary open replacement. The reported
scope reflects those findings. Final axiom closures and source status are
recorded only after successful checks; no finite tests stand in for universal
proofs.

All accepted headline closures contain only `propext`, `Quot.sound` and where
needed `Classical.choice`; none contains `sorryAx` or a custom axiom. Existing
verified gluing, contextual provider transport, K laws and the contraction
milestone were imported/reused rather than re-proved or rechecked separately.
The report distinguishes those **MECHANIZED** results from source comparison,
the closed-sector paper obstruction and the explicit open algebraic contracts.

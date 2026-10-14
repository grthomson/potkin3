# Native context packets and revival interfaces 12 October 2026

## Final verified milestone and precise scope

The continuation resumed and the concrete elaboration errors were fixed.
**The native bridge and signed context-action milestone is now kernel-checked:**
closed agreement and exact counting, universal native cut gluing with inverse
maps, scoped replacement, actual inside-factor cut-flag coherence, and all
requested finite-sum L/A/e/K laws. Coherence for every arbitrary noncrossing
two-cut schedule remains outside the proved scope. No fixture calculation or
failed-check placeholder is treated as proof.

HEAD remains `93b4a9abce87692ac32665132144ba1cd602808c`, branch `main`.
All changes remain uncommitted. Existing policy changes, document moves,
README changes and unrelated untracked work were preserved. No branch or commit
was created. Successful final-source checks and independent reviews are recorded
below; the earlier interrupted checkpoint has been superseded, not concealed.

### Newly MECHANIZED

| Source | Universal result and exact scope |
| --- | --- |
| [OpenCertificateKernel.lean](../../../Potkin/Research/OpenCertificateKernel.lean) | Type-valued continuation witnesses on the existing `RevivalInterface` native trees. Providers are indexed by physical `LeafOccurrence`, absolute address and inherited owner scope. `closed_nonempty_iff` proves existence agreement with the existing Prop relation under `LocallyAdmittedTree presentation tree`. `closedCountEquiv` proves `ClosedKernel tree address env ≃ Fin (certificateCount tree address env)` under that same admission hypothesis. |
| [CutHoleAdapter.lean](../../../Potkin/Research/CutHoleAdapter.lean) | For an explicitly complete source, the actual remainder holes are equivalent to native selected sites, preserving boundaries, addresses and aligned factors. Native simultaneous filling literally reconstructs the source. For arbitrary open filling, `filledLeafEquiv` distinguishes inherited interfaces using the dependent pair of original hole and filler hole; its address is the concatenation of those two physical addresses. |
| [CertificateCutGluing.lean](../../../Potkin/Research/CertificateCutGluing.lean) | `cutGluingEquiv`, `glue_restrict` and `restrict_glue` give actual witness-type gluing and both inverse maps for any complete native source and full branch cut, at any address and inherited scope. Each remainder callback evaluates its aligned detached factor under the scope supplied by that same remainder certificate. Local admission is required when connecting this structural equivalence to the existing logical certificate relation. `scopedReplacementEquiv` transports whole-context certificates through pointwise provider equivalences at matching physical holes, addresses and scopes. |
| [CutCertificateFlags.lean](../../../Potkin/Research/CutCertificateFlags.lean) | Native inside-factor cut flags use `ExpansionChoices`, `expandCut` and `compositeCutEquiv`. The compiled cut sites are equivalent to `Σ firstSite, lower.Site`, with literal address concatenation, exact boundaries and factor `HEq`. The combined remainder is the actual outer remainder filled with the lower remainders. This is geometric reindexing, not yet certificate-map coherence. |

The kernel retains the fixed two-colour palette, one shared colour for an
owner's ordered premises, and an eligible **scope index** for each right ghost.
Equal owner colours do not identify distinct ancestor choices. An unused owner
still chooses a colour. An interface invokes its provider before any root
checkpoint processing; its filled genuine root processes its conclusion once.
Malformed owner arities and non-nullary ghost-labelled ambient nodes have empty
witness types. Admission excludes those malformed shapes and ties checkpoint
processing to the existing `emptyConclusion_exact` actual-boundary theorem.

The older `HasScopedCertificate` relation is Prop-valued and expresses only
existence. The new Type-valued witnesses and `closedCountEquiv` retain the
multiplicity it cannot retain. Arbitrary inherited lists are continuation
parameters; the whole-source grounding interpretation starts at `[]`.

The branch gluing theorem covers empty cuts, root-excluding public cuts and
the separately represented full-branch `detach`. Public `CKCut` includes the
empty cut but never selects its own root. The factors need not be independently
closed-grounded. No additional proof, cut, context or forest carrier was added.

### Cooperative example, not the universal proof

[CertificateGluingExamples.lean](../../../Potkin/Research/CertificateGluingExamples.lean)
successfully checks the native two-module cut with ordered addresses `[1,0]`
and `[1,1]`, including equal-looking modules at different physical sites.
`cooperative_pattern` proves that the glued piece witness type is inhabited
exactly when the two colours agree: pp and qq are compatible, pq and qp are
not. Its argument uses the new gluing equivalence and the existing scoped
relation, not the old closed-count evaluation. `module_inherited_scope`
identifies compatibility with the shared owner colour, while
`independently_closed_factors_fail` shows why closing the factors separately
loses information. `cooperative_refill` verifies literal native reconstruction.
These instantiated examples illustrate the universal bridge; they do not
prove its universal statement and do not count ordinary revived LJ proofs.

### Newly completed coherence, counting and signed context action

[CertificateContinuationComposition.lean](../../../Potkin/Research/CertificateContinuationComposition.lean)
now verifies universal open substitution and actual provider-map naturality.
[CertificateNestedGluing.lean](../../../Potkin/Research/CertificateNestedGluing.lean)
verifies the independently constructor-defined hierarchical restriction diagram
and its inverse gluing diagram. The termination error was corrected by binding
the actual recursive argument explicitly in `termination_by`; recursive child
laws are obtained before eliminating the occurrence's data field. No heartbeat
override or weaker observer statement was substituted.

The stronger native bridge is in
[CertificateFlagGluing.lean](../../../Potkin/Research/CertificateFlagGluing.lean):
`native_restriction_coherence` and `native_gluing_coherence` compare the actual
one-shot `insideCombined` cut's existing `cutGluingEquiv` with independently
recursive nested restriction/gluing. The first source is explicitly complete;
each lower cut is a full native branch cut inside an aligned first factor,
including a lower whole-branch selection. `pulledCombinedAssignment_eq_lower`
proves exact callback/factor matching using native filling injectivity. Native
site reindexing and address concatenation come from `CutCertificateFlags`.
This is actual witness-map equality, not just equal cardinalities or a
conjunction of geometry and unrelated context lemmas. It is **MECHANIZED** for
arbitrary inside-factor flags; all arbitrary noncrossing schedules are unclaimed.

`piecesCountEquiv` is now exported from `CertificateCutGluing` and verified:
`PieceCertificates cut complete address scope ≃ Fin (certificateCount tree address scope)`
under exact source admission. The dependent piece type uses shared owner Sigma
choices and ordered premise products, with factor callbacks conditioned on that
same scope. It is not an unconditional product of closed factor counts.

[ContextCutAction.lean](../../../Potkin/Research/ContextCutAction.lean) now verifies:

* `delta_context`: δ G_C = L_C δ + A_C.
* `L_compose` and `A_compose`: L_CD = L_C L_D and A_CD = L_C A_D + A_C G_D.
* `e_delta`, `e_L`, `e_A`: eδ = id, eL_C = G_C e and eA_C = 0.
* `K_compose`, `delta_K`: K_CD = K_C K_D and δG_C = K_C δ, where K_C = L_C + A_C e.
* `e_K` and `G_compose` as additional consequences.

These are equalities of additive homomorphisms over arbitrary native typed
contexts, not fixture evaluations. `ExtractionRecords G` is the existing
`FreeAbelianGroup (CKForest sigma InstanceData × CKTree sigma InstanceData G)`:
a signed coefficient construction over native forests and literal typed states,
not a replacement proof/cut/context carrier. K composition therefore applies to
arbitrary signed records outside the image of δ. Sibling/ancestor cut-choice
splicing supplies L/A composition; insertion associativity alone is not used as
a substitute. Ordered addressed packets remain intact until `branchForest`
explicitly projects to the commutative forest. Typed Boxes remain native states,
distinct from the empty-forest coefficient unit.

Remaining limits: logical certificate interpretation uses the fixed admitted
right-ghost registry and a genuinely generated scope, normally `[]`. Ambient
constructor laws need no logical admission, but checked logical use invokes the
existing native admission results. No C1 LJ compiler, full-LQ adequacy,
H-linearity, Hopf-morphism or completed material-relative coaction is claimed.
No blanket unlimited heartbeat, custom axiom, authored `sorry` or `admit` was used.

### Targeted verification record

All commands below ran from the POTKIN3 root with the pinned Lean executable
and the existing project/package caches in the child `LEAN_PATH`. The executable
was `C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe`.
For every named module the exact command form was:

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/<Module>.olean Potkin/Research/<Module>.lean
```

| Module / final reported invocation | Seconds | Result |
| --- | ---: | --- |
| CutHoleAdapter | 43.741 | exit 0; final source passed |
| OpenCertificateKernel, including exact count equivalence | 79.554 | exit 0; final source passed |
| CertificateCutGluing, final conditioned piece-count export | 53.252 | exit 0; bridge, inverse laws, replacement and exact piece count passed |
| CutCertificateFlags | 108.356 | exit 0; final native flag geometry passed |
| CertificateGluingExamples | 82.742 | exit 0; final source passed |
| CertificateContinuationComposition, final expanded source | 108.138 | exit 0; actual-map naturality passed |
| CertificateNestedGluing | 106.041 | exit 0; both hierarchical map diagrams passed |
| CertificateFlagGluing | 100.386 | exit 0; actual native one-shot/nested witness diagrams passed |
| ContextCutAction | 127.518 | exit 0; all signed L/A/e/K laws passed |
| Final headline import-only print, `lean.exe --stdin` | 46.160 | exit 0; exact headline signatures and closures printed from the final compiled modules |

The final stdin query imported `Potkin.Research.CertificateFlagGluing` and
`Potkin.Research.ContextCutAction`; it printed `#check` for closed agreement/count,
native restriction/gluing coherence and all ten L/A/e/K/G headline laws, and
`#print axioms` for both native diagrams and the central L/A/e/K laws.

Earlier failed elaborations remain part of the record: continuation checks
50.898, 59.664, 185.902 and 131.771 seconds; nested checks 154.956 and 117.671
seconds. Corrected explicit recursion binders resolved those gates. Native flag
gluing checks 89.603 and 95.593 seconds failed local ghost-arity/coercion proofs
before final success. After the earlier 267.944-second action failure, corrected
action checks 270.001, 194.308, 131.419, 128.078 and 122.916 seconds failed
progressively localized constructor/list-projection proofs; the final 127.518-
second source passed. All reruns followed a concrete fix. Those costs explain
the delay; none is counted as mathematical evidence.

The named successful modules printed their headline signatures and axiom
closures during their successful checks. Adapter and flag geometry closures
are `[propext, Quot.sound]`. Closed existence agreement also has that closure.
Exact counting, filling, cut gluing, inverse laws and scoped replacement use
only `[propext, Classical.choice, Quot.sound]`. Cooperative address/refill and
module-scope statements use `[propext, Quot.sound]`; cooperative compatibility
adds `Classical.choice`. **No accepted headline closure contains `sorryAx` or a
custom axiom.** No axiom closure from a failed check is counted as verification.
The final native certificate diagrams and all signed L/A/e/K headline closures
are exactly `[propext, Classical.choice, Quot.sound]`; native assignment matching
and structural splice/refill closures are `[propext, Quot.sound]`.

The initial FreeAbelianGroup import probe used `lean.exe --stdin` and failed
after 26.777 seconds because `Mathlib.Data.Int.Cast.Defs.olean` was absent.
Only concretely missing existing dependency sources were compiled; no package
was installed and no full build was launched. Their exact command form was
`lean.exe -o .lake/packages/mathlib/.lake/build/lib/lean/<module/path>.olean
.lake/packages/mathlib/<module/path>.lean`:

| Existing dependency | Successful compilation seconds |
| --- | ---: |
| Mathlib.Data.Nat.Cast.Defs | 19.628 |
| Mathlib.Data.Int.Cast.Defs | 18.076 |
| Mathlib.Data.Int.Basic | 22.947 |
| Mathlib.Data.Int.Cast.Basic | 28.643 |
| Mathlib.Data.Nat.Cast.Basic | 41.729 |
| Mathlib.Data.Nat.Cast.Commute | 26.092 |
| Mathlib.Data.Nat.Sqrt | 21.980 |
| Mathlib.Data.Int.Sqrt | 56.139 |
| Mathlib.Data.Int.Cast.Lemmas | 58.388 |
| Mathlib.Data.Nat.Set | 30.617 |
| Mathlib.Data.Finset.Prod | 66.357 |
| Mathlib.Data.Finset.Option | 38.678 |
| Mathlib.Data.Finset.Piecewise | 37.570 |
| Mathlib.Data.Fin.VecNotation | 43.753 |

The exact finite witness equivalence ultimately used the lighter existing
`Mathlib.Logic.Equiv.Fin.Basic`, rather than relying on an unverified cardinality
import. Its repaired import-only probe passed in 64.889 seconds. These dependency
repairs did consume appreciable time; they are not mathematical results.

Every rerun followed a concrete source or cache repair. Child stdout/stderr
were drained asynchronously, with a 300-second actual-process bound and CPU/
memory progress checkpoints. No run above required a 600-second extension.
No full build, full suite, exhaustive finite enumeration or unchanged-prior-module
reverification was performed. Failed runs are recorded as failures, not proofs.

### Review and research consequence

Independent mathematical review accepted the physical hole/site adapter,
pre-root scope convention, actual gluing maps, exact finite witness indexing,
and the certificate-only scope of replacement. It specifically identified the
Prop-versus-Type distinction and the malformed-ghost admission hypothesis.
It initially rejected treating generic context coherence or geometric flag
reindexing alone as the requested actual cut-map coherence. Its subsequent
review accepted the independently constructed actual native inside-factor
diagram and matching-by-injectivity proof, with the precise scope limitation.
The finite-sum layer additionally passed its successful final Lean check;
static review alone was not promoted to that status.

**D4 advance:** native physical CK decomposition now has a universal scoped
certificate interpretation and constructive inverse gluing, beyond a scalar
closed-source observer. **D5 advance:** pointwise scoped certificate interfaces
transport grounding witnesses through a typed context. This is not C1, a
compiler to ordinary LJ derivations, unrestricted logical equivalence, or
full-LQ adequacy. The next D1 obligation is an admitted revival-to-ordinary-LJ
compiler/correctness bridge; the next D3 obligation is relating these finite
certificate fibres to the requested coefficient/debt interpretation. D2 and D6
remain downstream. Actual inside-factor native cut-map coherence and signed K
laws are now mechanized. Extending coherence to every arbitrary noncrossing
schedule, the LJ compiler and the debt/coefficient interpretation remain open.

---

## Earlier verified baseline and research record (retained)

The first two native bridges requested by the supplied Hopf research brief now
have additive Lean source: a full branch-cut packet equivalence through a typed
puncture, and a genuine finite LQ presentation with an occurrence-sensitive
certificate query. The context module is now kernel-checked, including all seven
headline axiom closures. The revival module is also now kernel-checked, including
its public-checker quotations, universal certificate-count correctness proof
and all headline axiom closures. Neither module has a headline dependency on
`sorryAx` or a custom axiom.
The integrated revival, coefficient and Hopf programme is **not complete**.

The useful mathematical distinction is that the packet theorem concerns full
native `CKBranchCut`, whereas certificate semantics must remain an additional
boundary-valued interpretation of those cuts. A scalar closed-source certificate
count cannot supply the missing interpretation on punctured fragments.

## Provenance and scope

Repository: `C:\Users\gavin\Desktop\coding2023\lean_projects\potkin3`.
Branch: `main`. HEAD: `93b4a9abce87692ac32665132144ba1cd602808c`.
All work remains uncommitted. No branch, commit, dependency installation, full
build, full test suite, Racket invocation or Python prototype execution was used.

The received prompt and its supporting package are preserved at
[the research archive](../../archives/2026-10-12/ck-research-evidence/hopf_research/README.txt).
The exact task is
[LEAN_RESEARCH_PROMPT.txt](../../archives/2026-10-12/ck-research-evidence/hopf_research/LEAN_RESEARCH_PROMPT.txt).
The package's captured validation counts are historical executable evidence,
not new POTKIN3 verification.

The earlier [structural-transformation report](structural-transformations.md)
and its three Lean sources are unchanged. Its inventory-only rule-permission
observer is not reused as a revival or CK-payoff result.

## Status of the new sources

| Source | What is actually represented | Status |
| --- | --- | --- |
| [ContextCutPackets.lean](../../../Potkin/Research/ContextCutPackets.lean) | Arbitrary native pointed-puncture packet decomposition, inverse constructions, ordered packet/remainder preservation, refill, conditional local admission and literal insertion composition. | MECHANIZED; targeted module check passed; seven headline closures contain only `propext` and `Quot.sound`. |
| [RevivalInterface.lean](../../../Potkin/Research/RevivalInterface.lean) | Native negation/disjunction formulas; 15 exact equipped occurrences; public-checker quotations for the 21/43-node examples; a right-ghost scoped certificate query and constructor proof of positive count iff a certificate exists. | MECHANIZED within that stated fragment; targeted module check passed; headline closures contain only standard Lean axioms. Literal fixture comparisons remain finite evidence, not full LQ adequacy. |

`PROVED` below means an explicitly scoped paper argument. The context module's
constructor proofs are `MECHANIZED`, not finite agreement. The revival module's
universal count/witness theorem is also `MECHANIZED`. Its literal 21/43-node
calculations and checked quotation comparisons establish those specific fixtures;
they do not prove unrestricted revival, open-fragment gluing or Hopf laws.

## Full native context packet equivalence

Namespace: `Potkin.Research.ContextCutPackets`. The central signature at source
line 357 is:

```lean
def fullPacketEquiv {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H) :
    CKBranchCut (hole.insert payload) ≃ NoSpine hole payload ⊕ Ancestor hole
```

`NoSpine` is the recursively ordered product of the payload's full branch cut
and all off-spine sibling cut choices. `Ancestor` is the sum over a uniquely
selected positive spine vertex, with independent sibling choices only above
that vertex. It contains no payload-cut choice and no choices in swallowed
lower siblings. These are indices built from native cuts using sums and
products, not another proof, cut, forest or context carrier.

The quantifiers allow arbitrary typed open payloads and open siblings, not a
bounded fixture family. `PunctureAt` selects one physical interface; any other
interfaces are fixed. It does not assert that the entire context has exactly
one interface. Local admission is a separate hypothesis, not implicit in an
ambient `CKTree`.

### Constructor proof at paper level

For an interface context, insertion is the payload, the no-spine index is its
branch cut and the ancestor index is empty. At an ordinary pointed root, a full
branch cut either detaches that whole root or descends into its ordered
premises. Whole detachment uniquely swallows the payload. Descent combines one
recursive pointed-child choice with independent cuts in every other premise.
The selected spine vertices form a chain, so prefix-freeness permits at most
one. Repeating the decomposition yields the stated disjoint sum. The inverse
rebuilds the same recursive native cut plan. Induction on the pointed path and
ordered child list proves both inverses. This proves the geometric statement
for finite unfiltered native trees at paper level; it is not finite agreement.

### Exact native packet and reconstruction

The source provides:

- `pointedBranchEquiv` at line 206, with explicit `assemble`/`decompose` inverses.
- `orderedPacket` at line 370, returning `List (CKCutEntry sigma InstanceData)`
  with each actual relative address, exact boundary, detached tree and
  ordinariness evidence.
- `orderedPacket_descend` at line 381: strict descent gives exactly the existing
  `CKCut.detachedTuple`, not a reordered or recovered forest.
- `packet_and_remainder_preserved` at line 385: inverse round-trip preserves the
  ordered packet and literal typed remainder by equality of the native witness.
- `assembled_refill` at line 399: `cut.fill cut.detached = hole.insert payload`.
  Filling consumes the native dependent site family, retaining the factor-to-hole
  matching rather than trying to recover it from a multiset.
- `assembled_admitted` at line 410: independently admitted context and payload
  in one exact equipped registry give admitted insertion, remainder and every
  detached factor. It does not establish those input hypotheses.
- `outer_ancestor_packet` at line 428: whole branch selection has one detached
  filled tree at relative address `[]` and the corresponding typed interface
  remainder. It is not fabricated as a proper root cut.
- `insert_compose` at line 447: prefixed puncture insertion equals successive
  native insertion, for arbitrary typed contexts and payloads.

Existing `installedCutEquiv` uses an installation at selected positive nonroot
vertices. An interface is not such a vertex. The new pointed specialization
therefore uses existing root-choice/content inverse lemmas while also covering
identity contexts and interface payloads.

## Affine and counit context laws at paper level

The following derivation is **PROVED at paper level** for finite unfiltered
positive typed trees and free additive extraction records. It does not assume
that POTKIN3 already has an instantiated Hopf algebra or material-restricted
coaction. Its Lean finite-sum realization is **OPEN**.

Write `δ(P)` for the finite sum of full native branch-cut records `(h,r)`, where
`h` is the detached commutative forest and `r` the typed remainder. Keep the
addressed packet separately before this forest projection. For a fixed pointed
context C, define `G_C(P)=C[P]`.

`L_C(h,r)` sums all off-spine sibling choices, multiplies their detached forests
with h and grafts their remainders with r in the original ordered slots.
`A_C(P)` sums unique ancestor selections and choices strictly above them. Its
ancestor factor is the actual filled subtree containing P, not a cut of P.
Extend G, L and A additively on their respective free modules. The packet
bijection proves:

```text
δ G_C = L_C δ + A_C
G_(C∘D) = G_C G_D
L_(C∘D) = L_C L_D
A_(C∘D) = L_C A_D + A_C G_D
```

For L composition, splice the independent sibling-choice lists along the two
pointed paths. For A composition, the unique selected ancestor lies either in
D, with all C choices above it, or in C, swallowing D[P]. These disjoint cases
prove the two terms. Native insertion associativity proves only the G law by
itself; it does not discharge the L/A splice laws in Lean.

Let `e(h,r)=r` when h is empty and zero otherwise. The unique all-empty sibling
choice gives `e L_C = G_C e`. Every A term has a positive ancestor factor, so
`e A_C=0`. The unique empty branch cut gives `e δ=id`. Consequently
`K_C=L_C+A_C e` satisfies:

```text
δ G_C = K_C δ
K_(C∘D) = K_C K_D
```

Indeed, expand the product: the term `A_C e A_D e` vanishes; the remaining
terms are `L_C L_D + (L_C A_D + A_C G_D)e`. This holds on arbitrary signed
records, not just records in the image of δ. The coefficient unit and typed
interface remain different: e discards a nonempty forest coefficient, never
identifies a typed Box with a scalar.

These are context-action laws, not H-linearity, an unchanged-coefficient
comodule morphism, a general monad distributive law or a completed native
Hopf representation. No Lean G/L/A/K finite-sum implementation was added after
the first verification gate failed. Cached mathlib `FreeAbelianGroup` is
source-present; the earlier missing Finsupp cache does not establish that all
signed linearization is unavailable.

## Genuine revival fragment and exact inventory separator

Namespace: `Potkin.Research.RevivalInterface`. The presentation uses native
`Formula sigma` with atoms p/q and genuine negation/disjunction operations,
native singleton hypersequents and supplied component incidence. Its 15 exact
stock occurrences comprise 12 ordinary identity, negation-left, weakening and
disjunction-left instances, two right ghost initials and one repeated-boundary
binary ghost owner. `exact_ordinary_instances` at line 215 checks the full
ordinary boundary schemas; `exact_ghost_instances` at line 236 specifies the
ghost boundaries. Stock names alone do not establish admission.

The presentation's exact material base is empty. Nevertheless its ordinary
vertices have native CK cuts: `CKCut`/`CKBranchCut` eligibility is not restricted
to `OccurrenceKind.material`. Material selectors are additional observations,
not the definition of the native cut family.

`raw_fixture_succeeds`, `checkedFixture`, `checkedGood` and `checkedBad` at
lines 402–426 use the public `presentation.checkAt` and `CheckResult.get`.
The realization equalities at lines 428 and 453 relate those quotations to the
native fixtures. Both success and realization declarations are now kernel-checked.
The proof composes checked children through one-root checker lemmas; it no longer
normalizes the entire 21/43-node checker inside a realization proof.

`OwnerSlot` at line 534 keeps physical owner address, atom colour, left/right
role and top-down checkpoint availability. One owner chooses a single colour
shared by its two branches, including when unused. Ghost leaves choose actual
eligible right ancestor slots. A node's empty succedent updates inherited
owners before the node introduces its own owner; therefore an owner's own
conclusion is excluded from its required right checkpoint. The source's exact
boundary theorem separately relates the checkpoint predicate to admitted
instances.

`count_positive_iff` at line 642 is a constructor-induction proof for arbitrary
native trees and environments under this explicitly represented query:

```lean
0 < certificateCount tree address env ↔ HasScopedCertificate tree address env
```

Interpreting a tree as this LQ fragment additionally requires its exact local
admission; a foreign occurrence is not classified from its label alone.

The source's specific regression targets are:

| Native fixture | Kernel-checked fixture result | Native declaration |
| --- | --- | --- |
| Four 21-node corner fillings pp, pq, qp, qq | Certificate counts 1, 0, 0, 1. | `literal_node_counts`, `cooperative_counts`. |
| 43-node `good = upper (fixture p p) (fixture q q)` and `bad = upper (fixture p q) (fixture p q)` | Same multiset of complete exact local occurrences; certificate counts 1 and 0. | `equal_exact_inventory`, `separator_counts`, `certificate_separator`. |

The inventory equality retains full occurrence values, including exact
boundaries, incidence and stock IDs, but forgets their physical placement.
The certificate separator tests the ownership arrangement lost by that
inventory; it is not the earlier rule-permission observer and not a claim that
the common ordinary endsequent lacks an LJ proof. Both rows are now checked
specific-fixture evidence, not universal LQ adequacy.

Lang's Definition 5 also has left and empty ghost initials; right ownership
requires an empty checkpoint strictly above the owner, and Theorem 12 sketches
revival with weak excluded middle assumptions. The present source represents
only the right-ghost part of that criterion, not the complete certificate
network or the constructive revival theorem.
[Primary source, Definition 5 and Theorem 12](https://discovery.ucl.ac.uk/id/eprint/10182303/1/tableauxRep.pdf).

### The first missing semantic bridge

`certificateCount` gives an unfilled interface zero because it asks for a
closed-source certificate. It is not an interface kernel for a cut piece.
An open coefficient must preserve inherited owner identities, joint colour
constraints, checkpoint obligations and live ports; those must be glued before
existential closing. Otherwise separately feasible pieces can be incompatible.
No cut is deleted by assigning coefficient zero.

Full Definition-5 routing/equality-network semantics, assignment-level
global-to-pieces bijections and cut-flag coherence are absent. So are C1
proof-producing ordinary LJ revival, C4 bottom-up pending-debt interfaces and
the 8-to-11-node zero-added-W/C example. Top-down `seenCheckpoint` is not
bottom-up pending debt. The paper's Boolean zeta change of coordinates needs
the entire formal interface domain and does not fill this native bridge.

The 963-cut cooperative cache polynomial, Hasse derivative calculation,
positive macro defects, checked hypersequent translation and native convolution
cache/antipode laws remain paper targets. The 21-node count fixture is not
their implementation. No fixture translator or generic tree was relabelled as
the missing analytic compiler.

### Open-fragment gluing contract

The following is a **PROVED paper-level constructor argument for the stated
right-ghost fragment**, not yet a Lean interface or a proof of full LQ adequacy.
It addresses the next priority without substituting a scalar product for shared
assignments.

Use a Type-valued continuation kernel on the existing native tree:

```text
Kernel(tree, provider, absoluteAddress, inheritedScope)
provider : tree.LeafOccurrence -> absoluteAddress -> inheritedScope -> Type
```

`LeafOccurrence` is the existing physical interface index, not a logical port
name or a new context. At an interface the kernel invokes its provider with
the unchanged pre-root scope: a typed vacancy does not introduce a checkpoint.
At a genuine ordinary occurrence, inherited owners advance past its actual
empty conclusion. An owner then chooses one colour, shared by its two ordered
premises, including when unused. A right ghost chooses an indexed eligible
ancestor from the resulting scope; using an index retains multiplicity when
owners have equal colours. Other ordinary occurrences take the ordered product
of their premise kernels. Malformed owner arities have no witness; exact local
admission excludes malformed ghost nodes. A closed kernel uses empty providers,
not a fabricated proof of a Box.

For a complete locally admitted source and native proper or empty cut `c`, the
geometric adapter required in Lean is

```text
c.remainder.LeafOccurrence ≃ c.Site
```

preserving each whole boundary and selected address. Completeness matters:
without it, old source interfaces must be distinguished from cut-created ones.
For each remainder hole, define the continuation to evaluate the aligned
detached factor's closed kernel at the hole's actual absolute address and
inherited scope. Then

```text
ClosedKernel(source, address, scope)
  ≃ Kernel(c.remainder, detachedContinuations, address, scope).
```

Proof: recurse mutually through the native cut plan and ordered children. A
detachment replaces precisely one factor witness by its interface callback.
Descent leaves the ordinary occurrence and its checkpoint update unchanged,
and applies the induction equivalences in premise order. At an owner, both
directions retain the same single colour choice before decomposing the children.
Restriction and gluing are inverse at every constructor; native addressed refill
identifies the reconstructed decorated source. The detached root processes its
own conclusion exactly once, after the seam, rather than treating the vacant
remainder slot as that vertex. The empty cut has no callbacks; the separately
represented whole branch has one callback for the whole source.

Equivalently this is a dependent sum of open remainder assignments with products
of compatible factor assignments *conditioned on the scopes exported by that
same remainder assignment*. It is not a product of independently closed piece
certificates. The required Lean hole/site adapter, continuation kernel and inverse
proof remain **OPEN**; they are the next priority now that the quotation gate is
closed, followed by the signed finite-sum `K_C` laws. No new
proof, cut, forest or context carrier is proposed by this metadata interface.

## Independent review and unresolved targets

Independent source review accepted the context decomposition's swallowing
semantics, premise order and full-branch versus proper-cut distinction. It
also identified the scope guard that the closed certificate count is not an
open-piece coefficient. All reviews are source/mathematical reviews, not
independent successful Lean checks.

A separate read-only review of RevivalInterface accepted its genuine boundary
instances, physical owner identity, exclusion of the owner's own conclusion
from checkpoint eligibility and full-inventory separator. It found no serious
logical inconsistency within that stated fragment, while confirming that the
observer does not establish unrestricted LQ adequacy or the missing CK bridge.

The D1–D6 meanings below are the supplied report's dictionary and programme,
not newly invented targets.

| Target | Present contribution | Remaining exact obligation |
| --- | --- | --- |
| D1 relative Cut | Existing native structural work remains available; no new general eliminator. | Source-specific ghostification/certificate reconstruction and a stated supplied base LJ normalizer. |
| D2 controlled copying and normalization | Physical cut addresses/order retained by the mechanized packet equivalence. | Checked process migration adapter and explicit fresh-copy/masking laws. |
| D3 actual structural lifts | Genuine weakening instances occur in the native fixture. | General compiler debt, contraction/weakening lifts and canonical boundary theorem with exact hypotheses. |
| D4 decomposition and analytic compilation | Mechanized universal pointed packet equivalence and the paper affine/K proof above. | Finite-sum choice splice; full scoped grammar and proof-producing revival; positive macro defect comparison. |
| D5 stable interfaces and reuse | Kernel-checked exact-inventory certificate separator and four coordinated fillings; paper continuation-gluing contract above. | Lean open interface and gluing; checked opaque replay, all-cut cache polynomial and cooperative sensitivity theorem. |
| D6 presentation/base comparison | Native all-positive cuts distinguished from material coefficient selection. | Actual open-boundary translation adapter and comparison laws retaining defects; no assumed Hopf morphism. |

In particular, subtree material purity is not automatically a persistent
vertex mark under puncturing/filling. The supplied eligibility adapter's
installation, inherited-state and remainder stability laws require an actual
native proof before they can justify a restricted cut/coaction statement.

## Authorized verification continuation

The user explicitly excepted these two modules from the repository's older
60-second/no-retry policy. The policy file itself remains unchanged. Startup
was isolated with pinned `lean.exe --stdin` and one import per invocation:

| Input | Duration | Child exit |
| --- | --- | --- |
| `import Potkin.CompositeCutExpansion` | 205.952 seconds | 0 |
| `import Potkin.GeneralFilling` | 62.285 seconds | 0 |

The context source was then corrected for concrete dependent-pattern and
`Sum.inr` congruence errors. The exact final command was:

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/ContextCutPackets.olean Potkin/Research/ContextCutPackets.lean
```

It completed in **100.460 seconds, child exit 0**, without timeout. Its in-source
`#print axioms` results were all exactly `[propext, Quot.sound]`:

- `fullPacketEquiv`
- `packet_and_remainder_preserved`
- `orderedPacket_descend`
- `assembled_refill`
- `assembled_admitted`
- `outer_ancestor_packet`
- `insert_compose`

No `sorryAx` or custom axiom occurs in those closures. These are universal
constructor results on the native typed trees and cuts, not bounded fixtures.

The revival source's first completed corrected check took 139.521 seconds and
reported concrete boundary-permutation, missing arithmetic-lemma and fixture
realization heartbeat failures. Those failures were corrected. The resumed
check of the corrected source used the analogous `lean.exe -o ...` command for
`RevivalInterface.lean`. It reached 300.262 seconds with 321.641 CPU seconds
recorded, was terminated at the announced bound and returned after **305.821
seconds, child exit −1**. No headline axiom output was obtained. A modular
quotation correction was then made to avoid normalizing the entire 43-node
checker inside `CheckResult.get`; at that stage this was still a verification gate.

That correction replaced large quotation normalization with one-root checker
lemmas and already checked ordered children. Its targeted check completed in
**102.653 seconds, child exit 1**, without timeout. It identified a reflexive
case-split goal, unreduced `True` guards in the new binary-root helper, a missed
child-realization rewrite and a separator elaboration heartbeat failure.
These are local proof failures, not mathematical counterexamples. Its output
gave clean closures for `exact_ordinary_instances`,
`exact_ghost_instances`, `equal_exact_inventory`, `count_positive_iff` and
`certificate_separator`; quotation-dependent declarations contained the
elaborator's failure placeholders (`sorryAx`) in this failed run. No failed
closure is counted as a verified theorem. The whole revival module was not
promoted to `MECHANIZED` at that failed checkpoint.

The next focused correction completed in **75.586 seconds, child exit 1**.
The checker helpers and `raw_fixture_succeeds` then had clean closures. Only
`checked_fixture_realizes` (child rewriting) and `checked_separator_realizes`
(elaboration heartbeats) failed. Their final correction uses explicit equality
composition and native constructor congruence instead of searching through
checked getters.

The final command on that corrected source was:

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/RevivalInterface.olean Potkin/Research/RevivalInterface.lean
```

It completed in **54.140 seconds, child exit 0**, without timeout. All headline
axiom closures were obtained on the successfully compiled final source:

| Declaration | Exact closure |
| --- | --- |
| `exact_ordinary_instances` | `[propext, Classical.choice, Quot.sound]` |
| `exact_ghost_instances` | `[propext, Quot.sound]` |
| `checked_fixture_realizes` | `[propext, Classical.choice, Quot.sound]` |
| `checked_separator_realizes` | `[propext, Classical.choice, Quot.sound]` |
| `equal_exact_inventory` | `[propext, Quot.sound]` |
| `count_positive_iff` | `[propext, Classical.choice, Quot.sound]` |
| `certificate_separator` | `[propext, Classical.choice, Quot.sound]` |

The additional phase checkpoint `raw_fixture_succeeds` has
`[propext, Classical.choice, Quot.sound]`. No headline closure contains `sorryAx`
or a custom axiom. A final focused source scan of these two modules found no
authored `sorry`, `admit`, `unsafe` or `axiom` declaration. Two harmless unused
simp-argument warnings remain at line 305; they were not edited after successful
verification. No new finite enumeration, full build or full suite was run.

The verification gate is therefore **closed for these two final sources**.
Open-fragment continuation kernels, the native hole/site adapter and gluing
theorem remain to be implemented, followed by the signed finite-sum `K_C`
composition laws. Their scoped paper arguments above are not promoted to Lean
mechanization, and the integrated research programme is not declared complete.

For completeness, the context source checks preceding its final success took
118.797, 83.137 and 122.822 seconds, each child exit 1 for the concrete dependent
pattern/congruence errors described above. Every rerun followed a source fix;
the successful context source was not rechecked.

An earlier line-based capture wrapper failed to enforce its limit while draining
long proof-error output. Its known Lean child was still alive at 663.096 seconds
and was terminated; subsequent runs
used asynchronous stream draining and bounded process waits. That monitoring
failure is not proof evidence. No whole-project build or test suite was run.

## Initial verification before the exception

Both commands ran from the POTKIN3 root, with a per-process `LEAN_PATH` containing
the existing repository and installed package `lib/lean` caches. No Lake build
or dependency compilation campaign was run.

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/ContextCutPackets.olean Potkin/Research/ContextCutPackets.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/RevivalInterface.olean Potkin/Research/RevivalInterface.lean
```

| Command | Duration | Result and last observable phase |
| --- | --- | --- |
| ContextCutPackets | 60.554 seconds | Wrapper terminated and joined the launched process; exit −1; stdout/stderr empty. No completed dependency or elaboration phase was reported. First source import: `Potkin.CompositeCutExpansion`; its completion is unknown. |
| RevivalInterface | 60.213 seconds | Wrapper terminated the launched process; exit −1; stdout/stderr empty. A process checkpoint recorded 5.141 CPU seconds and about 61.4 MB memory, but identified no completed checking phase. The current source imports only `Potkin.GeneralFilling`. |

At that initial checkpoint no launched Lean process was left running and neither
command had been retried.
Two unused RevivalInterface imports were removed after its timeout; at that
checkpoint the edited source was explicitly **NOT RECHECKED**. Silence did not identify
a dependency failure, a type error or a proof success.

Each module contains seven central `#print axioms` requests. Neither initial command
returned any of their output, so at that checkpoint axiom closures, including
absence of transitive `sorryAx`, were **UNVERIFIED**. Static inspection of just the two new modules
found no authored `sorry`, `admit` placeholder, custom axiom declaration or
`unsafe`; that is not a substitute for the missing kernel/dependency check.

The repository's older `AGENTS.MD` policy was left unchanged; the explicit
one-off user exception and its results are recorded above. The full prompt
has not been declared complete.

## Document organisation and preservation

The complete received wrapper moved from `docs/CK_RESEARCH_EVIDENCE/` to
`docs/archives/2026-10-12/ck-research-evidence/`. Its inner `hopf_research`
directory name, sibling relations, validation records, manifest paths and
prototype files remain intact. All 63 relocated files matched their original
SHA-256 hashes; no content was concatenated, deleted or rewritten.

This dated report is linked from [the documentation index](../../2026-10-12-index.md).
Prior reports and archives stay where the earlier cleanup placed them. Native
sources remain under `Potkin/Research/`; the root semantic contract, repository
policy, public imports and pre-existing native modules were not edited. The
documentation workflow kept one dated report and a surgical index update,
rather than producing further root-level notes or duplicating the bundle.
The existing 59-file protected baseline still matches its original hashes;
all local links in this report and the updated index resolve. Those are static
preservation/navigation checks, not additional mathematical verification.

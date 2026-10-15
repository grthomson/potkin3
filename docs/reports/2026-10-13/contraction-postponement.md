# Native CK certified contraction postponement 13 October 2026

Historical 13 October record, with a [15 October native HLJ continuation](#15-october-2026-strict-hlj-compilation-and-a-physical-lemma-frontier)
below. The earlier missing-rule statements describe the earlier snapshot, not
the new structural fragment.

Latest: [recursive prepared Sys(com) translation and reuse](#recursive-prepared-syscom-continuation--theorem-stated-before-implementation).
The [fixed X/Y application](#15-october-2026-prepared-syscom-translation-and-localized-ck-reuse)
is its verified predecessor.
The [whole-Plan certified pruning](#15-october-2026-continuation-whole-plan-certified-pruning)
milestone is complete in its recorded scope.
Earlier continuations are historical snapshots, including their then-open gates.

## Outcome and scope

HEAD is `93b4a9abce87692ac32665132144ba1cd602808c`, on `main`.
Work remains uncommitted. Existing AGENTS.MD, README, document moves and unrelated
Lean sources are preserved. No branch, commit, full build or finite test campaign
was created.

This is an additive, **parameterized** native milestone. The current stock does
not instantiate HLJ Communication, external weakening or external contraction.
The compiler requires genuine supplied rule instances and their admission; it
does not manufacture an admission theorem. The native compiler, exact costs,
completeness and checker realization are **MECHANIZED**. The universal physical
CK observation, native one-hole affine action and scalar K adapter are also
**MECHANIZED**, including the compiler-to-native-cut-objective integration. All
six new modules passed targeted Lean checking. Two requested extensions remain
**OPEN**: a genuine native HLJ+com/EW/EC instantiation and an instantiated
coefficientwise polynomial comparison. This is not a claim that every requested
concrete deliverable has been completed.

## Native rule gate

`ProofTheory.lean:126` defines user-supplied logical/structural predicates, and
`ProofTheory.lean:161` defines exact admission. `Presentation.lean:7` supplies a
finite equipped registry with unique IDs. Neither installs a general HG calculus.
The fixed stock at `Research/RevivalInterface.lean:177` has internal antecedent
weakening, not external EW. The contraction instances in
`Research/StructuralReduction.lean:144` and `:162` are internal antecedent
contractions, not external EC. Focused source inspection found no native HLJ+com
schema.

`ContractionPostponement.RuleInterface` therefore supplies:

- The exact ordered rule family with premises `K | C_i` and conclusion `K | H`.
- External EW with premise `G` and conclusion `{S} | G`.
- External EC with premise `{S} | G`, conclusion `G`, and explicit `S ∈ G`.
- Actual `T.Admits` evidence and supplied incidence on every instance; EW/EC
  occurrences must have structural kind.

Supplied incidence is retained with the native occurrence. Its presence does
not prove formula movement or identify a rule as Communication. Boundary equations
and genuine admission are separate obligations.

Arbitrary context extension belongs at the schema-level proof theory. Only the
finite occurrences of a chosen output must belong to its equipped registry.
Demanding infinitely many extensions in one finite registry would generally be
unrealizable. `compile` takes checked donors under one exact registry and requires
registration of the actual finished tree; the public checker then constructs
the output, with literal realization equality.

Consequently the paper's HLJ+com example is **not a registered native fixture**.
The reported 29/35 node and 7401/84105 full-cut comparisons remain paper-level;
no schematic four-component rule was relabelled as Communication.

## Exact compiler contract

`ContractionBoundaries.Problem` records positive `n`, positive multiplicities,
native component multisets, their support in `G`, and a nonempty native `H`.
At a bounded state `alpha`, its whole boundary is exactly

```text
G + G'' + (q - |alpha|) H + sum_i alpha_i {C_i},
q = 1 + sum_i (m_i - 1).
```

The indexed `ContractionPlans.Plan` has a threshold stop and a continuation with
every ordered `Fin n` child. `threshold_at_quota` is a universal pigeonhole proof;
`rank_decreases` proves termination by the remaining depth. `plan_exists` works
for every bounded state, not just small multiplicities.

`boundary_continue` and `boundary_child` prove the literal common-context rule
substitutions. The stop script weakens by the **actual multiset difference** from
the selected donor. `donor_le_state` proves its inclusion, and `stop_weight_exact`
proves the prescribed count

```text
w_i = |G''| - |G'_i| + (q - |alpha|)|H| + |alpha| - m_i.
```

The terminal queue removes `G'' + (q-1)H`, with every removed occurrence supported
by the retained `G | H`. Its length is exactly `|G''| + (q-1)|H|`. Aliased labels
are counted with multiplicity; support in `G` is not confused with multiset
inclusion in `G`.

The native interpreter exposes `interpret`, `finish`, `checkedFinish`, `compile`
and their complete-realization/cost laws. `CompleteQuotation.quote_realize` is a
universal checker-completeness helper: complete, exactly registered native trees
quote through `checkAt` and realize literally unchanged. No private checked
constructor or certificate for an unfilled Box is introduced.

EC postponement uses pre-terminal `interpret_avoids` with the exact EC predicate:
donors, EW and the continuing rule must avoid EC. The continuing-rule condition
is essential. Logical-Cut freedom uses `finish_avoids`, additionally requiring
the supplied terminal EC instances to avoid the exact logical-Cut predicate.
An arbitrary role name or occurrence kind is not such a predicate proof. The
construction locates new EC in the terminal queue; no stronger queue-address
classification theorem is claimed.

`minimum_attained`, `minimum_le_plan` and `bellman_alternative` prove attained
node optimization **only within this canonical opaque-donor language**.
`lexPlan_optimal` permits a secondary native cut-cardinality objective. These are
noncomputable attainment/selection theorems, not an executable Bellman-search
implementation or a global optimum among logical proofs.

### New native declarations

All paths below are relative to POTKIN3; none replaces an existing carrier.

| Module | Headline declarations and hypotheses |
| --- | --- |
| `Potkin/CompleteQuotation.lean` | `quote_correct`, `quote_succeeds`, `checkedOfComplete`, `quote_realize`: complete trees with exact `LocallyAdmittedTree P` evidence, under decidable native boundary equality. |
| `Potkin/Research/ContractionPlans.lean` | `threshold_at_quota`, `rank_decreases`, `plan_exists`: positive arity/multiplicities and bounded state; `minimum_attained`, `bellman_alternative`, `lexPlan_optimal`: the fixed indexed Plan language and supplied stop weights. |
| `Potkin/Research/ContractionBoundaries.lean` | `boundary_continue`, `boundary_child`, `donor_le_state`, `stop_weight_exact`, `terminal_boundary`, `terminal_cost`: exact multiset data in `Problem`; donor containment uses the selected threshold and terminal EC uses component support. |
| `Potkin/Research/ContractionPostponement.lean` | `interpret_degree`, `interpret_complete`, `interpret_avoids`, `finish_degree`, `finish_avoids`, `checkedFinish_realize`, `compile_realize`: supplied `RuleInterface`, donor hypotheses, and explicit registration of the finished output when checked quotation is requested. |
| `Potkin/Research/ContractionCutObservation.lean` | `Q_native`, `Q_one_card`, `Q_unary`, `Q_context`, `Q_context_totalLE`, `scalar_delta`, `scalar_K_context`: native full branch cuts, one physical puncture for the context laws, and explicit integer projection for the K adapter. |
| `Potkin/Research/ContractionCompilerCuts.lean` | `Q_stopTree`, `Q_interpret`, `Q_finish`, `finish_lex_optimal`, `finish_lex_cutCard_optimal`, `compile_Q`: exact compiler recurrence, native physical secondary objective, and the same checked-front-end registration gate; final-source verification is recorded below. |

## CK observation and contextual reuse

The existing native full convention is `CKBranchCut`: root-excluding descending
cuts and a separately represented whole-branch detachment. Typed interfaces have
only the empty choice. Public `CKCut` never selects its own root.

The new `ContractionCutObservation` uses constructor-recursive `Q z` in an
arbitrary commutative semiring. Its verified constructor laws and integrated
compiler recurrences are:

```text
Q_z(Box^G) = 1
Q_z(node(children)) = z + product Q_z(children)
Q_z(stop) = Q_z(donor) + w_i z
Q_z(finish) = Q_z(interpreted Plan) + terminalQueueLength z.
```

This is an observation, not a new proof/cut/forest/context carrier. The native
witness-sum theorem is over physical `CKBranchCut` objects before scalar
collection. `Q_native` proves equality with this finite witness sum for arbitrary
commutative semirings; `Q_one_card` proves that the total at `z=1` counts these
witnesses with full multiplicity.
An interface evaluating to `1` does not identify its typed proof state with the
empty-forest coefficient unit.

The one-hole affine law has actual native insertion on the left. Its coefficients
are built from off-spine sibling observations and ordinary spine vertices. Native
same-boundary fillings still require their own admission. The integer scalar
projection of the previously verified `delta/K` records forgets typed remainders
only at an explicit projection. The K adapter is restricted to the image of
`delta`; it does not claim that a scalar determines K on arbitrary records.

**OPEN:** an instantiated finite-coefficient polynomial carrier and a kernel-checked
coefficientwise-order adapter. A targeted Polynomial import closure hit missing
cache files; a minimal existing MonoidAlgebra import also failed on
`Mathlib.Data.Finsupp.Basic`. The fallback universal semiring laws are not finite
evaluations, but natural total-count dominance must not be called coefficientwise
dominance. The first-hit multinomial formula is optional and remains unimplemented.

## Obstructions and programme comparison

- Early stopping is not always cheaper: exact EW weights participate in Bellman
  optimization. Donor interiors are opaque; aliases can permit better scripts
  outside this language.
- Equal node/cut summaries do not identify literal typed remainders. This compiler
  retains the native tree and checker realization; no remainder equivalence is
  inferred from a scalar.
- Physical copying does not make scope-sensitive certificate choices independent.
  The verified shared-scope gluing theorem remains the relevant interface; this
  milestone does not replace it by products of closed counts.
- No coefficientwise-positive defect of EC postponement, tensor equality or
  material-relative conservation theorem is asserted.

| Programme | Additive result or precise remaining obligation |
| --- | --- |
| D1 relative Cut | Checked structural preprocessing is available conditionally on the rule interface. A supplied logical/base normalizer and source-specific analytic correctness bridge remain necessary. |
| D2 controlled copying | Ordered premise families and native physical copies remain intact. No independent scope choices or fresh-copy semantic adequacy theorem is inferred. |
| D3 structural lifts | Exact EW/EC boundary scripts and node costs are formalized; actual HLJ+com/EW/EC schema admission remains missing. |
| D4 decomposition and compilation | Native proof-producing Plan interpretation complements the already verified cut gluing and K laws; no general logical Cut eliminator is claimed. |
| D5 stable reuse | Native one-hole scalar affine action supports conditional total dominance. Shared-scope provider equivalence, not equal Q, is still required for certificate transport. |
| D6 presentation/base comparison | One equipped registry is required at quotation. There is no cross-snapshot cast, relative-material lift or asserted Hopf morphism. |

Compared with 12 October, gluing/coherence/K are reused rather than re-proved.
The additive advance is exact structural compilation and opaque-donor optimization,
with a physical CK observation. Actual rule instantiation and coefficientwise
comparison are separate open gates, not consequences of that older milestone.

## Verification record

All invocations use the pinned executable below and existing project/package
caches in `LEAN_PATH`, asynchronously drained output and a 300-second bound on
the actual Lean child. Checkpoints report CPU/memory progress. There was no timeout,
full build, suite, benchmark or finite-case oracle in this milestone.

The exact final Lean child commands, from the POTKIN3 root, are below. The
monitoring wrapper supplies `LEAN_PATH` and the stated bound; it is not a build.

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/CompleteQuotation.olean Potkin/CompleteQuotation.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/ContractionPlans.olean Potkin/Research/ContractionPlans.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/ContractionBoundaries.olean Potkin/Research/ContractionBoundaries.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/ContractionPostponement.olean Potkin/Research/ContractionPostponement.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/ContractionCutObservation.olean Potkin/Research/ContractionCutObservation.lean
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -o .lake/build/lib/lean/Potkin/Research/ContractionCompilerCuts.olean Potkin/Research/ContractionCompilerCuts.lean
```

| Final source check | Seconds | Result |
| --- | ---: | --- |
| CompleteQuotation | 58.405 | PASS; `[propext, Quot.sound]` for all four headline closures |
| ContractionPlans | 53.687 | PASS; all five headline closures printed clean in the successful integrated final check |
| ContractionBoundaries | 53.465 | PASS; headline closures `[propext, Classical.choice, Quot.sound]` |
| ContractionPostponement | 53.282 | PASS; all seven headline closures `[propext, Classical.choice, Quot.sound]` |
| ContractionCutObservation | 50.552 | PASS; all seven headline closures clean, detailed below |
| ContractionCompilerCuts | 57.202 | PASS; all five integration headline closures `[propext, Classical.choice, Quot.sound]` |

Earlier relevant-fix checks are not mathematical evidence: Plan 114.621, 20.778,
102.508 and 67.359 seconds; quotation 118.246, 75.803 and 59.194 seconds;
boundaries 62.019, 68.848 and 74.188 seconds; native interpreter 96.271, 67.621
and 58.368 seconds. They resolved named missing imports, dependent casts,
recursive parameter binding and local arithmetic. Failed-check placeholder
closures are rejected, even when other declarations in that run elaborated.

The CK observation required concrete fixes after 89.992, 58.645 and 90.849-second
checks; the last issue was the universe of its separate singleton whole-branch
choice. Its final successful source has `[propext, Classical.choice, Quot.sound]`
for `Q_native`, `Q_one_card`, `scalar_delta` and `scalar_K_context`, and
`[propext, Quot.sound]` for `Q_unary`, `Q_context` and `Q_context_totalLE`.
No accepted closure contains `sorryAx` or a custom axiom. The integration's first
77.199-second check found an ordered-list transport and redundant dependent
generalization; both were corrected before its successful final-source rerun.
That successful check printed `Q_interpret`, `Q_finish`, `finish_lex_optimal`,
`finish_lex_cutCard_optimal` and `compile_Q`, and the Plan headlines
`threshold_at_quota`, `plan_exists`, `minimum_attained`, `bellman_alternative` and
`lexPlan_optimal`. All ten accepted closures are exactly
`[propext, Classical.choice, Quot.sound]`.

The Polynomial route stopped at missing `Mathlib.Data.Finset.Powerset.olean`.
Earlier import failures took 188.512, 43.481, 28.259, 26.094 and 19.959 seconds.
Only explicitly missing existing Pi, Factorial.Basic, Choose.Basic and Max cache
modules were targeted: successful checks took 53.658, 49.953, 47.361 and 65.359
seconds respectively. Factorial's initial 52.618-second run passed its source but
failed writing an absent output directory; the rerun followed that exact repair.
The alternate MonoidAlgebra import probe failed after 19.896 seconds on missing
Finsupp.Basic. No package was installed or broad cache/build campaign launched.

Independent reviews checked boundary substitutions, support versus multiplicity,
finite registry feasibility and the restricted optimality language. They identified
the necessary non-EC continuing-rule condition and warned about dependent child
casts; those corrections are reflected in the implementation. No reviewer supplied
an admission theorem for the missing HG calculus.

The final independent static review also checked the observer/integration pair:
the witness-sum uses actual whole/descend and ordered head/tail bijections, Box
has only its empty choice, the whole endpoint remains separate, the scalar K
claim is restricted to the image of delta, and the physical-cut optimum has only
the stated Plan scope. It found no additional mathematical overclaim or missing
hypothesis in these statements. This review is source evidence, not a further
Lean invocation.

## 15 October 2026: strict HLJ compilation and a physical lemma frontier

### Outcome

HEAD: `2835d448722e6e366c26003004b19b631984691b`, existing `main` branch.
All changes remain uncommitted. The six pre-existing D3 source modules and
their uncommitted report/ledger changes were preserved; they were not rebuilt.
No Racket files, AGENTS policy, protected files, branch or remote were changed.

Four additive Lean modules now pass targeted checks. These are universal
constructor proofs, not agreement on finitely many generated derivations.

| Module | Newly MECHANIZED result |
|---|---|
| `Potkin/Research/HLJStructural.lean` | Exact identity, antecedent-repartition Communication, external weakening and indexed external contraction schemas. `theory` checks the full canonical occurrence, supplied component incidence and single-succedent validity of every active/passive component. `no_unconditional_hlj_interface` proves a genuine obstruction in the old unrestricted interface. |
| `Potkin/Research/HLJContraction.lean` | `finish_strict`: strict admission of every reached compiler occurrence, for arbitrary positive binary donor multiplicities, supported passive extras and well-formed common context. `checkedFinish_realize`: quotation into a strict admitting registry retains the literal native tree. |
| `Potkin/Research/StructuralLemmaCuts.lean` | A native proper CK frontier for an ordinary open scaffold filled with ordinary proofs; literal scaffold remainder, native refill, one site per physical hole, actual site/hole equivalence, exact aligned detached-provider equality, and exact expansion cost. `extractionEquiv` applies the existing installed-cut bijection, accounting for donor-interior cuts. |
| `Potkin/Research/HLJStructuralApplication.lean` | An actual three-entry strict registry and checked Communication proof, universally in formulas A,B. Separate closed-donor and physical-hole compiler front ends, exact closed-donor degree/Q adapters, `certifiedFrontier`, physical-hole expansion cost, and the signed contextual CK-difference corollary of the existing K law. |

### The admission correction and the actual rule

The actual Communication instance is

```text
K | phi,gamma1 => pi1       K | psi,gamma2 => pi2
------------------------------------------------ Com
K | psi,gamma1 => pi1 | phi,gamma2 => pi2
```

Premises are ordered. Every displayed succedent has cardinality at most one;
passive K is shared once in the conclusion. Formula contexts and hypersequents
remain multisets. EC records the index of an actual retained occurrence of S
in G, not merely the fact that an equal-looking component exists somewhere.

The old `RuleInterface` demands admitted EW for EVERY native sequent S. Native
sequents allow two succedents, so strict HLJ cannot meet that demand. The new
obstruction theorem uses S with rhs `{A,A}`; this is not a timeout or a failed
proof search. We did not weaken HLJ to fit the interface or replace the API.
Instead, `assemblyTheory` is an explicitly unchecked schema envelope used only
by the existing raw-tree assembler. Guarded induction proves strict admission
of the reached states/EW/Com/EC instances. Checked quotation uses only `theory`.

The admitted stock is the identity/Com/EW/EC STRUCTURAL FRAGMENT of HLJ+com.
It does not yet admit all LJ logical rules or logical Cut. Component incidence
is a declared genealogy convention: in particular, the active Com components
are related all-to-both. It is not a proved formula-occurrence resource action.
Candidate component edges are bounds-checked; a separate coverage theorem for
the generated edge list has not been added.

### The CK connection, and the exact remaining integration boundary

For any ordinary native open tree M and complete checked fillers at its
physical interfaces, `properFrontier` selects the actual inserted roots below
the whole root. Empty frontiers are allowed. A naked root Box is rejected as
the scaffold of a proper frontier. The global whole endpoint is not fabricated
as a root cut and remains separate in the existing full-branch Q/delta APIs.

`proper_remainder` proves literal native-tree equality with M.
`native_refill` reconstructs the completed proof using its native detached
family. `holeMatching` is an actual bijection, not equality of counts.
`alignedDetached_eq` proves equality of the ENTIRE original physical filler
provider after transport along that literal remainder equality. Repeated equal
fillers at different holes do not collapse. Native selected-site boundary and
address lemmas remain available through the reused `CutHoleAdapter`.

`filling_degree` proves

```text
degree(fill M providers) = degree(M) + sum over physical holes h of degree(provider h).
```

The existing `compositeCutEquiv` is reused to classify all root-excluding cuts
of the filled proof, including cuts newly available inside fillers. This is
stronger information than a scalar size or cut-count summary, but it is an
application of the verified native bijection, not a new abstract Hopf theorem.
Ordered packets and matching are retained before any commutative collection.

There are TWO deliberately separate compiler front ends:

- `compileStrict` uses the original indexed donors D_i. Its literal realization,
  exact Plan node costs and semiring Q recurrence are proved. Existing Plan
  optimality remains confined to its opaque-donor language and is noncomputable
  attainment, not an implemented search or global logical-proof optimum.
- `compileAtHoles` fills the compiled open scaffold by PHYSICAL hole occurrence.
  It has checked realization, a proper native frontier, exact remainder/refill
  and physical-hole degree cost. The Plan-derived hole-to-original-donor-index
  assignment and equality with `finish(D_i,plan)` are NOT yet implemented.
  Equal boundaries cannot recover donor identity. Therefore index-uniform
  `planQ`/optimality claims are not silently transferred to this workflow.

Both fronts require exact admission in ONE immutable strict registry. The
three-entry identity/Communication registry is constructed, not assumed.
Finite fresh consistent allocation for an arbitrary compiler output remains
a separate gate; there is no silent calculus extension or provenance cast.
The m=(2,2) paper counts 29/35 nodes and 7401/84105 cuts have NOT been reproduced
as an admitted compiler fixture in this continuation.

The context corollary is an exact signed extraction statement:

```text
delta([C[S]] - [C[T]]) = K_C(delta[S] - delta[T]).
```

It reuses `delta_K`; it does not re-prove K composition, assert tensor equality
between S and T, or assert a positive defect. It is a combinatorial law, not by
itself a checked-exterior correctness theorem or a material-profile theorem.

### Proof-theoretic value and programme position

The useful advance is an actual admitted structural compiler application plus
a native decomposition boundary for lemma use. A derived lemma's open premises
are explicit typed interfaces; filling them is not itself Gentzen Cut, and
compressing an arbitrary convex region to a newly admitted corolla is not
implemented here. The term "lemma rule" is helpful, but does not waive admission.

The potential practical payoff is a proof transformer whose output is checked,
whose specified expansion cost is known, and whose unchanged scaffold and
changed interior extraction families can be distinguished exactly. K propagates
the signed CK change through a surrounding typed context, including ancestor
effects. This is not merely rule inventory. It still needs an executable Plan
selector/registry allocator and the physical donor-index adapter before it is
a convenient end-to-end incremental analysis tool. No runtime advantage over
typed zipper/DAG caches, no literature novelty, and no process-calculus
application has been established by this milestone.

Using the ORIGINAL programme labels (not the historical internal D3 filenames):

| Direction | Advance / remaining obligation |
|---|---|
| D1: new relative logical-Cut obligations | Strict structural preprocessing can be quoted; full logical-rule admission and the actual source logical-Cut reduction bridge are still required. CK cuts are not logical Cut. |
| D2: nonlinear normalization | Genuine Com/EW/EC reached-instance correctness and exact costs now instantiate the old conditional construction. No general owner-copying, global termination/confluence or full HLJ normalization theorem is claimed. |
| D3: uniform weakening | Native guarded EW admission/scripts support the structural application. The earlier source-adequacy modules are NOT a uniform-weakening metatheorem; that general obligation remains distinct. |
| D4: decomposition yielding analytic calculi | Actual native physical frontier, exact matching and installed-cut classification connect compilation to CK decomposition. Analytic-calculus extraction remains downstream. |
| D5: stable fragments/reuse | One-registry checked fillings and a literally retained scaffold give a precise reuse boundary. Material/profile fidelity, nonlocal owner conditions and an incremental runtime checker are not added here. |
| D6: structural conservativity across bases | No new conservativity, base-extension adequacy or material-relative coaction theorem. |

### Targeted verification and independent review

The user's explicit exception authorized monitored 300-second targeted checks
and ONE independent mathematical reviewer. The wrapper drains stdout/stderr
asynchronously, monitors CPU/RSS and enforces its bound on the actual Lean child.
All invocations exited; none timed out. No full build, suites, enumerations,
benchmarks, import audit, dependency installation or unchanged-module recheck ran.

Exact child commands from the POTKIN3 root, with `LEAN_PATH` set to the existing
native/package build libraries, were:

```powershell
$ckLean='C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe'
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJStructural.olean Potkin/Research/HLJStructural.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJContraction.olean Potkin/Research/HLJContraction.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/StructuralLemmaCuts.olean Potkin/Research/StructuralLemmaCuts.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJStructuralApplication.olean Potkin/Research/HLJStructuralApplication.lean
```

| Final successful source | Seconds | Result / headline axiom closures |
|---|---:|---|
| HLJStructural | 36.415 | PASS. Obstruction, Com boundary lemmas and strict whole-boundary validity: `[propext, Classical.choice, Quot.sound]`. |
| HLJContraction | 36.420 | PASS. `finish_strict`, `checkedFinish_realize`: standard three axioms; `problem_wellFormed`: `[propext, Quot.sound]`. |
| StructuralLemmaCuts | 36.913 | PASS. Remainder, length, refill, degree, aligned-provider equality and checked-fill realization: `[propext, Quot.sound]`; hole/cut equivalences add `Classical.choice`. |
| HLJStructuralApplication | 40.698 | PASS. All ten printed headline closures are `[propext, Classical.choice, Quot.sound]`. |

All accepted closures come from successful FINAL-source checks. None contains
`sorryAx` or a custom axiom. Benign unused-variable/simp-style warnings remain.
Earlier checks, each followed by a concrete relevant source fix, took:
HLJStructural 80.253/36.797/35.840 s; HLJContraction 36.418/36.877/36.543 s;
StructuralLemmaCuts 39.340/37.036/36.444/36.290/36.729 s; application 53.921 s.
They repaired installed lemma names, dependent inference/elimination, indexed
list sums and quotation metadata. Their placeholder closures are NOT evidence.

The independent reviewer confirmed the actual antecedent-repartition rule,
passive context, indexed EC incidence, strict/envelope distinction, proper-root
frontier, full physical multiplicity, aligned-provider identity and restricted
cost claims. Review specifically caught the need to keep the two donor front
ends separate and to distinguish signed contextual extraction from checked
exterior correctness. Review was read-only, with no additional Lean commands.

## 15 October 2026 continuation: one costed output, one CK certificate

Historical checkpoint: the blocked-example status below is superseded by the
completed local-pruning and two-Plan comparison continuation at the end of this
report. Its successful general integration results remain available dependencies.

### Main result: MECHANIZED

The central integration obligation from the attached assessment is now closed.
At unchanged HEAD `2835d448722e6e366c26003004b19b631984691b`, two additive modules
have successfully checked:

- `ContractionDonorFilling.lean`: for every native supplied rule interface,
  arbitrary arity n, admissible Plan and original donor family, construct a
  donor index at EACH PHYSICAL scaffold hole, with an exact boundary equality,
  and prove literal native filling equals the existing indexed compiler output.
- `HLJDonorIntegration.lean`: instantiate that bridge on the strict binary
  Communication compiler. The SAME checked realization now has the Plan cost,
  Q recurrence, native proper frontier, exact original-provider matching,
  reconstruction and installed-cut classification.

`Labels` is just a function on the existing `LeafOccurrence`, valued in a
subtype of `Fin n` recording the matching whole boundary. It is not another
proof, cut, context or forest. Stopping at i records i; ordered family assembly
preserves that history; EW and EC transport it through unary native nodes.
No index is inferred from an equal-looking sequent or a collected coefficient.
The index function need not be injective; no bijection is assumed.

The headline equation `ContractionDonorFilling.RuleInterface.finish_fill` is

```text
plug (r.finish (Box at donor boundary i) plan) (finishLabels r plan) donors
  = r.finish donors plan.
```

Here `plug` is merely native `fillAssignment` using the recorded boundary
casts. All rule instances on both sides are those of the SAME r. The theorem
is equality of fully decorated native trees, not permutation equality,
multiset equality, equal cardinality or existence of an unrelated derivation.
Different donor indices can have identical boundaries; the universal theorem
still uses the recorded index. Physical repetitions remain separate holes.

### Checked and CK consequences

The checked client fixes one strict registry P and checked donors in P.
It assumes exact registration of the original completed output. It DOES NOT
need a second independently supplied registration hypothesis for the scaffold:
`admitted_scaffold` reflects registration through native filling.

`checked_frontends_agree` proves literal equality of the two checked native
realizations. No stronger equality of the checked wrapper proof objects is
claimed or needed. `compiled_certificate` then supplies, for that very output:

1. A proper native CK cut with literal scaffold remainder.
2. Full physical site multiplicity and native detached-family refill.
3. The existing exact Plan degree formula.
4. The existing Q formula in EVERY commutative semiring.

These are transferred through the filling equation, not separately evaluated
on two candidate outputs. `compiledFrontier` returns the actual existing
native `CKCut`, whose address-aligned detached tuple is available before
forest collection. `original_provider_matching` transfers exact equality of
the entire native detached provider with the history-selected donor provider.
`compiledExtractionEquiv` reuses the installed-cut bijection for all native
root-excluding cut plans of this same proof, including donor-interior choices.

Empty cuts are retained. Global whole selection is not a public root cut;
the separately represented whole branch remains included in the existing
full-branch Q observation. No commutative forest is described as ordered.
Premise order, physical addresses and tuple matching precede collection.
External EC contracts hypersequent components, not physical proof-tree copies.

The generic native theorem alone asserts no global discharge legality for
arbitrary owner-decorated payloads. The checked application remains in the
identity/Com/EW/EC fragment, with the earlier side conditions unchanged.
The old signed K law applies to this now-identified output; no coproduct
invariance, positive defect, material-relative fidelity or logical-Cut
elimination is inferred.

### Registered demonstration

`HLJPostponementExample.lean` implements the canonical existing compiler with
m=(1,2), q=2, D0 the A-identity and D1 the B-identity followed by EW, and Plan
`next(stop0, next(stop0, stop1))`. It uses one fixed ten-entry exact registry,
including genuine EW, Com and terminal EC. Components are obtained symbolically
from the actual H.toList; the construction does not evaluate Classical.choice
or impose a new hypersequent ordering. A and B must be distinct for this
particular reached-stock key classifier. No general allocator is being built.

**BLOCKED / NOT MECHANIZED as a complete demonstration.** Its proposed degree
11, full physical cut count 43 and checked transferred frontier are NOT accepted
final-source results. The universal bridge above has successful final axiom
closures independently of this file; neither verified module imports the example.

The first exact remaining gate is `HLJPostponementExample.output_registered`,
at the rewrite of `problem.terminalComponents` inside native `contractList`.
Its support proof and input-tree boundary depend on that same list. A direct
rewrite constructs an ill-typed motive: the old support proof is for
`problem.terminalComponents.toList`, not an arbitrary replacement list. Earlier
simplification attempts did not rewrite this dependent application. An explicit
dependent transport/congruence lemma is needed here; equality of the displayed
multisets does not by itself discharge this Lean goal.

The other residual goals are in `output_degree` and `output_Q`: rewrites of
the donor observations fail to match their occurrences after the Plan sum/product
reductions, despite the abbreviated pretty-printer showing identical expressions.
The separately established donor lemmas do not close these target substitutions
automatically. Their remaining expressions are respectively

```text
1 + (degree D0 + 2 + (1 + (degree D0 + 1 + degree D1))) = 9
```

and the corresponding nested Q expression. This is a concrete elaboration gate,
not a counterexample to the stated mathematics. No admission hypothesis was
invented to bypass it. The fixed presentation and source are retained uncommitted
for repair; the example is NOT a dependency of the accepted general result.

### Verification record

Only new-module targeted checks, using the earlier authorized monitored
300-second bound, were run. Commands use the same pinned Lean/LEAN_PATH as
the previous section:

```powershell
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/ContractionDonorFilling.olean Potkin/Research/ContractionDonorFilling.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJDonorIntegration.olean Potkin/Research/HLJDonorIntegration.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJPostponementExample.olean Potkin/Research/HLJPostponementExample.lean
```

The general bridge passed in 52.244 s. Its family law uses `[propext, Quot.sound]`;
weakening, interpretation, finish filling and donor-boundary closure use only
`[propext, Classical.choice, Quot.sound]`. The final integrated source passed
in 66.333 s; all seven printed headline closures are exactly those standard
three axioms. No accepted closure contains `sorryAx` or a custom axiom.

An initial partial-source check timed out at 301.837 s before diagnostics;
the actual child was terminated (last CPU44.4 s, RSS886.2 MiB). One stdin-only
diagnostic importing ContractionPostponement and AllHoleFilling passed in
36.651 s. Thus the imports were available; the exact transient wall-time cause
was not established. After completion of the source, a 49.690 s check exposed
local subtype/transport errors; those were fixed before the successful run.
The integration's earlier 48.197 s pass preceded the added exact-provider and
cut-classification transfers. The example had seven relevant-fix checks, all
unsuccessful: 74.885, 50.382, 171.602, 88.522, 51.058, 274.756 and 51.745 s.
The 274.756 s invocation was monitored throughout: it accumulated only about
16 seconds CPU in its first 210 seconds, then entered substantially heavier
computation, returned source diagnostics and exited before the 300-second bound.
It was not a timeout and was not classified as a mathematical failure.
The final attempt exposed the ill-typed dependent rewrite above. We stopped
rather than continuing a simplification/check loop. A collaborator's last
semicolon-only tactic edit raced that invocation; therefore no final-source
success is claimed for the example regardless of its diagnostics.

Failed/example checks and their `sorryAx` placeholder closures are NOT evidence.
The source contains no written `sorry`, `admit` or custom axiom in the three new
modules, but that source-text observation does NOT validate an unsuccessful
elaboration. Only the two successful module checks support the MECHANIZED claims.
Targeted documentation `git diff --check` passed, apart from Git's informational
LF-to-CRLF notices. No full build, suite, native cut enumeration,
benchmark, dependency installation, source-grouping restart or new algebra
hierarchy was undertaken. Everything remains uncommitted.

One collaborator independently reviewed the general labels and integration,
confirming construction-history identity, strict shared provenance and the
remaining admission/global-discharge limits, and separately contributed the
fixed example. The main agent integrated and checked it; this is not represented
as independent review of that collaborator's own example. The independent review
found no mathematical scope objection to the general theorem. It specifically
retained reached registration, owner-copy discharge legality, coefficientwise
or tensor conservation, full logical normalization and general allocation as
limits. Algebraic K transport alone is not a checked logical replacement theorem.

### Research meaning and remaining scope

The result is now ONE checked, quantitatively specified structural compilation
with ONE physical CK decomposition, rather than two unconnected presentations.
That is the right unit for a CK-resolved refinement of contraction postponement.
Its potential use is to retain an admitted structural scaffold while replacing
opaque lemma interiors, accounting for expansion cost and the resulting
extraction families, including changes propagated through enclosing contexts.
It is not yet a fast incremental tool: the optimal Plan selector and general
registry allocator remain non-executable/absent refinements respectively.

The immediate remaining obligation is the dependent finite-example proof above,
not another research framework. The next substantive question AFTER that fixed
demonstration is complete is
comparison of CK observations of competing admissible postponement choices.
One must prove a suitably restricted dominance theorem or exhibit a genuine
counterexample; equal node costs or equal Q cannot identify typed remainders.
We have not claimed such a comparison here, nor literature novelty, a new
normalization existence theorem, full HLJ normalization, analytic-calculus
extraction or a process-calculus application. The direct advance is D2/D4,
with a precise D5 reuse boundary; D1/D3/D6 remain as stated above.

## 15 October 2026 continuation: local pruning and two-Plan comparison

### Target and baseline

HEAD remains `2835d448722e6e366c26003004b19b631984691b`, on `main`.
The target is a checked quantitative comparison of actual structural compiler
choices, retaining native CK decomposition and the original donor assignment.
The existing general filling, installed-cut, gluing, affine-Q and signed-K laws
are dependencies, not new claims of this continuation.

The normalization baseline is Ciabattoni–Genco, [*Hypersequents and Systems of
Rules: Embeddings and Applications*, §4.2.1, Lemmas 4.6–4.8](https://arxiv.org/html/1805.04852v1).
They establish the structural transformations used by the construction. Our
increment is the specified construction's quantitative/native CK analysis, not
a new normalization-existence theorem, full HLJ normalization or logical-Cut
elimination. Literature novelty of the new comparison is UNASSESSED.

### MECHANIZED: a restricted local pruning theorem

`ContractionPlanComparison.lean` passed a targeted final check in 65.368 s.
It imports existing compiler/physical-cut observations and does not import the
example. The new result is universally quantified, not inferred from a finite
list of derivations or evaluations of z.

Fix a native binary rule interface over p with `p.H.components.card = 2`, a
state alpha, an eligible donor i (`p.m i ≤ alpha i`) and remaining depth
(`mass alpha < quota p.m`). Compare stopping at i with continuing ONCE and
then stopping at that SAME i in BOTH ordered premises. Native Communication
has exactly this arity/output-component convention. Arbitrary child donor
choices are explicitly outside the theorem.

Writing w for `p.stopWeight alpha i`, constructor arithmetic proves w≥2 and
the two child weights equal w−1. For every native donor family:

```text
N_delayed + 1 = 2 N_stop,       N_stop < N_delayed.
```

For every commutative semiring, put U=Q_z(D_i)+(w−1)z. `local_Q` proves

```text
Q_stop = U + z,                Q_delayed = U*U + z.
```

For natural z, `local_Q_defect` proves the NONNEGATIVE scalar defect

```text
Q_delayed = Q_stop + U*(U−1).
```

`Q_ge_one` is proved by native constructor recursion (the empty choice is
retained); it is not a finite test. At z=1, U≥2 and `local_total_strict` gives
strict growth of the full physical cut count. At z=0 the defect can vanish.
No coefficientwise polynomial or tensor order is inferred from natural-valued
pointwise inequalities.

`contextual_Q_LE` REUSES the existing affine law. Its checked corollary
`checked_context_Q_LE` requires actual source and target filled derivations
checked in the SAME P, and literal realization equalities with the native
typed insertions. It does not infer logical correctness from equal displayed
sequents or from a signed K identity. This yields a local pruning certificate
inside such checked exteriors, not global first-hit optimality.

### Repair of the concrete application

The old ill-typed dependent rewrite is removed. Private admission predicates
on the existing EW/EC scripts and Plan expose exactly the reached instances.
Their constructor lemmas quantify over the dependent support/input arguments
instead of rewriting them. The finite proof then establishes each complete
native descriptor's registry key and membership explicitly. These predicates
are proof obligations, not a replacement proof/cut/forest/context carrier.

For degree and Q, equality of the ENTIRE donor-observation function is
transported through the existing recurrence BEFORE reducing dependent Plan
branches. This avoids matching apparently identical abbreviated trees after
their hidden index transports have been normalized differently.

The first application remains m=(1,2), q=2, donor D0 the A-identity, donor D1
the B-identity followed by EW, A≠B. The second Plan delays the eligible left
stop by one Communication and then stops at D0 in both new premises:

```text
early:   next(stop0, next(stop0, stop1))
delayed: next(next(stop0, stop0), next(stop0, stop1)).
```

Both use the same donors and the same reached rule-instance convention. The
ten original registry entries remain unchanged. The classifier is refined on
the newly reached cases: Com with common context {C0} gets ID10 rather than
aliasing Com({C1}) at ID7; EW(C0,C0) gets ID11 rather than aliasing EW(C0,C1)
at ID3. `commonPresentation` appends these two genuine admitted descriptors.
`registry_inclusion` is explicit, and `commonDonors`/`checkedPlan` explicitly
re-quote/recheck in the common twelve-entry registry. No old checked proof is
silently cast into that snapshot; no general allocator is claimed.

**Concrete application: MECHANIZED.** The final unchanged source passed in
76.834 s, exit 0. Both distinct Plans are checked in the same common registry:

| Plan | Native vertices | Full physical CK cuts |
|---|---:|---:|
| Early | 11 | 43 |
| One delayed stop | 13 | 103 |

`output_registered` also establishes the early output's admission in the
original ten-entry registry. `checkedPlan_realize` and `checked_comparison`
attach the comparison to literal checked realizations in the common twelve-entry
registry. The cut counts are native cardinality theorems derived from the
universal recurrence, not enumerated test observations. D0 occurs physically
twice versus three times; D1 occurs once in each output.

### Symbolic comparison and physical interpretation

The source now states native symbolic formulas for arbitrary same-boundary
donors, not just the fixed identities. With d_i=degree(D_i):

```text
N_early   = 2*d0 + d1 + 7
N_delayed = 3*d0 + d1 + 8.
```

For X=Q_z(D0), Y=Q_z(D1), V=z+(X+z)Y, the two existing recurrences give

```text
Q_early   = z + (X+2z)*V + 2z
Q_delayed = z + (z+(X+z)*(X+z))*V + 2z.
```

`paired_Q_LE` applies the NEW local pruning criterion at the actual eligible
left state, then monotonic multiplication by the unchanged right sibling's
observation. It does not assume the desired Q inequality. Its domain is all
same-boundary native donor families and all natural z. The checked fixture and
its exterior corollary are separate admission-bearing applications of it.

Q is the already verified finite sum over physical `CKBranchCut` witnesses,
weighted by the number of ordered detached factors. It includes the empty cut
and the separately represented whole endpoint. A whole endpoint is never
fabricated as a public nonroot cut. Each Plan retains its own proper frontier,
typed scaffold remainder, original-provider matching and native refill through
`plan_frontier`, `plan_provider_matching` and the existing installed-cut
classification exposed by `plan_extraction`. The early/late frontiers have
different donor multiplicities; they are not equated. A logical donor index,
registry descriptor ID and physical application address remain different data.

No source-target tensor equality, equality of remainders, independent copying
of nonlocal discharge certificates, material-relative fidelity or antipode
result is asserted. Cancellation of scalar whole weights does not identify
the distinct native whole tensors.

### Use, review and remaining scope

A transformer may reject this precisely specified redundant continuation
without worsening its node cost or full-cut budget, and may carry that scalar
comparison into exteriors with separately checked native fillings. The CK
observation measures decomposition/interface workload and opportunities, not
execution time or universal proof quality. Extra cuts can also offer useful
reuse interfaces. No runtime speedup has been measured.

One independent reviewer found the local mathematics sound and emphasized:
same donor in both children; two output components counting multiplicity;
explicit common-registry admission and re-quotation; no global first-hit,
coefficientwise or tensor claim; and nonnegative versus strictly positive
defect. The concrete inequality now invokes the general criterion explicitly,
rather than independently reproving its square inequality. Final independent
source review found no remaining mathematical scope objection, including the
formal dependency of the application on the general comparison and the matching
native certificates. The review is source/mathematical review, not a substitute
for the successful Lean verification recorded below.

This advances D2 (nonlinear compilation choice), with D4's physical
decomposition support and a guarded D5 contextual comparison. D1's relative
logical-Cut bridge, D3's uniform-weakening metatheorem and D6 conservativity
remain separate obligations. There is no new counterexample claimed here;
the result is a sufficient criterion, not an assertion that arbitrary early
stopping always wins.

### Targeted verification record for this continuation

Only the two changed modules were checked. Direct commands (the pinned
executable and LEAN_PATH are the same as above):

```powershell
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/ContractionPlanComparison.olean Potkin/Research/ContractionPlanComparison.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJPostponementExample.olean Potkin/Research/HLJPostponementExample.lean
```

Each invocation uses the authorized actual-child 300-second bound, asynchronous
stdout/stderr draining, CPU/memory progress checkpoints and child termination
at the bound. Source SHA256 is compared before/after each run to exclude edit
races. The comparison module's final 65.368 s pass has closures exactly
`[propext, Classical.choice, Quot.sound]` for `delayed_nodes`, `local_Q`,
`local_Q_defect`, `local_total_strict` and `checked_context_Q_LE`.
Earlier relevant-fix comparison checks failed in 89.866 and 65.784 s.
Example repair checks failed in 248.281, 86.839, 85.640 and 102.927 s;
their placeholder axiom closures are NOT accepted evidence. Relevant fixes
addressed dependent script arguments, exact descriptor keys, explicit whole
provider transport, multiset exchange and the comparison's formal dependency.
The final application check PASSED in 76.834 s, exit 0, with unchanged source
SHA256 `54E00EFBC1E0612E2F51926149340D7D600EB9B570D2DCD1DEEADEE7476CCE91`.
Its final printed closures are exactly `[propext, Classical.choice, Quot.sound]`
for `checkedOutput_realize`, `output_degree`, `output_Q`,
`output_native_cut_count`, `output_frontier`, `output_registered`,
`paired_Q_LE`, `checked_comparison`, `checked_exterior_comparison`,
`plan_frontier`, `plan_provider_matching` and `plan_extraction`.
There is no `sorryAx` or custom axiom in these closures. The successful commands
still emit non-blocking unused-argument/variable and tactic-style warnings.
No declaration or proof changed after these final checks; the comparison
module's comment was subsequently clarified from positive to nonnegative.
No full build, test campaign, dependency installation, commit or push was
performed. Unrelated changes are preserved.

## 15 October 2026 continuation: whole-Plan certified pruning

HEAD remains `2835d448722e6e366c26003004b19b631984691b`, on `main`.
This continuation adds only `ContractionPlanPruning.lean`, `HLJPlanPruning.lean`
and `HLJPlanPruningExamples.lean`, plus in-place report/ledger updates. Earlier
uncommitted work, policy and unrelated sources are preserved.

### Universal theorem and executable strategy

`ContractionPlanPruning.prune` is an executable structural recursion on the
EXISTING binary indexed `Plan`. It first prunes both ordered children, then
collapses precisely a same-original-donor pair of stops when that donor is
already eligible at the parent. Actual donor indices and natural thresholds
are compared; proof terms are not compared. No proof/cut/forest/context carrier
is added, and donor interiors are opaque.

For arbitrary multiplicities m, state alpha and Plan at alpha:

- `prune_path` proves a literal finite sequence of positional atomic rewrites.
  `Step` is exactly the eligible local rewrite closed under one existing Plan
  position; `Path` is its finite sequence. `linearize` serializes the finite
  contextual derivation, processing the first premise before the second.
- `prune_normal` proves no occurrence of THIS redex remains, including parent
  redexes exposed by child pruning. `prune_idempotent` and
  `prune_eq_iff_normal` prove fixed-point behavior. Confluence and uniqueness
  across other strategies are not claimed.
- The result has the SAME indexed state/problem and thus the same whole native
  boundary. Termination is structural totality of the executable definition,
  not a bounded search or repeated testing of depths.

For every native binary rule interface with two output components, arbitrary
same-boundary donor family and every natural z, `finish_comparison` proves

```text
degree(finish(prune p)) <= degree(finish p)
Q_z(finish(prune p))    <= Q_z(finish p).
```

If pruning changes p, both inequalities are STRICT for nodes and Q at z=1.
Equivalently an input that is not Normal has strict decrease; the checked
corollary is `HLJPlanPruning.checked_strict_of_not_normal`. Local inequalities
are REUSED from `ContractionPlanComparison`. Node sums and natural products
lift them through arbitrary Plan positions; strict multiplication uses the
proved sibling bound Q>=1. Fixed terminal EC costs are then added to both sides.
No conclusion is inferred from numerical fixtures.

Plan-control size, compiled vertices and physical cut weights are distinct.
Q is still the existing finite sum over full native `CKBranchCut` witnesses,
weighted by detached-factor number. It retains the empty contribution and the
separate witness-free whole endpoint. Its scalar projection does not replace
the coproduct or identify a typed Box with a forest coefficient unit. No cut
injection, coefficientwise comparison, tensor positivity, equality of typed
remainders, or runtime superiority is proved.

### Exact admission: a finite sufficient closure, not a hidden conclusion

`HLJPlanPruning.StopStock` is indexed by the INPUT Plan. At each original
continued position it requests exact membership of the EW-only stop scaffold
for each parent-eligible donor. It recurses over the finite original control
tree; original stops require nothing additional. It is conservative, not a
claim of the smallest or necessary stock. Native vacant interfaces expose EW
descriptors here; they are not accepted as proof evidence.

`finish_prune_members` proves this closure plus source membership and donor
membership entails optimized-output membership. Its proof retains all surviving
Com descriptors at their original states and the identical terminal EC queue;
only new stop EW scripts need the extra closure. `optimized_registered` and
`optimized_realize` then re-use the public quotation/checker in ONE supplied
immutable strict presentation. They do not assume membership of the desired
whole optimized tree.

Strict HLJ schema correctness is separate: `optimized_strict` reuses the
existing `finish_strict`, with its valid shared hypersequent and admitted-donor
hypotheses. Source membership alone does not ensure the EW closure. The old
delayed example needs EW descriptors different from its pruned output's EW
descriptors. Moreover finite new stock need not fit an arbitrary existing key
map without collisions. No automatic compatible extension or fresh allocator
is asserted. Registry keys, original donor indices and physical addresses
remain distinct, with no snapshot cast.

### One optimized checked output, its own native CK certificate

`optimized` is the strict checked compiler on the pruned Plan, with membership
DERIVED from the preceding closure theorem. `checked_comparison` attaches the
universal quantitative guarantees to its literal native realization.
`optimized_frontier`, `optimized_provider_matching` and `optimized_extraction`
reuse `HLJDonorIntegration` unchanged: proper root-excluding physical frontier,
ordered factor/hole alignment, original history-selected donors, literal typed
scaffold remainder, refill, and installed-cut classification including cuts
inside donors. These concern that SAME optimized checked output. The proper
cut-plan classification and full branch-cut type counted by Q are not conflated.
Old/new frontier multiplicities and remainders need not agree.

`checked_exterior_Q` uses the existing affine law but requires BOTH actual
typed exterior fillings checked in the same P, with literal insertion
equalities. An algebraic K identity is not used as exterior admission evidence.
No material/profile preservation or independent nonlocal-certificate copying
is claimed.

### Applications and independent review

`prune_uniform` identifies the previous delayed Plan with the early Plan after
whole-Plan pruning. The same actual twelve-entry Communication/EW/EC registry
is reused. Its sufficient EW stock is certified by projecting the one required
script from the INDEPENDENTLY VERIFIED earlier registered output; it is not
proved using the optimizer's desired conclusion. `fixture_comparison` applies
the general checked optimizer theorem, and `fixture_numbers` recovers 13/103
to 11/43 (vertices/full physical CK cuts).

`nestedPlan` has m=(1,3), alpha=(1,0). Initially neither child is a stop, so
the parent is not a redex. Pruning the two children exposes and removes the
parent redex. This is a typed executable PLAN-CONTROL illustration, not an
additional registered whole hypersequent fixture. Four `#eval` observations
show control sizes, not proof-node/cut counts. The universal proofs establish
normalization and its semantic guarantees, not these finite observations.

One independent reviewer read the final sources without editing or execution.
They challenged parent eligibility, shared donor identity, state transports,
strictness and key collisions; requested explicit sequential linearization;
and found no remaining mathematical scope objection after that addition. They
confirmed that the fixture stock proof is noncircular and that closure remains
an explicit sufficient condition.

This is a direct D2 structural-compiler optimization advance. D4's decorated
physical CK decomposition measures decomposition budgets/opportunities and
supplies the optimized certificate; analytic-calculus extraction remains OPEN.
D5 has the scoped checked-exterior comparison, not a runtime-cache theorem.
D1 relative logical Cut, D3 uniform weakening and D6 conservativity remain
separate. The earlier Ciabattoni–Genco normalization baseline is unchanged;
literature novelty is UNASSESSED. Fewer cuts are not universal proof quality:
additional cuts can also supply useful reuse interfaces.

### Verification of this continuation

Only the three additive modules and one dependency-resolution diagnostic are
in scope. Direct checks use the pinned Lean 4.29.0-rc1 executable, the existing
local/library-package `LEAN_PATH`, async output draining, a 300-second actual
child bound, CPU/memory progress and source SHA256 checks. No full build,
Racket, enumeration campaign, dependency install, commit or push is performed.

```powershell
$ckLean = 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe'
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/ContractionPlanPruning.olean Potkin/Research/ContractionPlanPruning.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJPlanPruning.olean Potkin/Research/HLJPlanPruning.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJPlanPruningExamples.olean Potkin/Research/HLJPlanPruningExamples.lean
```

The initial check timed out at 300.771 s before any Lean diagnostic and its
child was terminated; CPU/memory showed work but the exact internal phase was
not emitted. The targeted `--deps` diagnostic resolved Init and the existing
comparison import in 0.377 s. Subsequent revised sources and streamed-output
checks exposed concrete errors, fixed locally: generated `below` name collision,
over-aggressive simplification, omitted section hypotheses, and a dependent
match rewrite. Failed checks 92.986 and 44.183 s are NOT accepted evidence.

`ContractionPlanPruning` final PASS: 83.642 s, exit 0, unchanged source hash
`9047C84CE20D6826F634F0382E59F3F7D84A069F5FA734E91EB25AB401D71237`.
Headline closures for `prune_normal`, `prune_idempotent`, `prune_path`,
`history_nodes`, `history_total`, `finish_comparison` contain exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or custom axiom.
`HLJPlanPruning` final PASS: 47.109 s, exit 0, unchanged source hash
`FDD2BBC9EDC1730F580AF8F4AC16D546F75E876BBE255618C76817FF98CEE0F5`.
Its closures are exactly `[propext, Classical.choice, Quot.sound]` for
`finish_prune_members`, `optimized_registered`, `optimized_realize`,
`checked_comparison`, `checked_exterior_Q`, `checked_strict_of_not_normal`,
`optimized_frontier`, `optimized_provider_matching`, `optimized_extraction`
and `optimized_strict`. Unused section-variable warnings are non-blocking.
Earlier relevant-fix checks failed in 52.116, 88.004 and 60.341 s (looping
simplification removed, notation capture avoided, proof-only hypotheses exposed
and explicit arguments supplied). These failed closures are not evidence.
`HLJPlanPruningExamples` final PASS: 58.409 s, exit 0, unchanged source hash
`16046CD0082779069CE3F9B97DA1715CB7F52E3BF8E0599E1FD75BAC658CC13E`.
The four executed control-size observations are respectively 7, 5, 7, 1.
Final closures for `prune_uniform`, `prune_nested`, `fixture_stock`,
`checkedPruned_realize`, `fixture_comparison`, `fixture_numbers` and
`fixture_frontier` are exactly `[propext, Classical.choice, Quot.sound]`.
There is no accepted `sorryAx`, custom axiom or unresolved placeholder.
Earlier example checks failed in 45.084, 43.809 and 95.192 s; fixes were confined
to explicit dependent constructor exposure, notation removal, whole-function
transport and reducing the problem's multiplicity projection before `decide`.
Those unsuccessful checks' closures are not accepted evidence.

No Lean declaration/proof changed after its module's final successful check.
Independent review was static and did not launch extra checks. Final handoff
uses only scoped source/status/whitespace inspection, not another verification
run. All work remains uncommitted.

| Status | Delivered scope |
|---|---|
| MECHANIZED | Universal finite rewrite path, redex-freeness, idempotence, same indexed boundary, quantitative guarantees and strictness; strict checked HLJ application and its native CK certificates; checked fixture recovered through the optimizer. |
| EXECUTABLE | Bottom-up Plan normalizer and the two Plan-control demonstrations; quotation and existing multiset-script selection remain noncomputable infrastructure. |
| CONDITIONAL | General exact finite-registry use requires source membership and the sufficient reached EW `StopStock`; checked exteriors require both actual admitted fillings. The concrete common-registry fixture discharges its stock condition. |
| OPEN | General fresh allocator; broader rewrites/different-child comparisons; global proof optimality, confluence, coefficientwise/tensor comparison, unchanged remainders and runtime improvement. |

## 15 October 2026: prepared Sys(com) translation and localized CK reuse

### Result, provenance and exact scope

This continuation applies the native CK machinery to the actual prepared
LJ+Sys(com)-to-HLJ+com construction, rather than another abstract derivative
identity. Starting HEAD is `2835d448722e6e366c26003004b19b631984691b`, branch
`main`. Previous uncommitted D3, contraction/compiler and documentation changes
are retained. No branch, commit or push is made.

The class is one nontrivial nested two-system shape, parametric in arbitrary
source formulas A,B,C. Its concrete donor interpretation uses identity and
internal weakening (IW). It is **not** a compiler for all prepared LJ+Sys(com),
nor a preparation normalizer. The independent source-correctness theorem is
broader than this donor interpretation: it admits complete, locally correct,
system-event-free source donors, but translating broader donors still requires
their actual target interpretation/admission. Fixed-boundary identity/IW donors
here have four weakenings, not unbounded lengths.

The paper antecedent is Ciabattoni–Genco, [§4.1](https://arxiv.org/html/1805.04852v1#S4.SS1):
prepared top-application combinations, copied translated premises, and bottom
contractions are theirs. The new application supplies physical copy maps,
checked passive-context matches, native CK installation and localized
retranslation for the specified class. Existing generic substitution, gluing,
flag and K laws are dependencies, not rediscoveries. No priority claim over an
exhaustive literature search is made; new abstract Hopf algebra is not a
prerequisite for the value of this structural-proof-theoretic application.

### Focused literature comparison

[Calaque–Ebrahimi-Fard–Manchon, *Two interacting Hopf algebras of trees*](https://arxiv.org/pdf/0806.2238),
§9.2, Theorem 8, equation (21), establishes compatibility of a subtree-contraction
coaction with the CK coproduct; its B-series applications include composition
and substitution. That abstract compatibility is an antecedent, not our new
identity. Contraction to a vertex in commutative nonplanar forests does not by
itself instantiate typed Boxes, system discharge, physical copy origins or
exact proof-registry admission. Our addition is the actual structural
translation's checked interpretation and reconstruction/reuse consequence.

[Wenzel, *Interaction with Formal Mathematical Documents in Isabelle/PIDE*](https://arxiv.org/html/1905.01735v1),
§1.2 and §§2–2.1, describes old-version result caching and dependency-aware
document updates. Reusing unchanged checked material is therefore not new by
itself. A competent zipper/DAG cache is a serious baseline. The increment here
is the actual translation's source-to-physical-use map together with CK
extraction classification and typed residuals. Neither this focused comparison
nor the implementation establishes a performance advantage or exhaustive
priority. Faà di Bruno/substitution terminology is not substituted for a new
structural-proof-theoretic consequence.

### Actual source and target, before any scalar observation

Both system instances share Phi={A}, Psi={B}, but have distinct owner IDs X=0,
Y=1. Put L = A²B²C ⇒ A. The donor boundaries are
a : A⁴C ⇒ A, b : A²B²C ⇒ A, c : AB³C ⇒ A.

The source is X-bottom(Y-bottom(Y-top0(X-top0a(a)),
Y-top1(X-top0b(b))), X-top1(c)). Source top addresses are [0,0,0],
[0,1,0], [1] for X and [0,0], [0,1] for Y; bottom addresses are [] and [0].
The source module proves local correctness, completeness, genuine branch and
parameter discharge, same-instance top antichains and disentanglement
independently of target checking. Neither bottom is dummy. Root-prefix
ancestry is explicitly distinguished from the paper's leaf-to-root orientation.

The union of all five top applications is **not** one CK antichain: a Y top
lies on the path to an X top. Preparation supplies the appropriate
same-instance/phase frontiers, not a global top-rule cut. The distinguished
three-site source CK frontier selects the ordinary donor roots below those
applications. `PreparedSysComSourceFrontier.plug_source`, `scaffold_addresses`,
`source_frontier` and `source_provider_matching` verify its actual encoding,
ordered addresses [0,0,0,0], [0,1,0,0], [1,0], matching and refill.

Write Va=A³BC⇒A and Vb=AB³C⇒A. X's Cartesian occurrence choices are (a,c)
and (b,c). Their two genuine Communication outputs are Va|L and Vb|L. Y uses
the **same passive L** in its ordered premises and concludes L|L|L. Its EC
contracts 3L to 2L; X's EC then contracts 2L to L. Thus

    T(a,b,c) = EC_X(EC_Y(Com_Y[{L}](Com_Xa(a,c), Com_Xb(b,c)))).

`phaseA`, `phaseB`, `join`, `translate` express these checked-boundary stages.
`HLJInternalWeakening` adds a strict genuine IW schema because the old target
stock had only identity/Com/EW/EC. It extends instance data/admission, not the
native proof, forest, cut, Box or context carrier. Old descriptors retain their
whole shapes and supplied component incidence. IW validates entire passive
hypersequents and single succedents; it does not claim formula-occurrence
resource action from component incidence.

### Paper theorem and proof

For this prepared shape, let a,b,c and replacement donors have their exact
boundaries and be complete. Require every quoted target filler and scaffold
occurrence to belong to one exact admitting registry P. For the actual source
application, additionally require its stated source constructors/translation
relation; boundary coincidence alone is not a source translation.

1. There is a native open target M with ordered physical donor origins
   [a,c,b,c]. Its interfaces occur at [0,0,0,0], [0,0,0,1], [0,0,1,0],
   [0,0,1,1]. These are native internal zero-based premise addresses.
2. Filling M by that origin-indexed family is literally T. Its proper native
   donor frontier retains the ordered detached providers, the exact typed
   remainder M, and native refill. The source has three donor occurrences;
   the target has four uses, not a bijective source/target frontier.
3. Every further nonroot target cut is classified by the existing installed
   outer/inner cut choices. Donor-internal cuts, independent cuts in the two
   c copies, and ancestor cuts swallowing one or both changed copies are
   included. The empty cut is retained; the global whole endpoint is separate.
4. If source origins J change, target dirty uses are the inverse image of J
   under kappa=[0,2,1,2]. Refreshing only those providers, retaining the other
   cached native pieces, reconstructs exactly the full retranslation. With
   checked fillers and explicit scaffold registration, the same statement
   holds for the public native checker in the unchanged P.

Proof: establish the source events and preparation directly. The two X choice
pairs give the displayed target premise boundaries; the exact Y instance and
the two distinct EC stages give its conclusion. Apply native simultaneous
filling to this scaffold. Its interface/frontier adapter supplies the cut,
matching and literal reconstruction, before collection. The installed-cut
equivalence classifies all target extractions, not merely this frontier.
Finally recover cached providers by the proved uncollected adapter, pull the
changed-origin predicate back along native labels, and use filling congruence.
The checker realization theorem gives checked reconstruction once admission is
supplied. No fixture evaluation is a step in this proof.

Payload replacement is correlated across copied uses; **cut choices are not**.
The two identical c trees may have different physical cuts. Forcing those
choices to agree would lose terms and multiplicity. A one-copy-only update may
still be a valid target proof, but is not a coordinated retranslation of one
source c. Forest product packages independent factors; it is not either Com
grafting or external Mix.

The ordered addressed providers are retained until the explicit
`Multiset.ofList` projection in `translated_origin_observation`. That projection
is the commutative native forest observation, not a full ordered/Foissy forest
algebra or an attempt to recover order from collected coefficients.

In particular the **paper-level** extraction-sum consequence is
Delta_nonroot(T) = sum over installed choices chi of P_chi tensor R_chi,
with the separately added T tensor 1 whole endpoint. The mechanized bijection
and `translated_origin_observation` justify the index correspondence and each
decorated forest/remainder summand. This continuation does not claim a new
linearized tensor identity or that the source coproduct maps unchanged to the
target. Ancestor-swallowing and donor-internal terms are the correction data.

### Dependency and increment table

| Existing dependency | Application-specific addition |
|---|---|
| D3 source grammar, independent grouping/correctness and encoding | Genuine nested prepared X/Y class, actual discharge events and preparation proofs |
| Strict HLJ identity/Com/EW/EC stock | Additive exact IW admission; same-snapshot finite stock for all translated pieces |
| Native physical donor labels and simultaneous filling | Actual Cartesian choice pullback [a,c,b,c], not a boundary-inferred map |
| Native frontier/refill and installed-cut equivalence | This translation's literal typed remainder, physical providers, all-cut classification |
| Scoped replacement and native checking | Cached-piece update equals full retranslation; actual checked example in one registry |
| Constructor Q observation and native finite-sum interpretation | Translation-specific nonlinear projection, including ancestor terms; no cut enumeration |
| Existing gluing/flag/K laws | Available dependencies; no new claim of coproduct invariance or K-based runtime implementation |

POTKIN Racket's `base-replacement-cut.rkt`, `material-context-transport.rkt`, and
`coloured-cut-query.rkt` were consulted statically only: **SOURCE-PRESENT / NOT
RECHECKED**. They already distinguish physical regions, root/whole endpoints
and compositional changes. Their nullary-old/pure-replacement positivity and
squarefree-root-colour contracts are not silently applied to this copied
ordinary donor translation.

### Checked application and practical consequence

`PreparedSysComGround.WordTranslation` pairs actual source identity/IW
constructors with target identity/IW constructors in the same formula order.
Source IW keys are preserved; target identity key 50 is an explicit translation
of source identity keys, not a provenance cast. The concrete IW words are
[C,A,A,A], [C,B,B,A], [C,B,B,B]; the replacement c uses [B,B,B,C].

One immutable registry contains the five exact assembly instances (keys 0–4),
the four IW instances for each word (10–13,20–23,30–33,40–43), and identity50:
22 descriptors, all with genuine admission and unique IDs. Both translations
have 25 vertices. Replacing c changes two five-node physical donor uses while
the same a,b checked pieces remain available. The five common assembly nodes
must be reconstructed/revalidated; their ancestor extraction observations must
not be declared unchanged.

The executable part computes changed uses/addresses. Native proof quotation
and existing multiset/incidence infrastructure remain noncomputable. In
particular, `checkedFill` is not a measured incremental checker that skips all
previous work. This is a proved reuse/recomputation contract and checked
construction, not a runtime speedup benchmark or a new global optimizer.
A competent typed zipper/DAG cache can implement the same origin pullback;
the additional CK deliverable is the extraction interface and classification
of donor-internal/ancestor corrections, with typed residuals and multiplicity.

`PreparedSysComApplication.translate_Q` proves the constructor identity in
**every commutative semiring**, equivalently

    Q_T(z) = 3z + (z + Q_a(z) Q_c(z)) (z + Q_b(z) Q_c(z)).

The three leading scalar z contributions comprise two proper ancestor choices
and the separately represented whole endpoint. Their scalar weights are
constant, but their detached proof contents are not: replacing c changes those
contents. `word_Q` proves the identity/IW word formula by induction for arbitrary
word lists. `checked_cut_counts` derives 1372 full native branch-cut witnesses
for each checked output from those universal identities and the existing
`Q_one_card` theorem, **without enumerating cuts**. This includes the empty and
separate whole choices; it is not a claim of 1372 proper cuts. Equal 25-node/
1372-cut summaries emphatically do not imply equal typed residuals or tensors.

### Final status and theorem map

| Status | Result |
|---|---|
| MECHANIZED | `PreparedSysComSource.source_correct`, `source_prepared`, `original_correct`, `replaced_correct`; exact source class, independent correctness/preparation |
| MECHANIZED | `PreparedSysComGround.wordTree_translation`: actual paired source/target identity/IW constructors, not boundary-only quotation |
| MECHANIZED | `PreparedSysComSourceFrontier.source_frontier`, `source_provider_matching`: native three-site source frontier, literal remainder and refill |
| MECHANIZED | `PreparedSysComTranslation.translate_is_fill`, `coordinated_update`, `donorCut_remainder`, `donorCut_provider`, `allCutsEquiv`: actual translated four-use native decomposition |
| MECHANIZED / EXECUTABLE control | `PreparedSysComReuse.native_locations`, `control_matches_native`, `refresh_retranslation`, `refresh_reuses`, `checkedRefresh_realize`: actual addresses, cached reuse and checked retranslation |
| MECHANIZED instantiated application | `PreparedSysComApplication.registry_admitted`, `checkedTranslation_realize`, `checkedUpdate_agrees_full_retranslation`, `checked_frontier`, `translated_origin_observation`; exact same-registry output, native witness/refill and decorated observation |
| MECHANIZED scalar projection | `translate_Q`, `word_Q`, `checked_sizes`, `checked_cut_counts`; universal recurrences, 25 vertices/1372 full native cuts in each application |
| PAPER / CONDITIONAL | The written class theorem with broader source donors requires their actual target interpretation and admission. The extraction-sum corollary is not an additional mechanized linearized tensor theorem. |
| OPEN | Full prepared-source compiler/preparation, general source-to-target transport of all donor cuts, runtime cache refinement, material/profile fidelity, global optimizer advantage and priority beyond the focused literature comparison |

The six generic exact signatures printed during the successful final
application check are `translate_is_fill`, `coordinated_update`,
`donorCut_provider`, `allCutsEquiv`, `refresh_retranslation`, and
`checkedRefresh_realize`. Their declarations in the named modules state the
dependent boundaries and completeness/admission hypotheses explicitly.
In particular the checked theorem takes old/new `CheckedDerivation P` families
and `LocallyAdmittedTree P scaffold` for the same P, not just equal displayed
sequents.

### Verification and independent review

All seven final additive module checks pass. Each invocation uses the pinned
Lean executable, the existing local/package `LEAN_PATH`, `-j1`, async draining,
CPU/RSS checkpoints, a 300-second actual-child bound and before/after source
hashes. Failed elaboration closures are discarded. No full build, Racket run,
suite, finite enumeration campaign, package installation, commit or push.

Actual child command lines, shown in equivalent PowerShell invocation notation,
run from `C:\Users\gavin\Desktop\coding2023\lean_projects\potkin3`:

```powershell
$ckLean = 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe'
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/HLJInternalWeakening.olean Potkin/Research/HLJInternalWeakening.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/PreparedSysComSource.olean Potkin/Research/PreparedSysComSource.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/PreparedSysComGround.olean Potkin/Research/PreparedSysComGround.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/PreparedSysComTranslation.olean Potkin/Research/PreparedSysComTranslation.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/PreparedSysComReuse.olean Potkin/Research/PreparedSysComReuse.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/PreparedSysComSourceFrontier.olean Potkin/Research/PreparedSysComSourceFrontier.lean
& $ckLean -j1 -o .lake/build/lib/lean/Potkin/Research/PreparedSysComApplication.olean Potkin/Research/PreparedSysComApplication.lean
```

The wrapper supplies the existing `.lake/build/lib/lean` and installed package
build-library directories in `LEAN_PATH`; no Lake startup, downloads or build
of unrelated modules is involved. The process stdout/stderr are asynchronously
drained; 30-second CPU/RSS checkpoints establish actual child activity. The
longest final check is 66.160 seconds. A relevant-fix reuse check took 144.641
seconds, showing CPU/RSS progress and then concrete errors; it was not silently
restarted or called a mathematical failure. No invocation reached its bound.

| Final source/module | Exit | Seconds | Printed headline closures |
|---|---:|---:|---|
| HLJInternalWeakening | 0 | 39.489 | lift_admitted, iw_admitted, iw_wholeValid |
| PreparedSysComSource | 0 | 64.640 | source_correct, source_prepared, original_correct, replaced_correct |
| PreparedSysComGround | 0 | 42.305 | wordStock_admitted, wordTree_translation, wordTree_registered, checkedWord_realize |
| PreparedSysComTranslation | 0 | 48.085 | translate_is_fill, coordinated_update, donorCut_remainder, donorCut_provider, allCutsEquiv |
| PreparedSysComReuse | 0 | 49.568 | native_locations, control_matches_native, refresh_retranslation, refresh_reuses, checkedRefresh_realize |
| PreparedSysComSourceFrontier | 0 | 66.160 | plug_source, scaffold_addresses, source_frontier, source_provider_matching |
| PreparedSysComApplication | 0 | 64.602 | registry_admitted, checkedTranslation_realize, checked_sizes, translate_Q, checked_cut_counts, checked_frontier, checkedUpdate_agrees_full_retranslation, translated_origin_observation |

Every listed final closure is exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx` or custom axioms.
No Lean source changed after its successful final check. There are harmless
unused-simp warnings; they do not change theorem status. The executed native-
address control prints `[(2,[0,0,0,1]), (2,[0,0,1,1])]`; target use indices are
`[1,3]`, with `[0,2]` retained. These are control evaluations supported by the
universal native correspondence theorem, not finite evidence for its truth.

Final SHA256 fingerprints:

```text
HLJInternalWeakening        4E2A9E2240D30DBF09A65E7BA67FD31B5FBF22E339E4EF3AB0374BC5FA6A2B45
PreparedSysComSource        153A45B454A9EC873E3B438616109504DB374FA4D3A5384A9683B0DED3D61F67
PreparedSysComGround        A48E70642C697D541E0BB127832415A3CFA450947F04358409878582AC009169
PreparedSysComTranslation   94E411BFEDA1C090092DD645BCA1FABCEF9B05886D5688985856673604D0FF8E
PreparedSysComReuse         DF1EAEABA436E21ACCF25FE868E8AE256340C7BB771FDAEF4AD378A443BC5626
PreparedSysComSourceFrontier 778FAEA6A00F5EE204A7FCED970BD3A5A39A928362B4E0CC10718F2C8C655315
PreparedSysComApplication   DBAE9724BAE44D5B659DFC49F8B51A52E68E293504B65002B3C1AC019938120F
```

For reproducibility, earlier failed versions of those same targeted commands
took: IW 75.688/40.319/83.738 s; source 42.034/44.065/47.159/86.045 s;
ground 50.762 s; translation 66.318/89.545/76.775 s;
reuse 53.950/144.641/43.923 s; source frontier 40.058/41.819/50.735 s;
application 44.731/56.314/83.914/77.207 s. Every rerun followed a concrete
source fix: finite-index motives/getters, mapped-multiset boundary normal forms,
native cast metadata, explicit implicit arguments, or scalar numeral coercion.
No failed run's printed closures are accepted as final evidence. These were
elaboration repairs of universal proofs, not tests over increasing finite n.

Three assigned investigations covered actual translation fidelity, CK/product
and admission integration, and an independent read-only mathematical review.
Review caught and resolved the source/target multiplicity distinction, Y's
3L-to-2L contraction, the finite identity/IW scope, and the need to connect
executable control to native physical addresses. It also required an actual
source/target constructor relation rather than a boundary-only assertion.

### D1–D6 and remaining obligations

- D1: no logical-Cut elimination claim. Native CK cuts remain extraction data.
- D2: an actual nonlinear translated proof transformation is analysed; no full
  preparation/normalization compiler, confluence or global optimum follows.
- D3 (uniform weakening): no general uniform-weakening metatheorem is proved.
  The genuine selected source constructors/strict target instances are
  supporting source-adequacy work, not completion of that programme direction.
- D4: concrete CK decomposition of copied translated derivations, including
  all installed cuts, is the principal advance.
- D5: physical-origin-localized native/checked reuse is the useful consequence;
  runtime cache refinement and material/profile fidelity are not supplied.
- D6 (structural conservativity across bases): no new base-conservativity
  theorem is proved. The secondary antipode investigation is deferred; no
  antipode normalization/equivalence theorem is claimed. No process-calculus
  operational semantics or termination theorem is inferred either.

The next mathematical enlargement is a constructor-compositional translation
for additional prepared source shapes, proving the actual copy/passive-context
map rather than assuming arbitrary same-boundary target pieces. It is not a
reason to restart the generic gluing, K, finite-change or Faà di Bruno work.

## Recursive prepared Sys(com) continuation — theorem stated before implementation

### Source class and intended theorem

This continuation starts at the same HEAD/main and preserves all existing
uncommitted work. The following is the paper statement fixing the scope before
new implementation; verification status will be recorded after checking.

The source class is generated independently of target success. A region is a
native typed source vacancy; ordinary IW prefixes are allowed. A phase X has
two recursively generated open source contexts U,V of the same end-sequent S,
one fixed shared parameter pack, and exact source top-rule data at every
physical region: each U region is a role-0 output, and each V region is a
role-1 output. Insert those top applications at the regions and put the actual
X bottom below U,V. Require X's owner ID to be fresh, child owner sets disjoint,
and actual single-succedent rule side conditions. Owner IDs are not descriptor
keys. Class membership has no target scaffold or target-checking premise.

Thus bottoms can form arbitrary binary trees, with each ancestor's tops applied
before the descendant owners at the leaves. The old X/Y class is one instance,
not the recursively iterated closed building block. The class excludes
entanglement, irregularly distributed ancestor tops, and arbitrary LJ branching
outside the stated constructors. Ordinary closed donors need their actual
identity/IW translation, not merely matching target boundaries.

For every such finite source construction and appropriately typed ordinary
donor family, the intended theorem produces its native target translation,
computed physical-use-to-source-origin map, literal open target scaffold, and
its native branch/proper frontier as appropriate. With source-only freshness
and boundary conditions, coordinated same-boundary ordinary donor replacement
preserves source correctness/preparation and commutes with that translation.
Checked reconstruction additionally requires one exact admitting registry with
the independently derived finite assembly stock and all checked donor pieces.

### Constructor proof and actual staging

At a phase, for each marked right region v, apply genuine Com to each left
region u and v. Interpret U with the right output at v as an additional passive
component, then interpret V with the completed S as passive. Finally apply EC
to the two S components. Every intermediate premise is a whole hypersequent,
not independently proved components. The passive-context equations follow
from the exact source top boundaries. Recursion is on U and V.

This is a controlled recursive case of the marked-occurrence construction in
[Ciabattoni–Genco, §4.1](https://arxiv.org/html/1805.04852v1#S4.SS1), not a claim
to implement every prepared source from that paper.

The resulting physical-use history is a pair of right/left recursive uses and
an ordered input choice. Its computed word is

    uses(phase U V) = uses(V).flatMap(v =>
      uses(U).flatMap(u => [left(origin(u)), right(origin(v))])).

Consequently F_leaf=1, F_IW=F_child, F_phase=2 F_U F_V. Left-origin multiplicity
is mu_U(i) F_V and right-origin multiplicity is F_U mu_V(j). The exact affected
use count is the sum of those multiplicities over changed source origins.
These are physical donor uses, not assembly-node costs or measured runtime.

Source correctness/preparation follows by structural induction: newly inserted
tops occupy the prefix-free source-region frontier, obey the designated root
branch, and share the new owner's parameters. Existing tops/bottoms retain
their scopes; fresh/disjoint owners prevent capture or duplication. A new
owner is uniformly above the child owners, so no two-way entanglement is
created. Closing regions with owner-free ordinary proofs preserves this.

Target scaffold filling and copy-map composition follow constructor by
constructor. Nested use indices retain both physical levels; their absolute
addresses concatenate through the existing native filled-hole equivalence.
The CK frontier adapter gives literal typed remainder/provider matching/refill;
the existing installed-cut and flag equivalences give the actual ordered
packets and remainder in staged extraction. Copies share replacement values,
not inner cut choices. A root interface has only its branch/whole treatment,
never a fabricated proper root cut. Commutative collection is explicit and
cannot be used to recover the physical map.

### Verification status

**Completed in the stated recursive subclass: MECHANIZED / EXECUTABLE control.**
All fourteen additive modules passed targeted verification on their final
sources, including the concrete checked application. Existing N6 dependencies
remain verified and were not rechecked just to strengthen this statement.
The initial theorem statement above preceded implementation; the final scope,
proofs and explicit remaining limits are recorded below.

### Native theorem interfaces and proof content

`RecursiveSysComSource.Source` is source construction/control metadata, not
another proof carrier or checker. `Source.erase` interprets it into the existing
native D3 `Diagram`. `TopSpec` records the exact two top rules' input/output
equations and single-succedent conditions. `WellScoped` fixes the actual owner
IDs and requires freshness/disjointness; it does not rename references or
assume successful target checking. The source grammar permits arbitrary finite
binary nesting, with each phase's tops placed at every child vacancy. It does
not encompass arbitrary prepared Sys(com), arbitrary ordinary LJ branches, or
arbitrary closed-source substitution into a previously prepared region.

MECHANIZED source results:

- `Source.localCorrect`, `Source.resolved`, `Source.correct`: actual local
  rule conditions and branch-specific owner discharge in the native diagram.
- `Source.prepared`: every same-owner top frontier is an antichain and owner
  systems are non-entangled. The proof uses physical hole prefix-freeness,
  the vacancy/vertex barrier and owner ranks, not bounded source generation.
- `Source.filled_correct`, `Source.filled_prepared`: filling the source's
  actual native holes with closed ordinary identity/IW diagrams preserves
  events at every absolute address and produces a complete correct prepared
  source. An unfilled vacancy is never made into a proof.

MECHANIZED target/control results:

- `RecursiveSysComCopy.words_uses`, `uses_length`, `phase_affected`: constructor
  composition, the exact unbounded physical-use count `2^phases`, and the
  weighted affected-use recurrence. List positions retain repeated uses.
- `RecursiveSysComTranslation.translate`: actual Com/IW/EC grafts, with the
  whole passive hypersequent passed through each recursive call.
  `scaffold_fill` is literal native filling equality for every source
  constructor and typed native provider family; `native_copy_word` identifies
  the computed origins of the actual ordered native holes with `uses`.
  `Ports` merely decorates those native holes with origins/boundary equalities.
- `RecursiveSysComCuts.leafOrder_fill`, `filled_addresses`,
  `filled_copy_count`: native dependent physical-copy splicing, with absolute
  address concatenation. The native filled-leaf equivalence keeps both
  outer and inner occurrence indices, not just their origin labels.
- `RecursiveSysComAdmission.allocated_consistent`, `mixed_consistent`:
  finite exact descriptor allocation can retain every donor descriptor below
  a disjoint offset. This helper alone does not prove recursive stock coverage.
  Allocation compares full native instance data and is noncomputable; the
  source copy/update control is separately executable. A deterministic numeric
  pair hint is not an occurrence identity or a substitute for exact data.
- `RecursiveSysComReached.stock`, `translate_all`, `stock_admitted`,
  `scaffold_admitted`, `checkedTranslation_realize`: the finite assembly stock
  is computed from source constructors, passive contexts and every ordered
  logical top pair, not by inspecting the desired completed output. It covers
  every actually reached target node and satisfies strict complete-boundary
  admission. Combining this stock with a consistent donor stock below a fresh
  offset gives the native checked target with literal realization. Donor
  interiors and all physical repetitions remain native; registry deduplication
  is not cut or occurrence deduplication. Target local admission does not imply
  source preparation: `WellScoped` and the independent source results above
  remain necessary for that interpretation.
- `RecursiveSysComReuse.refresh_retranslation`, `unchanged_cached`,
  `dirty_count`, `dirty_bound`, `checkedRefresh_realize`: cached pieces come
  from the native uncollected aligned detached family. A source-origin mask
  updates all its physical copies and leaves every other provider literally
  unchanged. Native filling equals full recursive retranslation. The checked
  version fixes one presentation for scaffold and both donor families;
  `Reached.scaffold_admitted` supplies its finite-stock premise. `dirty_count`
  ties the actual native-hole filter to the executable source control, with
  the universal affected-use bound `2^phases`. No address is reconstructed
  from an aggregated coefficient and no unchanged-ancestor observation is
  inferred.

The native ordered packet/flag results reuse `branchFlagEquiv` and its actual
map laws. No full ordered/Foissy Hopf algebra is inferred. Forest multiplication
appears only at the explicit `Multiset.ofList` projection of detached factors;
it is neither Communication nor filling. No equality of source and target
coproducts is asserted.

`RecursiveSysComCutApplication.actual_aligned_detached` identifies the exact
physical native provider family, `actual_proper_factor_count` gives its computed
copy-word length, and `actual_frontier_refill` reconstructs `translate` with the
literal scaffold as typed remainder. `actualAllCutsEquiv` classifies both donor-
interior choices and retained-assembly selections swallowing complete payloads.
Choices are indexed by physical sites: two copies of one donor have independent
inner cuts. `actual_flag_outputs` retains **both ordered packets and the final
typed remainder** under the established native flag reindexing;
`actual_flag_staged_refill` gives the two actual reconstruction equations.
This is a witness-level indexing/output theorem, not a new collected tensor
identity. For a source leaf, only the branch/whole treatment is provided; the
proper wrapper requires an ordinary scaffold. The witness-free global whole
endpoint is never represented as a proper root cut.

### Checked application and executable control

`RecursiveSysComExamples.nested` recovers the earlier X/Y source structure,
three logical donor origins and ordinary donor words. `balanced` is a genuinely
different three-owner source: both children contain an actual Sys(com) phase.
It uses nonempty parameters `Phi={A}`, `Psi={B}`, end-sequent
`A^2,B^2,C => C`, and four leaf boundaries
`A^4,C => C`, `A^2,B^2,C => C`, `A^2,B^2,C => C`, `B^4,C => C`.
Each is supplied by identity C and four actual IW applications, not by an
assumed proof of a matching boundary. Source correctness/preparation is an
application of the universal source theorems, not an inference from these
examples.

`RecursiveSysComApplication` fixes distinct atoms A=0, B=1, C=2. Its
`sourceOld`/`sourceNew` use the exact matching IW keys of the target words;
`old_word_translation`/`new_word_translation` invoke the existing actual
identity/IW constructor relation. The specified identity-to-descriptor-50
translation is retained. The source before and after are independently complete,
correct and prepared (`source_before_correct`, `source_after_correct`,
`source_before_prepared`, `source_after_prepared`).

| Source | Computed target word (logical origins) | Physical uses |
|---|---|---:|
| Old nested X/Y | `[0,2,1,2]` | 4 from 3 origins |
| New balanced X/Y/Z | `[0,2,1,2,0,3,1,3]` | 8 from 4 origins |

The update reorders the mixed donor's word from `[A,A,B,B]` to `[B,B,A,A]`.
The entire boundary is unchanged, but the actual internal rule occurrences
differ. It affects native ordered use positions **2 and 6** (zero-based),
through the child and outer translation layers. Executable `uses`,
`affectedIndices`, and the two `#eval`s produce the balanced word and `[2,6]`;
their relevance to native holes follows from `native_copy_word` and
`Reuse.dirty_count`, rather than an independently imagined copy diagram.
`Reuse.locations` retains the native absolute addresses separately from logical
origins. Its address observation is theorem-level native data, not a separately
refined fast executable address backend.

The joint donor stock has twenty IW descriptors and the shared identity C,
with distinct IDs below 10000. `Reached.stock source 0` supplies the assembly
descriptors; exact allocation above that offset yields **one immutable
presentation** `registry`. `checkedOld` and `checkedNew` are both produced by
the native public checker in that presentation. `checkedOld_realize` and
`checkedNew_realize` identify the actual recursive translations.
`coordinated_checked_reconstruction` equates cached-piece refresh with
`checkedNew.realize`, not a separate toy output or a cross-snapshot cast.

An inspectable certificate is `checked_native_certificate`: an actual
`CKCut checkedNew.realize` with **eight ordered sites**, typed remainder
`scaffold key source 0`, and native detached-tuple refill equal to that exact
checked output. The proof constructs it with the public native
`CutApplication.actualProperFrontier key source 0 new`; its ordered sites,
addresses, detached family and remainder remain native data before collection.
The universal `actualAllCutsEquiv` and `actual_flag_outputs` apply to this same
scaffold, including independent inner choices in its copied donors and ancestor
effects. No completed-proof cut enumeration was used.

### Targeted verification record

HEAD remains `2835d448722e6e366c26003004b19b631984691b`, branch `main`.
All pre-existing dirty work, including the earlier untracked research modules,
is preserved. No policy edit, full build/suite, dependency installation,
commit or push is performed.

Each check uses the pinned executable
`C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe`
from the POTKIN3 root, with local/package compiled-library paths in `LEAN_PATH`:

```powershell
& 'C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe' -j1 -o '.lake/build/lib/lean/Potkin/Research/<Module>.olean' 'Potkin/Research/<Module>.lean'
```

The established wrapper asynchronously drains both streams, reports child
CPU/working set every 30 seconds, enforces 300 seconds on the actual child and
kills/waits for timed-out children. Below are final successful checks, not
axiom output from failed elaborations:

| Module (`Potkin/Research/`) | Seconds | Exit |
|---|---:|---:|
| `RecursiveSysComSource` | 50.564 | 0 |
| `RecursiveSysComSourceLaws` | 58.666 | 0 |
| `RecursiveSysComSourcePreparation` | 126.033 | 0 |
| `RecursiveSysComSourceFilling` | 112.616 | 0 |
| `RecursiveSysComExamples` | 61.429 | 0 |
| `RecursiveSysComNative` | 72.924 | 0 |
| `RecursiveSysComCopy` | 57.194 | 0 |
| `RecursiveSysComTranslation` | 118.284 | 0 |
| `RecursiveSysComCuts` | 41.792 | 0 |
| `RecursiveSysComAdmission` | 73.872 | 0 |
| `RecursiveSysComReached` | 56.347 | 0 |
| `RecursiveSysComCutApplication` | 66.650 | 0 |
| `RecursiveSysComReuse` | 50.842 | 0 |
| `RecursiveSysComApplication` | 56.012 | 0 |

Every final headline closure is a subset of
`{propext, Classical.choice, Quot.sound}`. In particular `scaffold_fill` and
`native_copy_word` use exactly these three; `words_uses`, `uses_length`,
`phase_affected`, `affected_le` use `propext, Quot.sound`. No `sorryAx` or custom
axiom is accepted. Concrete failed checks exposed local parser/namespace,
dependent transport and arithmetic issues; fixes do not weaken theorem scope.
The unavailable optional `Mathlib.Data.Nat.Pairing` object was avoided by the
local numeric hint, not by building a dependency hierarchy.

Concurrent imports later showed very low CPU accumulation and tiny working
sets, followed by recovery when contention eased. Remaining integration checks
are consequently sequenced. One known-bad reuse child was stopped before its
bound to correct its namespace and avoid wasting work; this is not evidence
against the mathematical statement. No unchanged silent command is repeatedly
restarted.

For clarity, `<Module>` above is replaced by each exact table entry, with no
other Lean flags. The wrapper changes only process control, environment and
output draining. All final source fingerprints remained unchanged while their
checks ran. In particular Application final SHA256 is
`1DC545C62966CF9532E96CDD8D34CA53CBF3153A391EDB9029E7CE4A823ACA23`;
all four final application headline closures are exactly
`[propext, Classical.choice, Quot.sound]`, including the matched changed-source
correctness/preparation and checked native certificate. Harmless unused-simp
and section-variable warnings remain; no cleanup-only recheck was made.
No full build, suite, benchmark or finite cut-oracle campaign was run.
Final bounded source scan of only `RecursiveSysCom*.lean` found no
`sorry`/`admit` proof placeholders or custom axiom declarations. The final
provenance check still reports HEAD `2835d448722e6e366c26003004b19b631984691b`
and `main`; `git diff -- AGENTS.md` is empty. Only the fourteen new task
modules and the three maintained report/ledger documents were changed by
this continuation; the other pre-existing dirty files remain untouched.

Status distinction: the constructor arguments above are **PROVED** on paper
and **MECHANIZED** in the stated native interfaces; copy/update control is
**EXECUTABLE**. Native checking is conditional on the explicit common-registry
and ordinary-donor hypotheses, supplied by a proved finite exact-stock
construction (allocation/quotation itself is noncomputable).
General prepared-source adequacy and an efficient executable quotation/cache
refinement remain **OPEN**. The examples illustrate the universal theorems;
they are not the proof of them.

### Independent review and the actual increment

The source-fidelity reviewer/writer established source correctness and paper
preparation independently; the copy/CK reviewer checked the right-then-left
Cartesian staging and native physical packet/refill adapters. A third reviewer
read the integrated source/core/application without writing it. They found no
false recurrence, but did find an integration mismatch: the source-only
balanced example used IW keys starting at 2000, whereas the checked target
application uses keys 200/210/220/230. The existing `WordTranslation` preserves
IW keys. The application therefore now defines its **own matching source
donors**, including replacement word key 240, and records their constructor
translation and before/after source correctness/preparation. The separate
source-only example is not claimed to be literally that checked output.

The old nested X/Y is recovered as a derived recursive source with its original
source-rule labels, ordinary donor words and four-use pattern. No literal
legacy AST equality or unchanged legacy target registry is claimed. A named
source-order equation `origins.map holeEquiv = erase.holeOrder` has not been
added; the target copy word/native hole-order theorem is proved independently.

Relative to the fixed predecessor, the advance is an actual constructor-
compositional structural translation with unbounded nesting, rather than a
fresh parameter on its four holes. It determines exactly which physical donor
uses a coordinated source update affects; the native CK expansion additionally
accounts for ancestor cuts that swallow updated regions. This supports
certified cache-boundary and invalidation analysis of this translation. It is
not a measured runtime incremental checker or a global optimizer; identity/IW
donor reorderings at a fixed boundary have fixed node count.

- D1: no new logical-Cut reduction/relative Cut theorem. The exact translated
  regions and typed residual contracts are usable dependencies for a future
  specified logical-Cut application, not its completion.
- D2: a genuine nonlinear structural translation with correlated replacement
  and explicit physical duplication; no new optimization criterion or global
  normal-form theorem.
- D3: passive hypersequent contexts satisfy exact local rule side conditions;
  no general uniform-weakening metatheorem follows from this adapter.
- D4: principal advance—recursive source-derived CK factorization, independent
  copied-piece cut choices and native staged packet/remainder coherence.
- D5: exact coordinated reuse/reconstruction boundary. Executable control and
  theorem-backed checking are distinct from a deployed incremental verifier.
- D6: finite registry compatibility is not logical base conservativity. No new
  conservativity, material fidelity or antipode classification theorem.

The next enlargement, if selected, is additional **actual source constructors
and their prepared/discharge adapters**, not another generic chain rule or
another repetition of this closed example. Full prepared LJ translation,
arbitrary owned donor copying, formula-occurrence resource movement and
process-calculus operational consequences remain OPEN.

# Native CK certified contraction postponement 13 October 2026

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

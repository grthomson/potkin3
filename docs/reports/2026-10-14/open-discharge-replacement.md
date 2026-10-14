# Open discharge replacement: verified results and remaining gates

Report date: 14 October 2026. Repository: POTKIN3. HEAD:
`93b4a9abce87692ac32665132144ba1cd602808c`.

## Completed continuation: all four requested proof targets

**MECHANIZED.** The fixed-owner-ID milestone is complete. The missing reusable
connection is now proved, and the existing implication-right permutation has
actually been refactored to use it, including exterior contexts. Full summary
composition and the new Sys(com) cut-certificate diagrams are also verified.
This section supersedes the unfinished statuses in the historical recovery
report retained below.

| Requested target | Verified declarations and source |
| --- | --- |
| Exact exposure and correctness-flag laws | `OpenDischargeCompositionLaws.lean:372` `exposure_fill`; `:463` `ok_fill`. Both are unconditional, at arbitrary absolute address. |
| Entire summary composition and realizable associativity | `OpenDischargeCompositionLaws.lean:492` `directSummary_fill`; `:510` `composeSummary_realizable_assoc`, using the installed native physical-hole reindexing. |
| Generic fixed-owner replacement, future fillings and exterior contexts | `NativeDischargeReplacement.lean:266` `fixedOwner_replacement`; `:283` `summaryEquality_replacement`. No valid-filler or freshness premise excludes failures. |
| Existing implication-right application derived from the generic theorem | `DischargePermutation.lean:499` `implication_permutation_exterior`; `:516` `open_implication_permutation` is now its root-context specialization. Checked future/exterior corollaries are retained. |
| Actual Sys(com) two-stage witness diagrams | `DischargeCutFlags.lean:305` `restriction_branch`; `:322` `gluing_branch`, with independently constructor-defined reassociation under the actual native flag conversion. |
| Connection to full summary evaluation | `DischargeSummaryCutEvaluation.lean:186` `summary_flag_diagram`; `:199` `summary_and_ordered_outputs_coherent`; `:270` / `:287` joint summary/restriction and summary/gluing diagrams. |

### Exact scope of the reusable result

The primary literal-equality theorem is:

```lean
theorem summaryEquality_replacement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {H : Hypersequent sigma} {source target : CKTree sigma (Data sigma) H}
    (equal : directSummary Imp source [] = directSummary Imp target [])
    (left : source.LeafAssignment) (right : target.LeafAssignment)
    (matching : ∀ hole,
      HEq (left hole) (right (fullSummary_holeEquiv Imp equal hole)))
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    {address : InternalAddress} (context : CKTree.PunctureAt H tree address) :
    Legal Imp (context.insert (source.fillAssignment left)) [] [] ↔
      Legal Imp (context.insert (target.fillAssignment right)) [] []
```

Literal equality supplies its canonical **physical** hole correspondence;
address, exact boundary, and native order preservation are proved, not inferred
from equal displayed sequents. The two assignments are arbitrary corresponding
native donors, retaining the same owner references. They may be malformed,
ill-scoped, or collide with internal declarations: correctness and rejection
are both reflected. The exterior can have arbitrary unchanged siblings and
inherited vacancies. Completeness is not silently imposed on open derivations.

The more general `FixedOwnerInterface` permits physical holes to move, as they
do in the implication-right permutation. It requires a native hole equivalence
preserving ordered ports and exact boundaries, equal fixed owner inventories,
equal rooted pending-demand observations and correctness flags, and equal
owner/parameter/role exposures at each corresponding physical hole. These are
finite-summary conditions, **not assumed provider-certificate equivalences**.
Only the local suffix of pending top addresses is omitted by the rooted
observation: actual exterior ancestor compatibility cannot depend on it. The
original full summaries and native witnesses retain actual occurrence addresses.
Exact top-rule IDs, parameters, roles, and multiset multiplicities remain.

The proof uses verified native filling field laws and finite composition
congruence, then an induction on actual typed puncture contexts via ordinary
ordered-premise shells. It concludes the independent actual-tree `Legal`
relation; `Legal` was not redefined as success of the summary evaluator.

Owner IDs are fixed throughout. No global renaming theorem, outside-name-fixing
extension, or holewise freshening is assumed. The earlier capture objection
therefore does not arise. A future reference to an unbound name is not silently
redirected to a new declaration.

### Full summary composition, not a rooted-observer substitute

```lean
theorem directSummary_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    directSummary Imp (tree.fillAssignment assignment) address =
      composeSummary (directSummary Imp tree address)
        (attachedSummaries Imp tree assignment address)
```

This preserves every field: whole conclusion, ordered physical holes, complete
owner inventory, outstanding occurrence demands, exposure multiset, and failure
flag. The exposure proof sums actual physical hole/grant occurrences, copies
each inherited owner row once per surviving filler hole, and proves cross-hole
contributions zero by native vacancy geometry. Duplicate UIDs/rows are never
deduplicated. The correctness proof derives freshness inside the successful
global-Nodup branch, rather than requiring all future inputs to be fresh.

Associativity is proved on realized summaries using native
`composeLeafAssignment` and `fillAssignment_assoc`. It is not asserted for
arbitrary fabricated metadata records or unattached address configurations.
The rooted refinement used in the replacement proof is now accompanied by
this independently verified stronger all-field equality.

### Actual normalization and the CK connection

The existing ten-instance immutable registry remains unchanged. Both source
and target use UID 42 and `Phi={p}`, `Psi={q}`. Their registered common bottom
sequents differ as required; rule-instance IDs 707 and 709 are not conflated
with the system-owner UID. Implication-right remains the actual registered
logical instance. The public native quotation/checking wrappers recheck both
fillings in that registry.

The source `R(B(P,Q))` and target `B(R(P),R(Q))` now obtain their correctness
equivalence by applying `fixedOwner_replacement`. The old bespoke event lemmas
remain useful independent facts, but no longer supply the proof of
`open_implication_permutation`. `implication_permutation_exterior` quantifies
over arbitrary later `P,Q` and native typed surrounding derivations;
`checked_exterior_filling_permutation` applies it to the native checked donors.
The nonvacuous fixture and both independently unclosed donor results passed
again on this final source.

Semantic correctness is distinct from registry admission. Summary equality
does not admit an unregistered target instance or lift a foreign snapshot.
Using an exterior as a checked quotation still requires its native admission
in the same registry; existing insertion/admission APIs provide that gate.

The CK evaluators actually fold summaries of physical punctured remainders
and aligned detached factors. They are not defined to return the source's
summary. Full-summary equality holds along the native inside-factor versus
remainder-first flag equivalence, together with both addressed ordered packets
and the literal typed final remainder. The actual certificate restriction and
gluing maps commute after the same constructor reindexing. Inherited interfaces
retain their original typed Boxes; empty descent and separate whole selection
are not replaced by fabricated root cuts or coefficient units.

`branchSummary_success_iff_pieces`, `insideSummary_success_iff_pieces`, and
`serialSummary_success_iff_pieces` connect these finite evaluations to actual
jointly scoped Type-valued piece certificates. Their interpretation explicitly
requires exact local checking, unique owners, and source completeness. Factors
are evaluated under the scopes supplied by the same remainder certificate,
not independently closed and multiplied. The arbitrary-provider map diagrams
themselves do not require completeness.

### Final targeted verification

All commands ran in the POTKIN3 root with the pinned executable:

```text
C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe
```

Exact final argument vectors (each source prints its headline statements and
axiom closures):

```text
-j1 -o .lake/build/lib/lean/Potkin/Research/OpenDischargeComposition.olean Potkin/Research/OpenDischargeComposition.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/DischargeSummaryCongruence.olean Potkin/Research/DischargeSummaryCongruence.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/OpenDischargeCompositionLaws.olean Potkin/Research/OpenDischargeCompositionLaws.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/NativeDischargeReplacement.olean Potkin/Research/NativeDischargeReplacement.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/DischargeCutFlags.olean Potkin/Research/DischargeCutFlags.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/DischargePermutation.olean Potkin/Research/DischargePermutation.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/DischargeSummaryCutEvaluation.olean Potkin/Research/DischargeSummaryCutEvaluation.lean
```

| Final source | Exit | Duration | Final headline axiom closures |
| --- | --- | --- | --- |
| `OpenDischargeComposition` | 0 | 115.842 s | `propext`, `Classical.choice`, `Quot.sound` (some use fewer) |
| `DischargeSummaryCongruence` | 0 | 106.164 s | Composition: `propext`, `Quot.sound`; canonical hole map additionally `Classical.choice` |
| `OpenDischargeCompositionLaws` | 0 | 110.341 s | All five: `propext`, `Classical.choice`, `Quot.sound` |
| `NativeDischargeReplacement` | 0 | 140.902 s | All four: `propext`, `Classical.choice`, `Quot.sound` |
| `DischargeCutFlags` | 0 | 176.532 s | All four: `propext`, `Quot.sound` |
| `DischargePermutation` | 0 | 125.911 s | Interface/generic application/checked corollaries: `propext`, `Classical.choice`, `Quot.sound`; some unchanged native facts use fewer |
| `DischargeSummaryCutEvaluation` | 0 | 106.325 s | All ten: `propext`, `Classical.choice`, `Quot.sound` |

No accepted final closure has `sorryAx` or a custom axiom. A focused final source
search of these seven files found no `sorry`, `admit`, or custom `axiom`
declaration. Source cleanliness is supplementary; successful final checks and
their closures are the proof evidence.

All checks were serialized, asynchronously drained both stdout and stderr, and
bounded the actual child at 300 seconds with CPU/memory checkpoints. Concrete
failed checks were corrected before rerunning:

| Source | Earlier unsuccessful durations and exact correction class |
| --- | --- |
| Composition core | 131.749, 104.069, 93.828 s: prefix projections/decider-instance equality and explicit dependent/coercion annotations. |
| Congruence | 125.074 s: canonical inverse address orientation and explicit erased-field equality projections. |
| Full composition laws | 125.980, 98.305, 129.858 s: typed multiset annotations, reserved binders, exact bind/cons API orientation, prefix cancellation, and removal of already-closed tactics. |
| Native replacement | 83.193 s: explicit address arguments and native dependent `Sum` constructor matching. |
| Registered permutation | 219.701, 132.211 s: adjacent documentation syntax and opaque small-shell reductions; fixed using existing exact-instance lemmas and native constructor exposure tables. |
| Cut evaluation | 132.250 s: final reflexivity for whole-detach attachment and the exact native ordered-packet namespace. |

The initial repaired Flags command timed out at 300.675 s and its child was
terminated. One exact two-import diagnostic (`OpenDischargeCertificates` and
`RemainderExtractionFlags`, via `lean.exe --stdin`) passed in 215.138 s,
establishing substantial import/startup cost. The documented warmed final
source check then passed; timeout was not treated as mathematical failure.
Failed invocation footers containing placeholders were discarded.

There was no full build, full suite, Racket execution, Python prototype, finite
enumeration campaign, or benchmark. The small constructor calculations certify
an actual registered application; universal Lean proofs establish the theorem.
Unchanged gluing/K results were reused rather than re-verified.

### Independent review, scope boundaries, and D1–D6

Independent mathematical/source review checked full exposure multiplicity,
negative ownership cases, lack of unjustified freshness assumptions, actual
native filling associativity, fixed-ID future/exterior substitution, registered
shell boundaries, and independently defined certificate reassociation. Reviews
confirmed that no pointwise provider equivalence replaced the intended bridge.
Concrete namespace/coercion issues were corrected and final checks obtained.

**D4/D5 advance:** finite discharge information now justifies replacing an
unfinished derivation before its premises are supplied, under arbitrary matching
future fillings and surrounding native derivations; CK extraction can certify
that information in either compatible staged decomposition with actual witness
coherence. This is a structural modularity/normalization result, not an ATP or
a new abstract Hopf-algebra hierarchy.

**Still OPEN, not part of the four completed targets:** general owner renaming
with consistent transport/admission of every reference; a generic equivalence
of all internal certificate types/counts for different interiors; full source
LJ/Sys(com) erasure/decorability; logical-Cut elimination; copying system bottoms;
optional cost-polynomial results; executable Boolean/cache refinement and
performance claims. The unrelated source-only
`DischargeCertificatePermutation.lean` remains unverified and is not credited.
No full coproduct/tensor equality, Hopf character, or Hopf-morphism theorem is
implied by summary or correctness agreement.

D1 still requires the ordinary logical-derivation/relative-Cut bridge, not merely
native CK extraction. D3 still requires faithful full-rule/source admission and
erasure/decorability beyond the checked ten-instance application. D2 copying and
D6 presentation/material-base comparisons remain separate obligations. No new
research direction was opened.

HEAD and the existing branch are unchanged. All task changes are uncommitted;
AGENTS.MD, README, protected/relocated documents, unrelated untracked work, and
the Racket repository were preserved. No commit or push was made.

## D3 continuation: checked annotated-source bridge

Continuation date: 14 October 2026. HEAD remains
`93b4a9abce87692ac32665132144ba1cd602808c`; all additions remain uncommitted.
The fixed-owner milestone above was reused, not reopened. The **full D3 source
adequacy request remains PARTIAL**: the following universal results are now
MECHANIZED, but the stronger source-constructor and resource-action obligations
listed below are not.

### Source interpretation and application

The independently specified source grammar has natural-number atoms and
implication. Its rules are identity, internal weakening, internal contraction,
implication-right, and the two tops/common bottom of Sys(com). Contexts are
finite multisets; the single-conclusion side conditions are explicit.

`D3SourceEncoding.implication_image_iff` proves that the native `Imp` relation
on this image is precisely the source implication constructor.
`exact_instance_iff` and `exact_tree_iff` prove local soundness **and reflection
on the encoding image**, not full-LJ surjectivity. Source diagrams are independent
syntax for this adequacy result; extraction still uses the original native trees.

`holeEquiv`, `hole_boundary`, `hole_address`, and `hole_order` transport actual
physical vacancies. `encode_fill` and `encode_insert` are literal equalities for
every diagram, including bad tokens and declaration collisions. They keep the
same rule descriptors, owner references, ordered premises and incidence.

The independent discharge model uses physical ordinal top/bottom occurrences.
An inductive finite pending-elimination schedule removes precisely the selected
occurrences; eligibility is source pack equality and strict ordered-premise
ancestry. It is **not defined as native Legal or summary success**.
`D3DischargeGrouping.groupingAssignmentEquiv` constructs inverse maps to eligible
assignment data; `process_pending_outside` proves the actual elimination-fold
invariant. Unused bottom declarations are retained, repeated tops are allowed,
and no nearest-owner convention is imposed. `faithful_annotation` proves recovery
under injective naming. `two_eligible_choices_distinct` proves universally that
two eligible choices give distinct grouping witnesses, without a finite fixture.

`D3SourceAdequacy.source_correct_iff_native` connects this independently defined
fixed-reference source annotation model to native legality. Ordinal indices
retain multiplicities even for equal metadata. `source_completion_replacement`
then applies the old `fixedOwner_replacement` to actual simultaneous source
fillings and actual typed source exterior contexts. Duplicate declarations,
unresolved references and wrong branches are reflected as failures; there is no
freshness assumption or implicit renaming. `CompleteSourceCorrect` separately
requires absence of vacancies. A locally valid source hole is not a closed proof.

`D3SchemaPermutation.Schema.implication_permutation_schema_exterior` and
`checked_schema_exterior` quantify over arbitrary schema parameters and **any
one admitting immutable registry**. Their concrete bottom sequents change, but
their system UID and shared pack do not. The source holes at `[0,0]`, `[0,1]`
map to `[0,0]`, `[1,0]`, preserving their order and exact boundaries. The two
target implication nodes share a descriptor/key without identifying their
physical occurrences.

`D3SourcePermutation.Application.encoded_source_permutation_exterior` uses the
actual source rule encodings, not just an arbitrary ternary implication predicate.
`D3SourceCK.source_implication_replacement` transfers this to source correctness
under every typed source exterior. Its proof invokes the generic replacement
theorem through the checked interface. This removes the ten-instance restriction;
it does not claim a new logical permutation, full normalization or confluence.

### Admission and the actual CK consequence

`D3RegistryAdmission.finite_family_admission` constructs a common finite registry
under explicit exact-key consistency and descriptor admission. Its deduplication
is only of registry entries, **never of proof occurrences**.
`lookup_preserved` and `lift_realize` preserve old exact lookups and the complete
decorated tree when requoting through the public checker. `finite_extension`
requires consistency of old and new descriptors. This is admission preservation,
not logical/base conservativity or a Hopf morphism.

`D3SourceAdmission.finite_source_admission` discharges local descriptor validity
from the source inference schemes, for arbitrary finite families. Consistent key
allocation remains an explicit hypothesis; no universal finite registry or fresh
key allocator is claimed. `checkedSource_realize` requires completeness and uses
the public checker, not private checked-node constructors.

`D3SourceCK.source_two_stage_evaluation` proves that both native flag descriptions
evaluate the same independent source discharge condition, including failures.
`source_joint_pieces` connects that condition to **jointly scoped** Type-valued
piece certificates, requiring local source correctness, unique declarations and
completeness. `correct_source_supplies_joint_certificate` obtains the first two
premises from source correctness itself. It does not independently close each
detached factor.

`source_restriction_diagram` and `source_gluing_diagram` instantiate the established
actual witness maps; `source_ordered_outputs` retains both addressed ordered
packets and the literal typed remainder. These are not merely count equalities.
The native cut, factor, forest, scope, Box and context carriers are unchanged.
There is no coproduct-invariance claim across the permutation and no new antipode
or Hopf-character claim.

### Exact remaining gates

1. **OPEN: full recursive source grouping and closed erasure/decoration.** The
   finite pending-schedule/assignment equivalence is checked. The paper's
   constructor-by-constructor ordinary/top/bottom pending-set presentation,
   its equivalence to that schedule, and closed raw-source round trips under
   chosen declaration naming have not been mechanized. Do not credit the
   schedule theorem or the name `SourceCorrect` as completion of this stronger
   source-adequacy target. The all-possible-groupings permutation bijection also
   remains paper-level; the checked replacement concerns chosen fixed references.
2. **Missing native data: formula-occurrence action.** `ComponentIncidence`
   records displayed hypersequent-component indices and edges. It does not
   identify individual formula occurrences added by IW or paired by IC.
   The source encoding preserves multiset multiplicity and canonical component
   incidence, but that is not the stronger formula-occurrence/resource-action
   witness requested in the notes. No formula movement was inferred from those
   edges and no admission theorem for such movement was invented.
3. **OPEN: unconditional fresh-key realization.** Finite source admission is
   proved for an explicit `ConsistentKeys` allocation. A consistent allocator
   preserving all previously registered descriptors is not yet proved. This
   hypothesis is not owner-ID freshness and cannot be silently dropped.

Full LJ, logical Cut, copying system owners, executable summary refinement and
runtime benefit remain separate downstream obligations. D3 advances the selected
annotated-source client; D4/D5 now apply its CK/replacement machinery to that
client. D1 still needs a source logical-Cut bridge, D2 broader normalization,
and D6 a genuine presentation/material-base application.

### Final checks and independent review

Every invocation used the pinned executable above, in the POTKIN3 root, with
`LEAN_PATH` containing the existing native/package build libraries. Exact final
argument vectors were:

```text
-j1 -o .lake/build/lib/lean/Potkin/Research/D3DischargeGrouping.olean Potkin/Research/D3DischargeGrouping.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/D3SourceEncoding.olean Potkin/Research/D3SourceEncoding.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/D3SchemaPermutation.olean Potkin/Research/D3SchemaPermutation.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/D3SourcePermutation.olean Potkin/Research/D3SourcePermutation.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/D3SourceAdequacy.olean Potkin/Research/D3SourceAdequacy.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/D3RegistryAdmission.olean Potkin/Research/D3RegistryAdmission.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/D3SourceAdmission.olean Potkin/Research/D3SourceAdmission.lean
-j1 -o .lake/build/lib/lean/Potkin/Research/D3SourceCK.olean Potkin/Research/D3SourceCK.lean
```

| Module (exact basename) | Final exit | Duration | Accepted headline closures |
| --- | --- | --- | --- |
| `D3DischargeGrouping` | 0 | 70.890 s | Standard axioms only; fold invariant uses `propext`, `Quot.sound` |
| `D3SourceEncoding` | 0 | 59.410 s | Standard axioms only; formula injection/image theorem use `propext`, `Quot.sound` |
| `D3SchemaPermutation` | 0 | 58.993 s | Standard axioms only; admission/key lemmas use `propext`, `Quot.sound` |
| `D3SourcePermutation` | 0 | 69.456 s | `propext`, `Classical.choice`, `Quot.sound` |
| `D3SourceAdequacy` | 0 | 72.941 s | `propext`, `Classical.choice`, `Quot.sound` |
| `D3RegistryAdmission` | 0 | 50.055 s | Standard axioms only; lookup/lift use `propext`, `Quot.sound` |
| `D3SourceAdmission` | 0 | 44.771 s | `propext`, `Classical.choice`, `Quot.sound` |
| `D3SourceCK` | 0 | 76.328 s | `propext`, `Classical.choice`, `Quot.sound` |

“Standard axioms only” here means a subset of exactly `propext`,
`Classical.choice`, `Quot.sound`. No accepted closure contains `sorryAx` or a
custom axiom. Final source searches of these eight modules found no `sorry`,
`admit`, or custom axiom declaration. Headline statements and closures were
printed on successful final sources, not inferred from clean text.

The first registry invocation timed out at 301.101 s and its actual child was
terminated. One direct import-only diagnostic, `lean.exe -j1 --stdin` containing
`import Potkin.CompleteQuotation` and `#check ...quote_realize`, passed in
99.064 s. It isolated substantial import cost; no unchanged silent command was
repeated without diagnosis. All later checks were serialized with asynchronous
draining of both output streams, 30-second CPU/memory checkpoints and a 300-second
actual-child bound. No policy file was changed to record the exception.

Concrete unsuccessful source checks, followed only by relevant fixes:

| Module | Earlier completed failures | Correction |
| --- | --- | --- |
| Source encoding | 76.487, 75.272 s | Explicit injection function, existing finite-set import, typed component index; reducible dependent source-hole families and native nested-sum matching |
| Discharge grouping | 72.111 s | Pointwise filter congruence and exact `List.not_mem_nil` API |
| Schema permutation | 96.061 s | Removed one tactic after the goal was already solved |
| Source adequacy | 41.327 s | Qualified the independent source `Sequent`, avoiding the native namespace collision |
| Registry admission | 68.530, 38.968 s | Unpacked dependent lookup record; corrected declaration/documentation syntax |

Failed invocation axiom footers were discarded. Unused-simp/tactic warnings on
otherwise successful final sources were not treated as mathematical failures.

Independent reviewers checked source/noncircular discharge definitions,
physical multiplicity, actual formula interpretation, fixed-token filling,
registry quantifiers and novelty boundaries. Their two principal corrections
were adopted: use ordinal physical inventories rather than membership-subtype
identity, and distinguish complete source proofs from annotation-valid Boxes.
They explicitly identified the formula-action and recursive-source gates above.

No full build, full suite, Racket invocation, bounded fixture campaign, benchmark,
dependency installation, commit or push was run. Existing AGENTS.MD/README changes,
protected document relocations and all unrelated uncommitted work were preserved.

## Historical recovery report

## Outcome

**The integrated discharge-replacement milestone is not complete.** Eight
additive modules passed targeted Lean verification. They establish substantial
universal results, including an independently defined discharge relation,
native scoped cut-certificate gluing, and an actual checked implication-right
permutation under arbitrary future fillings. These are proofs, not conclusions
drawn from finite tests.

The first remaining compact-summary obligations are `exposure_fill` and
`ok_fill`. Consequently, exact equality of the entire composed summary,
realizable summary associativity, and the proposed generic replacement theorem
under arbitrary future fillings and exterior contexts are **OPEN**.

The new Sys(com) two-stage certificate diagram has a concrete elaboration
failure. A separate scoped permutation/cut application file was written but
not checked. Neither is included among the verified results.

This report consolidates the saved implementation/check record after the
disconnects. Recovery performed only focused source/provenance inspection and
documentation edits: no new Lean invocation, build, or test campaign.

## Scope and representation

The input package is `docs/discharge_proof_package/`, particularly `RESULT.txt`,
`LEAN_HANDOFF.txt`, and `unary_permutation_application.md`. Its proposed results
were treated as paper obligations, not pre-existing Lean theorems.

All constructions use existing native `CKTree`, ordered `CKChildren`, typed
interfaces, physical `LeafOccurrence`, native leaf assignments, `CKCutPlan`,
`CKCut`, and `CKBranchCut`. There is no replacement proof, cut, context, or
forest carrier. New summaries and certificate types are metadata and witnesses
over these native objects.

`OpenDischarge.Data` records exact rule-instance information, including bottom
UIDs and implication-right data. `ExactInstance`/`ExactTree` check rule shapes
independently of summary success. The represented logical fragment is identity,
internal weakening/contraction, implication-right, and the annotated Sys(com)
top/bottom rules. It is **not a mechanization of all LJ rules**, source erasure
or decorability adequacy, or full LJ with logical Cut.

The independent `Legal` relation inspects actual tree events: each top refers
to a designated bottom with the prescribed shared parameters and ordered
premise ancestry. Internal bottom declarations are unique; repeated tops and
nested distinct systems are allowed. This is not a nearest-owner convention.

Summary inventories, requirements, and exposures are finite **multisets**,
retaining occurrence multiplicities. Physical holes are ordered and addressed.
Native premise/packet order is retained separately; the compact summary does
not purport to reconstruct an ordered interleaving of hidden bottom instances.
`composeSummary` currently has a propositional correctness field and is not a
finished executable cache evaluator.

## Successfully checked modules

Paths below are relative to the repository root. Durations are those of the
successful final targeted invocations, not newly repeated checks.

| Module in `Potkin/Research/` | Newly MECHANIZED result | Final exit / duration |
| --- | --- | --- |
| `OpenDischarge.lean` | Independent exact/discharge semantics; `legality_interface_iff`; universal `exact_fill` for simultaneous typed filling. | 0 / 153.759 s |
| `OpenDischargeSummary.lean` | Address-prefix and native event filling laws, retained multiplicities, `closed_summary_agreement`, and both cross-discharge directions in `interior_append_iff`. | 0 / 91.871 s |
| `DischargeScopeGeometry.lean` | Native event-to-vertex geometry; `compatible_through_hole`; sibling and parent-to-descendant incompatibility. | 0 / 43.619 s |
| `OpenCutAssignments.lean` | Cut-created versus inherited interfaces; aligned detached assignment; literal native source reconstruction for arbitrary open sources. | 0 / 77.553 s |
| `OpenDischargeCertificates.lean` | Type-valued physical certificates; actual restriction/gluing equivalences for native cuts; inverse laws for serial remainder decomposition. | 0 / 95.223 s |
| `OpenDischargeAgreement.lean` | Soundness/completeness against independent legality for complete, exact sources with unique owners; universal scoped cut gluing. | 0 / 78.386 s |
| `OpenDischargeComposition.lean` | Native inventory/requirements/holes/conclusion filling laws and universal `native_scope_partition`, including negative ownership cases. Full compact-summary composition remains partial. | 0 / 91.474 s |
| `DischargePermutation.lean` | Actual immutable finite rule registry, checked nonvacuous source/target proofs, and legality preservation/reflection under arbitrary future fillings for the specified implication-right permutation. | 0 / 101.350 s |

### 1. Independent legality and certificate agreement

Namespace: `Potkin.Research.OpenDischargeAgreement`.
Source: `OpenDischargeAgreement.lean:544`.

```lean
theorem closed_kernel_iff_legal
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (complete : tree.IsComplete) :
    Nonempty (ClosedKernel tree [] []) ↔ Legal Imp tree [] []
```

Completeness is essential. The independent legality relation permits typed open
obligations, whereas an empty certificate provider returns `PEmpty` at an
unfilled interface. We do not manufacture a certificate for an unfilled Box.

The provider type, in `OpenDischargeCertificates.lean:26`, is:

```lean
abbrev Provider {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G) :=
  tree.LeafOccurrence → InternalAddress → List (OwnerSlot sigma) → Type (max u v)
```

A top retains an actual eligible finite ancestor position, rather than merely
a matching owner name. Bottom scope entries retain UID, physical address,
parameters, and ordered branch. Interfaces receive the unchanged pre-root
scope. A malformed bottom arity has no certificate; logical interpretation
additionally requires exact local admission.

### 2. Universal native cut gluing

Namespace: `Potkin.Research.OpenDischargeCertificates`.
Source: `OpenDischargeCertificates.lean:161`.

```lean
def branchEquiv : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (cut : CKBranchCut tree) →
    (provider : Provider tree) → (address : InternalAddress) →
    (scope : List (OwnerSlot sigma)) →
    Kernel tree provider address scope ≃
      Kernel cut.remainder (branchProvider cut provider) address scope
```

This is an equivalence of **witness types**, with restriction and gluing maps,
not equality of Prop proofs or agreement of scalar counts. It applies to native
open sources and arbitrary providers. The callback at a cut-created hole
evaluates the aligned detached factor with the scope supplied by that same
remainder certificate. Inherited holes keep their original callbacks. Detached
factors are not required to have independently closed certificates.

`OpenCutAssignments.lean` supplies the actual factor-to-hole adapter and literal
refill. Its `openDetachedAssignment_inherited` retains the original typed Box;
`fillAssignment_openDetached` reconstructs the source without pretending that
an arbitrary open source was complete. Empty descent and separate whole-branch
selection are covered by native representations, not a fabricated public root
cut.

The connection to independent rule-discharge semantics is:

```lean
theorem closed_legality_cut_gluing
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (complete : tree.IsComplete) (cut : CKBranchCut tree) :
    Legal Imp tree [] [] ↔
      Nonempty (Kernel cut.remainder (branchProvider cut (emptyProvider tree)) [] [])
```

This is `OpenDischargeAgreement.lean:564`; `proper_cut_legality_gluing` at line
580 specializes it to the public native `CKCut`. Scope choices, ordered
premises, addresses, and physical factor matching remain in the witness data.
No independent product of closed factor counts is substituted for gluing.

### 3. Composition: what is proved and what is not

`OpenDischargeComposition.lean` proves `inventory_fill`, `requirements_fill`,
`holes_fill`, and `conclusion_fill`, together with `attachment_holes`.

Its strongest new universal semantic result is `native_scope_partition`
(line 664). Under declaration freshness, internal legality after simultaneous
native filling is equivalent to:

1. Internal legality of the parent and every filler.
2. No outstanding parent demand becoming owned by a descendant filler.
3. No outstanding filler demand becoming owned inside the attached filler
   family, including a sibling.
4. Every filler demand naming a parent owner matching that hole's actual
   exposure, including its parameters and permitted branch.

References with no internal owner remain external. Freshness separates bottom
**declarations**; it does not prohibit legitimate cross-piece references.
Wrong parameters, wrong branches, hidden owners, and pre-existing input
failures are not silently turned into successful external obligations.

This proof is useful, but it is **not** the requested equality of every field
of `directSummary(fillAssignment ...)` and `composeSummary(...)`.
The exact exposure-multiset law and aggregate correctness-field law remain
missing. Accordingly, `directSummary_fill`, realizable summary associativity,
and the general replacement/cache refinement theorem are not reported proved.

### 4. Actual normalization application

Namespace: `Potkin.Research.DischargePermutation`.
Sources: `DischargePermutation.lean:451` and `:535`.

```lean
theorem open_implication_permutation (P Q : Tree GS) :
    Legal Imp (source P Q) [] [] ↔ Legal Imp (target P Q) [] []

theorem checked_future_filling_permutation (P Q : CheckedDerivation presentation GS) :
    Legal Imp (checkedSourceFor P Q).realize [] [] ↔
      Legal Imp (checkedTargetFor P Q).realize [] []
```

The source is `R(B(P,Q))`; the target is `B(R(P),R(Q))`. These quantify over
arbitrary future native fillings, not a bounded list. The outer parameters and
registered shell are a specific genuine instance, not a theorem for every
possible LJ/Sys(com) instance or every exterior context.

One immutable registry contains ten exact instances (IDs 700–709): identity,
the needed weakenings, both system tops, contraction, source bottom,
implication-right, and target bottom. Both bottoms keep UID 42 and shared
parameters `Phi={p}`, `Psi={q}`, while their common sequent changes from
`p,q => p` to `p => q -> p`. `CompleteQuotation.checkedOfComplete` constructs
the actual checked quotations; exact boundaries and incidence are verified.

Native hole addresses move from `[0,0]`, `[0,1]` to `[0,0]`, `[1,0]` in Lean's
address convention. The hole equivalence and all matching source fillings are
represented explicitly.

The nonvacuous left filler uses identity, weakening, and the first system top.
The right uses identity, two weakenings, the second top, and contraction. Both
global proofs are legal, while `left_not_closed` and `right_not_closed` show
that the detached fillers are not independently discharged. The surrounding
bottom matters. `forbidden_rule_preservation` preserves a supplied node-local
policy; this is not a general logical-Cut elimination result.

## Remaining gates and acceptance status

| Requested obligation | Status |
| --- | --- |
| A: exact compact summary adequacy/composition | **PARTIAL MECHANIZED**: field laws and complete native scope partition; `exposure_fill`, `ok_fill`, whole-summary equality and associativity remain **OPEN**. |
| B: generic replacement under all future fillings and exterior contexts | **OPEN**. Not replaced by assuming pointwise provider equivalences. The concrete permutation supplies an important instance, not the full theorem. |
| C: native CK compatibility | **MECHANIZED** cut-certificate gluing and independent legality agreement. Summary composition over every cut awaits A; the new two-description Sys(com) witness diagram is **NOT VERIFIED**. |
| D: actual implication-right application | **MECHANIZED** for the specified registered shell and arbitrary future fillings, with checked nonvacuous proofs. Its general derivation from B and the separate scoped Type-valued application remain unfinished. |
| E: optional extraction-cost formula | **NOT PURSUED**; prerequisites were not complete. |
| Executable summary composition/incremental cache | **OPEN**; no performance or workflow-completion claim. |

`DischargeCutFlags.lean` is **SOURCE-PRESENT / FAILED VERIFICATION**. Its last
targeted check exited 1 after 159.842 s: structural recursion was not accepted
for the call to `restriction_bottom ... witness` inside `restriction_plan`
(line 229 in the saved failure record). The independently defined
reassociation maps received a positive static review, but that is not a kernel
check. The attempted `restriction_branch`/`gluing_branch` closures from this
failed invocation contained `sorryAx` and are expressly rejected as evidence.
This was an elaboration failure, not a timeout or mathematical counterexample.

`DischargeCertificatePermutation.lean` is **SOURCE-PRESENT / NOT RECHECKED**.
It contains intended scoped equivalences and addressed cut/reconstruction
applications, but its author disconnected before targeted verification. None
of its declarations is credited as newly MECHANIZED here.

Existing verified right-ghost flag diagrams remain available. They do not
automatically establish these new Sys(com) diagrams.

## Independent review and corrections to the proposal

Independent work reviewed rule adequacy, physical scope geometry, global owner
transport, negative cases, and historical non-duplication. A replacement reviewer
completed and checked `OpenDischargeAgreement.lean`. Static approval of the
unverified flag/permutation files is kept distinct from Lean verification.

The principal mathematical corrections are:

- A bijection between internal owner inventories cannot generally extend to
  a global name permutation fixing every name outside the old inventory. With
  source owner 1, target owner 2, and a future reference to unbound owner 2,
  leaving that reference unchanged changes rejection into acceptance. A
  consistent global permutation must transport all declarations and references,
  or the inventory must remain fixed. The checked application keeps UID 42.
- Owner UIDs occur inside exact registered instance data. Equivariance of a raw
  rule schema alone does not prove admission in a fixed finite registry. Renamed
  instances require corresponding registrations/rechecking or explicit lifting.
- Hidden bottom identities must remain in the complete inventory. An internally
  owned but inaccessible demand is a failure, not an external demand. Demands
  targeting newly internal owners cease to be external even when ill-scoped.
- Completeness is necessary for closed legality/certificate-existence agreement.
  A typed unfilled interface is an open obligation, not a closed certificate.
- Generic replacement may reorder eligible ancestor positions. It requires
  owner-based reindexing, not an assumed identical finite position. Same-position
  transport is particular to the proposed concrete permutation application.
- The existing one-hole `K_C` does not establish a two-input operator
  `K_C(delta P, delta Q)` without a jointly admitted adapter. No such new law,
  Hopf character, forest coaction, or full coproduct invariance is claimed.

The source-rule review used [Ciabattoni–Genco, Definition 2.1 and Example 3.2](https://arxiv.org/html/1805.04852v1)
for shared parameters, repeated tops, and designated ordered branches. The
implication/parallel permutation has a historical antecedent in
[Aschieri–Ciabattoni–Genco, Figure 1 and subject-reduction case 7](https://arxiv.org/pdf/1607.05120).
No priority claim is made for the permutation itself or for a full source
translation. These were earlier task references, not new browsing during
report recovery.

## Reused work and D1–D6

Reused native dependencies include typed simultaneous filling,
`CompleteQuotation`, `CutHoleAdapter`, the existing physical
`RemainderExtractionFlags` equivalence, addressed `IteratedExtractionSums`,
right-ghost `IteratedCutCertificates`, and one-hole `ContextCutAction` laws.
Unchanged dependencies were not re-proved or subjected to a full rebuild.
The older `DependencyInterface.native_replacement` concerns fixed external
discharge information; it does not supply the missing arbitrary future-filling
quantifier for a fragment with an internal bottom.

| Direction | Advance or remaining obligation |
| --- | --- |
| D1: relative logical Cut | Scoped decomposition support is strengthened; logical-Cut elimination and the ordinary-derivation compiler remain open. CK extraction is not logical Cut. |
| D2: controlled copying/normalization | A genuine physical-hole-preserving unary permutation is checked. Arbitrary copying, correlated witnesses, and general freshening are not proved. |
| D3: actual structural lifts/admission | Ten genuine exact native instances and their quotations are checked. Full LJ/Sys(com) erasure/decorability and all-schema admission remain open. |
| D4: compositional decomposition/compilation | New independent-semantic scoped native cut gluing is mechanized; the corresponding two-stage witness diagram still has the stated elaboration gate. |
| D5: stable interfaces/reuse | Universal scope-failure partition and a future-filling application are proved. Exact compact summary composition and the reusable generic cache contract are unfinished. |
| D6: presentation/base comparison | No new base-change, material-profile, or Hopf-character theorem is asserted. |

Compared with the preceding iterated-decomposition milestone, the substantive
increment is agreement of Type-valued scoped native cut certificates with an
independently defined Sys(com) discharge relation, plus an actual logical
permutation whose future fillings can depend on its internal bottom. The
previous native cut-flag equivalence and signed context-action laws remain
dependencies, not results renamed as new.

## Verification record

The user authorized monitored 300-second targeted checks of these discharge
modules. `AGENTS.MD` was not changed to record that exception.

Executable:

```text
C:\Users\gavin\.elan\toolchains\leanprover--lean4---v4.29.0-rc1\bin\lean.exe
```

Working directory:

```text
C:\Users\gavin\Desktop\coding2023\lean_projects\potkin3
```

`LEAN_PATH` included the native `.lake/build/lib/lean` and existing immediate
package `.lake/build/lib/lean` directories. Each final module invocation used
the following exact argument pattern, with each basename from the successful
module table substituted for `MODULE`:

```text
lean.exe -j1 -o .lake/build/lib/lean/Potkin/Research/MODULE.olean Potkin/Research/MODULE.lean
```

The source files include the headline `#check`/`#print axioms` commands. A direct
child-process wrapper redirected both streams and began asynchronous draining
of both before waiting; it reported CPU/memory checkpoints and killed/waited
for the actual child on a 300-second timeout. A 60-second checkpoint was not
treated as mathematical failure.

Initial concurrent checks of `OpenDischarge` and `OpenCutAssignments` timed out
at 301.474 s and 300.779 s. Their children were terminated. One minimal import
probe isolated startup/import cost:

```text
lean.exe --stdin
```

```lean
import Potkin.Research.CutHoleAdapter
#check Potkin.CKBranchCut.fillAssignment_detached
```

It exited 0 in 165.450 s. Subsequent verification was serialized with `-j1`,
rather than repeatedly relaunching unchanged silent concurrent commands.

Concrete failed elaborations were corrected locally before the successful
final checks: reserved binders; explicit multiset coercions and reassociation;
native interface reductions; a mismatched recursive provider arity; exact
registered quotation projections; and six explicit `Events sigma` annotations.
Composition's earlier successful 84.861-second check was superseded by the
91.474-second final check including `native_scope_partition`. The flag-module
failure was not resolved or relabelled successful.

Representative successful final axiom closures:

| Declaration | Closure |
| --- | --- |
| `OpenDischarge.exact_fill` | `propext`, `Quot.sound` |
| `OpenDischarge.events_fill` | `propext`, `Quot.sound` |
| `OpenDischargeCertificates.branchEquiv` | `propext`, `Quot.sound` |
| `OpenDischargeCertificates.remainderStagesEquiv` and its two inverse laws | `propext`, `Quot.sound` |
| `OpenDischargeAgreement.closed_kernel_iff_legal` | `propext`, `Classical.choice`, `Quot.sound` |
| `OpenDischargeAgreement.closed_legality_cut_gluing` / `proper_cut_legality_gluing` | `propext`, `Classical.choice`, `Quot.sound` |
| `OpenDischarge.native_scope_partition` | `propext`, `Classical.choice`, `Quot.sound` |
| `DischargePermutation.open_implication_permutation` | `propext`, `Quot.sound` |
| `DischargePermutation.checked_future_filling_permutation` | `propext`, `Classical.choice`, `Quot.sound` |

Accepted final closures contain no `sorryAx` or custom axioms. Failed-source
footers are not accepted closures. There was no full build, full suite, Racket
execution, Python oracle campaign, or benchmark. No finite agreement was used
as proof of a universal result.

## Worktree and handoff

The branch and HEAD were retained; no commit or push was made. The existing
modified `AGENTS.MD` and `README.md`, relocated/deleted top-level documents,
and unrelated untracked native/research work were preserved. The Racket POTKIN
repository was not changed for this milestone.

The next exact proof seam is the exposure/aggregate-correctness equality in
native simultaneous filling; the separate known elaboration gate is the
`restriction_plan` structural recursion in `DischargeCutFlags.lean`. This
report records both rather than presenting the smaller completed theorems as
completion of the entire requested contract.

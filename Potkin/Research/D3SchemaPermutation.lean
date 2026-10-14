import Potkin.Research.NativeDischargeReplacement
import Potkin.CompleteQuotation

/-!
# Schema-general implication-right / Sys(com) permutation

This generalizes the admitted application, not the replacement theorem.
`Schema` contains rule-instance parameters; every proof, vacancy, ordered
assignment and exterior is an existing native object.  The implication
interpretation is an explicit premise and must be discharged by the source
formula interpretation when this module is applied to source syntax.

The three lookup keys are not system-owner identities.  Repeated target
implication occurrences share one descriptor and key but have different
physical addresses.  Source and target retain the same system UID.  Admission
is quantified over any one registry containing all three exact descriptors;
no finite registry is claimed to contain every possible schema instance.
-/

namespace Potkin.Research.D3SchemaPermutation

open OpenDischarge

universe u v
variable {sigma : Signature.{u, v}}

/-- Parameters of one actual rule-scheme application, not a proof carrier. -/
structure Schema (sigma : Signature.{u, v}) where
  gamma : Context sigma
  antecedent : Formula sigma
  consequent : Formula sigma
  result : Formula sigma
  parameters : Parameters sigma
  owner : Nat
  sourceKey : Nat
  implicationKey : Nat
  targetKey : Nat

namespace Schema

variable (s : Schema sigma)

def sourceSequent : Sequent sigma := ⟨{s.antecedent} + s.gamma, {s.consequent}⟩
def targetSequent : Sequent sigma := ⟨s.gamma, {s.result}⟩
def sourceBoundary : Hypersequent sigma := .singleton s.sourceSequent
def targetBoundary : Hypersequent sigma := .singleton s.targetSequent

private def profile (S : Sequent sigma) : ComponentProfile (.singleton S) := ⟨[S], rfl⟩

/-- Both singleton components are incident in the genuine unary inference. -/
def unaryIncidence (I O : Sequent sigma) :
    ComponentIncidence (⟨[.singleton I], .singleton O⟩ : OccurrenceShape sigma) where
  profiles := ⟨fun i => Fin.cases (profile I) (fun j => Fin.elim0 j) i, profile O⟩
  edges := {⟨⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩,
    ⟨0, by change 0 < 1; decide⟩⟩}

/-- Ordered premise 0 and premise 1 each retain their component incidence. -/
def binaryIncidence (S : Sequent sigma) :
    ComponentIncidence (⟨[.singleton S, .singleton S], .singleton S⟩ :
      OccurrenceShape sigma) where
  profiles := ⟨fun i => Fin.cases (profile S)
    (fun j => Fin.cases (profile S) (fun k => Fin.elim0 k) j) i, profile S⟩
  edges := {⟨⟨0, by change 0 < 2; decide⟩, ⟨0, by change 0 < 1; decide⟩,
      ⟨0, by change 0 < 1; decide⟩⟩,
    ⟨⟨1, by change 1 < 2; decide⟩, ⟨0, by change 0 < 1; decide⟩,
      ⟨0, by change 0 < 1; decide⟩⟩}

def implicationOccurrence : LocalOccurrence sigma (Data sigma) :=
  ⟨s.implicationKey, .logical,
    ⟨[s.sourceBoundary], s.targetBoundary⟩,
    .implicationRight s.gamma s.antecedent s.consequent s.result,
    some (unaryIncidence s.sourceSequent s.targetSequent)⟩

def sourceBottomOccurrence : LocalOccurrence sigma (Data sigma) :=
  ⟨s.sourceKey, .structural,
    ⟨[s.sourceBoundary, s.sourceBoundary], s.sourceBoundary⟩,
    .bottom s.parameters s.owner s.sourceSequent,
    some (binaryIncidence s.sourceSequent)⟩

def targetBottomOccurrence : LocalOccurrence sigma (Data sigma) :=
  ⟨s.targetKey, .structural,
    ⟨[s.targetBoundary, s.targetBoundary], s.targetBoundary⟩,
    .bottom s.parameters s.owner s.targetSequent,
    some (binaryIncidence s.targetSequent)⟩

theorem implication_exact
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (interpreted : Imp s.antecedent s.consequent s.result) :
    ExactInstance Imp s.implicationOccurrence := by
  simpa [ExactInstance, implicationOccurrence, sourceBoundary, targetBoundary,
    sourceSequent, targetSequent] using interpreted

theorem source_bottom_exact
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    ExactInstance Imp s.sourceBottomOccurrence := by
  simp [ExactInstance, sourceBottomOccurrence, sourceBoundary, sourceSequent]

theorem target_bottom_exact
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    ExactInstance Imp s.targetBottomOccurrence := by
  simp [ExactInstance, targetBottomOccurrence, targetBoundary, targetSequent]

abbrev Tree := CKTree sigma (Data sigma)

def implicationTree (P : Tree s.sourceBoundary) : Tree s.targetBoundary :=
  .ordinary s.implicationOccurrence (.cons P .nil)
def sourceBottom (P Q : Tree s.sourceBoundary) : Tree s.sourceBoundary :=
  .ordinary s.sourceBottomOccurrence (.cons P (.cons Q .nil))
def targetBottom (P Q : Tree s.targetBoundary) : Tree s.targetBoundary :=
  .ordinary s.targetBottomOccurrence (.cons P (.cons Q .nil))

def source (P Q : Tree s.sourceBoundary) : Tree s.targetBoundary :=
  s.implicationTree (s.sourceBottom P Q)
def target (P Q : Tree s.sourceBoundary) : Tree s.targetBoundary :=
  s.targetBottom (s.implicationTree P) (s.implicationTree Q)
def sourceShell : Tree s.targetBoundary :=
  s.source (.interface s.sourceBoundary) (.interface s.sourceBoundary)
def targetShell : Tree s.targetBoundary :=
  s.target (.interface s.sourceBoundary) (.interface s.sourceBoundary)

def sourceLeft : s.sourceShell.LeafOccurrence := .inl (.inl PUnit.unit)
def sourceRight : s.sourceShell.LeafOccurrence := .inl (.inr (.inl PUnit.unit))
def targetLeft : s.targetShell.LeafOccurrence := .inl (.inl PUnit.unit)
def targetRight : s.targetShell.LeafOccurrence := .inr (.inl (.inl PUnit.unit))

theorem source_left_address : s.sourceShell.leafAddress s.sourceLeft = [0, 0] := rfl
theorem source_right_address : s.sourceShell.leafAddress s.sourceRight = [0, 1] := rfl
theorem target_left_address : s.targetShell.leafAddress s.targetLeft = [0, 0] := rfl
theorem target_right_address : s.targetShell.leafAddress s.targetRight = [1, 0] := rfl

/-- Physical left/right vacancies, irrespective of equal displayed boundaries. -/
def holeEquiv : s.sourceShell.LeafOccurrence ≃ s.targetShell.LeafOccurrence where
  toFun
    | .inl (.inl h) => .inl (.inl h)
    | .inl (.inr (.inl h)) => .inr (.inl (.inl h))
    | .inl (.inr (.inr h)) => nomatch h
    | .inr h => nomatch h
  invFun
    | .inl (.inl h) => .inl (.inl h)
    | .inl (.inr h) => nomatch h
    | .inr (.inl (.inl h)) => .inl (.inr (.inl h))
    | .inr (.inl (.inr h)) => nomatch h
    | .inr (.inr h) => nomatch h
  left_inv h := by
    rcases h with (h | h)
    · rcases h with (h | h)
      · rfl
      · rcases h with (h | h)
        · rfl
        · exact nomatch h
    · exact nomatch h
  right_inv h := by
    rcases h with (h | h)
    · rcases h with (h | h)
      · rfl
      · exact nomatch h
    · rcases h with (h | h)
      · rcases h with (h | h)
        · rfl
        · exact nomatch h
      · exact nomatch h

theorem hole_boundary (h : s.sourceShell.LeafOccurrence) :
    s.sourceShell.leafBoundary h = s.targetShell.leafBoundary (s.holeEquiv h) := by
  rcases h with (h | h)
  · rcases h with (h | h)
    · rfl
    · rcases h with (h | h)
      · rfl
      · exact nomatch h
  · exact nomatch h

def sourceAssignment (P Q : Tree s.sourceBoundary) : s.sourceShell.LeafAssignment
  | .inl (.inl _) => P
  | .inl (.inr (.inl _)) => Q
  | .inl (.inr (.inr h)) => nomatch h
  | .inr h => nomatch h
def targetAssignment (P Q : Tree s.sourceBoundary) : s.targetShell.LeafAssignment
  | .inl (.inl _) => P
  | .inl (.inr h) => nomatch h
  | .inr (.inl (.inl _)) => Q
  | .inr (.inl (.inr h)) => nomatch h
  | .inr (.inr h) => nomatch h

/-- No future physical filling is excluded by the two-donor presentation. -/
theorem every_source_filling (F : s.sourceShell.LeafAssignment) :
    s.sourceShell.fillAssignment F = s.source (F s.sourceLeft) (F s.sourceRight) := rfl
theorem every_target_filling (F : s.targetShell.LeafAssignment) :
    s.targetShell.fillAssignment F = s.target (F s.targetLeft) (F s.targetRight) := rfl

theorem source_exact_iff
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (interpreted : Imp s.antecedent s.consequent s.result)
    (P Q : Tree s.sourceBoundary) :
    ExactTree Imp (s.source P Q) ↔ ExactTree Imp P ∧ ExactTree Imp Q := by
  simp [source, implicationTree, sourceBottom, ExactTree, ExactChildren,
    s.implication_exact Imp interpreted, s.source_bottom_exact Imp]

theorem target_exact_iff
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (interpreted : Imp s.antecedent s.consequent s.result)
    (P Q : Tree s.sourceBoundary) :
    ExactTree Imp (s.target P Q) ↔ ExactTree Imp P ∧ ExactTree Imp Q := by
  simp [target, implicationTree, targetBottom, ExactTree, ExactChildren,
    s.implication_exact Imp interpreted, s.target_bottom_exact Imp]

def shellGrant (address : InternalAddress) (key : Nat) : Grant sigma :=
  ⟨s.owner, address, key, s.parameters⟩

private theorem source_shell_exposure
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    (directSummary Imp s.sourceShell []).exposure =
      (exposureRows [⟨[0, 0], s.sourceBoundary⟩, ⟨[0, 1], s.sourceBoundary⟩]
        [s.shellGrant [0] s.sourceKey] : Multiset (Exposure sigma)) := rfl

private theorem target_shell_exposure
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    (directSummary Imp s.targetShell []).exposure =
      (exposureRows [⟨[0, 0], s.sourceBoundary⟩, ⟨[1, 0], s.sourceBoundary⟩]
        [s.shellGrant [] s.targetKey] : Multiset (Exposure sigma)) := rfl

/-- Uniform finite interface calculation, before any donors are supplied. -/
def implicationShell_interface
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (interpreted : Imp s.antecedent s.consequent s.result) :
    FixedOwnerInterface Imp s.sourceShell s.targetShell := by
  refine ⟨s.holeEquiv, s.hole_boundary, rfl, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    have exactSource : ExactTree Imp s.sourceShell :=
      (s.source_exact_iff Imp interpreted (.interface _) (.interface _)).mpr
        ⟨trivial, trivial⟩
    have exactTarget : ExactTree Imp s.targetShell :=
      (s.target_exact_iff Imp interpreted (.interface _) (.interface _)).mpr
        ⟨trivial, trivial⟩
    change (ExactTree Imp s.sourceShell ∧ UniqueOwners (events s.sourceShell []) ∧
      InteriorLegal (events s.sourceShell [])) ↔
      (ExactTree Imp s.targetShell ∧ UniqueOwners (events s.targetShell []) ∧
        InteriorLegal (events s.targetShell []))
    simp only [exactSource, exactTarget, true_and]
    simp [sourceShell, targetShell, source, target, implicationTree, sourceBottom,
      targetBottom, events, childEvents, rootEvents, implicationOccurrence,
      sourceBottomOccurrence, targetBottomOccurrence, Events.append,
      UniqueOwners, InteriorLegal]
  · intro hole
    rcases hole with (hole | hole)
    · rcases hole with (hole | hole)
      · cases hole
        change exposureAt (directSummary Imp s.sourceShell []) [0, 0] =
          exposureAt (directSummary Imp s.targetShell []) [0, 0]
        simp [exposureAt, s.source_shell_exposure, s.target_shell_exposure,
          eraseExposure, exposureRows, shellGrant, List.flatMap, List.map,
          List.filterMap, List.filter, List.cons.injEq]
      · rcases hole with (hole | hole)
        · cases hole
          change exposureAt (directSummary Imp s.sourceShell []) [0, 1] =
            exposureAt (directSummary Imp s.targetShell []) [1, 0]
          simp [exposureAt, s.source_shell_exposure, s.target_shell_exposure,
            eraseExposure, exposureRows, shellGrant, List.flatMap, List.map,
            List.filterMap, List.filter, List.cons.injEq]
        · exact nomatch hole
    · exact nomatch hole

/-- Failure-reflecting schema theorem: all donors and all typed exteriors,
with no freshness or successful-input hypothesis. -/
theorem implication_permutation_schema_exterior
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (interpreted : Imp s.antecedent s.consequent s.result)
    (P Q : Tree s.sourceBoundary)
    {G : Hypersequent sigma} {tree : Tree G} {address : InternalAddress}
    (context : CKTree.PunctureAt s.targetBoundary tree address) :
    Legal Imp (context.insert (s.source P Q)) [] [] ↔
      Legal Imp (context.insert (s.target P Q)) [] [] := by
  have matching (hole : s.sourceShell.LeafOccurrence) :
      HEq (s.sourceAssignment P Q hole)
        (s.targetAssignment P Q (s.holeEquiv hole)) := by
    rcases hole with (hole | hole)
    · rcases hole with (hole | hole)
      · rfl
      · rcases hole with (hole | hole)
        · rfl
        · exact nomatch hole
    · exact nomatch hole
  exact fixedOwner_replacement Imp (s.implicationShell_interface Imp interpreted)
    (s.sourceAssignment P Q) (s.targetAssignment P Q) matching context

variable {T : ProofTheory sigma (Data sigma)}

/-- Admission hypotheses are exact complete descriptor memberships, not names. -/
structure Admitted (registry : EquippedPresentation T) : Prop where
  implication : s.implicationOccurrence ∈ registry.registry
  sourceBottom : s.sourceBottomOccurrence ∈ registry.registry
  targetBottom : s.targetBottomOccurrence ∈ registry.registry

theorem source_registered {registry : EquippedPresentation T}
    (stock : s.Admitted registry) (P Q : Tree s.sourceBoundary)
    (hP : LocallyAdmittedTree registry P) (hQ : LocallyAdmittedTree registry Q) :
    LocallyAdmittedTree registry (s.source P Q) :=
  ⟨stock.implication, ⟨stock.sourceBottom, hP, hQ, trivial⟩, trivial⟩

theorem target_registered {registry : EquippedPresentation T}
    (stock : s.Admitted registry) (P Q : Tree s.sourceBoundary)
    (hP : LocallyAdmittedTree registry P) (hQ : LocallyAdmittedTree registry Q) :
    LocallyAdmittedTree registry (s.target P Q) :=
  ⟨stock.targetBottom, ⟨stock.implication, hP, trivial⟩,
    ⟨stock.implication, hQ, trivial⟩, trivial⟩

theorem admitted_exterior {registry : EquippedPresentation T}
    (stock : s.Admitted registry) (P Q : Tree s.sourceBoundary)
    (hP : LocallyAdmittedTree registry P) (hQ : LocallyAdmittedTree registry Q)
    {G : Hypersequent sigma} {tree : Tree G} {address : InternalAddress}
    (context : CKTree.PunctureAt s.targetBoundary tree address)
    (admitted : LocallyAdmittedTree registry tree) :
    LocallyAdmittedTree registry (context.insert (s.source P Q)) ∧
      LocallyAdmittedTree registry (context.insert (s.target P Q)) :=
  ⟨context.insertLocallyAdmitted admitted (s.source_registered stock P Q hP hQ),
    context.insertLocallyAdmitted admitted (s.target_registered stock P Q hP hQ)⟩

/-- Unique exact lookup forces different keys if the common sequents differ. -/
theorem bottom_keys_distinct {registry : EquippedPresentation T}
    (stock : s.Admitted registry) (different : s.sourceBoundary ≠ s.targetBoundary) :
    s.sourceKey ≠ s.targetKey := by
  intro same
  have occurrences : s.sourceBottomOccurrence = s.targetBottomOccurrence :=
    List.inj_on_of_nodup_map registry.uniqueIds stock.sourceBottom stock.targetBottom same
  exact different (congrArg (fun o => o.shape.conclusion) occurrences)

theorem source_complete (P Q : Tree s.sourceBoundary)
    (hP : P.IsComplete) (hQ : Q.IsComplete) : (s.source P Q).IsComplete :=
  ⟨⟨hP, hQ, trivial⟩, trivial⟩
theorem target_complete (P Q : Tree s.sourceBoundary)
    (hP : P.IsComplete) (hQ : Q.IsComplete) : (s.target P Q).IsComplete :=
  ⟨⟨hP, trivial⟩, ⟨hQ, trivial⟩, trivial⟩

variable [DecidableEq (Hypersequent sigma)]

/-- Both compiler outputs pass the public checker in the SAME registry. -/
def checkedSourceFor {registry : EquippedPresentation T}
    (stock : s.Admitted registry)
    (P Q : CheckedDerivation registry s.sourceBoundary) :=
  CompleteQuotation.checkedOfComplete registry (s.source P.realize Q.realize)
    (s.source_registered stock _ _ P.realizeLocallyAdmitted Q.realizeLocallyAdmitted)
    (s.source_complete _ _ P.realizeIsComplete Q.realizeIsComplete)
def checkedTargetFor {registry : EquippedPresentation T}
    (stock : s.Admitted registry)
    (P Q : CheckedDerivation registry s.sourceBoundary) :=
  CompleteQuotation.checkedOfComplete registry (s.target P.realize Q.realize)
    (s.target_registered stock _ _ P.realizeLocallyAdmitted Q.realizeLocallyAdmitted)
    (s.target_complete _ _ P.realizeIsComplete Q.realizeIsComplete)

theorem checked_schema_exterior
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (interpreted : Imp s.antecedent s.consequent s.result)
    {registry : EquippedPresentation T} (stock : s.Admitted registry)
    (P Q : CheckedDerivation registry s.sourceBoundary)
    {G : Hypersequent sigma} {tree : Tree G} {address : InternalAddress}
    (context : CKTree.PunctureAt s.targetBoundary tree address) :
    Legal Imp (context.insert (s.checkedSourceFor stock P Q).realize) [] [] ↔
      Legal Imp (context.insert (s.checkedTargetFor stock P Q).realize) [] [] := by
  rw [show (s.checkedSourceFor stock P Q).realize = s.source P.realize Q.realize from
    CompleteQuotation.quote_realize _ _ _ _]
  rw [show (s.checkedTargetFor stock P Q).realize = s.target P.realize Q.realize from
    CompleteQuotation.quote_realize _ _ _ _]
  exact s.implication_permutation_schema_exterior Imp interpreted P.realize Q.realize context

end Schema

#check @Schema.implication_permutation_schema_exterior
#check @Schema.checked_schema_exterior
#print axioms Schema.implicationShell_interface
#print axioms Schema.implication_permutation_schema_exterior
#print axioms Schema.admitted_exterior
#print axioms Schema.bottom_keys_distinct
#print axioms Schema.checked_schema_exterior

end Potkin.Research.D3SchemaPermutation

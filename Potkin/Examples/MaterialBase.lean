import Potkin.Examples.Anonymous
import Potkin.RealizedCut

/-!
# Exact occurrence-indexed material-base fixture

This small model witnesses positive-arity material admission, independence of
same-profile constructor IDs, persistent inclusion, and the absence of any
built-in Weakening, contraction, Gentzen Cut, or substitution closure.
-/

namespace Potkin.Examples.MaterialBase

open Anonymous

abbrev FixtureSignature := Anonymous.signature
abbrev FixtureData := Anonymous.InstanceData

def positiveShape : OccurrenceShape FixtureSignature :=
  ⟨[GS], GT⟩

/-- The first positive-arity material operation, identified by ID `50`. -/
def operation : LocalOccurrence FixtureSignature FixtureData where
  id := 50
  kind := .material
  shape := positiveShape
  instanceData := .merge
  incidence := none

/-- Same full boundary/instance/incidence profile, but a distinct ID. -/
def twinOperation : LocalOccurrence FixtureSignature FixtureData where
  id := 51
  kind := .material
  shape := positiveShape
  instanceData := .merge
  incidence := none

theorem operation_positive_arity : operation.arity = 1 := rfl

theorem twin_same_shape : twinOperation.shape = operation.shape := rfl

theorem twin_distinct_id : twinOperation.id ≠ operation.id := by decide

theorem positiveShape_primitive :
    positiveShape.IsPrimitiveBoundary primitiveFragment := by
  constructor
  · intro i
    exact Fin.cases GS_primitive (fun impossible => Fin.elim0 impossible) i
  · exact GT_primitive

inductive Member : LocalOccurrence FixtureSignature FixtureData -> Prop where
  | ground : Member baseSOccurrence
  | operation : Member operation

def base : MaterialBase FixtureSignature FixtureData primitiveFragment where
  Member := Member
  member_material := by
    intro o membership
    cases membership <;> rfl
  member_primitiveBoundary := by
    intro o membership
    cases membership with
    | ground => exact ⟨fun i => Fin.elim0 i, GS_primitive⟩
    | operation => exact positiveShape_primitive

def theory : ProofTheory FixtureSignature FixtureData where
  primitive := primitiveFragment
  base := base
  rules := { logical := fun _ => False, structural := fun _ => False }
  initial := fun _ => False

def presentation : EquippedPresentation theory where
  registry := [baseSOccurrence, operation]
  uniqueIds := by decide
  admitted := by
    intro o membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact .material .ground
    · exact .material .operation

def rawGround : RawDerivation FixtureSignature := .node 10 .nil

def rawPositive : RawDerivation FixtureSignature :=
  .node 50 (.cons rawGround .nil)

/-- A positive-arity material operation is registered and checked recursively. -/
theorem rawPositive_succeeds :
    CheckResult.Succeeded (presentation.checkAt GT rawPositive) := by
  decide

def checkedPositive : CheckedDerivation presentation GT :=
  CheckResult.get rawPositive_succeeds

theorem rawPositive_checks :
    presentation.checkAt GT rawPositive = .ok checkedPositive :=
  CheckResult.eq_ok_get rawPositive_succeeds

/-- Equal boundary profiles do not identify exact material occurrences. -/
theorem twin_not_member : ¬base.Member twinOperation := by
  intro membership
  cases membership

inductive ExtendedMember :
    LocalOccurrence FixtureSignature FixtureData -> Prop where
  | old {o} : Member o -> ExtendedMember o
  | extra : ExtendedMember baseTOccurrence

def extendedBase :
    MaterialBase FixtureSignature FixtureData primitiveFragment where
  Member := ExtendedMember
  member_material := by
    intro o membership
    cases membership with
    | old membership => cases membership <;> rfl
    | extra => rfl
  member_primitiveBoundary := by
    intro o membership
    cases membership with
    | old membership =>
        cases membership with
        | ground => exact ⟨fun i => Fin.elim0 i, GS_primitive⟩
        | operation => exact positiveShape_primitive
    | extra => exact ⟨fun i => Fin.elim0 i, GT_primitive⟩

def inclusion : BaseHom base extendedBase where
  map_member := ExtendedMember.old

theorem operation_survives_extension : extendedBase.Member operation :=
  inclusion.map_member .operation

/-- Extending by an unrelated occurrence does not include the same-profile twin. -/
theorem twin_not_automatically_admitted :
    ¬extendedBase.Member twinOperation := by
  intro membership
  cases membership with
  | old old => exact twin_not_member old

inductive BothMember :
    LocalOccurrence FixtureSignature FixtureData -> Prop where
  | old {o} : Member o -> BothMember o
  | twin : BothMember twinOperation

def bothBase : MaterialBase FixtureSignature FixtureData primitiveFragment where
  Member := BothMember
  member_material := by
    intro o membership
    cases membership with
    | old membership => cases membership <;> rfl
    | twin => rfl
  member_primitiveBoundary := by
    intro o membership
    cases membership with
    | old membership =>
        cases membership with
        | ground => exact ⟨fun i => Fin.elim0 i, GS_primitive⟩
        | operation => exact positiveShape_primitive
    | twin => exact positiveShape_primitive

theorem twin_independently_includable : bothBase.Member twinOperation :=
  .twin

/-! ## One explicit model with no automatic closure principles -/

def weakeningCandidate : LocalOccurrence FixtureSignature FixtureData where
  id := 60
  kind := .material
  shape := ⟨[GS], GST⟩
  instanceData := .merge
  incidence := none

def contractionCandidate : LocalOccurrence FixtureSignature FixtureData where
  id := 61
  kind := .material
  shape := ⟨[GST], GS⟩
  instanceData := .merge
  incidence := none

def cutCandidate : LocalOccurrence FixtureSignature FixtureData where
  id := 62
  kind := .material
  shape := ⟨[GS, GT], GU⟩
  instanceData := .merge
  incidence := none

def substitutedCandidate : LocalOccurrence FixtureSignature FixtureData where
  id := 63
  kind := .material
  shape := ⟨[GT], GU⟩
  instanceData := .merge
  incidence := none

theorem no_weakening_membership : ¬base.Member weakeningCandidate := by
  intro membership
  cases membership

theorem no_contraction_membership : ¬base.Member contractionCandidate := by
  intro membership
  cases membership

theorem no_cut_membership : ¬base.Member cutCandidate := by
  intro membership
  cases membership

theorem no_substitution_membership : ¬base.Member substitutedCandidate := by
  intro membership
  cases membership

theorem no_automatic_closure :
    ¬base.Member weakeningCandidate ∧
      ¬base.Member contractionCandidate ∧
      ¬base.Member cutCandidate ∧
      ¬base.Member substitutedCandidate :=
  ⟨no_weakening_membership, no_contraction_membership,
    no_cut_membership, no_substitution_membership⟩

end Potkin.Examples.MaterialBase

import Potkin.GeneralFilling
import Potkin.MaterialSupport
import Potkin.MaterialRegions
import Potkin.MaterialSupportListLaws
import Potkin.Examples.MaterialBase
import Potkin.Examples.RecursiveCut

/-!
# Exact material-support fixtures

These deterministic examples exercise occurrence-indexed material support on
very small checked or locally admitted trees.  The calculations are fixtures;
the structural statements live in `Potkin.MaterialSupport`.
-/

namespace Potkin.Examples.MaterialSupport

open Anonymous

abbrev FixtureSignature := Anonymous.signature
abbrev FixtureData := Anonymous.InstanceData

/-! ## Same-profile material occurrences remain distinct -/

/-- One presentation admitting both positive-arity material occurrences whose
profiles agree but whose registry IDs are `50` and `51`. -/
def sameProfileTheory : ProofTheory FixtureSignature FixtureData where
  primitive := Anonymous.primitiveFragment
  base := MaterialBase.bothBase
  rules := { logical := fun _ => False, structural := fun _ => False }
  initial := fun _ => False

def sameProfilePresentation : EquippedPresentation sameProfileTheory where
  registry :=
    [Anonymous.baseSOccurrence, MaterialBase.operation,
      MaterialBase.twinOperation]
  uniqueIds := by decide
  admitted := by
    intro occurrence member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .material (.old .ground)
    · exact .material (.old .operation)
    · exact .material .twin

def rawOperation : RawDerivation FixtureSignature :=
  MaterialBase.rawPositive

def rawTwin : RawDerivation FixtureSignature :=
  .node MaterialBase.twinOperation.id
    (.cons MaterialBase.rawGround .nil)

theorem rawOperation_succeeds :
    CheckResult.Succeeded
      (sameProfilePresentation.checkAt Anonymous.GT rawOperation) := by
  decide

theorem rawTwin_succeeds :
    CheckResult.Succeeded
      (sameProfilePresentation.checkAt Anonymous.GT rawTwin) := by
  decide

def checkedOperation :
    CheckedDerivation sameProfilePresentation Anonymous.GT :=
  CheckResult.get rawOperation_succeeds

def checkedTwin :
    CheckedDerivation sameProfilePresentation Anonymous.GT :=
  CheckResult.get rawTwin_succeeds

theorem checkedOperation_materialUseSummary :
    checkedOperation.materialUseSummary =
      [([], MaterialBase.operation.id),
        ([0], Anonymous.baseSOccurrence.id)] := by
  decide

theorem checkedTwin_materialUseSummary :
    checkedTwin.materialUseSummary =
      [([], MaterialBase.twinOperation.id),
        ([0], Anonymous.baseSOccurrence.id)] := by
  decide

theorem sameProfile_root_ids_remain_distinct :
    checkedOperation.materialUseSummary.head?.map (fun use => use.2) ≠
      checkedTwin.materialUseSummary.head?.map (fun use => use.2) := by
  decide

theorem sameProfile_material_use_object_counts :
    checkedOperation.materialUseList.length = 2 ∧
      checkedTwin.materialUseList.length = 2 := by
  decide

/-! ## Checked positive arity and logical interleaving -/

/-- The existing positive-arity checked proof contains its material root and
its recursively checked material premise. -/
theorem checkedPositive_materialUseSummary :
    MaterialBase.checkedPositive.materialUseSummary =
      [([], MaterialBase.operation.id),
        ([0], Anonymous.baseSOccurrence.id)] := by
  decide

theorem checkedPositive_material_use_object_count :
    MaterialBase.checkedPositive.materialUseList.length = 2 := by
  decide

/-- A logical identity-shaped bridge used only to place a logical vertex in
the premise derivation of the positive-arity material operation. -/
def logicalBridgeShape : OccurrenceShape FixtureSignature :=
  ⟨[Anonymous.GS], Anonymous.GS⟩

def logicalBridge : LocalOccurrence FixtureSignature FixtureData where
  id := 52
  kind := .logical
  shape := logicalBridgeShape
  instanceData := .lift
  incidence := none

def interleavedTheory : ProofTheory FixtureSignature FixtureData where
  primitive := Anonymous.primitiveFragment
  base := MaterialBase.base
  rules := {
    logical := fun occurrence => occurrence.id = logicalBridge.id
    structural := fun _ => False }
  initial := fun _ => False

def interleavedPresentation : EquippedPresentation interleavedTheory where
  registry :=
    [Anonymous.baseSOccurrence, MaterialBase.operation, logicalBridge]
  uniqueIds := by decide
  admitted := by
    intro occurrence member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .material .ground
    · exact .material .operation
    · exact .logical rfl rfl

def rawLogicalBridge : RawDerivation FixtureSignature :=
  .node logicalBridge.id (.cons MaterialBase.rawGround .nil)

def rawInterleaved : RawDerivation FixtureSignature :=
  .node MaterialBase.operation.id (.cons rawLogicalBridge .nil)

theorem rawInterleaved_succeeds :
    CheckResult.Succeeded
      (interleavedPresentation.checkAt Anonymous.GT rawInterleaved) := by
  decide

def checkedInterleaved :
    CheckedDerivation interleavedPresentation Anonymous.GT :=
  CheckResult.get rawInterleaved_succeeds

theorem checkedInterleaved_materialUseSummary :
    checkedInterleaved.materialUseSummary =
      [([], MaterialBase.operation.id),
        ([0, 0], Anonymous.baseSOccurrence.id)] := by
  decide

theorem checkedInterleaved_vertex_and_material_use_counts :
    checkedInterleaved.realize.degree = 3 ∧
      checkedInterleaved.materialUseList.length = 2 := by
  decide

theorem checkedInterleaved_not_wholly_material :
    ¬checkedInterleaved.realize.AllVerticesMaterial := by
  decide

theorem checkedInterleaved_not_materialDownwardClosed :
    ¬checkedInterleaved.realize.MaterialDownwardClosed := by
  intro closed
  exact checkedInterleaved_not_wholly_material
    (CKTree.MaterialDownwardClosed.allVerticesMaterial_of_rootMaterial
      closed rfl)

theorem checkedInterleaved_maximalMaterialAddresses :
    checkedInterleaved.realize.maximalMaterialAddresses = [[0, 0]] := by
  decide

/-- The material operation at the root is a genuine extracted use, but no
maximal wholly-material region contains that root. -/
theorem maximal_regions_miss_interleaved_material_root :
    [] ∈ checkedInterleaved.materialUseSummary.map (fun use => use.1) ∧
      [] ∉ checkedInterleaved.realize.maximalMaterialAddresses := by
  decide

theorem checkedPositive_is_wholly_material :
    MaterialBase.checkedPositive.realize.AllVerticesMaterial := by
  decide

theorem checkedPositive_materialDownwardClosed :
    MaterialBase.checkedPositive.realize.MaterialDownwardClosed :=
  checkedPositive_is_wholly_material.materialDownwardClosed

theorem checkedPositive_every_material_use_covered
    (use : CKTree.MaterialUse MaterialBase.base
      MaterialBase.checkedPositive.realize) :
    use.CoveredByMaximalMaterialRegion :=
  use.coveredByMaximalMaterialRegion_of_downwardClosed
    checkedPositive_materialDownwardClosed

theorem checkedPositive_maximalMaterialAddresses :
    MaterialBase.checkedPositive.realize.maximalMaterialAddresses = [[]] := by
  decide

/-! ## Persistent base extension -/

def mappedCheckedPositive :
    CheckedDerivation
      (MaterialBase.presentation.mapBase MaterialBase.inclusion) Anonymous.GT :=
  MaterialBase.checkedPositive.mapBase MaterialBase.inclusion

theorem mappedCheckedPositive_materialUseSummary :
    mappedCheckedPositive.materialUseSummary =
      [([], MaterialBase.operation.id),
        ([0], Anonymous.baseSOccurrence.id)] := by
  decide

theorem mappedCheckedPositive_material_use_object_count :
    mappedCheckedPositive.materialUseList.length = 2 := by
  decide

theorem mappedCheckedPositive_realization_literal :
    mappedCheckedPositive.realize = MaterialBase.checkedPositive.realize :=
  CheckedDerivation.realize_mapBase MaterialBase.inclusion
    MaterialBase.checkedPositive

/-! ## One-hole filling imports recursive material support -/

theorem rawGround_succeeds :
    CheckResult.Succeeded
      (MaterialBase.presentation.checkAt Anonymous.GS MaterialBase.rawGround) := by
  decide

def checkedGround :
    CheckedDerivation MaterialBase.presentation Anonymous.GS :=
  CheckResult.get rawGround_succeeds

def positiveContext :
    CKTree FixtureSignature FixtureData Anonymous.GT :=
  .ordinary MaterialBase.operation
    (.cons (.interface Anonymous.GS) .nil)

def positiveContext_locallyAdmitted :
    LocallyAdmittedTree MaterialBase.presentation positiveContext := by
  simp [positiveContext, MaterialBase.presentation,
    LocallyAdmittedTree, LocallyAdmittedChildren]

def positiveContextPuncture :
    CKTree.PunctureAt Anonymous.GS positiveContext [0] := by
  exact .child _ _ 0 [] (.head _ _ [] .root)

def filledPositive : CKTree FixtureSignature FixtureData Anonymous.GT :=
  positiveContextPuncture.insert checkedGround.realize

def filledPositive_locallyAdmitted :
    LocallyAdmittedTree MaterialBase.presentation filledPositive :=
  positiveContextPuncture.insertLocallyAdmitted
    positiveContext_locallyAdmitted checkedGround.realizeLocallyAdmitted

/-- The one-hole insertion is the exact decorated realization of the checked
positive-arity material proof. -/
theorem filledPositive_literal :
    filledPositive = MaterialBase.checkedPositive.realize := rfl

theorem positiveContext_materialUseSummary :
    positiveContext.materialUseSummary positiveContext_locallyAdmitted =
      [([], MaterialBase.operation.id)] := by
  decide

theorem checkedGround_materialUseSummary :
    checkedGround.materialUseSummary =
      [([], Anonymous.baseSOccurrence.id)] := by
  decide

theorem filledPositive_materialUseSummary :
    filledPositive.materialUseSummary filledPositive_locallyAdmitted =
      [([], MaterialBase.operation.id),
        ([0], Anonymous.baseSOccurrence.id)] := by
  decide

theorem filling_material_use_object_counts :
    (positiveContext.materialUseList
        MaterialBase.presentation positiveContext_locallyAdmitted).length = 1 ∧
      checkedGround.materialUseList.length = 1 ∧
      (filledPositive.materialUseList
        MaterialBase.presentation filledPositive_locallyAdmitted).length = 2 := by
  decide

/-! ## Equal inserted factors retain multiplicity -/

open RecursiveCut

theorem duplicate_materialUseSummary :
    checkedDuplicate.materialUseSummary =
      [([0], Anonymous.baseSOccurrence.id),
        ([1], Anonymous.baseSOccurrence.id)] := by
  decide

theorem duplicate_material_use_object_count :
    checkedDuplicate.materialUseList.length = 2 := by
  decide

def duplicateSource : RealizedOpenComponent duplicatePresentation :=
  checkedDuplicate.realizedOpenComponent

theorem duplicate_remainder_materialUseSummary :
    (duplicateSource.remainderOfCut duplicateBothCut).materialUseSummary = [] := by
  decide

theorem duplicate_detached_materialUseSummaries :
    (duplicateSource.detachedTupleOfCut duplicateBothCut).map
        RealizedOpenComponent.materialUseSummary =
      [[([], Anonymous.baseSOccurrence.id)],
        [([], Anonymous.baseSOccurrence.id)]] := by
  decide

theorem duplicate_filling_reconstructs :
    duplicateBothCut.fill duplicateBothCut.plan.detached = duplicateTree :=
  duplicateBothCut_reconstructs

/-- The universal cut-partition theorem instantiated on the two equal
detached occurrences.  This is an exact addressed-occurrence permutation;
the two identical displayed grounds remain separate list occurrences. -/
theorem duplicate_exact_cut_material_partition :
    (duplicateTree.addressedMaterialOccurrences duplicatePresentation
      checkedDuplicate.realizeLocallyAdmitted).Perm
      ((duplicateBothCut.remainder.addressedMaterialOccurrences
          duplicatePresentation
          (duplicateBothCut.remainder_locallyAdmitted
            checkedDuplicate.realizeLocallyAdmitted)) ++
        duplicateBothCut.fillerAddressedMaterialOccurrences
          duplicateBothCut.plan.detached
          (duplicateBothCut.detached_locallyAdmitted
            checkedDuplicate.realizeLocallyAdmitted)) :=
  CKCut.source_addressedMaterialOccurrences_perm_remainder_append_detached
    (cut := duplicateBothCut) checkedDuplicate.realizeLocallyAdmitted

end Potkin.Examples.MaterialSupport

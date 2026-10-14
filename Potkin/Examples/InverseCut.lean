import Potkin.InverseCut
import Potkin.Examples.MaterialRecordObstruction
import Potkin.AtomicIdentityFragment

/-! Constructor-level native fixtures; no cut-family enumeration is run.
Each example fixes its equipped presentation. No snapshot cast is used. -/
namespace Potkin.Examples.InverseCut
open Potkin
abbrev S := Anonymous.signature
abbrev D := Anonymous.InstanceData

def ground : CKTree S D Anonymous.GS := .ordinary Anonymous.baseSOccurrence .nil
def hole : CKTree S D Anonymous.GS := .interface Anonymous.GS

def unchanged : hole.LeafAssignment := fun _ => hole
def supplied : hole.LeafAssignment := fun _ => ground

theorem interface_identity : hole.fillAssignment unchanged = hole ∧
    hole.assignmentObservation unchanged = .descend (.interface Anonymous.GS) := ⟨rfl, rfl⟩

def groundEmpty : CKCut ground := ⟨trivial, .ordinary Anonymous.baseSOccurrence .nil .nil⟩
def groundWhole : CKBranchCut ground := hole.assignmentObservation supplied

theorem nullary_endpoints : groundEmpty.remainder = ground ∧
    groundEmpty.detachedTuple = [] ∧ groundWhole.remainder = hole ∧
    groundWhole.addressedTuple = [⟨[], Anonymous.GS, ground, trivial⟩] :=
  ⟨rfl, rfl, rfl, rfl⟩

def unaryOpen : CKTree S D Anonymous.GU :=
  .ordinary Anonymous.liftOccurrence (.cons (.interface Anonymous.GST) .nil)

def unaryTemplate : CKTree S D Anonymous.GU := .interface Anonymous.GU
def unaryProvider : unaryTemplate.LeafAssignment := fun _ => unaryOpen

theorem unary_open_provider : unaryTemplate.fillAssignment unaryProvider = unaryOpen ∧
    (unaryTemplate.assignmentObservation unaryProvider).remainder = unaryTemplate ∧
    unaryOpen.HasPunctureAt Anonymous.GST [0] :=
  ⟨rfl, rfl, ⟨.child _ _ 0 [] (.head _ _ [] .root)⟩⟩

theorem unary_admitted : LocallyAdmittedTree Anonymous.presentation unaryOpen :=
  ⟨by simp [Anonymous.presentation], trivial, trivial⟩

/-- Two equal-boundary physical holes in the existing registered binary cell. -/
def twoHoles : CKTree S D Anonymous.GST :=
  .ordinary RecursiveCut.duplicateOccurrence (.cons hole (.cons hole .nil))

def leftOnly : twoHoles.LeafAssignment := by
  intro h
  cases h with
  | inl _ => exact ground
  | inr h =>
      cases h with
      | inl _ => exact hole
      | inr impossible => exact nomatch impossible

def rightOnly : twoHoles.LeafAssignment := by
  intro h
  cases h with
  | inl _ => exact hole
  | inr h =>
      cases h with
      | inl _ => exact ground
      | inr impossible => exact nomatch impossible

def both : twoHoles.LeafAssignment := by
  intro h
  cases h with
  | inl _ => exact ground
  | inr h =>
      cases h with
      | inl _ => exact ground
      | inr impossible => exact nomatch impossible

def leftCut := twoHoles.assignmentProperCut (by trivial) leftOnly
def rightCut := twoHoles.assignmentProperCut (by trivial) rightOnly
def bothCut := twoHoles.assignmentProperCut (by trivial) both

theorem two_holes_admitted : LocallyAdmittedTree RecursiveCut.duplicatePresentation twoHoles :=
  ⟨by simp [RecursiveCut.duplicatePresentation], trivial, trivial, trivial⟩

theorem ground_admitted : LocallyAdmittedTree RecursiveCut.duplicatePresentation ground :=
  ⟨by simp [RecursiveCut.duplicatePresentation], trivial⟩

theorem left_providers_admitted : ∀ h, LocallyAdmittedTree RecursiveCut.duplicatePresentation (leftOnly h) := by
  intro h; cases h with
  | inl _ => exact ground_admitted
  | inr h => cases h with
      | inl _ => trivial
      | inr impossible => exact nomatch impossible

theorem left_source_admitted :
    LocallyAdmittedTree RecursiveCut.duplicatePresentation (twoHoles.fillAssignment leftOnly) :=
  twoHoles.fillAssignment_locallyAdmitted leftOnly two_holes_admitted left_providers_admitted

theorem right_providers_admitted : ∀ h, LocallyAdmittedTree RecursiveCut.duplicatePresentation (rightOnly h) := by
  intro h; cases h with
  | inl _ => trivial
  | inr h => cases h with
      | inl _ => exact ground_admitted
      | inr impossible => exact nomatch impossible

theorem both_providers_admitted : ∀ h, LocallyAdmittedTree RecursiveCut.duplicatePresentation (both h) := by
  intro h; cases h with
  | inl _ => exact ground_admitted
  | inr h => cases h with
      | inl _ => exact ground_admitted
      | inr impossible => exact nomatch impossible

theorem right_source_admitted :
    LocallyAdmittedTree RecursiveCut.duplicatePresentation (twoHoles.fillAssignment rightOnly) :=
  twoHoles.fillAssignment_locallyAdmitted rightOnly two_holes_admitted right_providers_admitted

theorem both_source_checked :
    twoHoles.fillAssignment both = RecursiveCut.checkedDuplicate.realize := rfl

theorem left_right_ambiguity :
    leftCut.remainder = twoHoles ∧ rightCut.remainder = twoHoles ∧
    leftCut.orderedAddresses = [[0]] ∧ rightCut.orderedAddresses = [[1]] ∧
    leftCut.detachedForest = rightCut.detachedForest ∧
    twoHoles.fillAssignment leftOnly ≠ twoHoles.fillAssignment rightOnly := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro equal
  have childEqual := CKTree.ordinary_children_injective RecursiveCut.duplicateOccurrence equal
  have headEqual := (CKChildren.cons.inj childEqual).1
  cases headEqual

theorem equal_provider_uses : bothCut.detachedTuple =
    [⟨[0], Anonymous.GS, ground, trivial⟩, ⟨[1], Anonymous.GS, ground, trivial⟩] ∧
    bothCut.detachedForest.card = 2 := ⟨rfl, rfl⟩

theorem singleton_values_distinct_addresses :
    leftCut.detachedTuple = [⟨[0], Anonymous.GS, ground, trivial⟩] ∧
    rightCut.detachedTuple = [⟨[1], Anonymous.GS, ground, trivial⟩] := ⟨rfl, rfl⟩

theorem native_refills : leftCut.fill leftCut.plan.detached = twoHoles.fillAssignment leftOnly ∧
    rightCut.fill rightCut.plan.detached = twoHoles.fillAssignment rightOnly ∧
    bothCut.fill bothCut.plan.detached = twoHoles.fillAssignment both :=
  ⟨leftCut.plan.fill_detached_reconstructs, rightCut.plan.fill_detached_reconstructs,
    bothCut.plan.fill_detached_reconstructs⟩

theorem reverse_left_unchanged_right :
    leftCut.plan.leafAssignment (Sum.inr (Sum.inl PUnit.unit)) = hole := rfl

/-- Existing independent AB/BA obstruction, reused without reevaluation. -/
theorem commutative_obstruction :
    MaterialRecordObstruction.cutAB.detachedForest = MaterialRecordObstruction.cutBA.detachedForest ∧
    MaterialRecordObstruction.cutAB.remainder = MaterialRecordObstruction.cutBA.remainder ∧
    RecursiveCut.tupleSummary MaterialRecordObstruction.cutAB ≠
      RecursiveCut.tupleSummary MaterialRecordObstruction.cutBA ∧
    MaterialRecordObstruction.treeAB ≠ MaterialRecordObstruction.treeBA :=
  MaterialRecordObstruction.greatest_term_loses_alignment

theorem boundary_mismatch : Anonymous.GS ≠ Anonymous.GT := by decide

theorem wrong_boundary_not_slot :
    Anonymous.checkedT.realize.rootBoundary ≠
      twoHoles.leafBoundary (Sum.inl PUnit.unit) := by
  exact Ne.symm boundary_mismatch

/-- In the actual checked unary RecursiveCut host, choose the nonroot merge
ancestor [0]. The installed sites [0,0] and [0,1] have NO inner choices. -/
def mergeAncestorChoices : RecursiveCut.bothGroundsCut.plan.ExpansionChoices
    RecursiveCut.bothGroundsCut.plan.detached := (Sum.inl PUnit.unit, PUnit.unit)

theorem recursive_ancestor_masks : ∀ site : RecursiveCut.bothGroundsCut.Site,
    RecursiveCut.bothGroundsCut.plan.expansionPayloadCut
      RecursiveCut.bothGroundsCut.plan.detached mergeAncestorChoices site = none := by
  intro site
  cases site with
  | inl site =>
      cases site with
      | inl _ => rfl
      | inr site => cases site with
          | inl _ => rfl
          | inr impossible => exact nomatch impossible
  | inr impossible => exact nomatch impossible

namespace ExactMaterial
open AtomicIdentityFragment
def openPure : Tree := binaryTree (.interface closedBoundary) tree₁
def rootHole : Tree := .interface closedBoundary
def pureProvider : rootHole.LeafAssignment := fun _ => openPure
def impureProvider : rootHole.LeafAssignment := fun _ => identityCut tree₀

theorem pure_open_admitted : LocallyAdmittedTree presentation openPure :=
  (ClosedFragment.binary .hole .ground₁).locallyAdmitted

theorem impure_provider_admitted : LocallyAdmittedTree presentation (identityCut tree₀) :=
  (ClosedFragment.identityCut .ground₀).locallyAdmitted

theorem exact_pure_open : openPure.AllVerticesInBase base :=
  ⟨.binary, trivial, ⟨.ground₁, trivial⟩, trivial⟩

theorem exact_material_accepts_open :
    (rootHole.assignmentObservation pureProvider).DetachedInBase base :=
  (rootHole.assignmentObservation_material_iff base pureProvider).mpr (fun _ => exact_pure_open)

theorem exact_material_rejects_impure :
    ¬ (rootHole.assignmentObservation impureProvider).DetachedInBase base := by
  intro pure
  have root := ((rootHole.assignmentObservation_material_iff base impureProvider).mp pure PUnit.unit).1
  cases root

theorem exact_material_interface :
    (rootHole.assignmentObservation (fun _ => rootHole)).DetachedInBase base :=
  (rootHole.assignmentObservation_material_iff base _).mpr (fun _ => trivial)

def originalChildren : CKChildren sigma Data [closedBoundary, closedBoundary] :=
  .cons tree₀ (.cons tree₁ .nil)
def installation : CKChildCuts originalChildren :=
  .cons _ _ (.detach trivial) (.cons _ _ (.detach trivial) .nil)
def compositeProviders : (site : installation.Site) → CKTree sigma Data (installation.siteBoundary site) := by
  intro site
  cases site with
  | inl _ => exact binaryTree tree₀ tree₁
  | inr site => cases site with
      | inl _ => exact binaryTree tree₁ tree₀
      | inr impossible => exact nomatch impossible

theorem installed_nested_admitted : LocallyAdmittedTree presentation
    (.ordinary materialBinary (installation.fill compositeProviders)) :=
  (ClosedFragment.binary (.binary .ground₀ .ground₁) (.binary .ground₁ .ground₀)).locallyAdmitted

/-- Selecting the retained outer ancestor suppresses EVERY internal provider
cut choice, including the nonempty internal choices of the binary providers. -/
theorem ancestor_masks_inner (site : installation.Site) :
    (CKBranchCut.descend (.ordinary materialBinary originalChildren installation)).expansionPayloadCut
      compositeProviders (.inl PUnit.unit) site = none :=
  CKBranchCut.oldAncestor_suppresses materialBinary originalChildren installation compositeProviders site
end ExactMaterial

end Potkin.Examples.InverseCut

#print axioms Potkin.Examples.InverseCut.left_right_ambiguity
#print axioms Potkin.Examples.InverseCut.equal_provider_uses
#print axioms Potkin.Examples.InverseCut.native_refills
#print axioms Potkin.Examples.InverseCut.ExactMaterial.exact_material_rejects_impure

import Potkin.MaterialRegions
import Potkin.Examples.RecursiveCut

/-!
# The greatest material term does not retain occurrence alignment

One finite native presentation checks two binary proofs with swapped,
same-boundary but distinct exact material grounds.  Their maximal material
cuts have the same decorated remainder and commutative detached forest, but
different address-aligned tuples and different native source trees.

This is an obstruction to reconstructing a rigid token-to-origin matching
from the greatest material term alone.  It is not a counterexample to an
equality of full coactions: no coaction or logical quotient is defined here.

The October 10 paper assumes persistent physical-origin names shared by
coefficient payloads and residual holes. Those additional names distinguish
the two greatest terms in its model. Native `interface` carries only its
boundary, so this example diagnoses a missing native bridge, not a refutation
of that named-seam theorem. Registered rule IDs are not physical-use IDs.
-/

namespace Potkin.Examples.MaterialRecordObstruction

open Potkin

abbrev FixtureSignature := Anonymous.signature
abbrev FixtureData := Anonymous.InstanceData

/-- A second exact ground with the complete boundary of the first ground. -/
def secondGround : LocalOccurrence FixtureSignature FixtureData where
  id := 71
  kind := .material
  shape := Anonymous.baseSShape
  instanceData := .extra
  incidence := some Anonymous.baseSKnownEmptyIncidence

inductive Member : LocalOccurrence FixtureSignature FixtureData -> Prop where
  | first : Member Anonymous.baseSOccurrence
  | second : Member secondGround

def base : MaterialBase FixtureSignature FixtureData
    Anonymous.primitiveFragment where
  Member := Member
  member_material := by
    intro occurrence membership
    cases membership <;> rfl
  member_primitiveBoundary := by
    intro occurrence membership
    cases membership <;>
      exact ⟨fun i => Fin.elim0 i, Anonymous.GS_primitive⟩

def theory : ProofTheory FixtureSignature FixtureData where
  primitive := Anonymous.primitiveFragment
  base := base
  rules := {
    logical := fun occurrence =>
      occurrence = RecursiveCut.duplicateOccurrence
    structural := fun _ => False }
  initial := fun _ => False

/-- Both proof presentations use this one immutable equipped registry. -/
def presentation : EquippedPresentation theory where
  registry :=
    [Anonymous.baseSOccurrence, secondGround,
      RecursiveCut.duplicateOccurrence]
  uniqueIds := by decide
  admitted := by
    intro occurrence member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .material .first
    · exact .material .second
    · exact .logical rfl rfl

def rawFirst : RawDerivation FixtureSignature :=
  .node Anonymous.baseSOccurrence.id .nil

def rawSecond : RawDerivation FixtureSignature :=
  .node secondGround.id .nil

def rawAB : RawDerivation FixtureSignature :=
  .node RecursiveCut.duplicateOccurrence.id
    (.cons rawFirst (.cons rawSecond .nil))

def rawBA : RawDerivation FixtureSignature :=
  .node RecursiveCut.duplicateOccurrence.id
    (.cons rawSecond (.cons rawFirst .nil))

theorem rawAB_succeeds : CheckResult.Succeeded
    (presentation.checkAt Anonymous.GST rawAB) := by decide

theorem rawBA_succeeds : CheckResult.Succeeded
    (presentation.checkAt Anonymous.GST rawBA) := by decide

def checkedAB : CheckedDerivation presentation Anonymous.GST :=
  CheckResult.get rawAB_succeeds

def checkedBA : CheckedDerivation presentation Anonymous.GST :=
  CheckResult.get rawBA_succeeds

def treeAB : CKTree FixtureSignature FixtureData Anonymous.GST :=
  checkedAB.realize

def treeBA : CKTree FixtureSignature FixtureData Anonymous.GST :=
  checkedBA.realize

theorem treeAB_not_pure : ¬ treeAB.AllVerticesMaterial := by decide
theorem treeBA_not_pure : ¬ treeBA.AllVerticesMaterial := by decide

def cutAB : CKCut treeAB :=
  treeAB.maximalMaterialCut checkedAB.realize_isOrdinary treeAB_not_pure

def cutBA : CKCut treeBA :=
  treeBA.maximalMaterialCut checkedBA.realize_isOrdinary treeBA_not_pure

theorem maximal_addresses :
    cutAB.orderedAddresses = [[0], [1]] ∧
      cutBA.orderedAddresses = [[0], [1]] := by decide

/-- Same native typed remainder, not merely the same output boundary. -/
theorem maximal_remainders_equal : cutAB.remainder = cutBA.remainder := rfl

def firstComponent : CKComponent FixtureSignature FixtureData where
  boundary := Anonymous.GS
  tree := .ordinary Anonymous.baseSOccurrence .nil
  ordinary := by trivial

def secondComponent : CKComponent FixtureSignature FixtureData where
  boundary := Anonymous.GS
  tree := .ordinary secondGround .nil
  ordinary := by trivial

theorem forestAB_literal :
    cutAB.detachedForest = {firstComponent, secondComponent} := rfl

theorem forestBA_literal :
    cutBA.detachedForest = {secondComponent, firstComponent} := rfl

/-- Collection preserves both factors but loses their two premise slots. -/
theorem maximal_forests_equal :
    cutAB.detachedForest = cutBA.detachedForest := by
  rw [forestAB_literal, forestBA_literal]
  exact Multiset.cons_swap _ _ _

theorem maximal_forest_multiplicity :
    cutAB.detachedForest.card = 2 ∧
      cutBA.detachedForest.card = 2 := by decide

theorem maximal_degrees :
    cutAB.detachedDegreeSum = 2 ∧
      cutBA.detachedDegreeSum = 2 := by decide

/-- Exact constructor IDs remain associated with distinct physical slots. -/
theorem ordered_tuple_summaries :
    RecursiveCut.tupleSummary cutAB =
      [([0], Anonymous.GS, some Anonymous.baseSOccurrence.id),
       ([1], Anonymous.GS, some secondGround.id)] ∧
    RecursiveCut.tupleSummary cutBA =
      [([0], Anonymous.GS, some secondGround.id),
       ([1], Anonymous.GS, some Anonymous.baseSOccurrence.id)] := by decide

theorem ordered_tuple_summaries_differ :
    RecursiveCut.tupleSummary cutAB ≠
      RecursiveCut.tupleSummary cutBA := by decide

def childRootIds : {boundaries : List (Hypersequent FixtureSignature)} ->
    CKChildren FixtureSignature FixtureData boundaries -> List (Option Nat)
  | _, .nil => []
  | _, .cons head tail => RecursiveCut.rootId head :: childRootIds tail

def rootChildIds : {G : Hypersequent FixtureSignature} ->
    CKTree FixtureSignature FixtureData G -> List (Option Nat)
  | _, .interface _ => []
  | _, .ordinary _ children => childRootIds children

theorem native_sources_differ : treeAB ≠ treeBA := by
  intro equal
  have same : rootChildIds treeAB = rootChildIds treeBA := congrArg rootChildIds equal
  have different : rootChildIds treeAB ≠ rootChildIds treeBA := by decide
  exact different same

theorem native_refills :
    cutAB.fill cutAB.plan.detached = treeAB ∧
      cutBA.fill cutBA.plan.detached = treeBA := by
  constructor
  · exact cutAB.plan.fill_detached_reconstructs
  · exact cutBA.plan.fill_detached_reconstructs

/-- A single greatest-term pair cannot recover a rigid addressed source. -/
theorem greatest_term_loses_alignment :
    cutAB.detachedForest = cutBA.detachedForest ∧
      cutAB.remainder = cutBA.remainder ∧
      RecursiveCut.tupleSummary cutAB ≠ RecursiveCut.tupleSummary cutBA ∧
      treeAB ≠ treeBA :=
  ⟨maximal_forests_equal, maximal_remainders_equal,
    ordered_tuple_summaries_differ, native_sources_differ⟩

end Potkin.Examples.MaterialRecordObstruction

#print axioms Potkin.Examples.MaterialRecordObstruction.greatest_term_loses_alignment
#print axioms Potkin.Examples.MaterialRecordObstruction.native_refills

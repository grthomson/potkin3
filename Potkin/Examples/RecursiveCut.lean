import Potkin.CKCutEnumeration
import Potkin.Examples.Anonymous

/-!
# Recursive CK-cut acceptance fixtures

These small anonymous fixtures exercise the occurrence-level recursive cut
API.  The exact computations below are falsification examples; reconstruction,
degree partition, and enumeration correctness are supplied by the universal
library theorems.
-/

namespace Potkin.Examples.RecursiveCut

open Potkin

abbrev FixtureSignature := Anonymous.signature
abbrev FixtureData := Anonymous.InstanceData

/-- The manuscript's running tree `i(m(bS,bT))`. -/
def runningTree :
    CKTree FixtureSignature FixtureData Anonymous.GU :=
  Anonymous.checkedUnary.realize

def runningTreeOrdinary : runningTree.IsOrdinary := by
  simpa [runningTree] using Anonymous.checkedUnary.realize_isOrdinary

/-- A literal ambient presentation of the running tree. -/
def literalMerge :
    CKTree FixtureSignature FixtureData Anonymous.GST :=
  .ordinary Anonymous.mergeOccurrence
    (.cons Anonymous.checkedS.realize
      (.cons Anonymous.checkedT.realize .nil))

def literalRunningTree :
    CKTree FixtureSignature FixtureData Anonymous.GU :=
  .ordinary Anonymous.liftOccurrence (.cons literalMerge .nil)

theorem runningTree_literal : runningTree = literalRunningTree := rfl

/-- The five generated objects are kept in the operational reference order. -/
def runningCuts : List (CKCut runningTree) :=
  CKCut.enumerate runningTree runningTreeOrdinary

def emptyCut : CKCut runningTree :=
  runningCuts.get ⟨0, by decide⟩

def wholeMergeCut : CKCut runningTree :=
  runningCuts.get ⟨1, by decide⟩

def leftGroundCut : CKCut runningTree :=
  runningCuts.get ⟨2, by decide⟩

def rightGroundCut : CKCut runningTree :=
  runningCuts.get ⟨3, by decide⟩

def bothGroundsCut : CKCut runningTree :=
  runningCuts.get ⟨4, by decide⟩

/-- Forget proof fields and expose the positive lists literally. -/
def racketSlots {G : Hypersequent FixtureSignature}
    {tree : CKTree FixtureSignature FixtureData G} (cut : CKCut tree) :
    List (List Nat) :=
  cut.orderedRacketAddresses.map RacketAddress.slots

theorem running_internal_address_family :
    runningCuts.map CKCut.orderedAddresses =
      [[], [[0]], [[0, 0]], [[0, 1]], [[0, 0], [0, 1]]] := by
  decide

theorem running_positive_address_family :
    runningCuts.map racketSlots =
      [[], [[1]], [[1, 1]], [[1, 2]], [[1, 1], [1, 2]]] := by
  decide

theorem running_cut_object_count : runningCuts.length = 5 := by
  decide

theorem running_proper_cut_object_count :
    (CKCut.enumerateProper runningTree runningTreeOrdinary).length = 4 := by
  decide

theorem emptyCut_internal : emptyCut.orderedAddresses = [] := by decide
theorem wholeMergeCut_internal : wholeMergeCut.orderedAddresses = [[0]] := by decide
theorem leftGroundCut_internal : leftGroundCut.orderedAddresses = [[0, 0]] := by decide
theorem rightGroundCut_internal : rightGroundCut.orderedAddresses = [[0, 1]] := by decide
theorem bothGroundsCut_internal :
    bothGroundsCut.orderedAddresses = [[0, 0], [0, 1]] := by decide

theorem emptyCut_positive : racketSlots emptyCut = [] := by decide
theorem wholeMergeCut_positive : racketSlots wholeMergeCut = [[1]] := by decide
theorem leftGroundCut_positive : racketSlots leftGroundCut = [[1, 1]] := by decide
theorem rightGroundCut_positive : racketSlots rightGroundCut = [[1, 2]] := by decide
theorem bothGroundsCut_positive :
    racketSlots bothGroundsCut = [[1, 1], [1, 2]] := by decide

/-- Root occurrence ID, used only to display the exact anonymous occurrence. -/
def rootId {G : Hypersequent FixtureSignature} :
    CKTree FixtureSignature FixtureData G -> Option Nat
  | .interface _ => none
  | .ordinary occurrence _ => some occurrence.id

/-- Address, exact boundary, and exact registry ID before forest collection. -/
def tupleSummary {G : Hypersequent FixtureSignature}
    {tree : CKTree FixtureSignature FixtureData G} (cut : CKCut tree) :
    List (InternalAddress × Hypersequent FixtureSignature × Option Nat) :=
  cut.detachedTuple.map fun entry =>
    (entry.address, entry.boundary, rootId entry.tree)

theorem emptyCut_tuple : tupleSummary emptyCut = [] := by decide

theorem wholeMergeCut_tuple :
    tupleSummary wholeMergeCut =
      [([0], Anonymous.GST, some Anonymous.mergeOccurrence.id)] := by
  decide

theorem leftGroundCut_tuple :
    tupleSummary leftGroundCut =
      [([0, 0], Anonymous.GS, some Anonymous.baseSOccurrence.id)] := by
  decide

theorem rightGroundCut_tuple :
    tupleSummary rightGroundCut =
      [([0, 1], Anonymous.GT, some Anonymous.baseTOccurrence.id)] := by
  decide

theorem bothGroundsCut_tuple :
    tupleSummary bothGroundsCut =
      [([0, 0], Anonymous.GS, some Anonymous.baseSOccurrence.id),
       ([0, 1], Anonymous.GT, some Anonymous.baseTOccurrence.id)] := by
  decide

def wholeMergeRemainder :
    CKTree FixtureSignature FixtureData Anonymous.GU :=
  .ordinary Anonymous.liftOccurrence
    (.cons (.interface Anonymous.GST) .nil)

def leftGroundRemainder :
    CKTree FixtureSignature FixtureData Anonymous.GU :=
  .ordinary Anonymous.liftOccurrence
    (.cons
      (.ordinary Anonymous.mergeOccurrence
        (.cons (.interface Anonymous.GS)
          (.cons Anonymous.checkedT.realize .nil)))
      .nil)

def rightGroundRemainder :
    CKTree FixtureSignature FixtureData Anonymous.GU :=
  .ordinary Anonymous.liftOccurrence
    (.cons
      (.ordinary Anonymous.mergeOccurrence
        (.cons Anonymous.checkedS.realize
          (.cons (.interface Anonymous.GT) .nil)))
      .nil)

def bothGroundsRemainder :
    CKTree FixtureSignature FixtureData Anonymous.GU :=
  .ordinary Anonymous.liftOccurrence
    (.cons
      (.ordinary Anonymous.mergeOccurrence
        (.cons (.interface Anonymous.GS)
          (.cons (.interface Anonymous.GT) .nil)))
      .nil)

theorem emptyCut_remainder_literal : emptyCut.remainder = runningTree := rfl
theorem wholeMergeCut_remainder_literal :
    wholeMergeCut.remainder = wholeMergeRemainder := rfl
theorem leftGroundCut_remainder_literal :
    leftGroundCut.remainder = leftGroundRemainder := rfl
theorem rightGroundCut_remainder_literal :
    rightGroundCut.remainder = rightGroundRemainder := rfl
theorem bothGroundsCut_remainder_literal :
    bothGroundsCut.remainder = bothGroundsRemainder := rfl

theorem reconstructs (cut : CKCut runningTree) :
    cut.fill cut.plan.detached = runningTree := by
  simpa [CKCut.fill] using cut.plan.fill_detached_reconstructs

theorem emptyCut_reconstructs :
    emptyCut.fill emptyCut.plan.detached = runningTree := reconstructs emptyCut
theorem wholeMergeCut_reconstructs :
    wholeMergeCut.fill wholeMergeCut.plan.detached = runningTree := reconstructs wholeMergeCut
theorem leftGroundCut_reconstructs :
    leftGroundCut.fill leftGroundCut.plan.detached = runningTree := reconstructs leftGroundCut
theorem rightGroundCut_reconstructs :
    rightGroundCut.fill rightGroundCut.plan.detached = runningTree := reconstructs rightGroundCut
theorem bothGroundsCut_reconstructs :
    bothGroundsCut.fill bothGroundsCut.plan.detached = runningTree := reconstructs bothGroundsCut

theorem runningTree_degree : runningTree.degree = 4 := by decide

theorem emptyCut_degree_literals :
    emptyCut.remainder.degree = 4 ∧ emptyCut.plan.detachedDegreeSum = 0 := by
  decide

theorem wholeMergeCut_degree_literals :
    wholeMergeCut.remainder.degree = 1 ∧
      wholeMergeCut.plan.detachedDegreeSum = 3 := by
  decide

theorem leftGroundCut_degree_literals :
    leftGroundCut.remainder.degree = 3 ∧
      leftGroundCut.plan.detachedDegreeSum = 1 := by
  decide

theorem rightGroundCut_degree_literals :
    rightGroundCut.remainder.degree = 3 ∧
      rightGroundCut.plan.detachedDegreeSum = 1 := by
  decide

theorem bothGroundsCut_degree_literals :
    bothGroundsCut.remainder.degree = 2 ∧
      bothGroundsCut.plan.detachedDegreeSum = 2 := by
  decide

theorem running_degree_partition (cut : CKCut runningTree) :
    runningTree.degree = cut.remainder.degree + cut.plan.detachedDegreeSum :=
  cut.plan.degree_partition

/-! ## Executable rejection and old/new puncture distinction -/

/-- Validators accept an antichain independently of the caller's list order. -/
theorem reversed_bothGrounds_accepted :
    (CKCut.validateAddresses runningTree runningTreeOrdinary
      [[0, 1], [0, 0]]).isSome = true := by
  decide

theorem reversed_bothGrounds_racket_accepted :
    (CKCut.validateRacketAddresses runningTree runningTreeOrdinary
      [InternalAddress.toRacket [0, 1],
        InternalAddress.toRacket [0, 0]]).isSome = true := by
  decide

/-- Canonicalisation sorts only; it never erases repeated requests. -/
theorem duplicate_address_request_rejected :
    (CKCut.validateAddresses runningTree runningTreeOrdinary
      [[0, 0], [0, 0]]).isNone = true := by
  decide

theorem root_address_rejected :
    (CKCut.validateAddresses runningTree runningTreeOrdinary [[]]).isNone = true := by
  decide

theorem ancestor_descendant_rejected :
    (CKCut.validateAddresses runningTree runningTreeOrdinary
      [[0], [0, 0]]).isNone = true := by
  decide

/-- An admitted open source `i(m(Box,bT))` with one old puncture. -/
def openSource :
    CKTree FixtureSignature FixtureData Anonymous.GU :=
  leftGroundRemainder

def openSourceOrdinary : openSource.IsOrdinary := by
  trivial

theorem openSource_old_puncture : openSource.InterfaceAt [0, 0] := by
  unfold openSource leftGroundRemainder
  exact .child _ _ ⟨0, by decide⟩
    (.child _ _ ⟨0, by decide⟩ (.root _))

theorem interface_address_rejected :
    (CKCut.validateAddresses openSource openSourceOrdinary
      [[0, 0]]).isNone = true := by
  decide

def openCuts : List (CKCut openSource) :=
  CKCut.enumerate openSource openSourceOrdinary

theorem open_address_family :
    openCuts.map CKCut.orderedAddresses =
      [[], [[0]], [[0, 1]]] := by
  decide

def openRightGroundCut : CKCut openSource :=
  openCuts.get ⟨2, by decide⟩

theorem openRightGroundCut_new_sites :
    openRightGroundCut.orderedAddresses = [[0, 1]] := by
  decide

theorem openRightGroundCut_remainder_literal :
    openRightGroundCut.remainder = bothGroundsRemainder := rfl

theorem openRightGroundCut_old_puncture_survives :
    openRightGroundCut.remainder.InterfaceAt [0, 0] := by
  rw [openRightGroundCut_remainder_literal]
  unfold bothGroundsRemainder
  exact .child _ _ ⟨0, by decide⟩
    (.child _ _ ⟨0, by decide⟩ (.root _))

theorem openRightGroundCut_new_puncture_created :
    openRightGroundCut.remainder.InterfaceAt [0, 1] := by
  rw [openRightGroundCut_remainder_literal]
  unfold bothGroundsRemainder
  exact .child _ _ ⟨0, by decide⟩
    (.child _ _ ⟨1, by decide⟩ (.root _))

theorem openRightGroundCut_reconstructs :
    openRightGroundCut.fill openRightGroundCut.plan.detached = openSource := by
  simpa [CKCut.fill] using openRightGroundCut.plan.fill_detached_reconstructs

/-! ## Equal detached occurrences retain multiplicity -/

def duplicateShape : OccurrenceShape FixtureSignature :=
  ⟨[Anonymous.GS, Anonymous.GS], Anonymous.GST⟩

def duplicateOccurrence : LocalOccurrence FixtureSignature FixtureData where
  id := 40
  kind := .logical
  shape := duplicateShape
  instanceData := .merge
  incidence := none

def duplicateRules : RuleSystem FixtureSignature FixtureData where
  logical := fun occurrence => occurrence.id = duplicateOccurrence.id
  structural := fun _ => False

def duplicateTheory : ProofTheory FixtureSignature FixtureData where
  base := Anonymous.materialBase
  rules := duplicateRules
  initial := fun _ => False

def duplicateAdmitsBaseS : duplicateTheory.Admits Anonymous.baseSOccurrence :=
  .material rfl rfl ⟨Anonymous.MaterialEvidence.s⟩

def duplicateAdmitsNode : duplicateTheory.Admits duplicateOccurrence :=
  .logical rfl rfl

def duplicatePresentation : EquippedPresentation duplicateTheory where
  registry := [Anonymous.baseSOccurrence, duplicateOccurrence]
  uniqueIds := by decide
  admitted := by
    intro occurrence member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact duplicateAdmitsBaseS
    · exact duplicateAdmitsNode

def rawDuplicate : RawDerivation FixtureSignature :=
  .node duplicateOccurrence.id
    (.cons Anonymous.rawS (.cons Anonymous.rawS .nil))

theorem rawDuplicate_succeeds :
    CheckResult.Succeeded
      (duplicatePresentation.checkAt Anonymous.GST rawDuplicate) := by
  decide

def checkedDuplicate :
    CheckedDerivation duplicatePresentation Anonymous.GST :=
  CheckResult.get rawDuplicate_succeeds

def duplicateTree :
    CKTree FixtureSignature FixtureData Anonymous.GST :=
  checkedDuplicate.realize

def duplicateTreeOrdinary : duplicateTree.IsOrdinary := by
  simpa [duplicateTree] using checkedDuplicate.realize_isOrdinary

def duplicateCuts : List (CKCut duplicateTree) :=
  CKCut.enumerate duplicateTree duplicateTreeOrdinary

theorem duplicate_address_family :
    duplicateCuts.map CKCut.orderedAddresses =
      [[], [[0]], [[1]], [[0], [1]]] := by
  decide

def duplicateBothCut : CKCut duplicateTree :=
  duplicateCuts.get ⟨3, by decide⟩

theorem duplicate_tuple_has_two_addressed_occurrences :
    tupleSummary duplicateBothCut =
      [([0], Anonymous.GS, some Anonymous.baseSOccurrence.id),
       ([1], Anonymous.GS, some Anonymous.baseSOccurrence.id)] := by
  decide

theorem duplicate_detached_tuple_length :
    duplicateBothCut.detachedTuple.length = 2 := by
  decide

theorem duplicate_detached_forest_card :
    duplicateBothCut.detachedForest.card = 2 := by
  decide

theorem duplicateBothCut_reconstructs :
    duplicateBothCut.fill duplicateBothCut.plan.detached = duplicateTree := by
  simpa [CKCut.fill] using duplicateBothCut.plan.fill_detached_reconstructs

end Potkin.Examples.RecursiveCut

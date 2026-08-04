import Potkin.Examples.MaterialBase
import Potkin.Examples.RecursiveCut
import Potkin.GeneralFilling
import Potkin.NestedCoherence

/-!
# P3-2 filling and nested-coherence fixtures

These examples exercise only very small concrete objects.  Universal claims
are supplied by the constructor-recursive library theorems.
-/

namespace Potkin.Examples.Coherence

open Anonymous RecursiveCut

abbrev FixtureSignature := Anonymous.signature
abbrev FixtureData := Anonymous.InstanceData

/- Executable decisions are kept local to this tiny falsification fixture. -/
local instance decidableAddressPrefix
    (left right : InternalAddress) : Decidable (AddressPrefix left right) := by
  unfold AddressPrefix
  infer_instance

local instance decidablePrefixIncomparable
    (left right : InternalAddress) :
    Decidable (PrefixIncomparable left right) := by
  unfold PrefixIncomparable
  infer_instance

local instance decidableStrictlyInside
    (inner outer : InternalAddress) : Decidable (StrictlyInside inner outer) := by
  unfold StrictlyInside
  infer_instance

local instance decidableHasInsideAddresses
    (inner outer : Finset InternalAddress) :
    Decidable (HasInsideAddresses inner outer) := by
  unfold HasInsideAddresses
  infer_instance

local instance decidableAddressFamiliesNoncrossing
    (first second : Finset InternalAddress) :
    Decidable (AddressFamiliesNoncrossing first second) := by
  unfold AddressFamiliesNoncrossing
  infer_instance

/-! ## The running nested pair -/

def runningOuter : ValidAddressCut runningTree :=
  wholeMergeCut.validAddressCut

def runningInner : ValidAddressCut runningTree :=
  bothGroundsCut.validAddressCut

theorem runningOuter_addresses : runningOuter.addresses = { [0] } := by
  decide

theorem runningInner_addresses :
    runningInner.addresses = { [0, 0], [0, 1] } := by
  decide

theorem running_noncrossing : Noncrossing runningOuter runningInner := by
  rw [noncrossing_iff_addressFamilies, runningOuter_addresses,
    runningInner_addresses]
  decide

/-- The two-branch opposite-orientation family is rejected, rather than
silently assigned one of the incompatible nesting directions. -/
theorem mixed_orientation_crossing_rejected :
    ¬ AddressFamiliesNoncrossing
      HierarchyGapFixture.mixedFirst HierarchyGapFixture.mixedSecond :=
  HierarchyGapFixture.mixed_orientation_rejected

def runningTwoStage :
    CanonicalTwoStageWitness runningOuter runningInner :=
  ⟨running_noncrossing⟩

/-- Canonical occurrence-decorated lower/middle/root decomposition of the
running `i(m(bS,bT))` proof. -/
def runningCanonicalDecomposition :=
  runningTwoStage.canonicalDecomposition

/-- The actual roots obtained in both orders are propositionally equal to one
another and to the canonical final decorated root. -/
theorem running_actual_final_roots_cohere :
    runningTwoStage.firstThenSecondRoot =
        runningTwoStage.secondThenFirstRoot ∧
      runningTwoStage.firstThenSecondRoot = runningTwoStage.finalRoot := by
  exact
    ⟨runningTwoStage.exactTwoStageRemainderCoherence.1.trans
        runningTwoStage.exactTwoStageRemainderCoherence.2.symm,
      runningTwoStage.exactTwoStageRemainderCoherence.1⟩

/-- The composed fill starts from `i(Box)`, fills `m(Box,Box)`, then fills
`bS` and `bT`, reconstructing the exact running decorated tree. -/
theorem running_canonical_composed_reconstructs :
    runningCanonicalDecomposition.composedFilling = runningTree :=
  runningCanonicalDecomposition.composedFilling_reconstructs

/-- The two staged schedules expose the same actual ordered
lower/middle/root basis data before any linearisation. -/
theorem running_schedule_region_data_cohere :
    runningTwoStage.firstScheduleRegionData =
      runningTwoStage.secondScheduleRegionData :=
  runningTwoStage.scheduleRegionData_cohere

theorem running_first_then_second_reconstructs :
    runningOuter.toCut.fill (fun site =>
      (runningTwoStage.secondInsideFirst site).toCut.fill
        (runningTwoStage.secondInsideFirst site).toCut.plan.detached) =
      runningTree :=
  runningTwoStage.first_then_second_inside_filling_reconstructs

theorem running_second_then_first_reconstructs :
    runningInner.toCut.fill (fun site =>
      (runningTwoStage.firstInsideSecond site).toCut.fill
        (runningTwoStage.firstInsideSecond site).toCut.plan.detached) =
      runningTree :=
  runningTwoStage.second_then_first_inside_filling_reconstructs

/-! ## Two genuinely incomparable cuts, in both orders -/

def siblingLeft : ValidAddressCut runningTree :=
  leftGroundCut.validAddressCut

def siblingRight : ValidAddressCut runningTree :=
  rightGroundCut.validAddressCut

theorem siblingLeft_addresses : siblingLeft.addresses = { [0, 0] } := by
  change leftGroundCut.plan.addressFinset = { [0, 0] }
  rw [leftGroundCut.addressFinset_eq_orderedAddresses_toFinset,
    leftGroundCut_internal]
  simp

theorem siblingRight_addresses : siblingRight.addresses = { [0, 1] } := by
  change rightGroundCut.plan.addressFinset = { [0, 1] }
  rw [rightGroundCut.addressFinset_eq_orderedAddresses_toFinset,
    rightGroundCut_internal]
  simp

theorem sibling_cuts_cross_incomparable :
    CrossIncomparableCuts siblingLeft siblingRight := by
  intro p pMember q qMember
  have pEq : p = [0, 0] := by
    change p ∈ leftGroundCut.plan.addressFinset at pMember
    rw [leftGroundCut.addressFinset_eq_orderedAddresses_toFinset,
      leftGroundCut_internal] at pMember
    simpa using pMember
  have qEq : q = [0, 1] := by
    change q ∈ rightGroundCut.plan.addressFinset at qMember
    rw [rightGroundCut.addressFinset_eq_orderedAddresses_toFinset,
      rightGroundCut_internal] at qMember
    simpa using qMember
  subst p
  subst q
  decide

theorem sibling_cuts_noncrossing :
    Noncrossing siblingLeft siblingRight :=
  Noncrossing.of_cross_incomparable sibling_cuts_cross_incomparable

def siblingTwoStage :
    CanonicalTwoStageWitness siblingLeft siblingRight :=
  ⟨sibling_cuts_noncrossing⟩

/-- Cutting the two independent ground branches in either order, or by the
canonical (here literal-union) frontier, produces the same actual decorated
open tree. -/
theorem sibling_actual_final_roots_cohere :
    siblingTwoStage.firstThenSecondRoot =
        siblingTwoStage.secondThenFirstRoot ∧
      siblingTwoStage.firstThenSecondRoot = siblingTwoStage.finalRoot := by
  exact
    ⟨siblingTwoStage.exactTwoStageRemainderCoherence.1.trans
        siblingTwoStage.exactTwoStageRemainderCoherence.2.symm,
      siblingTwoStage.exactTwoStageRemainderCoherence.1⟩

/-- The schedule bijection identifies actual detached decorated components,
not merely their source addresses. -/
theorem sibling_actual_detached_components_correspond
    (occurrence :
      CanonicalTwoStageWitness.FirstScheduleMiddleOccurrence siblingTwoStage) :
    siblingTwoStage.firstScheduleMiddleComponent occurrence =
      siblingTwoStage.secondScheduleMiddleComponent
        (siblingTwoStage.firstToSecondMiddleEquiv occurrence) :=
  siblingTwoStage.firstToSecondMiddleEquiv_component occurrence

/-- Staged filling from the common final root and direct filling of the
literal-union frontier agree as decorated trees. -/
theorem sibling_staged_filling_eq_direct :
    siblingTwoStage.canonicalDecomposition.composedFilling =
      siblingTwoStage.finalCut.toCut.fill
        siblingTwoStage.finalCut.toCut.plan.detached := by
  rw [siblingTwoStage.canonicalDecomposition.composedFilling_reconstructs,
    siblingTwoStage.frontier_filling_reconstructs]

/-! ## Existing holes, replacement holes, and independent insertion -/

/-- Exact left `GS` puncture of the already-open running context. -/
def leftPuncture :
    CKTree.PunctureAt Anonymous.GS bothGroundsRemainder [0, 0] := by
  unfold bothGroundsRemainder
  exact .child _ _ 0 [0]
    (.head _ _ [0]
      (.child _ _ 0 [] (.head _ _ [] .root)))

/-- Exact right `GT` puncture of the same context. -/
def rightPuncture :
    CKTree.PunctureAt Anonymous.GT bothGroundsRemainder [0, 1] := by
  unfold bothGroundsRemainder
  exact .child _ _ 0 [1]
    (.head _ _ [1]
      (.child _ _ 1 []
        (.tail _ _ 0 [] (.head _ _ [] .root))))

theorem siblingPunctures_incomparable :
    PrefixIncomparable ([0, 0] : InternalAddress) [0, 1] := by
  decide

/-- A positive-arity material context containing its own old puncture. -/
def puncturedMaterialReplacement :
    CKTree FixtureSignature FixtureData Anonymous.GT :=
  .ordinary MaterialBase.operation
    (.cons (.interface Anonymous.GS) .nil)

theorem puncturedMaterialReplacement_locallyAdmitted :
    LocallyAdmittedTree MaterialBase.presentation
      puncturedMaterialReplacement := by
  simp [puncturedMaterialReplacement, MaterialBase.presentation,
    LocallyAdmittedTree, LocallyAdmittedChildren]

def replacementPuncture :
    CKTree.PunctureAt Anonymous.GS puncturedMaterialReplacement [0] := by
  exact .child _ _ 0 [] (.head _ _ [] .root)

/-- The proof-relevant path produced by prefixing the replacement's `[0]`
address with the selected source address `[0,1]`. -/
def replacementPrefixedPuncture :
    CKTree.PunctureAt Anonymous.GS
      (rightPuncture.insert puncturedMaterialReplacement) [0, 1, 0] := by
  simpa using rightPuncture.insert_replacement replacementPuncture

/-- Inserting at `[0,1]` makes the prefixed puncture propositionally visible. -/
theorem replacement_puncture_prefixed :
    CKTree.HasPunctureAt Anonymous.GS
      (rightPuncture.insert puncturedMaterialReplacement) [0, 1, 0] :=
  ⟨replacementPrefixedPuncture⟩

/-- The proof-relevant route of the unrelated old left puncture after a
right-hand insertion. -/
def unrelatedOldPunctureAfterInsertion :
    CKTree.PunctureAt Anonymous.GS
      (rightPuncture.insert puncturedMaterialReplacement) [0, 0] :=
  rightPuncture.transportIncomparable leftPuncture
    (prefixIncomparable_symm siblingPunctures_incomparable)
    puncturedMaterialReplacement

/-- The unrelated old left puncture survives insertion on the right. -/
theorem unrelated_old_puncture_survives :
    CKTree.HasPunctureAt Anonymous.GS
      (rightPuncture.insert puncturedMaterialReplacement) [0, 0] :=
  ⟨unrelatedOldPunctureAfterInsertion⟩

/-- Independent sibling refinements commute as literal decorated trees. -/
theorem independent_refinement_interchange :
    (leftPuncture.transportIncomparable rightPuncture
        siblingPunctures_incomparable Anonymous.checkedS.realize).insert
          Anonymous.checkedT.realize =
      (rightPuncture.transportIncomparable leftPuncture
        (prefixIncomparable_symm siblingPunctures_incomparable)
        Anonymous.checkedT.realize).insert Anonymous.checkedS.realize :=
  leftPuncture.insertIncomparable_commutes rightPuncture
    siblingPunctures_incomparable Anonymous.checkedS.realize
    Anonymous.checkedT.realize

/-- Both replacement-internal frontiers have their own literal outer prefix
in the common independent-refinement result.  The left replacement is the
typed identity context, whose internal address is `[]`; the right replacement
has the genuine internal address `[0]`. -/
theorem both_replacement_frontiers_prefixed :
    CKTree.HasPunctureAt Anonymous.GS
        ((leftPuncture.transportIncomparable rightPuncture
          siblingPunctures_incomparable (.interface Anonymous.GS)).insert
            puncturedMaterialReplacement) [0, 0] ∧
      CKTree.HasPunctureAt Anonymous.GS
        ((leftPuncture.transportIncomparable rightPuncture
          siblingPunctures_incomparable (.interface Anonymous.GS)).insert
            puncturedMaterialReplacement) [0, 1, 0] :=
  leftPuncture.insertIncomparable_replacementPunctures_prefixed
    rightPuncture siblingPunctures_incomparable
    (.interface Anonymous.GS) puncturedMaterialReplacement
    (.root : CKTree.PunctureAt Anonymous.GS
      (.interface Anonymous.GS) []) replacementPuncture

/-! ## Public extensional enumeration -/

def runningExtensionalCuts : List (ExtensionalCKCut runningTree) :=
  ExtensionalCKCut.enumerate runningTree runningTreeOrdinary

theorem running_extensional_enumeration_nodup :
    runningExtensionalCuts.Nodup :=
  ExtensionalCKCut.enumerate_nodup runningTree runningTreeOrdinary

/-- Five generated cut objects, counted before any future linear collection. -/
theorem running_extensional_cut_object_count :
    runningExtensionalCuts.length = 5 := by
  decide

/-- Four generated cuts on the duplicate-factor fixture; its joint cut has
two equal detached occurrences rather than one idempotent factor. -/
theorem duplicate_cut_object_count : duplicateCuts.length = 4 := by
  decide

/-- The required outer-before-inner rank inequalities of the three-family
cycle are inconsistent. -/
theorem three_family_rank_cycle_rejected
    (rankA rankB rankC : Nat)
    (BA : rankB < rankA) (CB : rankC < rankB) (AC : rankA < rankC) : False :=
  HierarchyGapFixture.no_global_rank rankA rankB rankC BA CB AC

end Potkin.Examples.Coherence

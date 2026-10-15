import Potkin.Research.RecursiveSysComTranslation
import Potkin.Research.RecursiveSysComCuts

/-!
# Native CK certificates on the recursively computed Sys(com) target

This applies the physical substitution and cut-flag APIs to the actual target
computed from the recursive prepared source, not to an assumed origin map.
The source leaf case has a full branch frontier; it is not a fabricated proper
root cut.  The public proper frontier requires an ordinary retained scaffold.
-/
namespace Potkin.Research.RecursiveSysComCutApplication

open RecursiveSysComSource RecursiveSysComTranslation
open StructuralLemmaCuts RemainderExtractionFlags ContextCutPackets
open ContractionPostponement

abbrev Sig := RecursiveSysComTranslation.Sig
abbrev Data := RecursiveSysComTranslation.Data
abbrev Key := RecursiveSysComTranslation.Key

variable (key : Key) {S O bounds} (p : Source S O bounds)
variable (K : Multiset (Potkin.Sequent Sig))
variable (F : (o : O) → CKTree Sig Data (framed K (bounds o)))

private theorem ordinary_transport {G H : Hypersequent Sig} (equal : G = H)
    (tree : CKTree Sig Data G) : (equal ▸ tree).IsOrdinary ↔ tree.IsOrdinary := by
  cases equal
  rfl

theorem supplied_ordinary (ordinary : ∀ o, (F o).IsOrdinary)
    (h : (scaffold key p K).LeafOccurrence) :
    (supply _ (origins key p K) F h).IsOrdinary := by
  simpa only [supply, ordinary_transport] using ordinary (origins key p K h).1

theorem supplied_complete (complete : ∀ o, (F o).IsComplete)
    (h : (scaffold key p K).LeafOccurrence) :
    (supply _ (origins key p K) F h).IsComplete := by
  simpa only [supply, complete_transport] using complete (origins key p K h).1

noncomputable def actualFrontier (ordinary : ∀ o, (F o).IsOrdinary) :
    CKBranchCut (plug _ (scaffold key p K) (origins key p K) F) :=
  frontier (scaffold key p K) (supply _ (origins key p K) F)
    (supplied_ordinary key p K F ordinary)

theorem actual_frontier_remainder (ordinary : ∀ o, (F o).IsOrdinary) :
    (actualFrontier key p K F ordinary).remainder = scaffold key p K :=
  frontier_remainder _ _ _

/-- Reconstruction is the literal recursively translated proof. -/
theorem actual_frontier_refill (ordinary : ∀ o, (F o).IsOrdinary) :
    (actualFrontier key p K F ordinary).fill
      (actualFrontier key p K F ordinary).detached = translate key p K F :=
  (actualFrontier key p K F ordinary).fill_detached_reconstructs.trans
    (scaffold_fill key p K F)

noncomputable def actualProperFrontier
    (root : (scaffold key p K).IsOrdinary) (ordinary : ∀ o, (F o).IsOrdinary) :
    CKCut (plug _ (scaffold key p K) (origins key p K) F) :=
  properFrontier (scaffold key p K) root (supply _ (origins key p K) F)
    (supplied_ordinary key p K F ordinary)

/-- Exact physical multiplicity from the recursively computed copy word. -/
theorem actual_proper_factor_count
    (root : (scaffold key p K).IsOrdinary) (ordinary : ∀ o, (F o).IsOrdinary) :
    (actualProperFrontier key p K F root ordinary).plan.siteOrder.length =
      (RecursiveSysComCopy.uses p).length := by
  have copies := congrArg List.length (native_copy_word key p K)
  exact (proper_length (scaffold key p K) root (supply _ (origins key p K) F)
    (supplied_ordinary key p K F ordinary)).trans
      (by simpa only [List.length_map] using copies)

theorem actual_proper_refill
    (root : (scaffold key p K).IsOrdinary) (ordinary : ∀ o, (F o).IsOrdinary) :
    (actualProperFrontier key p K F root ordinary).fill
      (actualProperFrontier key p K F root ordinary).plan.detached = translate key p K F :=
  (actualProperFrontier key p K F root ordinary).fill_detached_reconstructs.trans
    (scaffold_fill key p K F)

/-- Exact dependent provider matching at every physical hole of the computed
target. Repeated copies of one logical donor are not collected together. -/
theorem actual_aligned_detached
    (root : (scaffold key p K).IsOrdinary) (complete : ∀ o, (F o).IsComplete) :
    alignedDetached (scaffold key p K) root (supply _ (origins key p K) F)
        (supplied_complete key p K F complete) = supply _ (origins key p K) F :=
  alignedDetached_eq _ _ _ _

/-- Donor-interior cuts and retained-assembly ancestor selections are both
accounted for by the installed native cut classification. -/
noncomputable def actualAllCutsEquiv
    (root : (scaffold key p K).IsOrdinary) (ordinary : ∀ o, (F o).IsOrdinary) :
    CKCutPlan (plug _ (scaffold key p K) (origins key p K) F) ≃
      (actualProperFrontier key p K F root ordinary).plan.ExpansionChoices
        (actualProperFrontier key p K F root ordinary).plan.detached :=
  extractionEquiv (scaffold key p K) root (supply _ (origins key p K) F)
    (supplied_ordinary key p K F ordinary)

noncomputable def actualFlag (ordinary : ∀ o, (F o).IsOrdinary)
    (inner : (site : (actualFrontier key p K F ordinary).Site) →
      CKBranchCut ((actualFrontier key p K F ordinary).detached site)) :
    BranchInside (plug _ (scaffold key p K) (origins key p K) F) :=
  ⟨actualFrontier key p K F ordinary, inner⟩

/-- The actual computed target retains two ordered physical packets and the
literal final typed remainder under the native staged-extraction bijection. -/
theorem actual_flag_outputs (ordinary : ∀ o, (F o).IsOrdinary)
    (inner : (site : (actualFrontier key p K F ordinary).Site) →
      CKBranchCut ((actualFrontier key p K F ordinary).detached site)) :
    (orderedPacket ((branchFlagEquiv _ (actualFlag key p K F ordinary inner)).1),
      orderedPacket ((branchFlagEquiv _ (actualFlag key p K F ordinary inner)).2),
      (branchFlagEquiv _ (actualFlag key p K F ordinary inner)).2.remainder) =
    (insideLowerPacket (actualFrontier key p K F ordinary) inner,
      insideMiddlePacket (actualFrontier key p K F ordinary) inner,
      insideRemainder (actualFrontier key p K F ordinary) inner) :=
  branchFlag_outputs _ (actualFlag key p K F ordinary inner)

theorem actual_flag_refill (ordinary : ∀ o, (F o).IsOrdinary)
    (inner : (site : (actualFrontier key p K F ordinary).Site) →
      CKBranchCut ((actualFrontier key p K F ordinary).detached site)) :
    (actualFrontier key p K F ordinary).fill
        (fun site => (inner site).fill (inner site).detached) = translate key p K F :=
  (inside_refill (actualFrontier key p K F ordinary) inner).trans (scaffold_fill key p K F)

theorem actual_flag_staged_refill (ordinary : ∀ o, (F o).IsOrdinary)
    (inner : (site : (actualFrontier key p K F ordinary).Site) →
      CKBranchCut ((actualFrontier key p K F ordinary).detached site)) :
    let flag := branchFlagEquiv _ (actualFlag key p K F ordinary inner)
    flag.2.fill flag.2.detached = flag.1.remainder ∧
      flag.1.fill flag.1.detached = translate key p K F := by
  have refill := remainder_refill _
    (branchFlagEquiv _ (actualFlag key p K F ordinary inner))
  exact ⟨refill.1, refill.2.trans (scaffold_fill key p K F)⟩

/-- Nested translation pieces keep the native dependent physical-copy
reindexing and concatenate absolute occurrence addresses. -/
theorem actual_nested_addresses
    (pieces : (scaffold key p K).LeafAssignment) :
    ((scaffold key p K).fillAssignment pieces).leafOrder.map
        ((scaffold key p K).fillAssignment pieces).leafAddress =
      (scaffold key p K).leafOrder.flatMap (fun h => (pieces h).leafOrder.map
        (fun k => (scaffold key p K).leafAddress h ++ (pieces h).leafAddress k)) :=
  RecursiveSysComCuts.filled_addresses _ pieces

#check @actualAllCutsEquiv
#check @actual_flag_outputs
#print axioms actual_frontier_refill
#print axioms actual_proper_factor_count
#print axioms actual_aligned_detached
#print axioms actualAllCutsEquiv
#print axioms actual_flag_outputs
#print axioms actual_flag_staged_refill

end Potkin.Research.RecursiveSysComCutApplication

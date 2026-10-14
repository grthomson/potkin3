import Potkin.Research.D3SourceAdequacy
import Potkin.Research.D3SourcePermutation
import Potkin.Research.DischargeSummaryCutEvaluation
import Potkin.Research.D3RegistryAdmission
import Potkin.Research.D3SourceAdmission

/-!
# Source application of the established CK witness bridge

The source correctness hypotheses are discharged on the source encoding image.
Physical cuts, ordered packets, factors, scopes and remainders remain native.
No detached factor is required to be independently closed. No coproduct
invariance across the implication permutation is asserted.
-/

namespace Potkin.Research.D3SourceCK
open D3SourceEncoding D3SourceAdequacy OpenDischarge
open OpenDischargeCertificates DischargeSummaryCutEvaluation
open DischargeCutFlags
open RemainderExtractionFlags ContextCutPackets

/-- All formula and system parameters are source parameters, not a finite
hand-selected instance stock. The existing native replacement theorem is used
through the actual source-encoded shell interface. -/
theorem source_implication_replacement
    (a : D3SourcePermutation.Application)
    (P Q : Diagram a.input)
    {S : D3SourceEncoding.Sequent} {E : Diagram S} {address : InternalAddress}
    (exterior : Diagram.PunctureAt a.output E address) :
    SourceCorrect (exterior.insert (a.source P Q)) ↔
      SourceCorrect (exterior.insert (a.target P Q)) := by
  rw [source_correct_iff_native, source_correct_iff_native, encode_insert, encode_insert]
  exact a.encoded_source_permutation_exterior P Q (encodePuncture exterior)

/-- Closed interpretations explicitly exclude every remaining source vacancy. -/
theorem source_implication_complete_replacement
    (a : D3SourcePermutation.Application) (P Q : Diagram a.input)
    {S : D3SourceEncoding.Sequent} {E : Diagram S} {address : InternalAddress}
    (exterior : Diagram.PunctureAt a.output E address)
    (completeSource : (exterior.insert (a.source P Q)).Complete)
    (completeTarget : (exterior.insert (a.target P Q)).Complete) :
    CompleteSourceCorrect (exterior.insert (a.source P Q)) ↔
      CompleteSourceCorrect (exterior.insert (a.target P Q)) := by
  simp only [CompleteSourceCorrect, completeSource, completeTarget, true_and]
  exact source_implication_replacement a P Q exterior

/-- Two native extraction stagings evaluate exactly the same independently
specified source discharge condition. This includes failures, not just proofs. -/
theorem source_two_stage_evaluation {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (upper : CKBranchCut (encode D))
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) :
    (SourceCorrect D ↔
      (insideSummary Imp upper inner []).ok ∧
        (insideSummary Imp upper inner []).requirements = 0) ∧
    (SourceCorrect D ↔
      (serialSummary Imp (toRemainderBranch upper inner).1
        (toRemainderBranch upper inner).2 []).ok ∧
      (serialSummary Imp (toRemainderBranch upper inner).1
        (toRemainderBranch upper inner).2 []).requirements = 0) := by
  rw [insideSummary_eq, serialSummary_eq]
  have agreement := (source_correct_iff_native D).trans
    (closed_summary_agreement Imp (encode D) [])
  exact ⟨agreement, agreement⟩

/-- The source interpretation is linked to the actual jointly scoped witness
types, with completeness, local soundness and unique declarations explicit. -/
theorem source_joint_pieces {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (locally : LocallyCorrect D)
    (unique : ((D3SourceAdequacy.events D []).bottoms.map D3SourceAdequacy.Bottom.uid).Nodup)
    (complete : D.Complete)
    (upper : CKBranchCut (encode D))
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) :
    SourceCorrect D ↔ Nonempty (Kernel upper.remainder
      (insideBranchProvider upper inner (emptyProvider (encode D))) [] []) := by
  have exactLocal := (exact_tree_iff D).mpr locally
  have nativeUnique : UniqueOwners (OpenDischarge.events (encode D) []) := by
    rw [encode_events]
    simpa [UniqueOwners, encodeEvents, List.map_map, encodeBottom] using unique
  exact (source_two_stage_evaluation D upper inner).1.trans
    (insideSummary_success_iff_pieces Imp (encode D) exactLocal nativeUnique
      ((complete_iff D).mpr complete) upper inner)

/-- Source correctness itself supplies the local and unique-owner premises;
the only extra closed interpretation premise is absence of vacancies. -/
theorem correct_source_supplies_joint_certificate {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (correct : SourceCorrect D) (complete : D.Complete)
    (upper : CKBranchCut (encode D))
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) :
    Nonempty (Kernel upper.remainder
      (insideBranchProvider upper inner (emptyProvider (encode D))) [] []) :=
  (source_joint_pieces D correct.1 correct.2.1 complete upper inner).mp correct

/-- Actual native witness coherence, not merely equality of accepted counts. -/
theorem source_restriction_diagram {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (upper : CKBranchCut (encode D))
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (provider : Provider (encode D)) (address : InternalAddress)
    (scope : List (OwnerSlot signature))
    (witness : Kernel (encode D) provider address scope) :
    insideSummary Imp upper inner address =
      serialSummary Imp (toRemainderBranch upper inner).1
        (toRemainderBranch upper inner).2 address ∧
    DischargeCutFlags.reassociateBranch upper inner provider address scope
      (DischargeCutFlags.insideBranchEquiv upper inner provider address scope witness) =
      remainderStagesEquiv (toRemainderBranch upper inner).1
        (toRemainderBranch upper inner).2 provider address scope witness :=
  summary_and_restriction_coherent Imp upper inner provider address scope witness

theorem source_gluing_diagram {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (upper : CKBranchCut (encode D))
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (provider : Provider (encode D)) (address : InternalAddress)
    (scope : List (OwnerSlot signature))
    (pieces : Kernel upper.remainder (insideBranchProvider upper inner provider) address scope) :
    insideSummary Imp upper inner address =
      serialSummary Imp (toRemainderBranch upper inner).1
        (toRemainderBranch upper inner).2 address ∧
    (remainderStagesEquiv (toRemainderBranch upper inner).1
      (toRemainderBranch upper inner).2 provider address scope).symm
      (reassociateBranch upper inner provider address scope pieces) =
      (insideBranchEquiv upper inner provider address scope).symm pieces :=
  summary_and_gluing_coherent Imp upper inner provider address scope pieces

/-- Addressed packets and literal typed remainder accompany the source result. -/
theorem source_ordered_outputs {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (flag : BranchInside (encode D)) (address : InternalAddress) :
    insideSummary Imp flag.1 flag.2 address =
      serialSummary Imp (branchFlagEquiv (encode D) flag).1
        (branchFlagEquiv (encode D) flag).2 address ∧
    (orderedPacket (branchFlagEquiv (encode D) flag).1,
      orderedPacket (branchFlagEquiv (encode D) flag).2,
      (branchFlagEquiv (encode D) flag).2.remainder) =
    (insideLowerPacket flag.1 flag.2, insideMiddlePacket flag.1 flag.2,
      insideRemainder flag.1 flag.2) :=
  summary_and_ordered_outputs_coherent Imp (encode D) flag address

#check @source_implication_replacement
#check @source_two_stage_evaluation
#check @source_joint_pieces
#check @correct_source_supplies_joint_certificate
#print axioms source_implication_replacement
#print axioms source_two_stage_evaluation
#print axioms source_joint_pieces
#print axioms correct_source_supplies_joint_certificate
#print axioms source_restriction_diagram
#print axioms source_gluing_diagram
#print axioms source_ordered_outputs
end Potkin.Research.D3SourceCK

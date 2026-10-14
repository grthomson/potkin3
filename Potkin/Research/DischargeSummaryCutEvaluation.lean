import Potkin.Research.OpenDischargeCompositionLaws
import Potkin.Research.OpenCutAssignments
import Potkin.Research.DischargeCutFlags
import Potkin.Research.OpenDischargeAgreement

/-!
# Full discharge-summary evaluation along native CK decompositions

The evaluators below actually compose the summaries of native remainders and
aligned detached factors. They are not defined to be the source's summary.
Inherited holes remain the same typed Boxes. The inner-first evaluator visits
the native upper-cut constructors in premise order; the remainder-first one
uses the existing physical flag conversion. Their equality is of every field
of `Summary`, including exposures and the failure flag, not a scalar observer.

The final diagrams combine this evaluation law with the separately
constructor-defined Type-valued certificate reassociation. No new proof, cut,
forest, or context carrier is introduced.
-/

namespace Potkin.Research.DischargeSummaryCutEvaluation

open OpenDischarge OpenDischargeCertificates DischargeCutFlags
open RemainderExtractionFlags
open ContextCutPackets

universe u v
variable {sigma : Signature.{u, v}}

/-- Recompute the root summary from its punctured remainder and actual
address-aligned factors; inherited interfaces get their original typed Box. -/
noncomputable def branchSummary
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (cut : CKBranchCut tree) (address : InternalAddress) : Summary sigma :=
  composeSummary (directSummary Imp cut.remainder address)
    (attachedSummaries Imp cut.remainder cut.openDetachedAssignment address)

theorem branchSummary_eq
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (cut : CKBranchCut tree) (address : InternalAddress) :
    branchSummary Imp cut address = directSummary Imp tree address := by
  unfold branchSummary
  rw [← directSummary_fill, cut.fillAssignment_openDetached]

/-- The public native CK-cut case. This does not manufacture a root cut. -/
noncomputable def cutSummary
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (cut : CKCut tree) (address : InternalAddress) : Summary sigma :=
  composeSummary (directSummary Imp cut.remainder address)
    (attachedSummaries Imp cut.remainder cut.plan.openDetachedAssignment address)

theorem cutSummary_eq
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (cut : CKCut tree) (address : InternalAddress) :
    cutSummary Imp cut address = directSummary Imp tree address := by
  unfold cutSummary
  rw [← directSummary_fill, cut.fillAssignment_openDetached]

mutual

/-- Inner-factor evaluations attached to the actual upper remainder slots. -/
noncomputable def insidePlanAttachments
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → {tree : CKTree sigma (Data sigma) G} →
    (upper : CKCutPlan tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) →
    InternalAddress → List (Attachment sigma)
  | G, _, .interface _, _, address =>
      [(⟨address, G⟩, directSummary Imp (.interface G) address)]
  | _, _, .ordinary _ _ children, inner, address =>
      insideChildrenAttachments Imp children inner address 0

noncomputable def insideChildrenAttachments
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → {trees : CKChildren sigma (Data sigma) Gs} →
    (upper : CKChildCuts trees) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) →
    InternalAddress → Nat → List (Attachment sigma)
  | _, _, .nil, _, _, _ => []
  | _, _, .cons _ _ head tail, inner, address, slot =>
      insideBranchAttachments Imp head (fun i => inner (.inl i)) (address ++ [slot]) ++
        insideChildrenAttachments Imp tail (fun i => inner (.inr i)) address (slot + 1)

noncomputable def insideBranchAttachments
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → {tree : CKTree sigma (Data sigma) G} →
    (upper : CKBranchCut tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) →
    InternalAddress → List (Attachment sigma)
  | G, _, .detach _, inner, address =>
      [(⟨address, G⟩, branchSummary Imp (inner PUnit.unit) address)]
  | _, _, .descend plan, inner, address =>
      insidePlanAttachments Imp plan inner address

end

mutual

theorem insidePlanAttachments_eq
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → {tree : CKTree sigma (Data sigma) G} →
    (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (address : InternalAddress) →
    insidePlanAttachments Imp upper inner address =
      attachedSummaries Imp upper.remainder upper.openDetachedAssignment address
  | _, _, .interface _, _, _ => rfl
  | _, _, .ordinary _ _ children, inner, address =>
      insideChildrenAttachments_eq Imp children inner address 0

theorem insideChildrenAttachments_eq
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → {trees : CKChildren sigma (Data sigma) Gs} →
    (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (address : InternalAddress) → (slot : Nat) →
    insideChildrenAttachments Imp upper inner address slot =
      attachedChildSummaries Imp upper.remainder upper.openDetachedAssignment address slot
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons _ _ head tail, inner, address, slot =>
      congrArg₂ List.append
        (insideBranchAttachments_eq Imp head (fun i => inner (.inl i)) (address ++ [slot]))
        (insideChildrenAttachments_eq Imp tail (fun i => inner (.inr i)) address (slot + 1))

theorem insideBranchAttachments_eq
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → {tree : CKTree sigma (Data sigma) G} →
    (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (address : InternalAddress) →
    insideBranchAttachments Imp upper inner address =
      attachedSummaries Imp upper.remainder upper.openDetachedAssignment address
  | _, _, .detach _, inner, address => by
      change [(_, branchSummary Imp (inner PUnit.unit) address)] =
        [(_, directSummary Imp _ address)]
      rw [branchSummary_eq]
      rfl
  | _, _, .descend plan, inner, address =>
      insidePlanAttachments_eq Imp plan inner address

end

noncomputable def insideSummary
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (upper : CKBranchCut tree)
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (address : InternalAddress) : Summary sigma :=
  composeSummary (directSummary Imp upper.remainder address)
    (insideBranchAttachments Imp upper inner address)

theorem insideSummary_eq
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (upper : CKBranchCut tree)
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (address : InternalAddress) :
    insideSummary Imp upper inner address = directSummary Imp tree address := by
  unfold insideSummary
  rw [insideBranchAttachments_eq, ← directSummary_fill,
    upper.fillAssignment_openDetached]

/-- Evaluate the second remainder cut, then attach the first cut's factors. -/
noncomputable def serialSummary
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (first : CKBranchCut tree) (second : CKBranchCut first.remainder)
    (address : InternalAddress) : Summary sigma :=
  composeSummary (branchSummary Imp second address)
    (attachedSummaries Imp first.remainder first.openDetachedAssignment address)

theorem serialSummary_eq
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (first : CKBranchCut tree) (second : CKBranchCut first.remainder)
    (address : InternalAddress) :
    serialSummary Imp first second address = directSummary Imp tree address := by
  unfold serialSummary
  rw [branchSummary_eq, ← directSummary_fill, first.fillAssignment_openDetached]

/-- Exact all-field summary coherence along the installed physical reindexing. -/
theorem summary_flag_diagram
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (upper : CKBranchCut tree)
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (address : InternalAddress) :
    insideSummary Imp upper inner address =
      serialSummary Imp (toRemainderBranch upper inner).1
        (toRemainderBranch upper inner).2 address := by
  rw [insideSummary_eq, serialSummary_eq]

/-- The summary equation is for the same physical flag correspondence that
retains both addressed ordered packets and the literal punctured remainder. -/
theorem summary_and_ordered_outputs_coherent
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (flag : BranchInside tree) (address : InternalAddress) :
    insideSummary Imp flag.1 flag.2 address =
      serialSummary Imp (branchFlagEquiv tree flag).1
        (branchFlagEquiv tree flag).2 address ∧
    (orderedPacket (branchFlagEquiv tree flag).1,
      orderedPacket (branchFlagEquiv tree flag).2,
      (branchFlagEquiv tree flag).2.remainder) =
    (insideLowerPacket flag.1 flag.2, insideMiddlePacket flag.1 flag.2,
      insideRemainder flag.1 flag.2) :=
  ⟨summary_flag_diagram Imp flag.1 flag.2 address, branchFlag_outputs tree flag⟩

/-- Compact evaluation accepts exactly when the actual cut pieces have a
jointly scoped certificate. This is not independent closure of the factors. -/
theorem branchSummary_success_iff_pieces
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (complete : tree.IsComplete) (cut : CKBranchCut tree) :
    (branchSummary Imp cut []).ok ∧ (branchSummary Imp cut []).requirements = 0 ↔
      Nonempty (Kernel cut.remainder (branchProvider cut (emptyProvider tree)) [] []) := by
  rw [branchSummary_eq]
  exact (closed_summary_agreement Imp tree []).symm.trans
    (OpenDischargeAgreement.closed_legality_cut_gluing Imp tree exactLocal unique complete cut)

theorem insideSummary_success_iff_pieces
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (complete : tree.IsComplete) (upper : CKBranchCut tree)
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) :
    (insideSummary Imp upper inner []).ok ∧
      (insideSummary Imp upper inner []).requirements = 0 ↔
      Nonempty (Kernel upper.remainder
        (insideBranchProvider upper inner (emptyProvider tree)) [] []) := by
  rw [insideSummary_eq]
  have agreement := (closed_summary_agreement Imp tree []).symm.trans
    (OpenDischargeAgreement.closed_kernel_iff_legal Imp tree exactLocal unique complete).symm
  constructor
  · intro accepted
    rcases agreement.mp accepted with ⟨witness⟩
    exact ⟨insideBranchEquiv upper inner (emptyProvider tree) [] [] witness⟩
  · rintro ⟨pieces⟩
    exact agreement.mpr
      ⟨(insideBranchEquiv upper inner (emptyProvider tree) [] []).symm pieces⟩

theorem serialSummary_success_iff_pieces
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (complete : tree.IsComplete) (first : CKBranchCut tree)
    (second : CKBranchCut first.remainder) :
    (serialSummary Imp first second []).ok ∧
      (serialSummary Imp first second []).requirements = 0 ↔
      Nonempty (Kernel second.remainder
        (branchProvider second (branchProvider first (emptyProvider tree))) [] []) := by
  rw [serialSummary_eq]
  have agreement := (closed_summary_agreement Imp tree []).symm.trans
    (OpenDischargeAgreement.closed_kernel_iff_legal Imp tree exactLocal unique complete).symm
  constructor
  · intro accepted
    rcases agreement.mp accepted with ⟨witness⟩
    exact ⟨remainderStagesEquiv first second (emptyProvider tree) [] [] witness⟩
  · rintro ⟨pieces⟩
    exact agreement.mpr
      ⟨(remainderStagesEquiv first second (emptyProvider tree) [] []).symm pieces⟩

/-- Full summary evaluation and the actual Type-valued restriction diagram
commute for the same native flags, absolute addresses and inherited scopes. -/
theorem summary_and_restriction_coherent
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (upper : CKBranchCut tree)
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (provider : Provider tree) (actual : InternalAddress)
    (inherited : List (OwnerSlot sigma)) (witness : Kernel tree provider actual inherited) :
    insideSummary Imp upper inner actual =
      serialSummary Imp (toRemainderBranch upper inner).1
        (toRemainderBranch upper inner).2 actual ∧
    reassociateBranch upper inner provider actual inherited
      (insideBranchEquiv upper inner provider actual inherited witness) =
      remainderStagesEquiv (toRemainderBranch upper inner).1 (toRemainderBranch upper inner).2
        provider actual inherited witness :=
  ⟨summary_flag_diagram Imp upper inner actual,
    restriction_branch upper inner provider actual inherited witness⟩

theorem summary_and_gluing_coherent
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (upper : CKBranchCut tree)
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (provider : Provider tree) (actual : InternalAddress)
    (inherited : List (OwnerSlot sigma))
    (pieces : Kernel upper.remainder (insideBranchProvider upper inner provider) actual inherited) :
    insideSummary Imp upper inner actual =
      serialSummary Imp (toRemainderBranch upper inner).1
        (toRemainderBranch upper inner).2 actual ∧
    (remainderStagesEquiv (toRemainderBranch upper inner).1 (toRemainderBranch upper inner).2
      provider actual inherited).symm
      (reassociateBranch upper inner provider actual inherited pieces) =
      (insideBranchEquiv upper inner provider actual inherited).symm pieces :=
  ⟨summary_flag_diagram Imp upper inner actual,
    gluing_branch upper inner provider actual inherited pieces⟩

#check @branchSummary_eq
#check @summary_flag_diagram
#check @summary_and_restriction_coherent
#check @summary_and_gluing_coherent
#check @insideSummary_success_iff_pieces
#check @summary_and_ordered_outputs_coherent
#print axioms branchSummary_eq
#print axioms cutSummary_eq
#print axioms insideBranchAttachments_eq
#print axioms summary_flag_diagram
#print axioms summary_and_restriction_coherent
#print axioms summary_and_gluing_coherent
#print axioms branchSummary_success_iff_pieces
#print axioms insideSummary_success_iff_pieces
#print axioms serialSummary_success_iff_pieces
#print axioms summary_and_ordered_outputs_coherent

end Potkin.Research.DischargeSummaryCutEvaluation

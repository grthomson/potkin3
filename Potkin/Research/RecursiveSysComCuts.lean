import Potkin.Research.StructuralLemmaCuts
import Potkin.Research.RemainderExtractionFlags

/-!
# Physical substitution and staged CK packets for recursive Sys(com)

All interfaces, cuts, packets and remainders below belong to the installed
native carriers.  The ordered substitution law is proved before any forest
collection, so equal donor labels and repeated equal trees keep their physical
multiplicity.  A complete donor is needed only for identifying every remainder
hole with a newly selected cut site, not for the open substitution law.
-/
namespace Potkin.Research.RecursiveSysComCuts

open StructuralLemmaCuts RemainderExtractionFlags ContextCutPackets
universe u v w r
variable {sigma : Signature.{u, v}} {D : Type w} {R : Type r}

private theorem observe_sum {α β γ : Type*} (f : α ⊕ β → γ)
    (xs : List α) (ys : List β) :
    (xs.map Sum.inl ++ ys.map Sum.inr).map f =
      xs.map (fun x => f (.inl x)) ++ ys.map (fun y => f (.inr y)) := by
  rw [List.map_append, List.map_map, List.map_map]
  rfl

private theorem flatMap_sum {α β γ : Type*} (f : α ⊕ β → List γ)
    (xs : List α) (ys : List β) :
    (xs.map Sum.inl ++ ys.map Sum.inr).flatMap f =
      xs.flatMap (fun x => f (.inl x)) ++ ys.flatMap (fun y => f (.inr y)) := by
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]

mutual

/-- Ordered physical-copy composition, with an arbitrary observation. -/
theorem leafOrder_fill : {G : Hypersequent sigma} →
    (M : CKTree sigma D G) → (F : M.LeafAssignment) →
    (obs : (M.fillAssignment F).LeafOccurrence → R) →
    (M.fillAssignment F).leafOrder.map obs =
      M.leafOrder.flatMap (fun h =>
        (F h).leafOrder.map (fun k => obs (M.fillLeafJoin F ⟨h, k⟩)))
  | _, .interface _, F, obs => by
      simp only [CKTree.fillAssignment, CKTree.PunctureAt.insert,
        CKTree.leafOrder, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rfl
  | _, .ordinary _ children, F, obs => children_leafOrder_fill children F obs

theorem children_leafOrder_fill : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma D Gs) → (F : children.LeafAssignment) →
    (obs : (children.fillAssignment F).LeafOccurrence → R) →
    (children.fillAssignment F).leafOrder.map obs =
      children.leafOrder.flatMap (fun h =>
        (F h).leafOrder.map (fun k => obs (children.fillLeafJoin F ⟨h, k⟩)))
  | _, .nil, _, _ => rfl
  | _, .cons head tail, F, obs => by
      let hf : head.LeafAssignment := fun h => F (.inl h)
      let tf : tail.LeafAssignment := fun h => F (.inr h)
      calc
        _ = (head.fillAssignment hf).leafOrder.map (fun k => obs (.inl k)) ++
              (tail.fillAssignment tf).leafOrder.map (fun k => obs (.inr k)) :=
          @observe_sum (head.fillAssignment hf).LeafOccurrence
            (tail.fillAssignment tf).LeafOccurrence R obs
            (head.fillAssignment hf).leafOrder (tail.fillAssignment tf).leafOrder
        _ = head.leafOrder.flatMap (fun h => (hf h).leafOrder.map
              (fun k => obs (.inl (head.fillLeafJoin hf ⟨h, k⟩)))) ++
            tail.leafOrder.flatMap (fun h => (tf h).leafOrder.map
              (fun k => obs (.inr (tail.fillLeafJoin tf ⟨h, k⟩)))) :=
          congrArg₂ List.append
            (leafOrder_fill head hf (fun k => obs (.inl k)))
            (children_leafOrder_fill tail tf (fun k => obs (.inr k)))
        _ = _ :=
          (@flatMap_sum head.LeafOccurrence tail.LeafOccurrence R
            (fun h => (F h).leafOrder.map
              (fun k => obs ((CKChildren.cons head tail).fillLeafJoin F ⟨h, k⟩)))
            head.leafOrder tail.leafOrder).symm

end

/-- Addresses are concatenated through physical substitution, not recovered
from a commutatively collected coefficient. -/
theorem filled_addresses {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) :
    (M.fillAssignment F).leafOrder.map (M.fillAssignment F).leafAddress =
      M.leafOrder.flatMap (fun h => (F h).leafOrder.map
        (fun k => M.leafAddress h ++ (F h).leafAddress k)) := by
  rw [leafOrder_fill]
  simp only [CKTree.fillLeafJoin_address]

theorem filled_boundaries {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) :
    (M.fillAssignment F).leafOrder.map (M.fillAssignment F).leafBoundary =
      M.leafOrder.flatMap (fun h => (F h).leafOrder.map (F h).leafBoundary) := by
  rw [leafOrder_fill]
  simp only [CKTree.fillLeafJoin_boundary]

/-- Every physical occurrence contributes, including multiple occurrences of
the same logical donor.  This is not a distinct-label cardinality. -/
theorem filled_copy_count {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) :
    (M.fillAssignment F).leafOrder.length =
      (M.leafOrder.map (fun h => (F h).leafOrder.length)).sum := by
  have ordered := leafOrder_fill M F (fun _ => (PUnit.unit : PUnit.{1}))
  have lengths := congrArg List.length ordered
  simpa only [List.length_map, List.length_flatMap] using lengths

/-- Native physical occurrence reindexing has actual inverse maps; it is not
an arbitrary source-to-target label function supplied as an assumption. -/
def physicalCopyEquiv {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) :
    (M.fillAssignment F).LeafOccurrence ≃
      Σ h : M.LeafOccurrence, (F h).LeafOccurrence := M.filledLeafEquiv F

theorem physicalCopy_address {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) (h : M.LeafOccurrence) (k : (F h).LeafOccurrence) :
    (M.fillAssignment F).leafAddress ((physicalCopyEquiv M F).symm ⟨h, k⟩) =
      M.leafAddress h ++ (F h).leafAddress k := M.fillLeafJoin_address F h k

theorem physicalCopy_boundary {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) (h : M.LeafOccurrence) (k : (F h).LeafOccurrence) :
    (M.fillAssignment F).leafBoundary ((physicalCopyEquiv M F).symm ⟨h, k⟩) =
      (F h).leafBoundary k := M.fillLeafJoin_boundary F h k

/-- Actual nested filling agrees with one-shot filling under the installed
physical reindexing; neither route forgets the intermediate matching. -/
theorem staged_filling {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) (H : (M.fillAssignment F).LeafAssignment) :
    (M.fillAssignment F).fillAssignment H =
      M.fillAssignment (M.composeLeafAssignment F H) := M.fillAssignment_assoc F H

/-- The two-stage flag is formed on this actual filled native tree and its
actual donor frontier, including ordinary whole-branch selection internally. -/
def frontierFlag {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) (ordinary : ∀ h, (F h).IsOrdinary)
    (inner : (site : (frontier M F ordinary).Site) →
      CKBranchCut ((frontier M F ordinary).detached site)) :
    BranchInside (M.fillAssignment F) := ⟨frontier M F ordinary, inner⟩

/-- Literal TWO ordered packets and final typed remainder commute under the
native cut-flag reindexing.  No tensor or cardinality projection is substituted
for these outputs. -/
theorem frontier_flag_outputs {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) (ordinary : ∀ h, (F h).IsOrdinary)
    (inner : (site : (frontier M F ordinary).Site) →
      CKBranchCut ((frontier M F ordinary).detached site)) :
    (orderedPacket ((branchFlagEquiv (M.fillAssignment F)
        (frontierFlag M F ordinary inner)).1),
      orderedPacket ((branchFlagEquiv (M.fillAssignment F)
        (frontierFlag M F ordinary inner)).2),
      (branchFlagEquiv (M.fillAssignment F) (frontierFlag M F ordinary inner)).2.remainder) =
    (insideLowerPacket (frontier M F ordinary) inner,
      insideMiddlePacket (frontier M F ordinary) inner,
      insideRemainder (frontier M F ordinary) inner) :=
  branchFlag_outputs (M.fillAssignment F) (frontierFlag M F ordinary inner)

theorem frontier_flag_refill {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) (ordinary : ∀ h, (F h).IsOrdinary)
    (inner : (site : (frontier M F ordinary).Site) →
      CKBranchCut ((frontier M F ordinary).detached site)) :
    (frontier M F ordinary).fill (fun site => (inner site).fill (inner site).detached) =
      M.fillAssignment F := inside_refill (frontier M F ordinary) inner

theorem frontier_flag_staged_refill {G : Hypersequent sigma} (M : CKTree sigma D G)
    (F : M.LeafAssignment) (ordinary : ∀ h, (F h).IsOrdinary)
    (inner : (site : (frontier M F ordinary).Site) →
      CKBranchCut ((frontier M F ordinary).detached site)) :
    let flag := branchFlagEquiv (M.fillAssignment F) (frontierFlag M F ordinary inner)
    flag.2.fill flag.2.detached = flag.1.remainder ∧
      flag.1.fill flag.1.detached = M.fillAssignment F :=
  remainder_refill (M.fillAssignment F)
    (branchFlagEquiv (M.fillAssignment F) (frontierFlag M F ordinary inner))

#print axioms leafOrder_fill
#print axioms filled_addresses
#print axioms filled_copy_count
#print axioms frontier_flag_outputs
#print axioms frontier_flag_refill

end Potkin.Research.RecursiveSysComCuts

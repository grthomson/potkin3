import Potkin.Research.CutCertificateFlags
import Potkin.Research.CertificateCutGluing
import Potkin.Research.CertificateContinuationComposition

/-!
# Certificate restriction along native inside-factor cut flags

The intermediate remainders below may be open.  Their holes are never
identified with the sites of the first cut.  Instead every second assignment
is the existing detached assignment of its own native branch cut, carried
through the ordered constructors of the first remainder.
-/

namespace Potkin

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual

/-- The actual second filling family at each physical first-remainder hole.
Whole lower branches are supported by the native `detach` constructor. -/
def CKCutPlan.lowerPhysicalAssignments : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (complete : tree.IsComplete) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (hole : first.remainder.LeafOccurrence) →
    (first.siteFillersToLeaves complete (fun i => (lower i).remainder) hole).LeafAssignment
  | _, _, .interface _, complete, _, _ => False.elim complete
  | _, _, .ordinary _ _ children, complete, lower, hole =>
      children.lowerPhysicalAssignments complete lower hole

def CKChildCuts.lowerPhysicalAssignments : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (complete : children.IsComplete) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (hole : first.remainder.LeafOccurrence) →
    (first.siteFillersToLeaves complete (fun i => (lower i).remainder) hole).LeafAssignment
  | _, _, .nil, _, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, complete, lower, hole =>
      match hole with
      | .inl hole => head.lowerPhysicalAssignments complete.1 (fun i => lower (.inl i)) hole
      | .inr hole => tail.lowerPhysicalAssignments complete.2 (fun i => lower (.inr i)) hole

def CKBranchCut.lowerPhysicalAssignments : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (complete : tree.IsComplete) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (hole : first.remainder.LeafOccurrence) →
    (first.siteFillersToLeaves complete (fun i => (lower i).remainder) hole).LeafAssignment
  | _, _, .detach _, complete, lower, _ =>
      (lower PUnit.unit).detachedLeafAssignment complete
  | _, _, .descend plan, complete, lower, hole =>
      plan.lowerPhysicalAssignments complete lower hole

end

mutual

/-- Filling each open lower remainder with its own aligned factors recovers
the corresponding first detached factor, as a literal native tree equality. -/
theorem CKCutPlan.lowerPhysicalAssignments_refill : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (complete : tree.IsComplete) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (hole : first.remainder.LeafOccurrence) →
    (first.siteFillersToLeaves complete (fun i => (lower i).remainder) hole).fillAssignment
      (first.lowerPhysicalAssignments complete lower hole) =
      first.detachedLeafAssignment complete hole
  | _, _, .interface _, complete, _, _ => False.elim complete
  | _, _, .ordinary _ _ children, complete, lower, hole =>
      children.lowerPhysicalAssignments_refill complete lower hole

theorem CKChildCuts.lowerPhysicalAssignments_refill : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (complete : children.IsComplete) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (hole : first.remainder.LeafOccurrence) →
    (first.siteFillersToLeaves complete (fun i => (lower i).remainder) hole).fillAssignment
      (first.lowerPhysicalAssignments complete lower hole) =
      first.detachedLeafAssignment complete hole
  | _, _, .nil, _, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, complete, lower, hole => by
      cases hole with
      | inl hole => exact head.lowerPhysicalAssignments_refill complete.1 (fun i => lower (.inl i)) hole
      | inr hole => exact tail.lowerPhysicalAssignments_refill complete.2 (fun i => lower (.inr i)) hole

theorem CKBranchCut.lowerPhysicalAssignments_refill : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (complete : tree.IsComplete) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (hole : first.remainder.LeafOccurrence) →
    (first.siteFillersToLeaves complete (fun i => (lower i).remainder) hole).fillAssignment
      (first.lowerPhysicalAssignments complete lower hole) =
      first.detachedLeafAssignment complete hole
  | _, _, .detach _, complete, lower, _ =>
      (lower PUnit.unit).fillAssignment_detached complete
  | _, _, .descend plan, complete, lower, hole =>
      plan.lowerPhysicalAssignments_refill complete lower hole

end

theorem CKCutPlan.lowerPhysicalAssignments_family {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (first : CKCutPlan tree)
    (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    (fun hole =>
      (first.siteFillersToLeaves complete (fun i => (lower i).remainder) hole).fillAssignment
        (first.lowerPhysicalAssignments complete lower hole)) =
      first.detachedLeafAssignment complete := by
  funext hole
  exact first.lowerPhysicalAssignments_refill complete lower hole

end Potkin

namespace Potkin.Research.CertificateFlagGluing

open RevivalInterface OpenCertificateKernel CertificateContinuationComposition

mutual

/-- Independently constructed restriction through an open intermediate
context.  No inverse of an existing restriction map defines this map. -/
def flatRestrictionEquiv : {G : Hypersequent sigma} →
    (context : CKTree sigma Data G) → (middle : context.LeafAssignment) →
    (lower : (context.fillAssignment middle).LeafAssignment) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    ClosedKernel ((context.fillAssignment middle).fillAssignment lower) address scope ≃
      Kernel context
        (factorProvider context middle
          (factorClosedProvider (context.fillAssignment middle) lower)) address scope
  | _, .interface _, middle, lower, address, scope =>
      fillEquiv (middle PUnit.unit) lower address scope
  | _, .ordinary o children, middle, lower, address, scope => by
      cases label : o.instanceData <;>
        simp only [ClosedKernel, CKTree.fillAssignment, Kernel, label]
      all_goals first
        | exact ghostDoubleFillEquiv children _ _ _ _
        | exact flatOwnerRestrictionEquiv children middle lower address _
        | exact flatChildrenRestrictionEquiv children middle lower address 0 _

def ghostDoubleFillEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (colour : Atom) →
    (scope : List OwnerSlot) → (middle : children.LeafAssignment) →
    (lower : (children.fillAssignment middle).LeafAssignment) →
    GhostKernel ((children.fillAssignment middle).fillAssignment lower) colour scope ≃
      GhostKernel children colour scope
  | _, .nil, _, _, _, _ => Equiv.refl _
  | _, .cons _ _, _, _, _, _ => Equiv.refl _

def flatChildrenRestrictionEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (middle : children.LeafAssignment) →
    (lower : (children.fillAssignment middle).LeafAssignment) →
    (address : InternalAddress) → (slot : Nat) → (scope : List OwnerSlot) →
    ChildrenKernel ((children.fillAssignment middle).fillAssignment lower)
      (fun _ _ _ => PEmpty) address slot scope ≃
      ChildrenKernel children
        (childFactorProvider children middle
          (fun hole actual inherited => ClosedKernel (lower hole) actual inherited))
        address slot scope
  | _, .nil, _, _, _, _, _ => Equiv.refl _
  | _, .cons head tail, middle, lower, address, slot, scope =>
      Equiv.prodCongr
        (flatRestrictionEquiv head (fun h => middle (.inl h))
          (fun h => lower (.inl h)) (address ++ [slot]) scope)
        (flatChildrenRestrictionEquiv tail (fun h => middle (.inr h))
          (fun h => lower (.inr h)) address (slot + 1) scope)

def flatOwnerRestrictionEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (middle : children.LeafAssignment) →
    (lower : (children.fillAssignment middle).LeafAssignment) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    OwnerKernel ((children.fillAssignment middle).fillAssignment lower)
      (fun _ _ _ => PEmpty) address scope ≃
      OwnerKernel children
        (childFactorProvider children middle
          (fun hole actual inherited => ClosedKernel (lower hole) actual inherited))
        address scope
  | _, .nil, _, _, _, _ => Equiv.refl _
  | _, .cons _ .nil, _, _, _, _ => Equiv.refl _
  | _, .cons left (.cons right .nil), middle, lower, address, scope =>
      Equiv.sigmaCongrRight fun colour => Equiv.prodCongr
        (flatRestrictionEquiv left (fun h => middle (.inl h))
          (fun h => lower (.inl h)) (address ++ [0])
          (enterOwner address colour false scope))
        (flatRestrictionEquiv right (fun h => middle (.inr (.inl h)))
          (fun h => lower (.inr (.inl h))) (address ++ [1])
          (enterOwner address colour true scope))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _ => Equiv.refl _

end

theorem ghostDoubleFill_coherence {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs) (colour : Atom) (scope : List OwnerSlot)
    (middle : children.LeafAssignment)
    (lower : (children.fillAssignment middle).LeafAssignment)
    (witness : GhostKernel ((children.fillAssignment middle).fillAssignment lower) colour scope) :
    ghostFillEquiv children colour scope middle
      (ghostFillEquiv (children.fillAssignment middle) colour scope lower witness) =
    ghostDoubleFillEquiv children colour scope middle lower witness := by
  cases children <;> rfl

mutual

/-- The actual one-shot-to-nested restriction diagram.  It preserves witness
choices, not merely their existence or cardinality. -/
theorem flat_restriction_coherence : {G : Hypersequent sigma} →
    (context : CKTree sigma Data G) → (middle : context.LeafAssignment) →
    (lower : (context.fillAssignment middle).LeafAssignment) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    (witness : ClosedKernel ((context.fillAssignment middle).fillAssignment lower) address scope) →
    continuationEquiv context middle
      (factorClosedProvider (context.fillAssignment middle) lower) address scope
      (fillEquiv (context.fillAssignment middle) lower address scope witness) =
    flatRestrictionEquiv context middle lower address scope witness
  | _, .interface _, _, _, _, _, _ => rfl
  | _, .ordinary o children, middle, lower, address, scope, witness => by
      have childLaw := flat_children_restriction_coherence children middle lower address 0
        (advance (emptyConclusion o.instanceData) scope)
      have ownerLaw := flat_owner_restriction_coherence children middle lower address
        (advance (emptyConclusion o.instanceData) scope)
      have ghostPLaw := ghostDoubleFill_coherence children Atom.p
        (advance (emptyConclusion o.instanceData) scope) middle lower
      have ghostQLaw := ghostDoubleFill_coherence children Atom.q
        (advance (emptyConclusion o.instanceData) scope) middle lower
      cases o with
      | mk identifier kind shape label incidence =>
          cases label <;> first
            | rfl
            | exact ownerLaw witness
            | exact childLaw witness
            | exact ghostPLaw witness
            | exact ghostQLaw witness
termination_by structural G context _ _ _ _ _ => context

theorem flat_children_restriction_coherence : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (middle : children.LeafAssignment) →
    (lower : (children.fillAssignment middle).LeafAssignment) →
    (address : InternalAddress) → (slot : Nat) → (scope : List OwnerSlot) →
    (witness : ChildrenKernel ((children.fillAssignment middle).fillAssignment lower)
      (fun _ _ _ => PEmpty) address slot scope) →
    childrenContinuationEquiv children middle
      (fun hole actual inherited => ClosedKernel (lower hole) actual inherited)
      address slot scope
      (childrenFillEquiv (children.fillAssignment middle) lower address slot scope witness) =
    flatChildrenRestrictionEquiv children middle lower address slot scope witness
  | _, .nil, _, _, _, _, _, witness => by cases witness; rfl
  | _, .cons head tail, middle, lower, address, slot, scope, witness => by
      rcases witness with ⟨headWitness, tailWitness⟩
      exact congrArg₂ Prod.mk
        (flat_restriction_coherence head (fun h => middle (.inl h)) (fun h => lower (.inl h))
          (address ++ [slot]) scope headWitness)
        (flat_children_restriction_coherence tail (fun h => middle (.inr h))
          (fun h => lower (.inr h)) address (slot + 1) scope tailWitness)
termination_by structural Gs children _ _ _ _ _ _ => children

theorem flat_owner_restriction_coherence : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (middle : children.LeafAssignment) →
    (lower : (children.fillAssignment middle).LeafAssignment) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    (witness : OwnerKernel ((children.fillAssignment middle).fillAssignment lower)
      (fun _ _ _ => PEmpty) address scope) →
    ownerContinuationEquiv children middle
      (fun hole actual inherited => ClosedKernel (lower hole) actual inherited)
      address scope
      (ownerFillEquiv (children.fillAssignment middle) lower address scope witness) =
    flatOwnerRestrictionEquiv children middle lower address scope witness
  | _, .nil, _, _, _, _, witness => nomatch witness
  | _, .cons _ .nil, _, _, _, _, witness => nomatch witness
  | _, .cons left (.cons right .nil), middle, lower, address, scope, witness => by
      rcases witness with ⟨colour, leftWitness, rightWitness⟩
      exact congrArg (Sigma.mk colour) (congrArg₂ Prod.mk
        (flat_restriction_coherence left (fun h => middle (.inl h)) (fun h => lower (.inl h))
          (address ++ [0]) (enterOwner address colour false scope) leftWitness)
        (flat_restriction_coherence right (fun h => middle (.inr (.inl h)))
          (fun h => lower (.inr (.inl h))) (address ++ [1])
          (enterOwner address colour true scope) rightWitness))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, witness => nomatch witness
termination_by structural Gs children _ _ _ _ _ => children

end

theorem flat_gluing_coherence {G : Hypersequent sigma} (context : CKTree sigma Data G)
    (middle : context.LeafAssignment) (lower : (context.fillAssignment middle).LeafAssignment)
    (address : InternalAddress) (scope : List OwnerSlot)
    (pieces : Kernel context
      (factorProvider context middle (factorClosedProvider (context.fillAssignment middle) lower))
      address scope) :
    (fillEquiv (context.fillAssignment middle) lower address scope).symm
      ((continuationEquiv context middle
        (factorClosedProvider (context.fillAssignment middle) lower) address scope).symm pieces) =
    (flatRestrictionEquiv context middle lower address scope).symm pieces := by
  apply (flatRestrictionEquiv context middle lower address scope).injective
  rw [← flat_restriction_coherence, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-! ## Specialization to the actual native combined cut -/

def moveAssignment {G : Hypersequent sigma} {left right : CKTree sigma Data G}
    (equal : left = right) (assignment : left.LeafAssignment) : right.LeafAssignment :=
  equal ▸ assignment

theorem moveAssignment_refill {G : Hypersequent sigma}
    {left right : CKTree sigma Data G} (equal : left = right)
    (assignment : left.LeafAssignment) :
    right.fillAssignment (moveAssignment equal assignment) = left.fillAssignment assignment := by
  cases equal
  rfl

def movePiecesEquiv {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (cut : CKBranchCut tree) (complete : tree.IsComplete)
    {context : CKTree sigma Data G} (equal : cut.remainder = context)
    (address : InternalAddress) (scope : List OwnerSlot) :
    CertificateCutGluing.PieceCertificates cut complete address scope ≃
      Kernel context (factorClosedProvider context
        (moveAssignment equal (cut.detachedLeafAssignment complete))) address scope :=
  Equiv.cast (by cases equal; rfl)

/-- Reindexing the *existing* native cut restriction along a literal remainder
equality agrees with filling restriction on that same reindexed assignment. -/
theorem move_cutGluingEquiv {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (cut : CKBranchCut tree) (complete : tree.IsComplete)
    {context : CKTree sigma Data G} (equal : cut.remainder = context)
    (address : InternalAddress) (scope : List OwnerSlot) :
    (CertificateCutGluing.cutGluingEquiv cut complete address scope).trans
      (movePiecesEquiv cut complete equal address scope) =
    (Equiv.cast (congrArg (fun t => ClosedKernel t address scope)
      ((moveAssignment_refill equal (cut.detachedLeafAssignment complete)).trans
        (cut.fillAssignment_detached complete)).symm)).trans
      (fillEquiv context (moveAssignment equal (cut.detachedLeafAssignment complete)) address scope) := by
  cases equal
  rfl

def middleAssignment {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :=
  first.siteFillersToLeaves complete (fun i => (lower i).remainder)

def installedComplete {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete) :
    (first.fill first.detached).IsComplete :=
  first.fill_detached_reconstructs.symm ▸ complete

def combinedAssignment {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    (first.remainder.fillAssignment (middleAssignment first complete lower)).LeafAssignment :=
  moveAssignment (first.insideCombined_remainder_allHoles complete lower)
    ((first.insideCombined lower).detachedLeafAssignment (installedComplete first complete))

theorem combinedAssignment_refill {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    (first.remainder.fillAssignment (middleAssignment first complete lower)).fillAssignment
      (combinedAssignment first complete lower) = first.fill first.detached :=
  (moveAssignment_refill (first.insideCombined_remainder_allHoles complete lower)
    ((first.insideCombined lower).detachedLeafAssignment (installedComplete first complete))).trans
      ((first.insideCombined lower).fillAssignment_detached (installedComplete first complete))

/-- The exact flat factors recover the first aligned detached family under
the native physical leaf reindexing.  Injectivity, not collected coefficients,
establishes the matching. -/
theorem combinedAssignment_composition {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    first.remainder.composeLeafAssignment (middleAssignment first complete lower)
      (combinedAssignment first complete lower) = first.detachedLeafAssignment complete := by
  apply first.remainder.fillAssignment_injective
  rw [← CKTree.fillAssignment_assoc]
  exact (combinedAssignment_refill first complete lower).trans
    (first.fill_detached_reconstructs.trans (first.fillAssignment_detached complete).symm)

def pulledCombinedAssignment {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site))
    (hole : first.remainder.LeafOccurrence) :
    (middleAssignment first complete lower hole).LeafAssignment :=
  fun inner => Eq.mp
    (congrArg (CKTree sigma Data)
      (first.remainder.fillLeafJoin_boundary (middleAssignment first complete lower) hole inner))
    (combinedAssignment first complete lower
      (first.remainder.fillLeafJoin (middleAssignment first complete lower) ⟨hole, inner⟩))

/-- Each lower callback uses exactly its own native detached assignment,
including callbacks at inherited holes in the open middle remainder. -/
theorem pulledCombinedAssignment_eq_lower {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    pulledCombinedAssignment first complete lower =
      first.lowerPhysicalAssignments complete lower := by
  funext hole
  apply (middleAssignment first complete lower hole).fillAssignment_injective
  exact (congrFun (combinedAssignment_composition first complete lower) hole).trans
    (first.lowerPhysicalAssignments_refill complete lower hole).symm

/-- Restrict by the actual one-shot native cut, retaining its native factors
and then merely transporting its literal remainder to the open flat context. -/
def nativeOneShotEquiv {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site))
    (address : InternalAddress) (scope : List OwnerSlot) :
    ClosedKernel (first.fill first.detached) address scope ≃
      Kernel (first.remainder.fillAssignment (middleAssignment first complete lower))
        (factorClosedProvider
          (first.remainder.fillAssignment (middleAssignment first complete lower))
          (combinedAssignment first complete lower)) address scope :=
  (CertificateCutGluing.cutGluingEquiv (.descend (first.insideCombined lower))
    (installedComplete first complete) address scope).trans
      (movePiecesEquiv (.descend (first.insideCombined lower)) (installedComplete first complete)
        (first.insideCombined_remainder_allHoles complete lower) address scope)

/-- The independently recursive two-level restriction, transported only at
its source by the separately proved literal native refill equality. -/
def nativeNestedEquiv {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site))
    (address : InternalAddress) (scope : List OwnerSlot) :
    ClosedKernel (first.fill first.detached) address scope ≃
      Kernel first.remainder
        (factorProvider first.remainder (middleAssignment first complete lower)
          (factorClosedProvider
            (first.remainder.fillAssignment (middleAssignment first complete lower))
            (combinedAssignment first complete lower))) address scope :=
  (Equiv.cast (congrArg (fun t => ClosedKernel t address scope)
    (combinedAssignment_refill first complete lower).symm)).trans
      (flatRestrictionEquiv first.remainder (middleAssignment first complete lower)
        (combinedAssignment first complete lower) address scope)

/-- Actual native combined-cut coherence for arbitrary complete first sources
and arbitrary full lower branch cuts inside their detached factors.  This is
map equality, with the exact factor-to-hole matching proved above. -/
theorem native_restriction_coherence {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site))
    (address : InternalAddress) (scope : List OwnerSlot)
    (witness : ClosedKernel (first.fill first.detached) address scope) :
    continuationEquiv first.remainder (middleAssignment first complete lower)
      (factorClosedProvider
        (first.remainder.fillAssignment (middleAssignment first complete lower))
        (combinedAssignment first complete lower)) address scope
      (nativeOneShotEquiv first complete lower address scope witness) =
    nativeNestedEquiv first complete lower address scope witness := by
  have moved := congrArg
    (fun (equivalence : ClosedKernel (first.fill first.detached) address scope ≃ _) =>
      equivalence witness)
    (move_cutGluingEquiv (.descend (first.insideCombined lower))
      (installedComplete first complete)
      (first.insideCombined_remainder_allHoles complete lower) address scope)
  change nativeOneShotEquiv first complete lower address scope witness =
    fillEquiv (first.remainder.fillAssignment (middleAssignment first complete lower))
      (combinedAssignment first complete lower) address scope
      (Equiv.cast (congrArg (fun t => ClosedKernel t address scope)
        (combinedAssignment_refill first complete lower).symm) witness) at moved
  rw [moved]
  exact flat_restriction_coherence first.remainder (middleAssignment first complete lower)
    (combinedAssignment first complete lower) address scope _

theorem native_gluing_coherence {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKCutPlan tree) (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site))
    (address : InternalAddress) (scope : List OwnerSlot)
    (pieces : Kernel first.remainder
      (factorProvider first.remainder (middleAssignment first complete lower)
        (factorClosedProvider
          (first.remainder.fillAssignment (middleAssignment first complete lower))
          (combinedAssignment first complete lower))) address scope) :
    (nativeOneShotEquiv first complete lower address scope).symm
      ((continuationEquiv first.remainder (middleAssignment first complete lower)
        (factorClosedProvider
          (first.remainder.fillAssignment (middleAssignment first complete lower))
          (combinedAssignment first complete lower)) address scope).symm pieces) =
    (nativeNestedEquiv first complete lower address scope).symm pieces := by
  apply (nativeNestedEquiv first complete lower address scope).injective
  rw [← native_restriction_coherence, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

end Potkin.Research.CertificateFlagGluing

#check Potkin.CKCutPlan.lowerPhysicalAssignments
#print axioms Potkin.CKCutPlan.lowerPhysicalAssignments_refill
#print axioms Potkin.CKCutPlan.lowerPhysicalAssignments_family
#check Potkin.Research.CertificateFlagGluing.flat_restriction_coherence
#print axioms Potkin.Research.CertificateFlagGluing.flat_restriction_coherence
#print axioms Potkin.Research.CertificateFlagGluing.flat_gluing_coherence
#check Potkin.Research.CertificateFlagGluing.native_restriction_coherence
#check Potkin.Research.CertificateFlagGluing.native_gluing_coherence
#print axioms Potkin.Research.CertificateFlagGluing.combinedAssignment_composition
#print axioms Potkin.Research.CertificateFlagGluing.pulledCombinedAssignment_eq_lower
#print axioms Potkin.Research.CertificateFlagGluing.native_restriction_coherence
#print axioms Potkin.Research.CertificateFlagGluing.native_gluing_coherence

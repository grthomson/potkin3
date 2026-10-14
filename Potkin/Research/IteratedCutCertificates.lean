import Potkin.Research.OpenCutCertificateGluing
import Potkin.Research.RemainderExtractionFlags

/-!
# Certificate reassociation for the two native extraction flag spaces

The left interpretation recursively restricts each actual outer detached factor;
the right interpretation extracts the lower frontier and then its open remainder.
Reassociation is constructor-defined, not defined by conjugating global gluing.
Owner colours and ancestor indices remain witnesses, with their actual scopes.
-/

namespace Potkin.Research.IteratedCutCertificates

open RevivalInterface OpenCertificateKernel OpenCutCertificateGluing
open RemainderExtractionFlags

mutual

def insidePlanProvider : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (upper : CKCutPlan tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) →
    Provider tree → Provider upper.remainder
  | _, _, .interface _, _, provider => provider
  | _, _, .ordinary _ _ children, inner, provider =>
      insideChildrenProvider children inner provider

def insideChildrenProvider : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) →
    ChildrenProvider trees → ChildrenProvider upper.remainder
  | _, _, .nil, _, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, inner, provider, hole =>
      match hole with
      | .inl hole => insideBranchProvider head (fun i => inner (.inl i))
          (fun h => provider (.inl h)) hole
      | .inr hole => insideChildrenProvider tail (fun i => inner (.inr i))
          (fun h => provider (.inr h)) hole

def insideBranchProvider : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (upper : CKBranchCut tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) →
    Provider tree → Provider upper.remainder
  | _, _, .detach _, inner, provider, _, actual, inherited =>
      Kernel (inner PUnit.unit).remainder
        (branchProvider (inner PUnit.unit) provider) actual inherited
  | _, _, .descend plan, inner, provider, hole, actual, inherited =>
      insidePlanProvider plan inner provider hole actual inherited

end

mutual

def insidePlanEquiv : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) → Kernel tree provider actual inherited ≃
      Kernel upper.remainder (insidePlanProvider upper inner provider) actual inherited
  | _, _, .interface _, _, _, _, _ => Equiv.refl _
  | _, _, .ordinary o _ children, inner, provider, actual, inherited => by
      cases label : o.instanceData <;> simp only [Kernel, CKCutPlan.remainder, label]
      all_goals first
        | exact ghostEquiv children _ _
        | exact insideOwnerEquiv children inner provider actual _
        | exact insideChildrenEquiv children inner provider actual 0 _

def insideChildrenEquiv : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (slot : Nat) → (inherited : List OwnerSlot) →
    ChildrenKernel trees provider actual slot inherited ≃
      ChildrenKernel upper.remainder (insideChildrenProvider upper inner provider)
        actual slot inherited
  | _, _, .nil, _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ head tail, inner, provider, actual, slot, inherited =>
      Equiv.prodCongr
        (insideBranchEquiv head (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [slot]) inherited)
        (insideChildrenEquiv tail (fun i => inner (.inr i))
          (fun h => provider (.inr h)) actual (slot + 1) inherited)

def insideOwnerEquiv : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) →
    OwnerKernel trees provider actual inherited ≃
      OwnerKernel upper.remainder (insideChildrenProvider upper inner provider) actual inherited
  | _, _, .nil, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ _ .nil, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ left (.cons _ _ right .nil), inner, provider, actual, inherited =>
      Equiv.sigmaCongrRight fun colour => Equiv.prodCongr
        (insideBranchEquiv left (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [0])
          (enterOwner actual colour false inherited))
        (insideBranchEquiv right (fun i => inner (.inr (.inl i)))
          (fun h => provider (.inr (.inl h))) (actual ++ [1])
          (enterOwner actual colour true inherited))
  | _, _, .cons _ _ _ (.cons _ _ _ (.cons _ _ _ _)), _, _, _, _ => Equiv.refl _

def insideBranchEquiv : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) → Kernel tree provider actual inherited ≃
      Kernel upper.remainder (insideBranchProvider upper inner provider) actual inherited
  | _, _, .detach _, inner, provider, actual, inherited =>
      branchEquiv (inner PUnit.unit) provider actual inherited
  | _, _, .descend plan, inner, provider, actual, inherited =>
      insidePlanEquiv plan inner provider actual inherited

end

/-- Transparent whole-endpoint case, parameterized by the actual inner cut.
Splitting that cut here avoids dependent rewriting inside a callback family. -/
def reassociateRoot {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) (provider : Provider tree)
    (actual : InternalAddress) (inherited : List OwnerSlot) :
    Kernel lower.remainder (branchProvider lower provider) actual inherited ≃
      Kernel (rootPair ordinary lower).2.remainder
        (branchProvider (rootPair ordinary lower).2
          (branchProvider (rootPair ordinary lower).1 provider)) actual inherited :=
  match lower with
  | .detach _ => Equiv.refl _
  | .descend _ => Equiv.refl _

theorem reassociateRoot_restriction {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) (provider : Provider tree)
    (actual : InternalAddress) (inherited : List OwnerSlot)
    (witness : Kernel tree provider actual inherited) :
    reassociateRoot ordinary lower provider actual inherited
      (branchEquiv lower provider actual inherited witness) =
      remainderStagesEquiv (rootPair ordinary lower).1 (rootPair ordinary lower).2
        provider actual inherited witness := by
  cases lower <;> rfl

mutual

/-- Independently constructed reassociation between the actual piece types. -/
def reassociatePlan : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) →
    Kernel upper.remainder (insidePlanProvider upper inner provider) actual inherited ≃
      Kernel (toRemainderPlan upper inner).2.remainder
        (remainderProvider (toRemainderPlan upper inner).2
          (remainderProvider (toRemainderPlan upper inner).1 provider)) actual inherited
  | _, _, .interface _, _, _, _, _ => Equiv.refl _
  | _, _, .ordinary o _ children, inner, provider, actual, inherited => by
      cases label : o.instanceData <;>
        simp only [Kernel, CKCutPlan.remainder, toRemainderPlan, label]
      all_goals first
        | exact reassociateGhost children _ _ inner
        | exact reassociateOwner children inner provider actual _
        | exact reassociateChildren children inner provider actual 0 _

def reassociateGhost : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    (colour : Atom) → (inherited : List OwnerSlot) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    GhostKernel upper.remainder colour inherited ≃
      GhostKernel (toRemainderChildren upper inner).2.remainder colour inherited
  | _, _, .nil, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ _ _, _, _, _ => Equiv.refl _

def reassociateChildren : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (slot : Nat) → (inherited : List OwnerSlot) →
    ChildrenKernel upper.remainder (insideChildrenProvider upper inner provider)
      actual slot inherited ≃
      ChildrenKernel (toRemainderChildren upper inner).2.remainder
        (childrenRemainderProvider (toRemainderChildren upper inner).2
          (childrenRemainderProvider (toRemainderChildren upper inner).1 provider))
        actual slot inherited
  | _, _, .nil, _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ head tail, inner, provider, actual, slot, inherited =>
      Equiv.prodCongr
        (reassociateBranch head (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [slot]) inherited)
        (reassociateChildren tail (fun i => inner (.inr i))
          (fun h => provider (.inr h)) actual (slot + 1) inherited)

def reassociateOwner : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) →
    OwnerKernel upper.remainder (insideChildrenProvider upper inner provider) actual inherited ≃
      OwnerKernel (toRemainderChildren upper inner).2.remainder
        (childrenRemainderProvider (toRemainderChildren upper inner).2
          (childrenRemainderProvider (toRemainderChildren upper inner).1 provider)) actual inherited
  | _, _, .nil, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ _ .nil, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ left (.cons _ _ right .nil), inner, provider, actual, inherited =>
      Equiv.sigmaCongrRight fun colour => Equiv.prodCongr
        (reassociateBranch left (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [0])
          (enterOwner actual colour false inherited))
        (reassociateBranch right (fun i => inner (.inr (.inl i)))
          (fun h => provider (.inr (.inl h))) (actual ++ [1])
          (enterOwner actual colour true inherited))
  | _, _, .cons _ _ _ (.cons _ _ _ (.cons _ _ _ _)), _, _, _, _ => Equiv.refl _

def reassociateBranch : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) →
    Kernel upper.remainder (insideBranchProvider upper inner provider) actual inherited ≃
      Kernel (toRemainderBranch upper inner).2.remainder
        (branchProvider (toRemainderBranch upper inner).2
          (branchProvider (toRemainderBranch upper inner).1 provider)) actual inherited
  | _, _, .detach ordinary, inner, provider, actual, inherited =>
      reassociateRoot ordinary (inner PUnit.unit) provider actual inherited
  | _, _, .descend plan, inner, provider, actual, inherited =>
      reassociatePlan plan inner provider actual inherited

end

theorem restriction_ghost : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (colour : Atom) → (inherited : List OwnerSlot) →
    (witness : GhostKernel trees colour inherited) →
    reassociateGhost upper colour inherited inner (ghostEquiv upper colour inherited witness) =
      ghostEquiv (toRemainderChildren upper inner).2 colour inherited
        (ghostEquiv (toRemainderChildren upper inner).1 colour inherited witness)
  | _, _, .nil, _, _, _, _ => rfl
  | _, _, .cons _ _ _ _, _, _, _, _ => rfl

mutual

theorem restriction_plan : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) → (witness : Kernel tree provider actual inherited) →
    reassociatePlan upper inner provider actual inherited
      (insidePlanEquiv upper inner provider actual inherited witness) =
      cutEquiv (toRemainderPlan upper inner).2
        (remainderProvider (toRemainderPlan upper inner).1 provider) actual inherited
        (cutEquiv (toRemainderPlan upper inner).1 provider actual inherited witness)
  | _, _, .interface _, _, _, _, _, _ => rfl
  | _, _, .ordinary o _ children, inner, provider, actual, inherited, witness => by
      have childLaw := restriction_children children inner provider actual 0
        (advance (emptyConclusion o.instanceData) inherited)
      have ownerLaw := restriction_owner children inner provider actual
        (advance (emptyConclusion o.instanceData) inherited)
      have ghostPLaw := restriction_ghost children inner Atom.p
        (advance (emptyConclusion o.instanceData) inherited)
      have ghostQLaw := restriction_ghost children inner Atom.q
        (advance (emptyConclusion o.instanceData) inherited)
      cases o with
      | mk identifier kind shape label incidence =>
          cases label <;> first
            | exact ownerLaw witness
            | exact childLaw witness
            | exact ghostPLaw witness
            | exact ghostQLaw witness
termination_by structural G tree upper _ _ _ _ _ => upper

theorem restriction_children : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (slot : Nat) → (inherited : List OwnerSlot) →
    (witness : ChildrenKernel trees provider actual slot inherited) →
    reassociateChildren upper inner provider actual slot inherited
      (insideChildrenEquiv upper inner provider actual slot inherited witness) =
      childrenEquiv (toRemainderChildren upper inner).2
        (childrenRemainderProvider (toRemainderChildren upper inner).1 provider)
        actual slot inherited
        (childrenEquiv (toRemainderChildren upper inner).1 provider actual slot inherited witness)
  | _, _, .nil, _, _, _, _, _, witness => by cases witness; rfl
  | _, _, .cons _ _ head tail, inner, provider, actual, slot, inherited, witness => by
      rcases witness with ⟨headWitness, tailWitness⟩
      exact congrArg₂ Prod.mk
        (restriction_branch head (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [slot]) inherited headWitness)
        (restriction_children tail (fun i => inner (.inr i))
          (fun h => provider (.inr h)) actual (slot + 1) inherited tailWitness)
termination_by structural Gs trees upper _ _ _ _ _ _ => upper

theorem restriction_owner : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) → (witness : OwnerKernel trees provider actual inherited) →
    reassociateOwner upper inner provider actual inherited
      (insideOwnerEquiv upper inner provider actual inherited witness) =
      ownerEquiv (toRemainderChildren upper inner).2
        (childrenRemainderProvider (toRemainderChildren upper inner).1 provider) actual inherited
        (ownerEquiv (toRemainderChildren upper inner).1 provider actual inherited witness)
  | _, _, .nil, _, _, _, _, witness => nomatch witness
  | _, _, .cons _ _ _ .nil, _, _, _, _, witness => nomatch witness
  | _, _, .cons _ _ left (.cons _ _ right .nil), inner, provider, actual, inherited, witness => by
      rcases witness with ⟨colour, leftWitness, rightWitness⟩
      exact congrArg (Sigma.mk colour) (congrArg₂ Prod.mk
        (restriction_branch left (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [0])
          (enterOwner actual colour false inherited) leftWitness)
        (restriction_branch right (fun i => inner (.inr (.inl i)))
          (fun h => provider (.inr (.inl h))) (actual ++ [1])
          (enterOwner actual colour true inherited) rightWitness))
  | _, _, .cons _ _ _ (.cons _ _ _ (.cons _ _ _ _)), _, _, _, _, witness => nomatch witness
termination_by structural Gs trees upper _ _ _ _ _ => upper

/-- The commuting diagram for the actual restriction maps.  The two sides
retain the same owner colours and indexed eligible-ancestor choices. -/
theorem restriction_branch : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) → (witness : Kernel tree provider actual inherited) →
    reassociateBranch upper inner provider actual inherited
      (insideBranchEquiv upper inner provider actual inherited witness) =
      remainderStagesEquiv (toRemainderBranch upper inner).1 (toRemainderBranch upper inner).2
        provider actual inherited witness
  | _, _, .detach ordinary, inner, provider, actual, inherited, witness =>
      reassociateRoot_restriction ordinary (inner PUnit.unit) provider actual inherited witness
  | _, _, .descend plan, inner, provider, actual, inherited, witness =>
      restriction_plan plan inner provider actual inherited witness
termination_by structural G tree upper _ _ _ _ _ => upper

end

theorem gluing_branch {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (upper : CKBranchCut tree) (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (provider : Provider tree) (actual : InternalAddress) (inherited : List OwnerSlot)
    (pieces : Kernel upper.remainder (insideBranchProvider upper inner provider) actual inherited) :
    (remainderStagesEquiv (toRemainderBranch upper inner).1 (toRemainderBranch upper inner).2
      provider actual inherited).symm
      (reassociateBranch upper inner provider actual inherited pieces) =
      (insideBranchEquiv upper inner provider actual inherited).symm pieces := by
  apply (remainderStagesEquiv (toRemainderBranch upper inner).1
    (toRemainderBranch upper inner).2 provider actual inherited).injective
  rw [Equiv.apply_symm_apply, ← restriction_branch, Equiv.apply_symm_apply]

#check @restriction_branch
#check @gluing_branch
#print axioms insideBranchEquiv
#print axioms reassociateBranch
#print axioms restriction_branch
#print axioms gluing_branch

end Potkin.Research.IteratedCutCertificates

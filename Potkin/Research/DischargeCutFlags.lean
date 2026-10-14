import Potkin.Research.OpenDischargeCertificates
import Potkin.Research.RemainderExtractionFlags

/-!
# Certificate reassociation for the two native extraction flag spaces

The left interpretation recursively restricts each actual outer detached factor;
the right interpretation extracts the lower frontier and then its open remainder.
Reassociation is constructor-defined, not defined by conjugating global gluing.
Designated bottom identities, ordered roles and physical ancestor indices remain
witnesses. This specializes the existing constructor proof pattern, not a new
cut-flag geometry or an assumed equality of Prop proofs.
-/

namespace Potkin.Research.DischargeCutFlags

open OpenDischarge OpenDischargeCertificates
universe u v
variable {sigma : Signature.{u, v}}
open RemainderExtractionFlags

mutual

def insidePlanProvider : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (upper : CKCutPlan tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) →
    Provider tree → Provider upper.remainder
  | _, _, .interface _, _, provider => provider
  | _, _, .ordinary _ _ children, inner, provider =>
      insideChildrenProvider children inner provider

def insideChildrenProvider : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma (Data sigma) Gs} → (upper : CKChildCuts trees) →
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
    {tree : CKTree sigma (Data sigma) G} → (upper : CKBranchCut tree) →
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
    {tree : CKTree sigma (Data sigma) G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List (OwnerSlot sigma)) → Kernel tree provider actual inherited ≃
      Kernel upper.remainder (insidePlanProvider upper inner provider) actual inherited
  | _, _, .interface _, _, _, _, _ => Equiv.refl _
  | _, _, .ordinary o _ children, inner, provider, actual, inherited => by
      cases label : o.instanceData <;> simp only [Kernel, CKCutPlan.remainder, label]
      all_goals first
        | exact Equiv.prodCongr (Equiv.refl _)
            (insideChildrenEquiv children inner provider actual 0 inherited)
        | exact insideBottomEquiv children inner provider _ _ actual inherited
        | exact insideChildrenEquiv children inner provider actual 0 inherited

def insideChildrenEquiv : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma (Data sigma) Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (slot : Nat) → (inherited : List (OwnerSlot sigma)) →
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

def insideBottomEquiv : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma (Data sigma) Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (uid : Nat) → (pack : Parameters sigma) →
    (actual : InternalAddress) → (inherited : List (OwnerSlot sigma)) →
    BottomKernel trees provider uid pack actual inherited ≃
      BottomKernel upper.remainder (insideChildrenProvider upper inner provider)
        uid pack actual inherited
  | _, _, .nil, _, _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ _ .nil, _, _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ left (.cons _ _ right .nil), inner, provider, uid, pack, actual, inherited =>
      Equiv.prodCongr
        (insideBranchEquiv left (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [0])
          (enterOwner uid pack actual 0 inherited))
        (insideBranchEquiv right (fun i => inner (.inr (.inl i)))
          (fun h => provider (.inr (.inl h))) (actual ++ [1])
          (enterOwner uid pack actual 1 inherited))
  | _, _, .cons _ _ _ (.cons _ _ _ (.cons _ _ _ _)), _, _, _, _, _, _ => Equiv.refl _

def insideBranchEquiv : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List (OwnerSlot sigma)) → Kernel tree provider actual inherited ≃
      Kernel upper.remainder (insideBranchProvider upper inner provider) actual inherited
  | _, _, .detach _, inner, provider, actual, inherited =>
      branchEquiv (inner PUnit.unit) provider actual inherited
  | _, _, .descend plan, inner, provider, actual, inherited =>
      insidePlanEquiv plan inner provider actual inherited

end

/-- Transparent whole-endpoint case, parameterized by the actual inner cut.
Splitting that cut here avoids dependent rewriting inside a callback family. -/
def reassociateRoot {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) (provider : Provider tree)
    (actual : InternalAddress) (inherited : List (OwnerSlot sigma)) :
    Kernel lower.remainder (branchProvider lower provider) actual inherited ≃
      Kernel (rootPair ordinary lower).2.remainder
        (branchProvider (rootPair ordinary lower).2
          (branchProvider (rootPair ordinary lower).1 provider)) actual inherited :=
  match lower with
  | .detach _ => Equiv.refl _
  | .descend _ => Equiv.refl _

theorem reassociateRoot_restriction {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) (provider : Provider tree)
    (actual : InternalAddress) (inherited : List (OwnerSlot sigma))
    (witness : Kernel tree provider actual inherited) :
    reassociateRoot ordinary lower provider actual inherited
      (branchEquiv lower provider actual inherited witness) =
      remainderStagesEquiv (rootPair ordinary lower).1 (rootPair ordinary lower).2
        provider actual inherited witness := by
  cases lower <;> rfl

mutual

/-- Independently constructed reassociation between the actual piece types. -/
def reassociatePlan : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List (OwnerSlot sigma)) →
    Kernel upper.remainder (insidePlanProvider upper inner provider) actual inherited ≃
      Kernel (toRemainderPlan upper inner).2.remainder
        (remainderProvider (toRemainderPlan upper inner).2
          (remainderProvider (toRemainderPlan upper inner).1 provider)) actual inherited
  | _, _, .interface _, _, _, _, _ => Equiv.refl _
  | _, _, .ordinary o _ children, inner, provider, actual, inherited => by
      cases label : o.instanceData <;>
        simp only [Kernel, CKCutPlan.remainder, toRemainderPlan, label]
      all_goals first
        | exact Equiv.prodCongr (Equiv.refl _)
            (reassociateChildren children inner provider actual 0 inherited)
        | exact reassociateBottom children inner provider _ _ actual inherited
        | exact reassociateChildren children inner provider actual 0 inherited



def reassociateChildren : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma (Data sigma) Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (slot : Nat) → (inherited : List (OwnerSlot sigma)) →
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

def reassociateBottom : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma (Data sigma) Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (uid : Nat) → (pack : Parameters sigma) →
    (actual : InternalAddress) → (inherited : List (OwnerSlot sigma)) →
    BottomKernel upper.remainder (insideChildrenProvider upper inner provider)
      uid pack actual inherited ≃
      BottomKernel (toRemainderChildren upper inner).2.remainder
        (childrenRemainderProvider (toRemainderChildren upper inner).2
          (childrenRemainderProvider (toRemainderChildren upper inner).1 provider))
        uid pack actual inherited
  | _, _, .nil, _, _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ _ .nil, _, _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ left (.cons _ _ right .nil), inner, provider, uid, pack, actual, inherited =>
      Equiv.prodCongr
        (reassociateBranch left (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [0])
          (enterOwner uid pack actual 0 inherited))
        (reassociateBranch right (fun i => inner (.inr (.inl i)))
          (fun h => provider (.inr (.inl h))) (actual ++ [1])
          (enterOwner uid pack actual 1 inherited))
  | _, _, .cons _ _ _ (.cons _ _ _ (.cons _ _ _ _)), _, _, _, _, _, _ => Equiv.refl _

def reassociateBranch : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List (OwnerSlot sigma)) →
    Kernel upper.remainder (insideBranchProvider upper inner provider) actual inherited ≃
      Kernel (toRemainderBranch upper inner).2.remainder
        (branchProvider (toRemainderBranch upper inner).2
          (branchProvider (toRemainderBranch upper inner).1 provider)) actual inherited
  | _, _, .detach ordinary, inner, provider, actual, inherited =>
      reassociateRoot ordinary (inner PUnit.unit) provider actual inherited
  | _, _, .descend plan, inner, provider, actual, inherited =>
      reassociatePlan plan inner provider actual inherited

end



mutual

theorem restriction_plan : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List (OwnerSlot sigma)) → (witness : Kernel tree provider actual inherited) →
    reassociatePlan upper inner provider actual inherited
      (insidePlanEquiv upper inner provider actual inherited witness) =
      cutEquiv (toRemainderPlan upper inner).2
        (remainderProvider (toRemainderPlan upper inner).1 provider) actual inherited
        (cutEquiv (toRemainderPlan upper inner).1 provider actual inherited witness)
  | _, _, .interface _, _, _, _, _, _ => rfl
  | _, _, .ordinary o _ children, inner, provider, actual, inherited, witness => by
      have childLaw := restriction_children children inner provider actual 0 inherited
      have bottomLaw (uid : Nat) (pack : Parameters sigma) :=
        restriction_bottom children inner provider uid pack actual inherited
      cases o with
      | mk identifier kind shape label incidence =>
          cases label <;> first
            | exact childLaw witness
            | exact congrArg (Prod.mk witness.1) (childLaw witness.2)
            | exact bottomLaw _ _ witness

termination_by structural G tree upper _ _ _ _ _ => upper

theorem restriction_children : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma (Data sigma) Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (slot : Nat) → (inherited : List (OwnerSlot sigma)) →
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

theorem restriction_bottom : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma (Data sigma) Gs} → (upper : CKChildCuts trees) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : ChildrenProvider trees) → (uid : Nat) → (pack : Parameters sigma) →
    (actual : InternalAddress) → (inherited : List (OwnerSlot sigma)) →
    (witness : BottomKernel trees provider uid pack actual inherited) →
    reassociateBottom upper inner provider uid pack actual inherited
      (insideBottomEquiv upper inner provider uid pack actual inherited witness) =
      bottomEquiv (toRemainderChildren upper inner).2
        (childrenRemainderProvider (toRemainderChildren upper inner).1 provider)
        uid pack actual inherited
        (bottomEquiv (toRemainderChildren upper inner).1 provider uid pack actual inherited witness)
  | _, _, .nil, _, _, _, _, _, _, witness => nomatch witness
  | _, _, .cons _ _ _ .nil, _, _, _, _, _, _, witness => nomatch witness
  | _, _, .cons _ _ left (.cons _ _ right .nil), inner, provider, uid, pack, actual, inherited, witness => by
      rcases witness with ⟨leftWitness, rightWitness⟩
      exact congrArg₂ Prod.mk
        (restriction_branch left (fun i => inner (.inl i))
          (fun h => provider (.inl h)) (actual ++ [0])
          (enterOwner uid pack actual 0 inherited) leftWitness)
        (restriction_branch right (fun i => inner (.inr (.inl i)))
          (fun h => provider (.inr (.inl h))) (actual ++ [1])
          (enterOwner uid pack actual 1 inherited) rightWitness)
  | _, _, .cons _ _ _ (.cons _ _ _ (.cons _ _ _ _)), _, _, _, _, _, _, witness => nomatch witness
termination_by structural Gs trees upper _ _ _ _ _ _ _ => upper

/-- The commuting diagram for the actual restriction maps.  The two sides
retain the same designated owners, ordered roles and indexed ancestor choices. -/
theorem restriction_branch : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List (OwnerSlot sigma)) → (witness : Kernel tree provider actual inherited) →
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

theorem gluing_branch {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (upper : CKBranchCut tree) (inner : (site : upper.Site) → CKBranchCut (upper.detached site))
    (provider : Provider tree) (actual : InternalAddress) (inherited : List (OwnerSlot sigma))
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

end Potkin.Research.DischargeCutFlags

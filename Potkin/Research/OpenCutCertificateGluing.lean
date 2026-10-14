import Potkin.Research.OpenCertificateKernel

/-!
# Native extraction certificates for arbitrary open sources

A remainder interface is either inherited or cut-created.  The former keeps
its original provider; the latter invokes the actual detached tree under the
unchanged absolute address and inherited owner scope.  This distinction makes
successive extraction from a previously punctured remainder meaningful.

The auxiliary providers and equivalences are certificate metadata over native
trees and cuts, not a second proof, cut, forest or context representation.
-/

namespace Potkin.Research.OpenCutCertificateGluing

open RevivalInterface OpenCertificateKernel

mutual

def remainderProvider : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (cut : CKCutPlan tree) →
    Provider tree → Provider cut.remainder
  | _, _, .interface _, provider => provider
  | _, _, .ordinary _ _ children, provider =>
      childrenRemainderProvider children provider

def childrenRemainderProvider : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (cuts : CKChildCuts trees) →
    ChildrenProvider trees → ChildrenProvider cuts.remainder
  | _, _, .nil, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, provider, hole =>
      match hole with
      | .inl hole => branchProvider head (fun h => provider (.inl h)) hole
      | .inr hole => childrenRemainderProvider tail (fun h => provider (.inr h)) hole

def branchProvider : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (cut : CKBranchCut tree) →
    Provider tree → Provider cut.remainder
  | _, tree, .detach _, provider, _, actual, inherited =>
      Kernel tree provider actual inherited
  | _, _, .descend plan, provider, hole, actual, inherited =>
      remainderProvider plan provider hole actual inherited

end

mutual

/-- Constructor restriction with inherited interfaces retained.  No source
completeness is asserted or required. -/
def cutEquiv : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (cut : CKCutPlan tree) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) →
    Kernel tree provider actual inherited ≃
      Kernel cut.remainder (remainderProvider cut provider) actual inherited
  | _, _, .interface _, _, _, _ => Equiv.refl _
  | _, _, .ordinary o _ children, provider, actual, inherited => by
      cases label : o.instanceData <;> simp only [Kernel, CKCutPlan.remainder, label]
      all_goals first
        | exact ghostEquiv children _ _
        | exact ownerEquiv children provider actual _
        | exact childrenEquiv children provider actual 0 _

def ghostEquiv : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (cuts : CKChildCuts trees) →
    (colour : Atom) → (inherited : List OwnerSlot) →
    GhostKernel trees colour inherited ≃ GhostKernel cuts.remainder colour inherited
  | _, _, .nil, _, _ => Equiv.refl _
  | _, _, .cons _ _ _ _, _, _ => Equiv.refl _

def childrenEquiv : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (cuts : CKChildCuts trees) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (slot : Nat) → (inherited : List OwnerSlot) →
    ChildrenKernel trees provider actual slot inherited ≃
      ChildrenKernel cuts.remainder (childrenRemainderProvider cuts provider)
        actual slot inherited
  | _, _, .nil, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ head tail, provider, actual, slot, inherited =>
      Equiv.prodCongr
        (branchEquiv head (fun h => provider (.inl h)) (actual ++ [slot]) inherited)
        (childrenEquiv tail (fun h => provider (.inr h)) actual (slot + 1) inherited)

def ownerEquiv : {Gs : List (Hypersequent sigma)} →
    {trees : CKChildren sigma Data Gs} → (cuts : CKChildCuts trees) →
    (provider : ChildrenProvider trees) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) →
    OwnerKernel trees provider actual inherited ≃
      OwnerKernel cuts.remainder (childrenRemainderProvider cuts provider) actual inherited
  | _, _, .nil, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ _ .nil, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ left (.cons _ _ right .nil), provider, actual, inherited =>
      Equiv.sigmaCongrRight fun colour => Equiv.prodCongr
        (branchEquiv left (fun h => provider (.inl h)) (actual ++ [0])
          (enterOwner actual colour false inherited))
        (branchEquiv right (fun h => provider (.inr (.inl h))) (actual ++ [1])
          (enterOwner actual colour true inherited))
  | _, _, .cons _ _ _ (.cons _ _ _ (.cons _ _ _ _)), _, _, _ => Equiv.refl _

def branchEquiv : {G : Hypersequent sigma} →
    {tree : CKTree sigma Data G} → (cut : CKBranchCut tree) →
    (provider : Provider tree) → (actual : InternalAddress) →
    (inherited : List OwnerSlot) →
    Kernel tree provider actual inherited ≃
      Kernel cut.remainder (branchProvider cut provider) actual inherited
  | _, _, .detach _, _, _, _ => Equiv.refl _
  | _, _, .descend plan, provider, actual, inherited =>
      cutEquiv plan provider actual inherited

end

/-- Exact two-stage certificate interpretation when the SECOND extraction
acts on the first remainder, which is generally open. -/
def remainderStagesEquiv {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKBranchCut tree) (second : CKBranchCut first.remainder)
    (provider : Provider tree) (actual : InternalAddress)
    (inherited : List OwnerSlot) :
    Kernel tree provider actual inherited ≃
      Kernel second.remainder
        (branchProvider second (branchProvider first provider)) actual inherited :=
  (branchEquiv first provider actual inherited).trans
    (branchEquiv second (branchProvider first provider) actual inherited)

theorem staged_glue_restrict {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKBranchCut tree) (second : CKBranchCut first.remainder)
    (provider : Provider tree) (actual : InternalAddress)
    (inherited : List OwnerSlot) (certificate : Kernel tree provider actual inherited) :
    (remainderStagesEquiv first second provider actual inherited).symm
      (remainderStagesEquiv first second provider actual inherited certificate) = certificate :=
  (remainderStagesEquiv first second provider actual inherited).symm_apply_apply certificate

theorem staged_restrict_glue {G : Hypersequent sigma} {tree : CKTree sigma Data G}
    (first : CKBranchCut tree) (second : CKBranchCut first.remainder)
    (provider : Provider tree) (actual : InternalAddress)
    (inherited : List OwnerSlot)
    (pieces : Kernel second.remainder
      (branchProvider second (branchProvider first provider)) actual inherited) :
    remainderStagesEquiv first second provider actual inherited
      ((remainderStagesEquiv first second provider actual inherited).symm pieces) = pieces :=
  (remainderStagesEquiv first second provider actual inherited).apply_symm_apply pieces

#check @branchEquiv
#check @remainderStagesEquiv
#print axioms branchEquiv
#print axioms remainderStagesEquiv
#print axioms staged_glue_restrict
#print axioms staged_restrict_glue

end Potkin.Research.OpenCutCertificateGluing

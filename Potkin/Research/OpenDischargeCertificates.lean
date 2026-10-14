import Potkin.Research.OpenDischarge
import Potkin.Research.OpenCutAssignments
import Mathlib.Logic.Equiv.Prod

/-!
# Physical discharge certificates and native extraction

These are witness types over `CKTree`, not derivations.  A scope entry is one
actual bottom occurrence and its ordered premise branch.  At a top, the finite
ancestor index is retained.  At an interface, its callback receives the actual
absolute address and the unchanged scope.  Local rule admission is separate.
-/

namespace Potkin.Research.OpenDischargeCertificates

open OpenDischarge
universe u v
variable {sigma : Signature.{u, v}}

structure OwnerSlot (sigma : Signature.{u, v}) where
  uid : Nat
  address : InternalAddress
  parameters : Parameters sigma
  role : Fin 2

abbrev Provider {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G) :=
  tree.LeafOccurrence → InternalAddress → List (OwnerSlot sigma) → Type (max u v)

abbrev ChildrenProvider {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma (Data sigma) Gs) :=
  children.LeafOccurrence → InternalAddress → List (OwnerSlot sigma) → Type (max u v)

/-- A physical ancestor position, not just a matching owner name. -/
abbrev EligibleOwner (uid : Nat) (pack : Parameters sigma) (role : Fin 2)
    (scope : List (OwnerSlot sigma)) :=
  {index : Fin scope.length //
    (scope.get index).uid = uid ∧ (scope.get index).parameters = pack ∧
      (scope.get index).role = role}

def enterOwner (uid : Nat) (pack : Parameters sigma) (address : InternalAddress)
    (role : Fin 2) (scope : List (OwnerSlot sigma)) : List (OwnerSlot sigma) :=
  ⟨uid, address, pack, role⟩ :: scope

mutual

def Kernel : {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    Provider tree → InternalAddress → List (OwnerSlot sigma) → Type (max u v)
  | _, .interface _, provider, address, scope => provider PUnit.unit address scope
  | _, .ordinary o children, provider, address, scope =>
      match o.instanceData with
      | .top role pack uid _ _ =>
          EligibleOwner uid pack role scope ×
            ChildrenKernel children provider address 0 scope
      | .bottom pack uid _ => BottomKernel children provider uid pack address scope
      | _ => ChildrenKernel children provider address 0 scope

def ChildrenKernel : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → ChildrenProvider children →
    InternalAddress → Nat → List (OwnerSlot sigma) → Type (max u v)
  | _, .nil, _, _, _, _ => PUnit
  | _, .cons head tail, provider, address, slot, scope =>
      Kernel head (fun h => provider (.inl h)) (address ++ [slot]) scope ×
        ChildrenKernel tail (fun h => provider (.inr h)) address (slot + 1) scope

/-- Malformed bottom arities have no certificate; exact admission separately
checks the genuine equal-sequent binary rule. -/
def BottomKernel : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → ChildrenProvider children →
    Nat → Parameters sigma → InternalAddress → List (OwnerSlot sigma) → Type (max u v)
  | _, .nil, _, _, _, _, _ => PEmpty
  | _, .cons _ .nil, _, _, _, _, _ => PEmpty
  | _, .cons left (.cons right .nil), provider, uid, pack, address, scope =>
      Kernel left (fun h => provider (.inl h)) (address ++ [0])
          (enterOwner uid pack address 0 scope) ×
        Kernel right (fun h => provider (.inr (.inl h))) (address ++ [1])
          (enterOwner uid pack address 1 scope)
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, _ => PEmpty

end

def emptyProvider {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G) :
    Provider tree := fun _ _ _ => PEmpty

abbrev ClosedKernel {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) (scope : List (OwnerSlot sigma)) :=
  Kernel tree (emptyProvider tree) address scope

mutual

def remainderProvider : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (cut : CKCutPlan tree) →
    Provider tree → Provider cut.remainder
  | _, _, .interface _, provider => provider
  | _, _, .ordinary _ _ cuts, provider => childrenRemainderProvider cuts provider

def childrenRemainderProvider : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma (Data sigma) Gs} → (cuts : CKChildCuts children) →
    ChildrenProvider children → ChildrenProvider cuts.remainder
  | _, _, .nil, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, provider, hole =>
      match hole with
      | .inl hole => branchProvider head (fun h => provider (.inl h)) hole
      | .inr hole => childrenRemainderProvider tail (fun h => provider (.inr h)) hole

def branchProvider : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (cut : CKBranchCut tree) →
    Provider tree → Provider cut.remainder
  | _, tree, .detach _, provider, _, address, scope => Kernel tree provider address scope
  | _, _, .descend cut, provider, hole, address, scope =>
      remainderProvider cut provider hole address scope

end

mutual

/-- Actual restriction/gluing of ordered certificate entries, before collection.
Inherited source holes keep their providers; detached factors inherit the scope
supplied by the same remainder certificate. No independent closure is assumed. -/
def cutEquiv : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (cut : CKCutPlan tree) →
    (provider : Provider tree) → (address : InternalAddress) →
    (scope : List (OwnerSlot sigma)) →
    Kernel tree provider address scope ≃
      Kernel cut.remainder (remainderProvider cut provider) address scope
  | _, _, .interface _, _, _, _ => Equiv.refl _
  | _, _, .ordinary o _ cuts, provider, address, scope => by
      cases label : o.instanceData <;> simp only [Kernel, CKCutPlan.remainder, label]
      all_goals first
        | exact Equiv.prodCongr (Equiv.refl _) (childrenEquiv cuts provider address 0 scope)
        | exact bottomEquiv cuts provider _ _ address scope
        | exact childrenEquiv cuts provider address 0 scope

def childrenEquiv : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma (Data sigma) Gs} → (cuts : CKChildCuts children) →
    (provider : ChildrenProvider children) → (address : InternalAddress) →
    (slot : Nat) → (scope : List (OwnerSlot sigma)) →
    ChildrenKernel children provider address slot scope ≃
      ChildrenKernel cuts.remainder (childrenRemainderProvider cuts provider) address slot scope
  | _, _, .nil, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ head tail, provider, address, slot, scope =>
      Equiv.prodCongr
        (branchEquiv head (fun h => provider (.inl h)) (address ++ [slot]) scope)
        (childrenEquiv tail (fun h => provider (.inr h)) address (slot + 1) scope)

def bottomEquiv : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma (Data sigma) Gs} → (cuts : CKChildCuts children) →
    (provider : ChildrenProvider children) → (uid : Nat) → (pack : Parameters sigma) →
    (address : InternalAddress) → (scope : List (OwnerSlot sigma)) →
    BottomKernel children provider uid pack address scope ≃
      BottomKernel cuts.remainder (childrenRemainderProvider cuts provider) uid pack address scope
  | _, _, .nil, _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ _ .nil, _, _, _, _, _ => Equiv.refl _
  | _, _, .cons _ _ left (.cons _ _ right .nil), provider, uid, pack, address, scope =>
      Equiv.prodCongr
        (branchEquiv left (fun h => provider (.inl h)) (address ++ [0])
          (enterOwner uid pack address 0 scope))
        (branchEquiv right (fun h => provider (.inr (.inl h))) (address ++ [1])
          (enterOwner uid pack address 1 scope))
  | _, _, .cons _ _ _ (.cons _ _ _ (.cons _ _ _ _)), _, _, _, _, _ => Equiv.refl _

def branchEquiv : {G : Hypersequent sigma} →
    {tree : CKTree sigma (Data sigma) G} → (cut : CKBranchCut tree) →
    (provider : Provider tree) → (address : InternalAddress) →
    (scope : List (OwnerSlot sigma)) →
    Kernel tree provider address scope ≃
      Kernel cut.remainder (branchProvider cut provider) address scope
  | _, _, .detach _, _, _, _ => Equiv.refl _
  | _, _, .descend cut, provider, address, scope => cutEquiv cut provider address scope

end

def remainderStagesEquiv {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (first : CKBranchCut tree) (second : CKBranchCut first.remainder)
    (provider : Provider tree) (address : InternalAddress) (scope : List (OwnerSlot sigma)) :
    Kernel tree provider address scope ≃
      Kernel second.remainder (branchProvider second (branchProvider first provider)) address scope :=
  (branchEquiv first provider address scope).trans
    (branchEquiv second (branchProvider first provider) address scope)

theorem staged_glue_restrict {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (first : CKBranchCut tree) (second : CKBranchCut first.remainder)
    (provider : Provider tree) (address : InternalAddress) (scope : List (OwnerSlot sigma))
    (certificate : Kernel tree provider address scope) :
    (remainderStagesEquiv first second provider address scope).symm
      (remainderStagesEquiv first second provider address scope certificate) = certificate :=
  (remainderStagesEquiv first second provider address scope).symm_apply_apply certificate

theorem staged_restrict_glue {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    (first : CKBranchCut tree) (second : CKBranchCut first.remainder)
    (provider : Provider tree) (address : InternalAddress) (scope : List (OwnerSlot sigma))
    (pieces : Kernel second.remainder
      (branchProvider second (branchProvider first provider)) address scope) :
    remainderStagesEquiv first second provider address scope
      ((remainderStagesEquiv first second provider address scope).symm pieces) = pieces :=
  (remainderStagesEquiv first second provider address scope).apply_symm_apply pieces

#check @branchEquiv
#print axioms branchEquiv
#print axioms remainderStagesEquiv
#print axioms staged_glue_restrict
#print axioms staged_restrict_glue

end Potkin.Research.OpenDischargeCertificates

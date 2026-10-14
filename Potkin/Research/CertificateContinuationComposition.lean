import Potkin.Research.OpenCertificateKernel
import Potkin.Research.CutHoleAdapter

/-!
# Open continuation substitution with physical interface reindexing

This layer permits open fillers.  The inherited interfaces are reindexed by
the native filled-leaf equivalence, not confused with cut-created interfaces.
All kernel maps below act on actual witness choices, before counting.
-/

namespace Potkin.Research.CertificateContinuationComposition

open RevivalInterface OpenCertificateKernel

def factorProvider {G : Hypersequent sigma} (tree : CKTree sigma Data G)
    (fillers : tree.LeafAssignment) (provider : Provider (tree.fillAssignment fillers)) :
    Provider tree := fun hole address scope =>
  Kernel (fillers hole)
    (fun inner => provider (tree.fillLeafJoin fillers ⟨hole, inner⟩)) address scope

def childFactorProvider {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs) (fillers : children.LeafAssignment)
    (provider : ChildrenProvider (children.fillAssignment fillers)) : ChildrenProvider children :=
  fun hole address scope => Kernel (fillers hole)
    (fun inner => provider (children.fillLeafJoin fillers ⟨hole, inner⟩)) address scope

mutual

/-- Universal open substitution.  The map retains shared owner colours,
indexed ancestor choices, ordered premise witnesses and interface identity. -/
def continuationEquiv : {G : Hypersequent sigma} → (tree : CKTree sigma Data G) →
    (fillers : tree.LeafAssignment) → (provider : Provider (tree.fillAssignment fillers)) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    Kernel (tree.fillAssignment fillers) provider address scope ≃
      Kernel tree (factorProvider tree fillers provider) address scope
  | _, .interface _, _, _, _, _ => Equiv.refl _
  | _, .ordinary o children, fillers, provider, address, scope => by
      cases label : o.instanceData <;>
        simp only [CKTree.fillAssignment, Kernel, label]
      all_goals first
        | exact ghostFillEquiv children _ _ fillers
        | exact ownerContinuationEquiv children fillers provider address _
        | exact childrenContinuationEquiv children fillers provider address 0 _

def childrenContinuationEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (fillers : children.LeafAssignment) →
    (provider : ChildrenProvider (children.fillAssignment fillers)) →
    (address : InternalAddress) → (slot : Nat) → (scope : List OwnerSlot) →
    ChildrenKernel (children.fillAssignment fillers) provider address slot scope ≃
      ChildrenKernel children (childFactorProvider children fillers provider) address slot scope
  | _, .nil, _, _, _, _, _ => Equiv.refl _
  | _, .cons head tail, fillers, provider, address, slot, scope =>
      Equiv.prodCongr
        (continuationEquiv head (fun h => fillers (.inl h))
          (fun h => provider (.inl h)) (address ++ [slot]) scope)
        (childrenContinuationEquiv tail (fun h => fillers (.inr h))
          (fun h => provider (.inr h)) address (slot + 1) scope)

def ownerContinuationEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (fillers : children.LeafAssignment) →
    (provider : ChildrenProvider (children.fillAssignment fillers)) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    OwnerKernel (children.fillAssignment fillers) provider address scope ≃
      OwnerKernel children (childFactorProvider children fillers provider) address scope
  | _, .nil, _, _, _, _ => Equiv.refl _
  | _, .cons _ .nil, _, _, _, _ => Equiv.refl _
  | _, .cons left (.cons right .nil), fillers, provider, address, scope =>
      Equiv.sigmaCongrRight fun colour => Equiv.prodCongr
        (continuationEquiv left (fun h => fillers (.inl h))
          (fun h => provider (.inl h)) (address ++ [0])
          (enterOwner address colour false scope))
        (continuationEquiv right (fun h => fillers (.inr (.inl h)))
          (fun h => provider (.inr (.inl h))) (address ++ [1])
          (enterOwner address colour true scope))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _ => Equiv.refl _

end

/-- Replacement at the inherited interfaces of open fillers. -/
def factorProviderEquiv {G : Hypersequent sigma} (tree : CKTree sigma Data G)
    (fillers : tree.LeafAssignment)
    (left right : Provider (tree.fillAssignment fillers))
    (change : ∀ hole address scope, left hole address scope ≃ right hole address scope)
    (hole : tree.LeafOccurrence) (address : InternalAddress) (scope : List OwnerSlot) :
    factorProvider tree fillers left hole address scope ≃
      factorProvider tree fillers right hole address scope :=
  providerEquiv (fillers hole)
    (fun inner => left (tree.fillLeafJoin fillers ⟨hole, inner⟩))
    (fun inner => right (tree.fillLeafJoin fillers ⟨hole, inner⟩))
    (fun inner => change (tree.fillLeafJoin fillers ⟨hole, inner⟩)) address scope

def childFactorProviderEquiv {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs) (fillers : children.LeafAssignment)
    (left right : ChildrenProvider (children.fillAssignment fillers))
    (change : ∀ hole address scope, left hole address scope ≃ right hole address scope)
    (hole : children.LeafOccurrence) (address : InternalAddress) (scope : List OwnerSlot) :
    childFactorProvider children fillers left hole address scope ≃
      childFactorProvider children fillers right hole address scope :=
  providerEquiv (fillers hole)
    (fun inner => left (children.fillLeafJoin fillers ⟨hole, inner⟩))
    (fun inner => right (children.fillLeafJoin fillers ⟨hole, inner⟩))
    (fun inner => change (children.fillLeafJoin fillers ⟨hole, inner⟩)) address scope

mutual

/-- Naturality is an equality of the actual restriction maps, not merely
equality of cardinalities or a definition by conjugation. -/
theorem continuation_naturality : {G : Hypersequent sigma} →
    (tree : CKTree sigma Data G) → (fillers : tree.LeafAssignment) →
    (left right : Provider (tree.fillAssignment fillers)) →
    (change : ∀ hole address scope, left hole address scope ≃ right hole address scope) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    (witness : Kernel (tree.fillAssignment fillers) left address scope) →
    providerEquiv tree (factorProvider tree fillers left) (factorProvider tree fillers right)
      (factorProviderEquiv tree fillers left right change) address scope
      (continuationEquiv tree fillers left address scope witness) =
    continuationEquiv tree fillers right address scope
      (providerEquiv (tree.fillAssignment fillers) left right change address scope witness)
  | _, .interface _, _, _, _, _, _, _, _ => rfl
  | _, .ordinary o children, fillers, left, right, change, address, scope, witness => by
      have childLaw := childrenContinuation_naturality children fillers left right change address 0
        (advance (emptyConclusion o.instanceData) scope)
      have ownerLaw := ownerContinuation_naturality children fillers left right change address
        (advance (emptyConclusion o.instanceData) scope)
      cases o with
      | mk identifier kind shape label incidence =>
          cases label <;> first
            | rfl
            | exact ownerLaw witness
            | exact childLaw witness
termination_by structural _ tree _ _ _ _ _ _ _ => tree

theorem childrenContinuation_naturality : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (fillers : children.LeafAssignment) →
    (left right : ChildrenProvider (children.fillAssignment fillers)) →
    (change : ∀ hole address scope, left hole address scope ≃ right hole address scope) →
    (address : InternalAddress) → (slot : Nat) → (scope : List OwnerSlot) →
    (witness : ChildrenKernel (children.fillAssignment fillers) left address slot scope) →
    childrenProviderEquiv children (childFactorProvider children fillers left)
      (childFactorProvider children fillers right)
      (childFactorProviderEquiv children fillers left right change) address slot scope
      (childrenContinuationEquiv children fillers left address slot scope witness) =
    childrenContinuationEquiv children fillers right address slot scope
      (childrenProviderEquiv (children.fillAssignment fillers) left right change address slot scope witness)
  | _, .nil, _, _, _, _, _, _, _, witness => by cases witness; rfl
  | _, .cons head tail, fillers, left, right, change, address, slot, scope, witness => by
      rcases witness with ⟨headWitness, tailWitness⟩
      exact congrArg₂ Prod.mk
        (continuation_naturality head (fun h => fillers (.inl h))
          (fun h => left (.inl h)) (fun h => right (.inl h))
          (fun h => change (.inl h)) (address ++ [slot]) scope headWitness)
        (childrenContinuation_naturality tail (fun h => fillers (.inr h))
          (fun h => left (.inr h)) (fun h => right (.inr h))
          (fun h => change (.inr h)) address (slot + 1) scope tailWitness)
termination_by structural _ children _ _ _ _ _ _ _ _ => children

theorem ownerContinuation_naturality : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (fillers : children.LeafAssignment) →
    (left right : ChildrenProvider (children.fillAssignment fillers)) →
    (change : ∀ hole address scope, left hole address scope ≃ right hole address scope) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    (witness : OwnerKernel (children.fillAssignment fillers) left address scope) →
    ownerProviderEquiv children (childFactorProvider children fillers left)
      (childFactorProvider children fillers right)
      (childFactorProviderEquiv children fillers left right change) address scope
      (ownerContinuationEquiv children fillers left address scope witness) =
    ownerContinuationEquiv children fillers right address scope
      (ownerProviderEquiv (children.fillAssignment fillers) left right change address scope witness)
  | _, .nil, _, _, _, _, _, _, witness => nomatch witness
  | _, .cons _ .nil, _, _, _, _, _, _, witness => nomatch witness
  | _, .cons leftTree (.cons rightTree .nil), fillers, left, right, change, address, scope, witness => by
      rcases witness with ⟨colour, leftWitness, rightWitness⟩
      exact congrArg (Sigma.mk colour) (congrArg₂ Prod.mk
        (continuation_naturality leftTree (fun h => fillers (.inl h))
          (fun h => left (.inl h)) (fun h => right (.inl h)) (fun h => change (.inl h))
          (address ++ [0]) (enterOwner address colour false scope) leftWitness)
        (continuation_naturality rightTree (fun h => fillers (.inr (.inl h)))
          (fun h => left (.inr (.inl h))) (fun h => right (.inr (.inl h)))
          (fun h => change (.inr (.inl h))) (address ++ [1])
          (enterOwner address colour true scope) rightWitness))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, _, _, witness => nomatch witness
termination_by structural _ children _ _ _ _ _ _ _ => children

end

end Potkin.Research.CertificateContinuationComposition

#check Potkin.Research.CertificateContinuationComposition.continuationEquiv
#print axioms Potkin.Research.CertificateContinuationComposition.continuationEquiv
#print axioms Potkin.Research.CertificateContinuationComposition.factorProviderEquiv
#print axioms Potkin.Research.CertificateContinuationComposition.continuation_naturality

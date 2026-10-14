import Potkin.Research.CertificateCutGluing
import Potkin.Research.CertificateContinuationComposition

/-!
# Actual two-level certificate restriction maps

The intermediate pieces are allowed to be open.  Their interfaces are physical
native leaves, rather than an identification of every open leaf with a first
cut site.  The nested map is constructed independently by recursion; its
commuting theorem is not a definition by conjugation.
-/

namespace Potkin.Research.CertificateNestedGluing

open RevivalInterface OpenCertificateKernel

def NestedProvider {G : Hypersequent sigma} (context : CKTree sigma Data G)
    (first : context.LeafAssignment)
    (second : ∀ hole, (first hole).LeafAssignment) : Provider context :=
  fun hole actual inherited =>
    Kernel (first hole) (factorClosedProvider (first hole) (second hole)) actual inherited

def nestedAssignment {G : Hypersequent sigma} (context : CKTree sigma Data G)
    (first : context.LeafAssignment)
    (second : ∀ hole, (first hole).LeafAssignment) : context.LeafAssignment :=
  fun hole => (first hole).fillAssignment (second hole)

def NestedChildrenProvider {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs) (first : children.LeafAssignment)
    (second : ∀ hole, (first hole).LeafAssignment) : ChildrenProvider children :=
  fun hole actual inherited =>
    Kernel (first hole) (factorClosedProvider (first hole) (second hole)) actual inherited

mutual

/-- Independently constructed two-level restriction: each first interface
continues into its own open intermediate piece and then its aligned factors. -/
def nestedRestrictionEquiv : {G : Hypersequent sigma} →
    (context : CKTree sigma Data G) → (first : context.LeafAssignment) →
    (second : ∀ hole, (first hole).LeafAssignment) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    ClosedKernel (context.fillAssignment (nestedAssignment context first second)) address scope ≃
      Kernel context (NestedProvider context first second) address scope
  | _, .interface _, first, second, address, scope =>
      fillEquiv (first PUnit.unit) (second PUnit.unit) address scope
  | _, .ordinary o children, first, second, address, scope => by
      cases label : o.instanceData <;>
        simp only [ClosedKernel, CKTree.fillAssignment, Kernel, label]
      all_goals first
        | exact ghostFillEquiv children _ _ _
        | exact nestedOwnerRestrictionEquiv children first second address _
        | exact nestedChildrenRestrictionEquiv children first second address 0 _

def nestedChildrenRestrictionEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (first : children.LeafAssignment) →
    (second : ∀ hole, (first hole).LeafAssignment) →
    (address : InternalAddress) → (slot : Nat) → (scope : List OwnerSlot) →
    ChildrenKernel (children.fillAssignment (fun hole => (first hole).fillAssignment (second hole)))
      (fun _ _ _ => PEmpty) address slot scope ≃
      ChildrenKernel children (NestedChildrenProvider children first second) address slot scope
  | _, .nil, _, _, _, _, _ => Equiv.refl _
  | _, .cons head tail, first, second, address, slot, scope =>
      Equiv.prodCongr
        (nestedRestrictionEquiv head (fun h => first (.inl h))
          (fun h => second (.inl h)) (address ++ [slot]) scope)
        (nestedChildrenRestrictionEquiv tail (fun h => first (.inr h))
          (fun h => second (.inr h)) address (slot + 1) scope)

def nestedOwnerRestrictionEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (first : children.LeafAssignment) →
    (second : ∀ hole, (first hole).LeafAssignment) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    OwnerKernel (children.fillAssignment (fun hole => (first hole).fillAssignment (second hole)))
      (fun _ _ _ => PEmpty) address scope ≃
      OwnerKernel children (NestedChildrenProvider children first second) address scope
  | _, .nil, _, _, _, _ => Equiv.refl _
  | _, .cons _ .nil, _, _, _, _ => Equiv.refl _
  | _, .cons left (.cons right .nil), first, second, address, scope =>
      Equiv.sigmaCongrRight fun colour => Equiv.prodCongr
        (nestedRestrictionEquiv left (fun h => first (.inl h)) (fun h => second (.inl h))
          (address ++ [0]) (enterOwner address colour false scope))
        (nestedRestrictionEquiv right (fun h => first (.inr (.inl h)))
          (fun h => second (.inr (.inl h)))
          (address ++ [1]) (enterOwner address colour true scope))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _ => Equiv.refl _

end

def secondRestriction {G : Hypersequent sigma} (context : CKTree sigma Data G)
    (first : context.LeafAssignment) (second : ∀ hole, (first hole).LeafAssignment)
    (address : InternalAddress) (scope : List OwnerSlot) :=
  providerEquiv context (factorClosedProvider context (nestedAssignment context first second))
    (NestedProvider context first second)
    (fun hole actual inherited => fillEquiv (first hole) (second hole) actual inherited)
    address scope

def secondChildrenRestriction {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs)
    (first : children.LeafAssignment) (second : ∀ hole, (first hole).LeafAssignment)
    (address : InternalAddress) (slot : Nat) (scope : List OwnerSlot) :=
  childrenProviderEquiv children
    (fun hole actual inherited => ClosedKernel ((first hole).fillAssignment (second hole)) actual inherited)
    (NestedChildrenProvider children first second)
    (fun hole actual inherited => fillEquiv (first hole) (second hole) actual inherited)
    address slot scope

def secondOwnerRestriction {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs)
    (first : children.LeafAssignment) (second : ∀ hole, (first hole).LeafAssignment)
    (address : InternalAddress) (scope : List OwnerSlot) :=
  ownerProviderEquiv children
    (fun hole actual inherited => ClosedKernel ((first hole).fillAssignment (second hole)) actual inherited)
    (NestedChildrenProvider children first second)
    (fun hole actual inherited => fillEquiv (first hole) (second hole) actual inherited)
    address scope

mutual

/-- Actual restriction diagram: first restrict the source to the outer pieces,
then restrict their callbacks, or recurse directly through both levels.  The
same colours and indexed ghost assignments result, not just equal counts. -/
theorem restriction_coherence : {G : Hypersequent sigma} →
    (context : CKTree sigma Data G) → (first : context.LeafAssignment) →
    (second : ∀ hole, (first hole).LeafAssignment) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    (witness : ClosedKernel (context.fillAssignment (nestedAssignment context first second)) address scope) →
    secondRestriction context first second address scope
      (fillEquiv context (nestedAssignment context first second) address scope witness) =
    nestedRestrictionEquiv context first second address scope witness
  | _, .interface _, _, _, _, _, _ => rfl
  | _, .ordinary o children, first, second, address, scope, witness => by
      have childLaw := childrenRestriction_coherence children first second address 0
        (advance (emptyConclusion o.instanceData) scope)
      have ownerLaw := ownerRestriction_coherence children first second address
        (advance (emptyConclusion o.instanceData) scope)
      cases o with
      | mk identifier kind shape label incidence =>
          cases label <;> first
            | rfl
            | exact ownerLaw witness
            | exact childLaw witness
termination_by structural _ context _ _ _ _ _ => context

theorem childrenRestriction_coherence : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (first : children.LeafAssignment) →
    (second : ∀ hole, (first hole).LeafAssignment) →
    (address : InternalAddress) → (slot : Nat) → (scope : List OwnerSlot) →
    (witness : ChildrenKernel
      (children.fillAssignment (fun h => (first h).fillAssignment (second h)))
      (fun _ _ _ => PEmpty) address slot scope) →
    secondChildrenRestriction children first second address slot scope
      (childrenFillEquiv children (fun h => (first h).fillAssignment (second h)) address slot scope witness) =
    nestedChildrenRestrictionEquiv children first second address slot scope witness
  | _, .nil, _, _, _, _, _, witness => by cases witness; rfl
  | _, .cons head tail, first, second, address, slot, scope, witness => by
      rcases witness with ⟨headWitness, tailWitness⟩
      exact congrArg₂ Prod.mk
        (restriction_coherence head (fun h => first (.inl h)) (fun h => second (.inl h))
          (address ++ [slot]) scope headWitness)
        (childrenRestriction_coherence tail (fun h => first (.inr h)) (fun h => second (.inr h))
          address (slot + 1) scope tailWitness)
termination_by structural _ children _ _ _ _ _ _ => children

theorem ownerRestriction_coherence : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (first : children.LeafAssignment) →
    (second : ∀ hole, (first hole).LeafAssignment) →
    (address : InternalAddress) → (scope : List OwnerSlot) →
    (witness : OwnerKernel
      (children.fillAssignment (fun h => (first h).fillAssignment (second h)))
      (fun _ _ _ => PEmpty) address scope) →
    secondOwnerRestriction children first second address scope
      (ownerFillEquiv children (fun h => (first h).fillAssignment (second h)) address scope witness) =
    nestedOwnerRestrictionEquiv children first second address scope witness
  | _, .nil, _, _, _, _, witness => nomatch witness
  | _, .cons _ .nil, _, _, _, _, witness => nomatch witness
  | _, .cons left (.cons right .nil), first, second, address, scope, witness => by
      rcases witness with ⟨colour, leftWitness, rightWitness⟩
      exact congrArg (Sigma.mk colour) (congrArg₂ Prod.mk
        (restriction_coherence left (fun h => first (.inl h)) (fun h => second (.inl h))
          (address ++ [0]) (enterOwner address colour false scope) leftWitness)
        (restriction_coherence right (fun h => first (.inr (.inl h)))
          (fun h => second (.inr (.inl h))) (address ++ [1])
          (enterOwner address colour true scope) rightWitness))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, witness => nomatch witness
termination_by structural _ children _ _ _ _ _ => children

end

/-- The inverse diagram follows from the proved map equality and genuine
inverse laws, retaining the same global witness. -/
theorem gluing_coherence {G : Hypersequent sigma} (context : CKTree sigma Data G)
    (first : context.LeafAssignment) (second : ∀ hole, (first hole).LeafAssignment)
    (address : InternalAddress) (scope : List OwnerSlot)
    (pieces : Kernel context (NestedProvider context first second) address scope) :
    (fillEquiv context (nestedAssignment context first second) address scope).symm
      ((secondRestriction context first second address scope).symm pieces) =
    (nestedRestrictionEquiv context first second address scope).symm pieces := by
  apply (nestedRestrictionEquiv context first second address scope).injective
  rw [← restriction_coherence, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

end Potkin.Research.CertificateNestedGluing

#check Potkin.Research.CertificateNestedGluing.restriction_coherence
#print axioms Potkin.Research.CertificateNestedGluing.restriction_coherence
#print axioms Potkin.Research.CertificateNestedGluing.gluing_coherence

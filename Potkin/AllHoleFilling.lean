import Potkin.GeneralFilling

/-!
# Simultaneous filling of all native typed interfaces

`LeafOccurrence` is a canonical occurrence INDEX, not another tree syntax.
It has one value per physical interface; no PunctureAt evidence is part of
its identity. The dependent assignment retains the entire native boundary.
The adapter recurses through the native ordered children and invokes native
puncture insertion at the interface clause. It is independent of CK cuts.
-/

namespace Potkin
universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual
def CKTree.LeafOccurrence : {G : Hypersequent sigma} →
    CKTree sigma InstanceData G → Type (max (max u v) w)
  | _, .interface _ => PUnit.{max (max u v) w + 1}
  | _, .ordinary _ children => children.LeafOccurrence

def CKChildren.LeafOccurrence : {Gs : List (Hypersequent sigma)} →
    CKChildren sigma InstanceData Gs → Type (max (max u v) w)
  | _, .nil => PEmpty.{max (max u v) w + 1}
  | _, .cons head tail => head.LeafOccurrence ⊕ tail.LeafOccurrence
end

mutual
def CKTree.leafBoundary : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → tree.LeafOccurrence → Hypersequent sigma
  | G, .interface _, _ => G
  | _, .ordinary _ children, hole => children.leafBoundary hole

def CKChildren.leafBoundary : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) →
      children.LeafOccurrence → Hypersequent sigma
  | _, .nil, hole => nomatch hole
  | _, .cons head tail, hole =>
      match hole with
      | Sum.inl hole => head.leafBoundary hole
      | Sum.inr hole => tail.leafBoundary hole
end

mutual
def CKTree.leafAddress : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → tree.LeafOccurrence → InternalAddress
  | _, .interface _, _ => []
  | _, .ordinary _ children, hole => children.leafAddress hole

def CKChildren.leafAddress : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → children.LeafOccurrence → InternalAddress
  | _, .nil, hole => nomatch hole
  | _, .cons head tail, hole =>
      match hole with
      | Sum.inl hole => 0 :: head.leafAddress hole
      | Sum.inr hole => InternalAddress.shiftHead (tail.leafAddress hole)
end

mutual
def CKTree.leafOrder : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → List tree.LeafOccurrence
  | _, .interface _ => [PUnit.unit]
  | _, .ordinary _ children => children.leafOrder

def CKChildren.leafOrder : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → List children.LeafOccurrence
  | _, .nil => []
  | _, .cons head tail => head.leafOrder.map Sum.inl ++ tail.leafOrder.map Sum.inr
end

abbrev CKTree.LeafAssignment {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) :=
  (hole : tree.LeafOccurrence) → CKTree sigma InstanceData (tree.leafBoundary hole)

abbrev CKChildren.LeafAssignment {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData Gs) :=
  (hole : children.LeafOccurrence) → CKTree sigma InstanceData (children.leafBoundary hole)

mutual
def CKTree.fillAssignment : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → tree.LeafAssignment → CKTree sigma InstanceData G
  | G, .interface _, assignment =>
      (CKTree.PunctureAt.root : CKTree.PunctureAt G (.interface G) []).insert
        (assignment PUnit.unit)
  | _, .ordinary o children, assignment =>
      .ordinary o (children.fillAssignment assignment)

def CKChildren.fillAssignment : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → children.LeafAssignment →
      CKChildren sigma InstanceData Gs
  | _, .nil, _ => .nil
  | _, .cons head tail, assignment =>
      .cons (head.fillAssignment (fun h => assignment (.inl h)))
        (tail.fillAssignment (fun h => assignment (.inr h)))
end

theorem CKTree.ordinary_children_injective (o : LocalOccurrence sigma InstanceData)
    {left right : CKChildren sigma InstanceData o.shape.premises}
    (equal : CKTree.ordinary o left = CKTree.ordinary o right) : left = right := by
  exact CKTree.ordinary.inj equal

mutual
theorem CKTree.fillAssignment_injective : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → Function.Injective tree.fillAssignment
  | _, .interface _, left, right, equal => by
      funext hole
      cases hole
      exact equal
  | _, .ordinary o children, left, right, equal =>
      children.fillAssignment_injective (CKTree.ordinary_children_injective o equal)

theorem CKChildren.fillAssignment_injective : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → Function.Injective children.fillAssignment
  | _, .nil, left, right, _ => by funext hole; exact nomatch hole
  | _, .cons head tail, left, right, equal => by
      have pieces := CKChildren.cons.inj equal
      have heads := head.fillAssignment_injective pieces.1
      have tails := tail.fillAssignment_injective pieces.2
      funext hole
      cases hole with
      | inl hole => exact congrFun heads hole
      | inr hole => exact congrFun tails hole
end

mutual
theorem CKTree.fillAssignment_locallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} → (tree : CKTree sigma InstanceData G) →
    (assignment : tree.LeafAssignment) → LocallyAdmittedTree P tree →
    (∀ hole, LocallyAdmittedTree P (assignment hole)) →
      LocallyAdmittedTree P (tree.fillAssignment assignment)
  | _, .interface _, _, _, providers => providers PUnit.unit
  | _, .ordinary _ children, assignment, source, providers =>
      ⟨source.1, children.fillAssignment_locallyAdmitted assignment source.2 providers⟩

theorem CKChildren.fillAssignment_locallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma InstanceData Gs) →
    (assignment : children.LeafAssignment) → LocallyAdmittedChildren P children →
    (∀ hole, LocallyAdmittedTree P (assignment hole)) →
      LocallyAdmittedChildren P (children.fillAssignment assignment)
  | _, .nil, _, _, _ => trivial
  | _, .cons head tail, assignment, source, providers =>
      ⟨head.fillAssignment_locallyAdmitted (fun h => assignment (.inl h)) source.1
          (fun h => providers (.inl h)),
        tail.fillAssignment_locallyAdmitted (fun h => assignment (.inr h)) source.2
          (fun h => providers (.inr h))⟩
end

theorem CKTree.fillAssignment_isOrdinary {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (assignment : tree.LeafAssignment) : (tree.fillAssignment assignment).IsOrdinary := by
  cases tree with
  | interface _ => exact ordinary.elim
  | ordinary _ _ => trivial

end Potkin

#print axioms Potkin.CKTree.fillAssignment_injective
#print axioms Potkin.CKTree.fillAssignment_locallyAdmitted

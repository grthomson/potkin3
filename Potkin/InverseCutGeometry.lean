import Potkin.AllHoleFilling

namespace Potkin
universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual
def CKTree.leafPuncture : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (hole : tree.LeafOccurrence) →
      CKTree.PunctureAt (tree.leafBoundary hole) tree (tree.leafAddress hole)
  | _, .interface _, _ => .root
  | _, .ordinary o children, hole => by
      let below := children.leafPuncture hole
      rw [show (CKTree.ordinary o children).leafAddress hole = below.slot :: below.rest
        from below.address_eq]
      exact .child o children below.slot below.rest below.witness

def CKChildren.leafPuncture : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (hole : children.LeafOccurrence) →
      CKChildren.AddressPuncture (children.leafBoundary hole) children (children.leafAddress hole)
  | _, .nil, hole => nomatch hole
  | _, .cons head tail, hole =>
      match hole with
      | Sum.inl hole =>
          ⟨0, head.leafAddress hole, rfl, .head head tail _ (head.leafPuncture hole)⟩
      | Sum.inr hole => by
          let below := tail.leafPuncture hole
          exact ⟨below.slot + 1, below.rest,
            congrArg InternalAddress.shiftHead below.address_eq,
            .tail head tail below.slot below.rest below.witness⟩
end

mutual
theorem CKTree.leafAddress_injective : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → Function.Injective tree.leafAddress
  | _, .interface _, left, right, _ => by cases left; cases right; rfl
  | _, .ordinary _ children, _, _, equal => children.leafAddress_injective equal

theorem CKChildren.leafAddress_injective : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → Function.Injective children.leafAddress
  | _, .nil, hole, _, _ => nomatch hole
  | _, .cons head tail, left, right, equal => by
      cases left with
      | inl left =>
          cases right with
          | inl right =>
              exact congrArg Sum.inl (head.leafAddress_injective (List.cons.inj equal).2)
          | inr right =>
              have part := tail.leafPuncture right
              change 0 :: _ = InternalAddress.shiftHead (tail.leafAddress right) at equal
              rw [part.address_eq] at equal
              exact False.elim (Nat.succ_ne_zero _ (List.cons.inj equal).1.symm)
      | inr left =>
          cases right with
          | inl right =>
              have part := tail.leafPuncture left
              change InternalAddress.shiftHead (tail.leafAddress left) = 0 :: _ at equal
              rw [part.address_eq] at equal
              exact False.elim (Nat.succ_ne_zero _ (List.cons.inj equal).1)
          | inr right =>
              have lp := tail.leafPuncture left
              have rp := tail.leafPuncture right
              apply congrArg Sum.inr
              apply tail.leafAddress_injective
              exact InternalAddress.shiftHead_injective_of_nonempty
                (by rw [lp.address_eq]; simp) (by rw [rp.address_eq]; simp) equal
end

mutual
theorem CKTree.PunctureAt.exists_leafOccurrence : {G H : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → {address : InternalAddress} →
    CKTree.PunctureAt H tree address →
      ∃ hole : tree.LeafOccurrence, tree.leafAddress hole = address ∧ tree.leafBoundary hole = H
  | _, _, _, _, .root => ⟨PUnit.unit, rfl, rfl⟩
  | _, _, _, _, .child _ _ _ _ below => below.exists_leafOccurrence

theorem CKChildren.PunctureAt.exists_leafOccurrence : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    CKChildren.PunctureAt H children slot address →
      ∃ hole : children.LeafOccurrence,
        children.leafAddress hole = slot :: address ∧ children.leafBoundary hole = H
  | _, _, _, _, _, .head _ _ _ below => by
      rcases below.exists_leafOccurrence with ⟨hole, addr, boundary⟩
      exact ⟨.inl hole, congrArg (List.cons 0) addr, boundary⟩
  | _, _, _, _, _, .tail _ _ _ _ below => by
      rcases below.exists_leafOccurrence with ⟨hole, addr, boundary⟩
      exact ⟨.inr hole, congrArg InternalAddress.shiftHead addr, boundary⟩
end

mutual
theorem CKTree.leaf_mem_leafOrder : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (hole : tree.LeafOccurrence) → hole ∈ tree.leafOrder
  | _, .interface _, hole => by cases hole; simp [CKTree.leafOrder]
  | _, .ordinary _ children, hole => children.leaf_mem_leafOrder hole

theorem CKChildren.leaf_mem_leafOrder : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) →
      (hole : children.LeafOccurrence) → hole ∈ children.leafOrder
  | _, .nil, hole => nomatch hole
  | _, .cons head tail, hole => by
      cases hole with
      | inl hole => exact
          List.mem_append_left _ (List.mem_map.mpr ⟨hole, head.leaf_mem_leafOrder hole, rfl⟩)
      | inr hole => exact
          List.mem_append_right _ (List.mem_map.mpr ⟨hole, tail.leaf_mem_leafOrder hole, rfl⟩)
end

mutual
theorem CKTree.leafOrder_nodup : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → tree.leafOrder.Nodup
  | _, .interface _ => by simp [CKTree.leafOrder]
  | _, .ordinary _ children => children.leafOrder_nodup

theorem CKChildren.leafOrder_nodup : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → children.leafOrder.Nodup
  | _, .nil => by simp [CKChildren.leafOrder]
  | _, .cons head tail => by
      change (head.leafOrder.map (Sum.inl : head.LeafOccurrence →
        head.LeafOccurrence ⊕ tail.LeafOccurrence) ++
        tail.leafOrder.map Sum.inr).Nodup
      rw [List.nodup_append]
      refine ⟨head.leafOrder_nodup.map Sum.inl_injective,
        tail.leafOrder_nodup.map Sum.inr_injective, ?_⟩
      intro left leftMem right rightMem
      rcases List.mem_map.mp leftMem with ⟨_, _, rfl⟩
      rcases List.mem_map.mp rightMem with ⟨_, _, rfl⟩
      simp
end

end Potkin

#print axioms Potkin.CKTree.leafAddress_injective
#print axioms Potkin.CKTree.PunctureAt.exists_leafOccurrence

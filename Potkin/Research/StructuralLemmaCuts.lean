import Potkin.Research.CutHoleAdapter
import Potkin.CompositeCutExpansion
import Potkin.CompleteQuotation

/-!
# A physical CK frontier for native open structural derivations

Filling each physical interface with an ordinary proof creates a native cut
whose remainder is literally the original open derivation. Equal donor trees
at different holes stay different selected occurrences. No forest collection
or coefficient is used to construct this frontier.
-/
namespace Potkin.Research.StructuralLemmaCuts
universe u v w
variable {sigma : Signature.{u, v}} {D : Type w}

private theorem split_sum {α β : Type*} (f : α ⊕ β → Nat) (xs : List α) (ys : List β) :
    (List.map f (xs.map Sum.inl ++ ys.map Sum.inr)).sum =
      (xs.map (fun x => f (.inl x))).sum + (ys.map (fun y => f (.inr y))).sum := by
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  rfl

mutual
def frontier : {G : Hypersequent sigma} → (tree : CKTree sigma D G) →
    (fillers : tree.LeafAssignment) → (∀ h, (fillers h).IsOrdinary) →
    CKBranchCut (tree.fillAssignment fillers)
  | _, .interface _, fillers, ordinary => .detach (ordinary PUnit.unit)
  | _, .ordinary o children, fillers, ordinary =>
      .descend (.ordinary o _ (childFrontier children fillers ordinary))

def childFrontier : {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma D Gs) →
    (fillers : children.LeafAssignment) → (∀ h, (fillers h).IsOrdinary) →
    CKChildCuts (children.fillAssignment fillers)
  | _, .nil, _, _ => .nil
  | _, .cons head tail, fillers, ordinary =>
      .cons _ _ (frontier head (fun h => fillers (.inl h)) (fun h => ordinary (.inl h)))
        (childFrontier tail (fun h => fillers (.inr h)) (fun h => ordinary (.inr h)))
end

mutual
@[simp] theorem frontier_remainder : {G : Hypersequent sigma} →
    (tree : CKTree sigma D G) → (fillers : tree.LeafAssignment) →
    (ordinary : ∀ h, (fillers h).IsOrdinary) → (frontier tree fillers ordinary).remainder = tree
  | _, .interface _, _, _ => rfl
  | _, .ordinary o children, fillers, ordinary =>
      congrArg (CKTree.ordinary o) (childFrontier_remainder children fillers ordinary)

@[simp] theorem childFrontier_remainder : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma D Gs) → (fillers : children.LeafAssignment) →
    (ordinary : ∀ h, (fillers h).IsOrdinary) →
    (childFrontier children fillers ordinary).remainder = children
  | _, .nil, _, _ => rfl
  | _, .cons head tail, fillers, ordinary => by
      change CKChildren.cons _ _ = CKChildren.cons head tail
      rw [frontier_remainder, childFrontier_remainder]
end

mutual
@[simp] theorem frontier_length : {G : Hypersequent sigma} →
    (tree : CKTree sigma D G) → (fillers : tree.LeafAssignment) →
    (ordinary : ∀ h, (fillers h).IsOrdinary) →
    (frontier tree fillers ordinary).siteOrder.length = tree.leafOrder.length
  | _, .interface _, _, _ => rfl
  | _, .ordinary _ children, fillers, ordinary => childFrontier_length children fillers ordinary

@[simp] theorem childFrontier_length : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma D Gs) → (fillers : children.LeafAssignment) →
    (ordinary : ∀ h, (fillers h).IsOrdinary) →
    (childFrontier children fillers ordinary).siteOrder.length = children.leafOrder.length
  | _, .nil, _, _ => rfl
  | _, .cons head tail, fillers, ordinary => by
      change (List.map Sum.inl (frontier head (fun h => fillers (.inl h)) _).siteOrder ++
        List.map Sum.inr (childFrontier tail (fun h => fillers (.inr h)) _).siteOrder).length =
        (List.map Sum.inl head.leafOrder ++ List.map Sum.inr tail.leafOrder).length
      simp only [List.length_append, List.length_map, frontier_length, childFrontier_length]
end

mutual
theorem filling_complete : {G : Hypersequent sigma} →
    (tree : CKTree sigma D G) → (fillers : tree.LeafAssignment) →
    (∀ h, (fillers h).IsComplete) → (tree.fillAssignment fillers).IsComplete
  | _, .interface _, _, complete => complete PUnit.unit
  | _, .ordinary _ children, fillers, complete => childFilling_complete children fillers complete

theorem childFilling_complete : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma D Gs) → (fillers : children.LeafAssignment) →
    (∀ h, (fillers h).IsComplete) → (children.fillAssignment fillers).IsComplete
  | _, .nil, _, _ => trivial
  | _, .cons head tail, fillers, complete =>
      ⟨filling_complete head _ (fun h => complete (.inl h)),
        childFilling_complete tail _ (fun h => complete (.inr h))⟩
end

theorem complete_ordinary {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (complete : tree.IsComplete) : tree.IsOrdinary := by
  cases tree with
  | interface => exact complete.elim
  | ordinary => trivial

/-- The public cut excludes root selection. An ordinary scaffold is essential. -/
def properFrontier {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (root : tree.IsOrdinary) (fillers : tree.LeafAssignment)
    (ordinary : ∀ h, (fillers h).IsOrdinary) : CKCut (tree.fillAssignment fillers) := by
  cases tree with
  | interface => exact root.elim
  | ordinary o children => exact ⟨trivial, .ordinary o _ (childFrontier children fillers ordinary)⟩

@[simp] theorem proper_remainder {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (root : tree.IsOrdinary) (fillers : tree.LeafAssignment)
    (ordinary : ∀ h, (fillers h).IsOrdinary) :
    (properFrontier tree root fillers ordinary).plan.remainder = tree := by
  cases tree with
  | interface => exact root.elim
  | ordinary o children => exact frontier_remainder (.ordinary o children) fillers ordinary

theorem native_refill {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (root : tree.IsOrdinary) (fillers : tree.LeafAssignment)
    (ordinary : ∀ h, (fillers h).IsOrdinary) :
    (properFrontier tree root fillers ordinary).fill
      (properFrontier tree root fillers ordinary).plan.detached = tree.fillAssignment fillers :=
  (properFrontier tree root fillers ordinary).fill_detached_reconstructs

@[simp] theorem proper_length {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (root : tree.IsOrdinary) (fillers : tree.LeafAssignment)
    (ordinary : ∀ h, (fillers h).IsOrdinary) :
    (properFrontier tree root fillers ordinary).plan.siteOrder.length = tree.leafOrder.length := by
  cases tree with
  | interface => exact root.elim
  | ordinary o children => exact frontier_length (.ordinary o children) fillers ordinary

mutual
/-- Exact expansion cost over physical holes, including repeated equal fillers. -/
theorem filling_degree : {G : Hypersequent sigma} → (tree : CKTree sigma D G) →
    (fillers : tree.LeafAssignment) →
    (tree.fillAssignment fillers).degree = tree.degree +
      (tree.leafOrder.map (fun h => (fillers h).degree)).sum
  | _, .interface _, fillers => by
      change (fillers PUnit.unit).degree = 0 + ((fillers PUnit.unit).degree + 0)
      omega
  | _, .ordinary _ children, fillers => by
      simpa [CKTree.fillAssignment, CKTree.degree, CKTree.leafOrder, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using childFilling_degree children fillers

theorem childFilling_degree : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma D Gs) → (fillers : children.LeafAssignment) →
    (children.fillAssignment fillers).degree = children.degree +
      (children.leafOrder.map (fun h => (fillers h).degree)).sum
  | _, .nil, _ => rfl
  | _, .cons head tail, fillers => by
      change (head.fillAssignment (fun h => fillers (.inl h))).degree +
        (tail.fillAssignment (fun h => fillers (.inr h))).degree =
        head.degree + tail.degree +
          (List.map (fun h => (fillers h).degree)
            (List.map Sum.inl head.leafOrder ++ List.map Sum.inr tail.leafOrder)).sum
      rw [filling_degree, childFilling_degree]
      have split := split_sum (fun h => (fillers h).degree) head.leafOrder tail.leafOrder
      exact (Nat.add_add_add_comm _ _ _ _).trans
        (congrArg (fun k => head.degree + tail.degree + k) split.symm)
end

/-- Exact physical hole/selected-factor matching; completeness excludes inherited holes. -/
noncomputable def holeMatching {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (root : tree.IsOrdinary) (fillers : tree.LeafAssignment)
    (complete : ∀ h, (fillers h).IsComplete) :
    (properFrontier tree root fillers (fun h => complete_ordinary _ (complete h))).Site ≃
      tree.LeafOccurrence :=
  ((properFrontier tree root fillers (fun h => complete_ordinary _ (complete h))).completeHoleEquiv
    (filling_complete tree fillers complete)).symm.trans
    (Equiv.cast (congrArg (fun t : CKTree sigma D G => t.LeafOccurrence)
      (proper_remainder tree root fillers _)))

/-- Reuse the installed-cut bijection on the actual reconstructed proof.
This accounts for new donor-internal cuts, not just the inherited frontier. -/
noncomputable def extractionEquiv {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (root : tree.IsOrdinary) (fillers : tree.LeafAssignment)
    (ordinary : ∀ h, (fillers h).IsOrdinary) :
    CKCutPlan (tree.fillAssignment fillers) ≃
      (properFrontier tree root fillers ordinary).plan.ExpansionChoices
        (properFrontier tree root fillers ordinary).plan.detached :=
  (Equiv.cast (congrArg (fun t : CKTree sigma D G => CKCutPlan t)
    (native_refill tree root fillers ordinary).symm)).trans
      ((properFrontier tree root fillers ordinary).plan.compositeCutEquiv
        (properFrontier tree root fillers ordinary).plan.detached)

private theorem filling_transport {G : Hypersequent sigma}
    {tree other : CKTree sigma D G} (equal : tree = other) (fillers : tree.LeafAssignment) :
    other.fillAssignment (equal ▸ fillers) = tree.fillAssignment fillers := by
  cases equal; rfl

/-- Native detached factors aligned back to the original physical interfaces. -/
noncomputable def alignedDetached {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (root : tree.IsOrdinary) (fillers : tree.LeafAssignment)
    (complete : ∀ h, (fillers h).IsComplete) : tree.LeafAssignment :=
  (proper_remainder tree root fillers (fun h => complete_ordinary _ (complete h))) ▸
    (properFrontier tree root fillers (fun h => complete_ordinary _ (complete h))).plan.detachedLeafAssignment
      (filling_complete tree fillers complete)

/-- Exact provider equality, not a multiset equality or scalar coefficient. -/
theorem alignedDetached_eq {G : Hypersequent sigma} (tree : CKTree sigma D G)
    (root : tree.IsOrdinary) (fillers : tree.LeafAssignment)
    (complete : ∀ h, (fillers h).IsComplete) :
    alignedDetached tree root fillers complete = fillers := by
  apply tree.fillAssignment_injective
  unfold alignedDetached
  rw [filling_transport]
  exact (properFrontier tree root fillers (fun h => complete_ordinary _ (complete h))).plan.fillAssignment_detached
    (filling_complete tree fillers complete)

section Checked
variable {T : ProofTheory sigma D} [DecidableEq (Hypersequent sigma)]

/-- Every filler and the open scaffold belong to one unchanged registry. -/
noncomputable def checkedFill (P : EquippedPresentation T) {G : Hypersequent sigma}
    (tree : CKTree sigma D G) (admitted : LocallyAdmittedTree P tree)
    (fillers : (h : tree.LeafOccurrence) → CheckedDerivation P (tree.leafBoundary h)) :
    CheckedDerivation P G :=
  CompleteQuotation.checkedOfComplete P (tree.fillAssignment (fun h => (fillers h).realize))
    (tree.fillAssignment_locallyAdmitted _ admitted (fun h => (fillers h).realizeLocallyAdmitted))
    (filling_complete tree _ (fun h => (fillers h).realizeIsComplete))

theorem checkedFill_realize (P : EquippedPresentation T) {G : Hypersequent sigma}
    (tree : CKTree sigma D G) (admitted : LocallyAdmittedTree P tree)
    (fillers : (h : tree.LeafOccurrence) → CheckedDerivation P (tree.leafBoundary h)) :
    (checkedFill P tree admitted fillers).realize =
      tree.fillAssignment (fun h => (fillers h).realize) :=
  CompleteQuotation.quote_realize P _ _ _
end Checked

#check @proper_remainder
#check @native_refill
#print axioms frontier_remainder
#print axioms frontier_length
#print axioms proper_remainder
#print axioms native_refill
#print axioms filling_degree
#print axioms holeMatching
#print axioms extractionEquiv
#print axioms alignedDetached_eq
#print axioms checkedFill_realize
end Potkin.Research.StructuralLemmaCuts

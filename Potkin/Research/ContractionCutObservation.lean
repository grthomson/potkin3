import Potkin.Research.ContextCutAction

/-!
# Full physical CK generating-function observation

The constructor recurrence is interpreted in any commutative semiring. It is
proved equal to the finite sum over existing physical native branch-cut
witnesses, before equal scalar contributions are collected. This introduces
no proof, cut, forest, context, tensor, or coefficient carrier.

The separately represented whole endpoint contributes `z`; a typed interface
has only its empty choice and scalar `1`, without becoming a coefficient unit
as a proof object. These are full structural cuts, not a material filter.

The actual finitely supported polynomial carrier/its coefficientwise order
is NOT imported or claimed here: the installed Mathlib cache is missing
dependencies of both Polynomial.Basic and MonoidAlgebra.Defs. The universal
semiring identity is stronger than a check at finitely many values, but the
coefficientwise dominance adapter remains an explicit outstanding obligation.
-/

namespace Potkin.Research.ContractionCutObservation

open scoped BigOperators
open ContextCutAction

universe u v w x
variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {R : Type x} [CommSemiring R]

private theorem sum_alternatives {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (f : α ⊕ β → R) :
    (∑ choice, f choice) = (∑ a, f (.inl a)) + ∑ b, f (.inr b) :=
  Finset.sum_disjSum _ _ _

private theorem sum_pair {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (f : α × β → R) :
    (∑ pair, f pair) = ∑ a, ∑ b, f (a, b) :=
  Finset.sum_product _ _ _

private theorem sum_mul_local {α : Type*} (s : Finset α) (f : α → R) (r : R) :
    (∑ a ∈ s, f a) * r = ∑ a ∈ s, f a * r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, add_mul, ih]

private theorem mul_sum_local {α : Type*} (s : Finset α) (r : R) (f : α → R) :
    r * (∑ a ∈ s, f a) = ∑ a ∈ s, r * f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, mul_add, ih]

mutual
/-- Constructor recursion for the full structural native CK observation. -/
def Q (z : R) : {G : Hypersequent sigma} → CKTree sigma InstanceData G → R
  | _, .interface _ => 1
  | _, .ordinary _ children => z + QChildren z children

def QChildren (z : R) : {Gs : List (Hypersequent sigma)} →
    CKChildren sigma InstanceData Gs → R
  | _, .nil => 1
  | _, .cons head tail => Q z head * QChildren z tail
end

def ordinaryTo (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises) :
    CKBranchCut (.ordinary o children) → PUnit.{1} ⊕ CKChildCuts children := fun cut =>
  match cut.rootChoice with
  | .inl _ => .inl PUnit.unit
  | .inr plan => .inr plan.contents

def ordinaryFrom (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises) :
    PUnit.{1} ⊕ CKChildCuts children → CKBranchCut (.ordinary o children)
  | .inl _ => .detach trivial
  | .inr cuts => .descend (.ordinary o children cuts)

/-- The whole endpoint is distinct from every strict descending cut. -/
def ordinaryCutEquiv (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises) :
    CKBranchCut (.ordinary o children) ≃ PUnit.{1} ⊕ CKChildCuts children where
  toFun := ordinaryTo o children
  invFun := ordinaryFrom o children
  left_inv cut := by
    have reconstruct := CKBranchCut.rootChoice_reconstructs
      (tree := CKTree.ordinary o children) (by trivial) cut
    generalize eq : cut.rootChoice = choice at *
    cases choice with
    | inl value => simpa only [ordinaryTo, ordinaryFrom, eq] using reconstruct
    | inr plan =>
        simp only [ordinaryTo, ordinaryFrom, eq]
        have planEq : CKCutPlan.ordinary o children plan.contents = plan :=
          plan.contents_reconstructs
        exact (congrArg CKBranchCut.descend planEq).trans reconstruct
  right_inv choice := by cases choice with
    | inl value => cases value; rfl
    | inr cuts => rfl

/-- The product retains the physical ordered head/tail choices. -/
def childCutEquiv {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
    (head : CKTree sigma InstanceData G) (tail : CKChildren sigma InstanceData Gs) :
    CKChildCuts (.cons head tail) ≃ CKBranchCut head × CKChildCuts tail where
  toFun | .cons _ _ headCut tailCuts => (headCut, tailCuts)
  invFun pair := .cons head tail pair.1 pair.2
  left_inv cuts := by cases cuts; rfl
  right_inv pair := rfl

noncomputable section

mutual
/-- Universal equality with actual native branch-cut witnesses, weighted by
the length of their ordered physical site list. Not a bounded evaluation. -/
theorem Q_native (z : R) : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) →
    Q z tree = ∑ cut : CKBranchCut tree, z ^ cut.siteOrder.length
  | _, .interface G => by
      letI : Unique (CKBranchCut (.interface G : CKTree sigma InstanceData G)) :=
        ⟨⟨.descend (.interface G)⟩, CKBranchCut.interface_unique⟩
      simp only [Q, Fintype.sum_unique]
      change 1 = z ^ 0
      simp
  | _, .ordinary o children => by
      have ih := QChildren_native z children
      symm
      calc
        (∑ cut : CKBranchCut (.ordinary o children), z ^ cut.siteOrder.length) =
          ∑ choice : PUnit.{1} ⊕ CKChildCuts children,
            z ^ ((ordinaryCutEquiv o children).symm choice).siteOrder.length := by
              apply Fintype.sum_equiv (ordinaryCutEquiv o children)
              intro cut
              rw [Equiv.symm_apply_apply]
        _ = z + ∑ cuts : CKChildCuts children, z ^ cuts.siteOrder.length := by
              rw [sum_alternatives]
              simp [ordinaryCutEquiv, ordinaryFrom, CKBranchCut.siteOrder,
                CKCutPlan.siteOrder]
              rfl
        _ = Q z (.ordinary o children) := by rw [← ih]; rfl

theorem QChildren_native (z : R) : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) →
    QChildren z children = ∑ cuts : CKChildCuts children, z ^ cuts.siteOrder.length
  | _, .nil => by
      letI : Unique (CKChildCuts (.nil : CKChildren sigma InstanceData [])) :=
        ⟨⟨.nil⟩, fun cuts => by cases cuts; rfl⟩
      simp only [QChildren, Fintype.sum_unique]
      change 1 = z ^ 0
      simp
  | _, .cons head tail => by
      have ihHead := Q_native z head
      have ihTail := QChildren_native z tail
      symm
      calc
        (∑ cuts : CKChildCuts (.cons head tail), z ^ cuts.siteOrder.length) =
          ∑ pair : CKBranchCut head × CKChildCuts tail,
            z ^ ((childCutEquiv head tail).symm pair).siteOrder.length := by
              apply Fintype.sum_equiv (childCutEquiv head tail)
              intro cuts
              rw [Equiv.symm_apply_apply]
        _ = ∑ pair : CKBranchCut head × CKChildCuts tail,
              z ^ pair.1.siteOrder.length * z ^ pair.2.siteOrder.length := by
              apply Finset.sum_congr rfl
              intro pair _
              change z ^ (List.map Sum.inl pair.1.siteOrder ++
                List.map Sum.inr pair.2.siteOrder).length = _
              simp only [List.length_append, List.length_map, pow_add]
        _ = (∑ cut : CKBranchCut head, z ^ cut.siteOrder.length) *
            ∑ cuts : CKChildCuts tail, z ^ cuts.siteOrder.length := by
              rw [sum_pair]
              rw [sum_mul_local]
              simp only [mul_sum_local]
        _ = QChildren z (.cons head tail) := by rw [← ihHead, ← ihTail]; rfl
end

/-- Total physical cut count, including empty and separate whole endpoints. -/
theorem Q_one_card {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    Q (1 : ℕ) tree = Fintype.card (CKBranchCut tree) := by
  rw [Q_native]
  simp

theorem QChildren_cast (z : R) {Gs Hs : List (Hypersequent sigma)} (h : Gs = Hs)
    (children : CKChildren sigma InstanceData Gs) :
    QChildren z (h ▸ children) = QChildren z children := by
  cases h
  rfl

/-- A unary ordinary node adds one full-root cut. It is EW/EC only under a
separate exact admission witness; its kind or name is not used here. -/
theorem Q_unary (z : R) (o : LocalOccurrence sigma InstanceData)
    {G : Hypersequent sigma} (child : CKTree sigma InstanceData G)
    (arity : o.shape.premises = [G]) :
    Q z (.ordinary o (arity.symm ▸ CKChildren.cons child .nil)) = z + Q z child := by
  change z + QChildren z (arity.symm ▸ CKChildren.cons child .nil) = z + Q z child
  rw [QChildren_cast]
  simp [QChildren]

mutual
/-- Affine coefficients along the existing native typed puncture spine. -/
def affine (z : R) : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    CKTree.PunctureAt H context address → R × R
  | _, _, _, _, .root => (0, 1)
  | _, _, _, _, .child _ _ _ _ below =>
      let pair := affineChildren z below
      (z + pair.1, pair.2)

def affineChildren (z : R) : {Gs : List (Hypersequent sigma)} → {H : Hypersequent sigma} →
    {children : CKChildren sigma InstanceData Gs} → {slot : Nat} →
    {address : InternalAddress} → CKChildren.PunctureAt H children slot address → R × R
  | _, _, _, _, _, .head _ tail _ below =>
      let pair := affine z below
      (pair.1 * QChildren z tail, pair.2 * QChildren z tail)
  | _, _, _, _, _, .tail head _ _ _ below =>
      let pair := affineChildren z below
      (Q z head * pair.1, Q z head * pair.2)
end

mutual
/-- Universal affine formula for literal typed native filling. -/
theorem Q_context (z : R) : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) →
    Q z (hole.insert payload) = (affine z hole).1 + (affine z hole).2 * Q z payload
  | _, _, _, _, .root, payload => by
      change Q z payload = 0 + 1 * Q z payload
      simp
  | _, _, _, _, .child _ _ _ _ below, payload => by
      have ih := QChildren_context z below payload
      change z + QChildren z (below.insert payload) =
        z + (affineChildren z below).1 + (affineChildren z below).2 * Q z payload
      rw [ih, add_assoc]

theorem QChildren_context (z : R) : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    QChildren z (hole.insert payload) =
      (affineChildren z hole).1 + (affineChildren z hole).2 * Q z payload
  | _, _, _, _, _, .head _ tail _ below, payload => by
      have ih := Q_context z below payload
      change Q z (below.insert payload) * QChildren z tail = _
      rw [ih, add_mul]
      simp only [affineChildren, mul_assoc, mul_comm (Q z payload), mul_left_comm]
  | _, _, _, _, _, .tail head _ _ _ below, payload => by
      have ih := QChildren_context z below payload
      change Q z head * QChildren z (below.insert payload) = _
      rw [ih, mul_add]
      simp only [affineChildren, mul_assoc]
end

/-- Pointwise natural-valued dominance at ANY chosen z; this is not asserted
to be coefficientwise polynomial order. Both logical fillings must separately
be admitted when applying this combinatorial theorem to checked proofs. -/
theorem Q_context_LE (z : ℕ) {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (left right : CKTree sigma InstanceData H) (h : Q z left ≤ Q z right) :
    Q z (hole.insert left) ≤ Q z (hole.insert right) := by
  rw [Q_context, Q_context]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

/-- Total-count dominance is the specialization z=1. -/
theorem Q_context_totalLE {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (left right : CKTree sigma InstanceData H) (h : Q (1 : ℕ) left ≤ Q 1 right) :
    Q (1 : ℕ) (hole.insert left) ≤ Q 1 (hole.insert right) :=
  Q_context_LE 1 hole left right h

/-- Explicit integer-valued projection of signed native extraction records.
Only this projection forgets typed remainders. Signed defects may be negative. -/
def scalarProjection (z : ℤ) {G : Hypersequent sigma} :
    ExtractionRecords (InstanceData := InstanceData) G →+ ℤ :=
  FreeAbelianGroup.lift fun record => z ^ record.1.card

theorem branchForest_card {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree) :
    (branchForest cut).card = cut.siteOrder.length := by
  simp [branchForest, ContextCutPackets.orderedPacket]

/-- Exact adapter from existing native coaction to this universal observation. -/
theorem scalar_delta (z : ℤ) {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    scalarProjection z (delta (FreeAbelianGroup.of tree)) = Q z tree := by
  simp only [delta, scalarProjection, FreeAbelianGroup.lift_apply_of, map_sum]
  rw [Q_native]
  simp only [branchForest_card]

/-- Proved adapter to the verified K law, on the image of delta. Scalar data
alone are not claimed to determine K on arbitrary signed records. -/
theorem scalar_K_context (z : ℤ) {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H) :
    scalarProjection z (K hole (delta (FreeAbelianGroup.of payload))) =
      Q z (hole.insert payload) := by
  have law := DFunLike.congr_fun (delta_K hole) (FreeAbelianGroup.of payload)
  simp only [AddMonoidHom.comp_apply] at law
  rw [← law]
  simpa only [ContextCutAction.G, FreeAbelianGroup.lift_apply_of] using
    scalar_delta z (hole.insert payload)

#check @Q_native
#check @Q_context
#check @scalar_delta
#check @scalar_K_context
#print axioms Q_native
#print axioms Q_one_card
#print axioms Q_unary
#print axioms Q_context
#print axioms Q_context_totalLE
#print axioms scalar_delta
#print axioms scalar_K_context

end
end Potkin.Research.ContractionCutObservation

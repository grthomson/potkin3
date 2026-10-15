import Potkin.Research.HLJInternalWeakening
import Potkin.Research.HLJContraction

/-!
# Native full-context grafts for recursive prepared Sys(com) translation

These constructors use the existing native tree and exact strict HLJ+IW
descriptors.  A registry key is chosen from the complete instance data.  The
premises of Communication remain ordered; external contexts remain multisets.
No formula-occurrence action is inferred from the supplied component incidence.
-/
namespace Potkin.Research.RecursiveSysComNative

open ContractionBoundaries ContractionPostponement
universe u v
variable {sigma : Signature.{u, v}}

abbrev Data (sigma : Signature.{u, v}) := HLJInternalWeakening.Data sigma

def frame (K : Multiset (Sequent sigma)) (S : Sequent sigma) : Hypersequent sigma :=
  extend K (.singleton S)

def pairFrame (K : Multiset (Sequent sigma)) (U V : Sequent sigma) : Hypersequent sigma :=
  extend K (.pair U V)

@[simp] theorem frame_components (K : Multiset (Sequent sigma)) (S : Sequent sigma) :
    (frame K S).components = K + {S} := rfl

@[simp] theorem pairFrame_components (K : Multiset (Sequent sigma)) (U V : Sequent sigma) :
    (pairFrame K U V).components = K + ({U} + {V}) := rfl

theorem frame_pair (K : Multiset (Sequent sigma)) (U V : Sequent sigma) :
    frame (K + {V}) U = pairFrame K U V := by
  apply Hypersequent.ext
  change (K + {V}) + {U} = K + ({U} + {V})
  ac_rfl

theorem frame_pair_right (K : Multiset (Sequent sigma)) (U V : Sequent sigma) :
    frame (K + {U}) V = pairFrame K U V := by
  apply Hypersequent.ext
  change (K + {U}) + {V} = K + ({U} + {V})
  exact add_assoc _ _ _

theorem pairFrame_swap (K : Multiset (Sequent sigma)) (U V : Sequent sigma) :
    pairFrame K U V = pairFrame K V U := by
  apply Hypersequent.ext
  change K + ({U} + {V}) = K + ({V} + {U})
  rw [add_comm ({U} : Multiset (Sequent sigma))]

theorem frame_duplicate (K : Multiset (Sequent sigma)) (S : Sequent sigma) :
    extend {S} (frame K S) = pairFrame K S S := by
  apply Hypersequent.ext
  change {S} + (K + {S}) = K + ({S} + {S})
  ac_rfl

theorem frame_valid (K : Multiset (Sequent sigma)) (S : Sequent sigma)
    (valid : HLJStructural.ValidComponents K) (single : HLJStructural.Single S) :
    HLJStructural.ValidBoundary (frame K S) :=
  (HLJStructural.valid_extend _ _).mpr
    ⟨valid, (HLJStructural.valid_singleton _).mpr single⟩

theorem frame_member (K : Multiset (Sequent sigma)) (S : Sequent sigma) :
    S ∈ (frame K S).components := by simp

noncomputable def comInstance (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma) :
    LocalOccurrence sigma (Data sigma) :=
  let d : HLJStructural.Data sigma := .com K phi psi gamma₁ gamma₂ pi₁ pi₂
  HLJInternalWeakening.oldOccurrence (key (.inl d)) d

noncomputable def iwInstance (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma) :
    LocalOccurrence sigma (Data sigma) :=
  let d : HLJInternalWeakening.IWData sigma := ⟨K, A, gamma, pi⟩
  HLJInternalWeakening.iwOccurrence (key (.inr d)) K A gamma pi

noncomputable def ecInstance (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma) :
    LocalOccurrence sigma (Data sigma) :=
  let G := frame K S
  let d : HLJStructural.Data sigma :=
    .ec G S (HLJStructural.retainedIndex G S (frame_member K S)).val
  HLJInternalWeakening.oldOccurrence (key (.inl d)) d

@[simp] theorem com_premises (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma) :
    (comInstance key K phi psi gamma₁ gamma₂ pi₁ pi₂).shape.premises =
      [frame K ⟨phi + gamma₁, pi₁⟩, frame K ⟨psi + gamma₂, pi₂⟩] := by
  simp only [comInstance, HLJInternalWeakening.old_premises, HLJStructural.com_premises]
  rfl

@[simp] theorem com_conclusion (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma) :
    (comInstance key K phi psi gamma₁ gamma₂ pi₁ pi₂).shape.conclusion =
      pairFrame K ⟨psi + gamma₁, pi₁⟩ ⟨phi + gamma₂, pi₂⟩ := by
  simp only [comInstance, HLJInternalWeakening.old_conclusion, HLJStructural.com_conclusion]
  rfl

@[simp] theorem iw_premises (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma) :
    (iwInstance key K A gamma pi).shape.premises = [frame K ⟨gamma, pi⟩] := rfl

@[simp] theorem iw_conclusion (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma) :
    (iwInstance key K A gamma pi).shape.conclusion = frame K ⟨{A} + gamma, pi⟩ := rfl

@[simp] theorem ec_premises (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma) :
    (ecInstance key K S).shape.premises = [pairFrame K S S] := by
  simp only [ecInstance, HLJInternalWeakening.old_premises, HLJStructural.ec_premises,
    frame_duplicate]

@[simp] theorem ec_conclusion (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma) :
    (ecInstance key K S).shape.conclusion = frame K S := by
  simp only [ecInstance, HLJInternalWeakening.old_conclusion, HLJStructural.ec_conclusion]

theorem com_admitted (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma)
    (valid : HLJStructural.ValidComponents K) (single₁ : pi₁.card ≤ 1)
    (single₂ : pi₂.card ≤ 1) :
    (HLJInternalWeakening.theory sigma).Admits
      (comInstance key K phi psi gamma₁ gamma₂ pi₁ pi₂) :=
  HLJInternalWeakening.lift_admitted _
    (HLJContraction.com_strict ⟨phi, psi, gamma₁, gamma₂, pi₁, pi₂, single₁, single₂⟩ _ K valid)

theorem iw_admitted (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma)
    (valid : HLJStructural.ValidComponents K) (single : pi.card ≤ 1) :
    (HLJInternalWeakening.theory sigma).Admits (iwInstance key K A gamma pi) :=
  HLJInternalWeakening.iw_admitted _ _ _ _ _ valid single

theorem ec_admitted (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma)
    (valid : HLJStructural.ValidComponents K) (single : HLJStructural.Single S) :
    (HLJInternalWeakening.theory sigma).Admits (ecInstance key K S) :=
  HLJInternalWeakening.lift_admitted _
    (HLJContraction.ec_strict _ _ S (frame_member K S) (frame_valid K S valid single))

/-- Ordered graft of the actual antecedent-repartition Communication instance. -/
noncomputable def comNode (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma)
    (left : CKTree sigma (Data sigma) (frame K ⟨phi + gamma₁, pi₁⟩))
    (right : CKTree sigma (Data sigma) (frame K ⟨psi + gamma₂, pi₂⟩)) :
    CKTree sigma (Data sigma) (pairFrame K ⟨psi + gamma₁, pi₁⟩ ⟨phi + gamma₂, pi₂⟩) :=
  node (comInstance key K phi psi gamma₁ gamma₂ pi₁ pi₂)
    (com_premises ..) (com_conclusion ..) (.cons left (.cons right .nil))

noncomputable def iwNode (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma)
    (child : CKTree sigma (Data sigma) (frame K ⟨gamma, pi⟩)) :
    CKTree sigma (Data sigma) (frame K ⟨{A} + gamma, pi⟩) :=
  node (iwInstance key K A gamma pi) (iw_premises ..) (iw_conclusion ..) (.cons child .nil)

noncomputable def ecNode (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma)
    (child : CKTree sigma (Data sigma) (pairFrame K S S)) :
    CKTree sigma (Data sigma) (frame K S) :=
  node (ecInstance key K S) (ec_premises ..) (ec_conclusion ..) (.cons child .nil)

@[simp] theorem comNode_degree (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma)
    (left : CKTree sigma (Data sigma) (frame K ⟨phi + gamma₁, pi₁⟩))
    (right : CKTree sigma (Data sigma) (frame K ⟨psi + gamma₂, pi₂⟩)) :
    (comNode key K phi psi gamma₁ gamma₂ pi₁ pi₂ left right).degree =
      left.degree + right.degree + 1 := by simp [comNode, CKChildren.degree]

@[simp] theorem iwNode_degree (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma)
    (child : CKTree sigma (Data sigma) (frame K ⟨gamma, pi⟩)) :
    (iwNode key K A gamma pi child).degree = child.degree + 1 := by
  simp [iwNode, CKChildren.degree]

@[simp] theorem ecNode_degree (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma)
    (child : CKTree sigma (Data sigma) (pairFrame K S S)) :
    (ecNode key K S child).degree = child.degree + 1 := by
  simp [ecNode, CKChildren.degree]

@[simp] theorem comNode_all (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma)
    (left : CKTree sigma (Data sigma) (frame K ⟨phi + gamma₁, pi₁⟩))
    (right : CKTree sigma (Data sigma) (frame K ⟨psi + gamma₂, pi₂⟩))
    (R : LocalOccurrence sigma (Data sigma) → Prop) :
    AllNodes R (comNode key K phi psi gamma₁ gamma₂ pi₁ pi₂ left right) ↔
      R (comInstance key K phi psi gamma₁ gamma₂ pi₁ pi₂) ∧ AllNodes R left ∧ AllNodes R right := by
  simp [comNode, AllChildren]

@[simp] theorem iwNode_all (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma)
    (child : CKTree sigma (Data sigma) (frame K ⟨gamma, pi⟩))
    (R : LocalOccurrence sigma (Data sigma) → Prop) :
    AllNodes R (iwNode key K A gamma pi child) ↔
      R (iwInstance key K A gamma pi) ∧ AllNodes R child := by simp [iwNode, AllChildren]

@[simp] theorem ecNode_all (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma)
    (child : CKTree sigma (Data sigma) (pairFrame K S S))
    (R : LocalOccurrence sigma (Data sigma) → Prop) :
    AllNodes R (ecNode key K S child) ↔
      R (ecInstance key K S) ∧ AllNodes R child := by simp [ecNode, AllChildren]

@[simp] theorem comNode_complete (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma)
    (left : CKTree sigma (Data sigma) (frame K ⟨phi + gamma₁, pi₁⟩))
    (right : CKTree sigma (Data sigma) (frame K ⟨psi + gamma₂, pi₂⟩)) :
    (comNode key K phi psi gamma₁ gamma₂ pi₁ pi₂ left right).IsComplete ↔
      left.IsComplete ∧ right.IsComplete := by
  simp [comNode, CKChildren.IsComplete]

@[simp] theorem iwNode_complete (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma)
    (child : CKTree sigma (Data sigma) (frame K ⟨gamma, pi⟩)) :
    (iwNode key K A gamma pi child).IsComplete ↔ child.IsComplete := by
  simp [iwNode, CKChildren.IsComplete]

@[simp] theorem ecNode_complete (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma)
    (child : CKTree sigma (Data sigma) (pairFrame K S S)) :
    (ecNode key K S child).IsComplete ↔ child.IsComplete := by
  simp [ecNode, CKChildren.IsComplete]

theorem node_ordinary {Gs : List (Hypersequent sigma)} {G : Hypersequent sigma}
    (o : LocalOccurrence sigma (Data sigma)) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (children : CKChildren sigma (Data sigma) Gs) :
    (node o hp hc children).IsOrdinary := by subst Gs; subst G; trivial

@[simp] theorem comNode_ordinary (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma)
    (left : CKTree sigma (Data sigma) (frame K ⟨phi + gamma₁, pi₁⟩))
    (right : CKTree sigma (Data sigma) (frame K ⟨psi + gamma₂, pi₂⟩)) :
    (comNode key K phi psi gamma₁ gamma₂ pi₁ pi₂ left right).IsOrdinary := node_ordinary ..

@[simp] theorem iwNode_ordinary (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (A : Formula sigma) (gamma pi : Context sigma)
    (child : CKTree sigma (Data sigma) (frame K ⟨gamma, pi⟩)) :
    (iwNode key K A gamma pi child).IsOrdinary := node_ordinary ..

@[simp] theorem ecNode_ordinary (key : Data sigma → Nat)
    (K : Multiset (Sequent sigma)) (S : Sequent sigma)
    (child : CKTree sigma (Data sigma) (pairFrame K S S)) :
    (ecNode key K S child).IsOrdinary := node_ordinary ..

#print axioms com_admitted
#print axioms iw_admitted
#print axioms ec_admitted
#print axioms comNode_all
#print axioms ecNode_complete

end Potkin.Research.RecursiveSysComNative

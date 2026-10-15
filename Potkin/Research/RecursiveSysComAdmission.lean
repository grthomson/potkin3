import Potkin.Research.RecursiveSysComNative

/-!
# Finite exact allocation for reached recursive Sys(com) instances

The input stock is a finite list of source-computed tagged schema instances.
Allocation retains the tag as well as the complete native instance data.  It
does not change owner/reference names or assign a fresh key per physical copy.
An existing donor stock is retained literally below a disjoint numeric offset.
The native finite-presentation constructor performs the only registry assembly.
-/
namespace Potkin.Research.RecursiveSysComAdmission

open ContractionPostponement
universe u v
variable {sigma : Signature.{u, v}}

abbrev Data (sigma : Signature.{u, v}) := HLJInternalWeakening.Data sigma
abbrev TaggedData (sigma : Signature.{u, v}) := Nat × Data sigma

noncomputable def allocatedKey (offset : Nat) (stock : List (TaggedData sigma))
    (hint : Nat) (d : Data sigma) : Nat := by
  classical
  exact offset + @List.idxOf _ ⟨fun a b => decide (a = b)⟩ (hint, d) stock

theorem allocatedKey_ge (offset : Nat) (stock : List (TaggedData sigma))
    (hint : Nat) (d : Data sigma) : offset ≤ allocatedKey offset stock hint d := by
  classical
  simp only [allocatedKey]
  omega

/-- The numerical key uniquely identifies a reached tagged descriptor, even
when the source supplied the same hint for distinct passive contexts. -/
theorem allocatedKey_injective (offset : Nat) (stock : List (TaggedData sigma))
    (a b : TaggedData sigma) (ha : a ∈ stock)
    (equal : allocatedKey offset stock a.1 a.2 = allocatedKey offset stock b.1 b.2) :
    a = b := by
  classical
  letI : BEq (TaggedData sigma) := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq (TaggedData sigma) :=
    { eq_of_beq := of_decide_eq_true, rfl := of_decide_eq_self_eq_true _ }
  have indices : stock.idxOf a = stock.idxOf b := by
    simpa only [allocatedKey, Nat.add_left_cancel_iff] using equal
  exact (List.idxOf_inj ha).mp indices

/-- The canonical descriptor is the existing strict descriptor, including its
entire supplied component incidence. -/
noncomputable def canonicalOccurrence (id : Nat) : Data sigma → LocalOccurrence sigma (Data sigma)
  | .inl d => HLJInternalWeakening.oldOccurrence id d
  | .inr d => HLJInternalWeakening.iwOccurrence id d.passive d.formula d.gamma d.pi

@[simp] theorem canonicalOccurrence_id (id : Nat) (d : Data sigma) :
    (canonicalOccurrence id d).id = id := by cases d <;> rfl

@[simp] theorem canonicalOccurrence_data (id : Nat) (d : Data sigma) :
    (canonicalOccurrence id d).instanceData = d := by
  cases d with
  | inl d => rfl
  | inr d => cases d; rfl

noncomputable def allocatedOccurrence (offset : Nat) (stock : List (TaggedData sigma))
    (a : TaggedData sigma) : LocalOccurrence sigma (Data sigma) :=
  canonicalOccurrence (allocatedKey offset stock a.1 a.2) a.2

@[simp] theorem allocatedOccurrence_id (offset : Nat) (stock : List (TaggedData sigma))
    (a : TaggedData sigma) :
    (allocatedOccurrence offset stock a).id = allocatedKey offset stock a.1 a.2 :=
  canonicalOccurrence_id _ _

theorem allocatedOccurrence_ge (offset : Nat) (stock : List (TaggedData sigma))
    (a : TaggedData sigma) : offset ≤ (allocatedOccurrence offset stock a).id := by
  simpa only [allocatedOccurrence_id] using allocatedKey_ge offset stock a.1 a.2

theorem allocated_consistent (offset : Nat) (stock : List (TaggedData sigma)) :
    D3RegistryAdmission.ConsistentKeys (stock.map (allocatedOccurrence offset stock)) := by
  intro o ho p hp equal
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
  have same := allocatedKey_injective offset stock a b ha
    (by simpa only [allocatedOccurrence_id] using equal)
  cases same
  rfl

/-- Existing donor descriptors are not renamed.  The strict numeric separation
rules out a collision with every newly allocated reached instance. -/
theorem mixed_consistent (offset : Nat) (stock : List (TaggedData sigma))
    (donors : List (LocalOccurrence sigma (Data sigma)))
    (consistent : D3RegistryAdmission.ConsistentKeys donors)
    (below : ∀ o ∈ donors, o.id < offset) :
    D3RegistryAdmission.ConsistentKeys
      (donors ++ stock.map (allocatedOccurrence offset stock)) := by
  intro o ho p hp equal
  rcases List.mem_append.mp ho with ho | ho <;>
    rcases List.mem_append.mp hp with hp | hp
  · exact consistent o ho p hp equal
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
    have small := below o ho
    have large := allocatedOccurrence_ge offset stock b
    omega
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp ho
    have small := below p hp
    have large := allocatedOccurrence_ge offset stock a
    omega
  · exact allocated_consistent offset stock o ho p hp equal

noncomputable def presentation
    (offset : Nat) (stock : List (TaggedData sigma))
    (donors : List (LocalOccurrence sigma (Data sigma)))
    (consistent : D3RegistryAdmission.ConsistentKeys donors)
    (below : ∀ o ∈ donors, o.id < offset)
    (donorsValid : ∀ o ∈ donors, (HLJInternalWeakening.theory sigma).Admits o)
    (stockValid : ∀ a ∈ stock,
      (HLJInternalWeakening.theory sigma).Admits (allocatedOccurrence offset stock a)) :
    EquippedPresentation (HLJInternalWeakening.theory sigma) :=
  D3RegistryAdmission.finitePresentation _
    (donors ++ stock.map (allocatedOccurrence offset stock))
    (mixed_consistent offset stock donors consistent below) (by
      intro o ho
      rcases List.mem_append.mp ho with ho | ho
      · exact donorsValid o ho
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
        exact stockValid a ha)

@[simp] theorem mem_presentation
    (offset : Nat) (stock : List (TaggedData sigma))
    (donors : List (LocalOccurrence sigma (Data sigma)))
    (consistent : D3RegistryAdmission.ConsistentKeys donors)
    (below : ∀ o ∈ donors, o.id < offset)
    (donorsValid : ∀ o ∈ donors, (HLJInternalWeakening.theory sigma).Admits o)
    (stockValid : ∀ a ∈ stock,
      (HLJInternalWeakening.theory sigma).Admits (allocatedOccurrence offset stock a))
    (o : LocalOccurrence sigma (Data sigma)) :
    o ∈ (presentation offset stock donors consistent below donorsValid stockValid).registry ↔
      o ∈ donors ∨ ∃ a ∈ stock, allocatedOccurrence offset stock a = o := by
  simp only [presentation, D3RegistryAdmission.mem_finitePresentation, List.mem_append,
    List.mem_map]

/-- Check a tree from its constructor-derived reached stock.  No assumption
that this entire finished output was registered is required. -/
theorem admitted_of_reached
    (offset : Nat) (stock : List (TaggedData sigma))
    (donors : List (LocalOccurrence sigma (Data sigma)))
    (consistent : D3RegistryAdmission.ConsistentKeys donors)
    (below : ∀ o ∈ donors, o.id < offset)
    (donorsValid : ∀ o ∈ donors, (HLJInternalWeakening.theory sigma).Admits o)
    (stockValid : ∀ a ∈ stock,
      (HLJInternalWeakening.theory sigma).Admits (allocatedOccurrence offset stock a))
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (reached : AllNodes (fun o => o ∈ donors ∨
      ∃ a ∈ stock, allocatedOccurrence offset stock a = o) tree) :
    LocallyAdmittedTree
      (presentation offset stock donors consistent below donorsValid stockValid) tree := by
  apply RuleInterface.registered_all tree |>.mp
  simpa only [mem_presentation] using reached

#print axioms allocatedKey_injective
#print axioms allocated_consistent
#print axioms mixed_consistent
#print axioms admitted_of_reached

end Potkin.Research.RecursiveSysComAdmission

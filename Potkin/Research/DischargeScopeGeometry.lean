import Potkin.Research.OpenDischargeSummary

/-!
# Actual occurrences and native vacancy barriers

Finite event rows are tied to native `VertexAt` witnesses. A parent bottom
therefore cannot occur at or below a physical vacant interface. This is the
address fact needed to reduce a filling's designated-owner condition to the
parent's per-hole exposure, without assuming a well-scoped filling.
-/

namespace Potkin.Research.DischargeScopeGeometry

open OpenDischarge
universe u v
variable {sigma : Signature.{u, v}}

mutual

theorem events_vertices : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (address : InternalAddress) →
    (∀ request ∈ (events tree address).requirements,
      ∃ relative, request.topAddress = address ++ relative ∧ tree.VertexAt relative) ∧
    (∀ owner ∈ (events tree address).grants,
      ∃ relative, owner.address = address ++ relative ∧ tree.VertexAt relative)
  | _, .interface _, _ => by
      constructor <;> intro row present <;> cases present
  | _, .ordinary o children, address => by
      have below := childEvents_vertices children address 0
      constructor
      · intro request present
        rcases List.mem_append.mp present with root | child
        · cases label : o.instanceData <;>
            simp only [rootEvents, label, List.mem_singleton, List.not_mem_nil] at root
          subst request
          exact ⟨[], by simp, .root o children⟩
        · rcases below.1 request child with ⟨index, relative, equal, vertex⟩
          refine ⟨index.val :: relative, ?_, .child o children index vertex⟩
          simpa only [Nat.zero_add, List.append_assoc, List.singleton_append] using equal
      · intro owner present
        rcases List.mem_append.mp present with root | child
        · cases label : o.instanceData <;>
            simp only [rootEvents, label, List.mem_singleton, List.not_mem_nil] at root
          subst owner
          exact ⟨[], by simp, .root o children⟩
        · rcases below.2 owner child with ⟨index, relative, equal, vertex⟩
          refine ⟨index.val :: relative, ?_, .child o children index vertex⟩
          simpa only [Nat.zero_add, List.append_assoc, List.singleton_append] using equal

theorem childEvents_vertices : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → (address : InternalAddress) →
    (slot : Nat) →
    (∀ request ∈ (childEvents children address slot).requirements,
      ∃ index : Fin Gs.length, ∃ relative,
        request.topAddress = address ++ [slot + index.val] ++ relative ∧
          (children.get index).VertexAt relative) ∧
    (∀ owner ∈ (childEvents children address slot).grants,
      ∃ index : Fin Gs.length, ∃ relative,
        owner.address = address ++ [slot + index.val] ++ relative ∧
          (children.get index).VertexAt relative)
  | _, .nil, _, _ => by
      constructor <;> intro row present <;> cases present
  | _, .cons head tail, address, slot => by
      have first := events_vertices head (address ++ [slot])
      have rest := childEvents_vertices tail address (slot + 1)
      constructor
      · intro request present
        rcases List.mem_append.mp present with present | present
        · rcases first.1 request present with ⟨relative, equal, vertex⟩
          exact ⟨⟨0, by simp⟩, relative, by simpa only [Nat.add_zero] using equal, vertex⟩
        · rcases rest.1 request present with ⟨index, relative, equal, vertex⟩
          refine ⟨index.succ, relative, ?_, vertex⟩
          simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using equal
      · intro owner present
        rcases List.mem_append.mp present with present | present
        · rcases first.2 owner present with ⟨relative, equal, vertex⟩
          exact ⟨⟨0, by simp⟩, relative, by simpa only [Nat.add_zero] using equal, vertex⟩
        · rcases rest.2 owner present with ⟨index, relative, equal, vertex⟩
          refine ⟨index.succ, relative, ?_, vertex⟩
          simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using equal

end

/-- Distinct physical vacancies have incomparable native addresses. Equal
boundaries do not identify their occurrences. -/
theorem distinct_holes_not_prefix {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (left right : tree.LeafOccurrence)
    (different : left ≠ right) :
    ¬ AddressPrefix (tree.leafAddress left) (tree.leafAddress right) := by
  rintro ⟨suffix, equal⟩
  by_cases vacant : suffix = []
  · subst suffix
    apply different
    apply tree.leafAddress_injective
    simpa only [List.append_nil] using equal
  · have status := (tree.leafPuncture right).toInterfaceAt.statusAt_eq_interface
    rw [← equal, interface_status_append (tree.leafPuncture left).toInterfaceAt] at status
    simp only [vacant, if_false] at status
    cases status

theorem append_equal_prefix_comparable (left right suffixLeft suffixRight : InternalAddress)
    (equal : left ++ suffixLeft = right ++ suffixRight) :
    AddressPrefix left right ∨ AddressPrefix right left := by
  induction left generalizing right with
  | nil => exact Or.inl ⟨right, rfl⟩
  | cons head tail ih =>
      cases right with
      | nil => exact Or.inr ⟨head :: tail, rfl⟩
      | cons first rest =>
          have pieces : head = first ∧ tail ++ suffixLeft = rest ++ suffixRight := by
            simpa only [List.cons_append, List.cons.injEq] using equal
          rcases pieces with ⟨sameHead, tailsEqual⟩
          subst first
          rcases ih rest tailsEqual with ⟨suffix, comparable⟩ | ⟨suffix, comparable⟩
          · exact Or.inl ⟨suffix, congrArg (List.cons head) comparable⟩
          · exact Or.inr ⟨suffix, congrArg (List.cons head) comparable⟩

/-- Cross-piece designated references are not made external when their owner
is declared in a different filling: the actual ancestry test is false. -/
theorem incompatible_different_hole_fillings {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (left right : tree.LeafOccurrence)
    (different : left ≠ right) (request : Requirement sigma) (owner : Grant sigma) :
    ¬ Compatible (prefixRequirement (tree.leafAddress left) request)
      (prefixGrant (tree.leafAddress right) owner) := by
  rintro ⟨_, _, suffix, equal⟩
  have comparable := append_equal_prefix_comparable (tree.leafAddress left)
    (tree.leafAddress right) request.topAddress
    (owner.address ++ [request.role.val] ++ suffix)
    (by simpa only [prefixRequirement, prefixGrant, List.append_assoc] using equal)
  rcases comparable with comparable | comparable
  · exact distinct_holes_not_prefix tree left right different comparable
  · exact distinct_holes_not_prefix tree right left different.symm comparable

/-- A later inserted declaration is below an existing parent top, never its
discharging ancestor, even if its UID and parameter pack match. -/
theorem incompatible_parent_top_filling_owner {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (hole : tree.LeafOccurrence)
    (request : Requirement sigma) (owner : Grant sigma)
    (present : request ∈ (events tree []).requirements) :
    ¬ Compatible request (prefixGrant (tree.leafAddress hole) owner) := by
  rcases (events_vertices tree []).1 request present with ⟨relative, equal, vertex⟩
  have requestRelative : request.topAddress = relative := by simpa using equal
  have outside : ¬ AddressPrefix (tree.leafAddress hole) request.topAddress := by
    rw [requestRelative]
    exact hole_not_prefix_vertex tree hole vertex
  rintro ⟨_, _, suffix, compatible⟩
  apply outside
  refine ⟨owner.address ++ [request.role.val] ++ suffix, ?_⟩
  simpa only [prefixGrant, List.append_assoc] using compatible.symm

/-- Prefix cancellation at a genuine frontier: if the declaration is not
inside the hole, its designated premise prefix must already reach that hole. -/
theorem branch_prefix_before_hole (owner hole payload : InternalAddress) (role : Nat)
    (outside : ¬ AddressPrefix hole owner)
    (inside : ∃ suffix, hole ++ payload = owner ++ [role] ++ suffix) :
    ∃ suffix, hole = owner ++ [role] ++ suffix := by
  induction owner generalizing hole with
  | nil =>
      cases hole with
      | nil => exact False.elim (outside ⟨[], rfl⟩)
      | cons head tail =>
          rcases inside with ⟨suffix, equal⟩
          have same : head = role := by
            simpa only [List.cons_append, List.nil_append, List.singleton_append] using
              (List.cons.inj equal).1
          exact ⟨tail, by simp only [List.nil_append, List.singleton_append, same]⟩
  | cons head tail ih =>
      cases hole with
      | nil => exact False.elim (outside ⟨head :: tail, rfl⟩)
      | cons first rest =>
          rcases inside with ⟨suffix, equal⟩
          have pieces : first = head ∧ rest ++ payload = tail ++ [role] ++ suffix := by
            simpa only [List.cons_append, List.cons.injEq] using equal
          rcases pieces with ⟨sameHead, tailsEqual⟩
          subst first
          have outsideRest : ¬ AddressPrefix rest tail := by
            rintro ⟨suffix, equal⟩
            apply outside
            exact ⟨suffix, congrArg (List.cons head) equal⟩
          rcases ih rest outsideRest ⟨suffix, tailsEqual⟩ with ⟨remaining, holeEqual⟩
          exact ⟨remaining, congrArg (List.cons head) holeEqual⟩

/-- An arbitrary filling demand resolves against a parent bottom exactly
when its UID/pack and the native parent hole exposure match.  There is no
assumption that the demand has a valid owner in advance. -/
theorem compatible_through_hole {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (hole : tree.LeafOccurrence)
    (request : Requirement sigma) (owner : Grant sigma)
    (present : owner ∈ (events tree []).grants) :
    Compatible (prefixRequirement (tree.leafAddress hole) request) owner ↔
      request.owner = owner.uid ∧ request.parameters = owner.parameters ∧
        AddressPrefix (owner.address ++ [request.role.val]) (tree.leafAddress hole) := by
  rcases (events_vertices tree []).2 owner present with ⟨relative, equal, vertex⟩
  have ownerRelative : owner.address = relative := by simpa using equal
  have outside : ¬ AddressPrefix (tree.leafAddress hole) owner.address := by
    rw [ownerRelative]
    exact hole_not_prefix_vertex tree hole vertex
  constructor
  · rintro ⟨uid, pack, suffix, compatible⟩
    rcases branch_prefix_before_hole owner.address (tree.leafAddress hole)
        request.topAddress request.role.val outside ⟨suffix, compatible⟩ with
      ⟨suffix, exposed⟩
    exact ⟨uid, pack, suffix, exposed.symm⟩
  · rintro ⟨uid, pack, suffix, exposed⟩
    refine ⟨uid, pack, suffix ++ request.topAddress, ?_⟩
    simp only [prefixRequirement]
    rw [← exposed]
    simp only [List.append_assoc]

#check @events_vertices
#check @compatible_through_hole
#print axioms events_vertices
#print axioms branch_prefix_before_hole
#print axioms compatible_through_hole
#print axioms incompatible_different_hole_fillings
#print axioms incompatible_parent_top_filling_owner

end Potkin.Research.DischargeScopeGeometry

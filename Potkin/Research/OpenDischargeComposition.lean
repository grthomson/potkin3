import Potkin.Research.OpenDischargeSummary
import Potkin.Research.DischargeScopeGeometry
import Potkin.Research.CutHoleAdapter
import Mathlib.Data.Multiset.Bind

/-!
# Compact finite composition: scope tests and exact inventory transport

The operation below consumes only summaries and physical attachment rows.
An input child's address-bearing metadata must already have been prefixed
to its actual attachment site. `attachedSummaries` is the native adapter.
This is finite metadata, not another proof/context carrier.

Universal inventory, outstanding-demand and ordered-hole laws are proved below.
The actual parent exposure and negative reverse-ownership adapters are included.
A theorem equating **all** fields of `directSummary(fillAssignment ...)` with
`composeSummary` still requires exact exposure multiplicity and aggregate
failure-flag refinement and is deliberately not asserted by this module.
In particular failure persistence is not that exact native refinement theorem.
-/

namespace Potkin.Research.OpenDischarge

open Potkin.Research.DischargeScopeGeometry

universe u v
variable {sigma : Signature.{u, v}}

/-- Exact finite-summary adequacy against a fixed, disjoint external owner
environment. This independently uses actual native event legality; it is
not the stronger replacement theorem under arbitrary subsequent fillings.
Completeness remains separate when interpreting this as a finished proof. -/
theorem summary_legality_iff
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) (external : List (Grant sigma))
    (fresh : Fresh (events tree address) external) :
    Legal Imp tree address external ↔
      (directSummary Imp tree address).ok ∧
        ∀ r ∈ (directSummary Imp tree address).requirements,
          ∃ grant ∈ external, Compatible r grant := by
  rw [Legal, legality_interface_iff _ _ fresh]
  change (ExactTree Imp tree ∧ UniqueOwners (events tree address) ∧
    InteriorLegal (events tree address) ∧ OutstandingLegal (events tree address) external) ↔
    (ExactTree Imp tree ∧ UniqueOwners (events tree address) ∧
      InteriorLegal (events tree address)) ∧
      OutstandingLegal (events tree address) external
  constructor
  · rintro ⟨hExact, unique, inside, outside⟩
    exact ⟨⟨hExact, unique, inside⟩, outside⟩
  · rintro ⟨⟨hExact, unique, inside⟩, outside⟩
    exact ⟨hExact, unique, inside, outside⟩

abbrev Attachment (sigma : Signature.{u, v}) := Hole sigma × Summary sigma

def offsetFirst (slot : Nat) : InternalAddress → InternalAddress
  | [] => []
  | index :: rest => (slot + index) :: rest

theorem offsetFirst_zero (address : InternalAddress) : offsetFirst 0 address = address := by
  cases address <;> simp [offsetFirst]

theorem offsetFirst_shift (slot : Nat) (address : InternalAddress) :
    offsetFirst slot (InternalAddress.shiftHead address) = offsetFirst (slot + 1) address := by
  cases address <;> simp [offsetFirst, InternalAddress.shiftHead, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

def holeRows {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) : List (Hole sigma) :=
  tree.leafOrder.map fun h => ⟨address ++ tree.leafAddress h, tree.leafBoundary h⟩

def childHoleRows {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma (Data sigma) Gs) (address : InternalAddress)
    (slot : Nat) : List (Hole sigma) :=
  children.leafOrder.map fun h =>
    ⟨address ++ offsetFirst slot (children.leafAddress h), children.leafBoundary h⟩

theorem childHoleRows_cons (head : CKTree sigma (Data sigma) G)
    (tail : CKChildren sigma (Data sigma) Gs) (address : InternalAddress) (slot : Nat) :
    childHoleRows (.cons head tail) address slot =
      holeRows head (address ++ [slot]) ++ childHoleRows tail address (slot + 1) := by
  simp only [childHoleRows, CKChildren.leafOrder]
  change List.map
    (fun (h : head.LeafOccurrence ⊕ tail.LeafOccurrence) =>
      (⟨address ++ offsetFirst slot ((CKChildren.cons head tail).leafAddress h),
        (CKChildren.cons head tail).leafBoundary h⟩ : Hole sigma))
      (List.map Sum.inl head.leafOrder ++ List.map Sum.inr tail.leafOrder) = _
  rw [@List.map_append (head.LeafOccurrence ⊕ tail.LeafOccurrence) (Hole sigma)]
  simp only [List.map_map]
  congr 1
  · apply List.map_congr_left
    intro hole present
    simp [holeRows, CKChildren.leafAddress, CKChildren.leafBoundary,
      offsetFirst, List.append_assoc]
  · apply List.map_congr_left
    intro hole present
    simp [CKChildren.leafAddress, CKChildren.leafBoundary, offsetFirst_shift]

theorem holeRows_ordinary (o : LocalOccurrence sigma (Data sigma))
    (children : CKChildren sigma (Data sigma) o.shape.premises) (address : InternalAddress) :
    holeRows (.ordinary o children) address = childHoleRows children address 0 := by
  simp only [holeRows, childHoleRows, CKTree.leafOrder, CKTree.leafAddress,
    CKTree.leafBoundary, offsetFirst_zero]
  rfl

def sumInventories (inputs : List (Attachment sigma)) : Multiset Nat :=
  inputs.foldr (fun input total => input.2.inventory + total) 0

def combinedInventory (parent : Summary sigma) (inputs : List (Attachment sigma)) :
    Multiset Nat := parent.inventory + sumInventories inputs

def sumRequirements (inputs : List (Attachment sigma)) : Multiset (Requirement sigma) :=
  inputs.foldr (fun input total => input.2.requirements + total) 0

def MatchesExposure (hole : InternalAddress) (r : Requirement sigma)
    (exposure : Exposure sigma) : Prop :=
  exposure.hole = hole ∧ exposure.owner = r.owner ∧
    exposure.parameters = r.parameters ∧ exposure.role = r.role

private theorem role_mem_two (role : Fin 2) : role ∈ ([0, 1] : List (Fin 2)) := by
  have roleCases : role = 0 ∨ role = 1 := by
    by_cases zero : role.val = 0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (by have bound := role.isLt; omega))
  rcases roleCases with rfl | rfl <;> simp

theorem mem_exposureRows (holes : List (Hole sigma)) (grants : List (Grant sigma))
    (exposure : Exposure sigma) :
    exposure ∈ exposureRows holes grants ↔
      ∃ hole ∈ holes, ∃ grant ∈ grants,
        exposure.hole = hole.address ∧ exposure.owner = grant.uid ∧
          exposure.parameters = grant.parameters ∧
          ∃ suffix, hole.address = grant.address ++ [exposure.role.val] ++ suffix := by
  classical
  constructor
  · intro present
    rcases List.mem_flatMap.mp present with ⟨hole, holePresent, inner⟩
    rcases List.mem_flatMap.mp inner with ⟨grant, grantPresent, selected⟩
    rcases List.mem_filterMap.mp selected with ⟨role, rolePresent, selected⟩
    change (if ∃ suffix, hole.address = grant.address ++ [role.val] ++ suffix then
      some (⟨hole.address, grant.uid, grant.parameters, role⟩ : Exposure sigma)
      else none) = some exposure at selected
    split at selected
    · rename_i prefixExists
      have same : (⟨hole.address, grant.uid, grant.parameters, role⟩ : Exposure sigma) = exposure :=
        Option.some.inj selected
      subst exposure
      exact ⟨hole, holePresent, grant, grantPresent, rfl, rfl, rfl, prefixExists⟩
    · cases selected
  · rintro ⟨hole, holePresent, grant, grantPresent, holeEqual, ownerEqual, packEqual, suffix, path⟩
    apply List.mem_flatMap.mpr ⟨hole, holePresent, ?_⟩
    apply List.mem_flatMap.mpr ⟨grant, grantPresent, ?_⟩
    apply List.mem_filterMap.mpr ⟨exposure.role, role_mem_two exposure.role, ?_⟩
    have prefixExists : ∃ suffix, hole.address = grant.address ++ [exposure.role.val] ++ suffix :=
      ⟨suffix, path⟩
    have same : (⟨hole.address, grant.uid, grant.parameters, exposure.role⟩ : Exposure sigma) = exposure := by
      cases exposure
      simp_all
    change (if ∃ suffix, hole.address = grant.address ++ [exposure.role.val] ++ suffix then
      some (⟨hole.address, grant.uid, grant.parameters, exposure.role⟩ : Exposure sigma)
      else none) = some exposure
    rw [if_pos prefixExists]
    exact congrArg some same

/-- Native parent exposure lookup is exactly actual discharge against an
existing parent bottom. This includes missing/invisible owners and wrong
pack/role cases; no premise presupposes that the demand is well scoped. -/
theorem parent_exposure_resolves
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (hole : tree.LeafOccurrence) (r : Requirement sigma) :
    (∃ grant ∈ (events tree []).grants,
      Compatible (prefixRequirement (tree.leafAddress hole) r) grant) ↔
      ∃ exposure ∈ (directSummary Imp tree []).exposure,
        MatchesExposure (tree.leafAddress hole) r exposure := by
  classical
  constructor
  · rintro ⟨grant, grantPresent, valid⟩
    rcases (compatible_through_hole tree hole r grant grantPresent).mp valid with
      ⟨ownerEqual, packEqual, suffix, path⟩
    let exposure : Exposure sigma := ⟨tree.leafAddress hole, grant.uid, grant.parameters, r.role⟩
    refine ⟨exposure, ?_, rfl, ownerEqual.symm, packEqual.symm, rfl⟩
    change exposure ∈ (exposureRows (holeRows tree []) (events tree []).grants :
      Multiset (Exposure sigma))
    rw [Multiset.mem_coe, mem_exposureRows]
    refine ⟨⟨tree.leafAddress hole, tree.leafBoundary hole⟩, ?_, grant, grantPresent,
      rfl, rfl, rfl, suffix, path.symm⟩
    apply List.mem_map.mpr
    exact ⟨hole, tree.leaf_mem_leafOrder hole, by simp⟩
  · rintro ⟨exposure, exposurePresent, matched⟩
    change exposure ∈ (exposureRows (holeRows tree []) (events tree []).grants :
      Multiset (Exposure sigma)) at exposurePresent
    rw [Multiset.mem_coe, mem_exposureRows] at exposurePresent
    rcases exposurePresent with
      ⟨boundaryHole, boundaryPresent, grant, grantPresent, holeEqual, ownerEqual, packEqual,
        suffix, path⟩
    refine ⟨grant, grantPresent,
      (compatible_through_hole tree hole r grant grantPresent).mpr ?_⟩
    refine ⟨matched.2.1.symm.trans ownerEqual,
      matched.2.2.1.symm.trans packEqual, suffix, ?_⟩
    rw [← matched.2.2.2]
    exact (matched.1.symm.trans (holeEqual.trans path)).symm

/-- The global owner inventory distinguishes a genuinely external demand
from an invalid hidden/sibling/descendant owner. No input references are
assumed well scoped. -/
def compositionOK (parent : Summary sigma) (inputs : List (Attachment sigma)) : Prop :=
  parent.ok ∧
  (∀ input ∈ inputs, input.2.ok ∧ input.1.boundary = input.2.conclusion) ∧
  inputs.map Prod.fst = parent.holes ∧
  (combinedInventory parent inputs).Nodup ∧
  (∀ r ∈ parent.requirements, r.owner ∉ combinedInventory parent inputs) ∧
  (∀ input ∈ inputs, ∀ r ∈ input.2.requirements,
    r.owner ∈ combinedInventory parent inputs →
      r.owner ∈ parent.inventory ∧
        ∃ exposure ∈ parent.exposure, MatchesExposure input.1.address r exposure)

noncomputable def remainingRequirements (parent : Summary sigma)
    (inputs : List (Attachment sigma)) : Multiset (Requirement sigma) := by
  classical
  exact (parent.requirements + sumRequirements inputs).filter
    (fun r => r.owner ∉ combinedInventory parent inputs)

noncomputable def inheritedExposure (parent : Summary sigma)
    (input : Attachment sigma) : Multiset (Exposure sigma) := by
  classical
  exact input.2.holes.foldr (fun hole total =>
    (parent.exposure.filter (fun exposure => exposure.hole = input.1.address)).map
      (fun exposure => {exposure with hole := hole.address}) + total) 0

noncomputable def composeSummary (parent : Summary sigma)
    (inputs : List (Attachment sigma)) : Summary sigma where
  conclusion := parent.conclusion
  holes := inputs.flatMap (fun input => input.2.holes)
  inventory := combinedInventory parent inputs
  requirements := remainingRequirements parent inputs
  exposure := inputs.foldr (fun input total =>
    input.2.exposure + inheritedExposure parent input + total) 0
  ok := compositionOK parent inputs

theorem compose_failure_persists (parent : Summary sigma)
    (inputs : List (Attachment sigma)) (failed : ¬ parent.ok) :
    ¬ (composeSummary parent inputs).ok := by
  intro accepted
  exact failed accepted.1

theorem child_failure_persists (parent : Summary sigma)
    (inputs : List (Attachment sigma)) (input : Attachment sigma)
    (present : input ∈ inputs) (failed : ¬ input.2.ok) :
    ¬ (composeSummary parent inputs).ok := by
  intro accepted
  exact failed (accepted.2.1 input present).1

theorem newly_internal_not_external (parent : Summary sigma)
    (inputs : List (Attachment sigma)) (r : Requirement sigma)
    (internal : r.owner ∈ combinedInventory parent inputs) :
    r ∉ (composeSummary parent inputs).requirements := by
  classical
  simp [composeSummary, remainingRequirements, internal]

theorem mem_composed_requirements (parent : Summary sigma)
    (inputs : List (Attachment sigma)) (r : Requirement sigma) :
    r ∈ (composeSummary parent inputs).requirements ↔
      r ∈ parent.requirements + sumRequirements inputs ∧
        r.owner ∉ combinedInventory parent inputs := by
  classical
  change r ∈ (parent.requirements + sumRequirements inputs).filter
    (fun r => r.owner ∉ combinedInventory parent inputs) ↔ _
  exact Multiset.mem_filter

mutual
/-- All physical vacancies, visited in native premise order; ordinary parent
vertices are not recomputed as input pieces. -/
noncomputable def attachedSummaries
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    tree.LeafAssignment → InternalAddress → List (Attachment sigma)
  | G, .interface _, assignment, address =>
      [(⟨address, G⟩, directSummary Imp (assignment PUnit.unit) address)]
  | _, .ordinary _ children, assignment, address =>
      attachedChildSummaries Imp children assignment address 0

noncomputable def attachedChildSummaries
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    children.LeafAssignment → InternalAddress → Nat → List (Attachment sigma)
  | _, .nil, _, _, _ => []
  | _, .cons head tail, assignment, address, slot =>
      attachedSummaries Imp head (fun h => assignment (.inl h)) (address ++ [slot]) ++
        attachedChildSummaries Imp tail (fun h => assignment (.inr h)) address (slot + 1)
end

theorem interior_of_event_bags (left right : Events sigma)
    (requirements : (left.requirements : Multiset (Requirement sigma)) =
      (right.requirements : Multiset (Requirement sigma)))
    (grants : (left.grants : Multiset (Grant sigma)) =
      (right.grants : Multiset (Grant sigma))) :
    InteriorLegal left ↔ InteriorLegal right := by
  have requestMembership (r : Requirement sigma) :
      r ∈ left.requirements ↔ r ∈ right.requirements := by
    change r ∈ (left.requirements : Multiset (Requirement sigma)) ↔
      r ∈ (right.requirements : Multiset (Requirement sigma))
    rw [requirements]
  have grantMembership (g : Grant sigma) : g ∈ left.grants ↔ g ∈ right.grants := by
    change g ∈ (left.grants : Multiset (Grant sigma)) ↔
      g ∈ (right.grants : Multiset (Grant sigma))
    rw [grants]
  constructor
  · intro legal r present internal
    rcases internal with ⟨owner, ownerPresent, ownerEqual⟩
    rcases legal r ((requestMembership r).mpr present)
      ⟨owner, (grantMembership owner).mpr ownerPresent, ownerEqual⟩ with ⟨g, hg, compatible⟩
    exact ⟨g, (grantMembership g).mp hg, compatible⟩
  · intro legal r present internal
    rcases internal with ⟨owner, ownerPresent, ownerEqual⟩
    rcases legal r ((requestMembership r).mp present)
      ⟨owner, (grantMembership owner).mp ownerPresent, ownerEqual⟩ with ⟨g, hg, compatible⟩
    exact ⟨g, (grantMembership g).mpr hg, compatible⟩

mutual
/-- The existing event carrier, restricted to the inserted pieces. This
helper is a proof adapter, not the compact production representation. -/
def attachedEvents : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → tree.LeafAssignment →
    InternalAddress → Events sigma
  | _, .interface _, assignment, address => events (assignment PUnit.unit) address
  | _, .ordinary _ children, assignment, address =>
      attachedChildEvents children assignment address 0

def attachedChildEvents : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → children.LeafAssignment →
    InternalAddress → Nat → Events sigma
  | _, .nil, _, _, _ => ⟨[], []⟩
  | _, .cons head tail, assignment, address, slot =>
      (attachedEvents head (fun h => assignment (.inl h)) (address ++ [slot])).append
        (attachedChildEvents tail (fun h => assignment (.inr h)) address (slot + 1))
end

mutual
theorem attached_event_bags : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (assignment : tree.LeafAssignment) →
    (address : InternalAddress) →
    ((attachedEvents tree assignment address).requirements : Multiset _) =
      attachedRequirements tree assignment address ∧
    ((attachedEvents tree assignment address).grants : Multiset _) =
      attachedGrants tree assignment address
  | _, .interface _, _, _ => ⟨rfl, rfl⟩
  | _, .ordinary _ children, assignment, address =>
      attached_child_event_bags children assignment address 0

theorem attached_child_event_bags : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    ((attachedChildEvents children assignment address slot).requirements : Multiset _) =
      attachedChildRequirements children assignment address slot ∧
    ((attachedChildEvents children assignment address slot).grants : Multiset _) =
      attachedChildGrants children assignment address slot
  | _, .nil, _, _, _ => ⟨rfl, rfl⟩
  | _, .cons head tail, assignment, address, slot => by
      rcases attached_event_bags head (fun h => assignment (.inl h)) (address ++ [slot]) with
        ⟨hr, hg⟩
      rcases attached_child_event_bags tail (fun h => assignment (.inr h)) address (slot + 1) with
        ⟨tr, tg⟩
      simp only [attachedChildEvents, Events.append, ← Multiset.coe_add,
        attachedChildRequirements, attachedChildGrants]
      exact ⟨by rw [hr, tr], by rw [hg, tg]⟩
end

/-- Native simultaneous filling agrees with disjoint event-piece checking.
The right side does not reorder or regenerate proof vertices: only event
list order, which is immaterial to this independently defined relation,
is changed. Physical addresses and occurrence multiplicities are fixed. -/
theorem interior_fill_partition {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (assignment : tree.LeafAssignment)
    (address : InternalAddress) :
    InteriorLegal (events (tree.fillAssignment assignment) address) ↔
      InteriorLegal ((events tree address).append (attachedEvents tree assignment address)) := by
  rcases events_fill tree assignment address with ⟨hr, hg⟩
  rcases attached_event_bags tree assignment address with ⟨ar, ag⟩
  apply interior_of_event_bags
  · simpa only [Events.append, ← Multiset.coe_add, ar] using hr
  · simpa only [Events.append, ← Multiset.coe_add, ag] using hg

mutual
theorem attached_grant_origin : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (assignment : tree.LeafAssignment) →
    (address : InternalAddress) → (grant : Grant sigma) →
    grant ∈ (attachedEvents tree assignment address).grants →
    ∃ hole : tree.LeafOccurrence, ∃ original ∈ (events (assignment hole) []).grants,
      grant = prefixGrant (address ++ tree.leafAddress hole) original
  | _, .interface _, assignment, address, grant, present => by
      change grant ∈ (events (assignment PUnit.unit) address).grants at present
      rw [events_at] at present
      rcases List.mem_map.mp present with ⟨original, originalPresent, same⟩
      exact ⟨PUnit.unit, original, originalPresent, by
        simpa [CKTree.leafAddress] using same.symm⟩
  | _, .ordinary _ children, assignment, address, grant, present => by
      rcases attached_child_grant_origin children assignment address 0 grant present with
        ⟨hole, original, originalPresent, same⟩
      exact ⟨hole, original, originalPresent, by
        simpa [CKTree.leafAddress, offsetFirst_zero] using same⟩

theorem attached_child_grant_origin : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    (grant : Grant sigma) → grant ∈ (attachedChildEvents children assignment address slot).grants →
    ∃ hole : children.LeafOccurrence, ∃ original ∈ (events (assignment hole) []).grants,
      grant = prefixGrant (address ++ offsetFirst slot (children.leafAddress hole)) original
  | _, .nil, _, _, _, _, present => by cases present
  | _, .cons head tail, assignment, address, slot, grant, present => by
      rcases List.mem_append.mp present with inHead | inTail
      · rcases attached_grant_origin head (fun h => assignment (.inl h))
          (address ++ [slot]) grant inHead with ⟨hole, original, originalPresent, same⟩
        exact ⟨.inl hole, original, originalPresent, by
          simpa [CKChildren.leafAddress, offsetFirst, List.append_assoc] using same⟩
      · rcases attached_child_grant_origin tail (fun h => assignment (.inr h))
          address (slot + 1) grant inTail with ⟨hole, original, originalPresent, same⟩
        exact ⟨.inr hole, original, originalPresent, by
          simpa [CKChildren.leafAddress, offsetFirst_shift] using same⟩
end

/-- A parent top cannot acquire a discharge owner from a descendant filling.
The rejection is a theorem about real physical vacancies and vertices,
not a prohibited-reference assumption placed on the input. -/
theorem parent_to_filling_iff {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (assignment : tree.LeafAssignment) :
    CrossLegal (events tree []) (attachedEvents tree assignment []) ↔
      ∀ r ∈ outstanding (events tree []),
        ¬ HasInternalOwner (attachedEvents tree assignment []) r := by
  constructor
  · intro cross r present newlyInternal
    rcases cross r present newlyInternal with ⟨grant, grantPresent, valid⟩
    rcases attached_grant_origin tree assignment [] grant grantPresent with
      ⟨hole, original, originalPresent, same⟩
    have parentPresent := ((mem_outstanding _ r).mp present).1
    have rejected := incompatible_parent_top_filling_owner tree hole r original parentPresent
    apply rejected
    simpa [same] using valid
  · intro noOwner r present newlyInternal
    exact False.elim (noOwner r present newlyInternal)

mutual
theorem attached_requirement_origin : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (assignment : tree.LeafAssignment) →
    (address : InternalAddress) → (r : Requirement sigma) →
    r ∈ (attachedEvents tree assignment address).requirements →
    ∃ hole : tree.LeafOccurrence, ∃ original ∈ (events (assignment hole) []).requirements,
      r = prefixRequirement (address ++ tree.leafAddress hole) original
  | _, .interface _, assignment, address, r, present => by
      change r ∈ (events (assignment PUnit.unit) address).requirements at present
      rw [events_at] at present
      rcases List.mem_map.mp present with ⟨original, originalPresent, same⟩
      exact ⟨PUnit.unit, original, originalPresent, by
        simpa [CKTree.leafAddress] using same.symm⟩
  | _, .ordinary _ children, assignment, address, r, present => by
      rcases attached_child_requirement_origin children assignment address 0 r present with
        ⟨hole, original, originalPresent, same⟩
      exact ⟨hole, original, originalPresent, by
        simpa [CKTree.leafAddress, offsetFirst_zero] using same⟩

theorem attached_child_requirement_origin : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    (r : Requirement sigma) → r ∈ (attachedChildEvents children assignment address slot).requirements →
    ∃ hole : children.LeafOccurrence, ∃ original ∈ (events (assignment hole) []).requirements,
      r = prefixRequirement (address ++ offsetFirst slot (children.leafAddress hole)) original
  | _, .nil, _, _, _, _, present => by cases present
  | _, .cons head tail, assignment, address, slot, r, present => by
      rcases List.mem_append.mp present with inHead | inTail
      · rcases attached_requirement_origin head (fun h => assignment (.inl h))
          (address ++ [slot]) r inHead with ⟨hole, original, originalPresent, same⟩
        exact ⟨.inl hole, original, originalPresent, by
          simpa [CKChildren.leafAddress, offsetFirst, List.append_assoc] using same⟩
      · rcases attached_child_requirement_origin tail (fun h => assignment (.inr h))
          address (slot + 1) r inTail with ⟨hole, original, originalPresent, same⟩
        exact ⟨.inr hole, original, originalPresent, by
          simpa [CKChildren.leafAddress, offsetFirst_shift] using same⟩
end

mutual
theorem attached_requirement_mem : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (assignment : tree.LeafAssignment) →
    (address : InternalAddress) → (hole : tree.LeafOccurrence) → (r : Requirement sigma) →
    r ∈ (events (assignment hole) []).requirements →
    prefixRequirement (address ++ tree.leafAddress hole) r ∈
      (attachedEvents tree assignment address).requirements
  | _, .interface _, assignment, address, hole, r, present => by
      cases hole
      change prefixRequirement (address ++ []) r ∈
        (events (assignment PUnit.unit) address).requirements
      rw [List.append_nil, events_at]
      exact List.mem_map.mpr ⟨r, present, rfl⟩
  | _, .ordinary _ children, assignment, address, hole, r, present => by
      simpa [CKTree.leafAddress, offsetFirst_zero] using
        attached_child_requirement_mem children assignment address 0 hole r present

theorem attached_child_requirement_mem : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    (hole : children.LeafOccurrence) → (r : Requirement sigma) →
    r ∈ (events (assignment hole) []).requirements →
    prefixRequirement (address ++ offsetFirst slot (children.leafAddress hole)) r ∈
      (attachedChildEvents children assignment address slot).requirements
  | _, .nil, _, _, _, hole, _, _ => nomatch hole
  | _, .cons head tail, assignment, address, slot, hole, r, present => by
      cases hole with
      | inl h =>
          apply List.mem_append_left
          simpa [CKChildren.leafAddress, offsetFirst, List.append_assoc] using
            attached_requirement_mem head (fun h => assignment (.inl h)) (address ++ [slot]) h r present
      | inr h =>
          apply List.mem_append_right
          simpa [CKChildren.leafAddress, offsetFirst_shift] using
            attached_child_requirement_mem tail (fun h => assignment (.inr h)) address (slot + 1) h r present
end

mutual
theorem attached_grant_mem : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (assignment : tree.LeafAssignment) →
    (address : InternalAddress) → (hole : tree.LeafOccurrence) → (grant : Grant sigma) →
    grant ∈ (events (assignment hole) []).grants →
    prefixGrant (address ++ tree.leafAddress hole) grant ∈
      (attachedEvents tree assignment address).grants
  | _, .interface _, assignment, address, hole, grant, present => by
      cases hole
      change prefixGrant (address ++ []) grant ∈ (events (assignment PUnit.unit) address).grants
      rw [List.append_nil, events_at]
      exact List.mem_map.mpr ⟨grant, present, rfl⟩
  | _, .ordinary _ children, assignment, address, hole, grant, present => by
      simpa [CKTree.leafAddress, offsetFirst_zero] using
        attached_child_grant_mem children assignment address 0 hole grant present

theorem attached_child_grant_mem : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    (hole : children.LeafOccurrence) → (grant : Grant sigma) →
    grant ∈ (events (assignment hole) []).grants →
    prefixGrant (address ++ offsetFirst slot (children.leafAddress hole)) grant ∈
      (attachedChildEvents children assignment address slot).grants
  | _, .nil, _, _, _, hole, _, _ => nomatch hole
  | _, .cons head tail, assignment, address, slot, hole, grant, present => by
      cases hole with
      | inl h =>
          apply List.mem_append_left
          simpa [CKChildren.leafAddress, offsetFirst, List.append_assoc] using
            attached_grant_mem head (fun h => assignment (.inl h)) (address ++ [slot]) h grant present
      | inr h =>
          apply List.mem_append_right
          simpa [CKChildren.leafAddress, offsetFirst_shift] using
            attached_child_grant_mem tail (fun h => assignment (.inr h)) address (slot + 1) h grant present
end

/-- Exact simultaneous inserted-piece failure partition, including ill-scoped
cross references. A demand naming a sibling owner is internal to the pool
but cannot be discharged. No assumption bans such references in advance. -/
theorem attached_interior_iff {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (assignment : tree.LeafAssignment) :
    InteriorLegal (attachedEvents tree assignment []) ↔
      (∀ hole, InteriorLegal (events (assignment hole) [])) ∧
      (∀ hole, ∀ r ∈ outstanding (events (assignment hole) []),
        ¬ HasInternalOwner (attachedEvents tree assignment [])
          (prefixRequirement (tree.leafAddress hole) r)) := by
  have requestMember (hole : tree.LeafOccurrence) (r : Requirement sigma)
      (present : r ∈ (events (assignment hole) []).requirements) :
      prefixRequirement (tree.leafAddress hole) r ∈
        (attachedEvents tree assignment []).requirements := by
    simpa using attached_requirement_mem tree assignment [] hole r present
  have grantMember (hole : tree.LeafOccurrence) (g : Grant sigma)
      (present : g ∈ (events (assignment hole) []).grants) :
      prefixGrant (tree.leafAddress hole) g ∈
        (attachedEvents tree assignment []).grants := by
    simpa using attached_grant_mem tree assignment [] hole g present
  constructor
  · intro legal
    constructor
    · intro hole r present internal
      rcases internal with ⟨owner, ownerPresent, ownerEqual⟩
      have poolOwner : HasInternalOwner (attachedEvents tree assignment [])
          (prefixRequirement (tree.leafAddress hole) r) :=
        ⟨prefixGrant (tree.leafAddress hole) owner, grantMember hole owner ownerPresent,
          by simpa [prefixGrant, prefixRequirement] using ownerEqual⟩
      rcases legal _ (requestMember hole r present) poolOwner with ⟨g, hg, valid⟩
      rcases attached_grant_origin tree assignment [] g hg with
        ⟨other, original, originalPresent, same⟩
      have valid : Compatible (prefixRequirement (tree.leafAddress hole) r)
          (prefixGrant (tree.leafAddress other) original) := by simpa [same] using valid
      by_cases sameHole : hole = other
      · subst other
        exact ⟨original, originalPresent, (compatible_prefix _ _ _).mp valid⟩
      · exact False.elim (incompatible_different_hole_fillings tree hole other sameHole r original valid)
    · intro hole r present internal
      rcases (mem_outstanding _ r).mp present with ⟨rPresent, outside⟩
      rcases legal _ (requestMember hole r rPresent) internal with ⟨g, hg, valid⟩
      rcases attached_grant_origin tree assignment [] g hg with
        ⟨other, original, originalPresent, same⟩
      have valid : Compatible (prefixRequirement (tree.leafAddress hole) r)
          (prefixGrant (tree.leafAddress other) original) := by simpa [same] using valid
      by_cases sameHole : hole = other
      · subst other
        have localValid := (compatible_prefix _ _ _).mp valid
        exact outside ⟨original, originalPresent, localValid.1.symm⟩
      · exact incompatible_different_hole_fillings tree hole other sameHole r original valid
  · rintro ⟨localLegal, outsideOwners⟩ r present internal
    rcases attached_requirement_origin tree assignment [] r present with
      ⟨hole, original, originalPresent, same⟩
    have same : r = prefixRequirement (tree.leafAddress hole) original := by simpa using same
    subst r
    by_cases localOwner : HasInternalOwner (events (assignment hole) []) original
    · rcases localLegal hole original originalPresent localOwner with ⟨g, hg, valid⟩
      exact ⟨prefixGrant (tree.leafAddress hole) g, grantMember hole g hg,
        (compatible_prefix _ _ _).mpr valid⟩
    · exact False.elim (outsideOwners hole original
        ((mem_outstanding _ original).mpr ⟨originalPresent, localOwner⟩) internal)

/-- Once sibling-reference failures are retained, upward discharge of an
inserted top is exactly the finite exposure lookup at its actual hole. -/
theorem filling_to_parent_iff
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment)
    (outsideOwners : ∀ hole, ∀ r ∈ outstanding (events (assignment hole) []),
      ¬ HasInternalOwner (attachedEvents tree assignment [])
        (prefixRequirement (tree.leafAddress hole) r)) :
    CrossLegal (attachedEvents tree assignment []) (events tree []) ↔
      ∀ hole, ∀ r ∈ outstanding (events (assignment hole) []),
        HasInternalOwner (events tree []) r →
          ∃ exposure ∈ (directSummary Imp tree []).exposure,
            MatchesExposure (tree.leafAddress hole) r exposure := by
  constructor
  · intro cross hole r pending parentOwner
    have present : prefixRequirement (tree.leafAddress hole) r ∈
        (attachedEvents tree assignment []).requirements := by
      simpa using attached_requirement_mem tree assignment [] hole r
        ((mem_outstanding _ r).mp pending).1
    have prefOwner : HasInternalOwner (events tree [])
        (prefixRequirement (tree.leafAddress hole) r) := by
      rcases parentOwner with ⟨g, hg, equal⟩
      exact ⟨g, hg, by simpa [prefixRequirement] using equal⟩
    apply (parent_exposure_resolves Imp tree hole r).mp
    exact cross _ ((mem_outstanding _ _).mpr
      ⟨present, outsideOwners hole r pending⟩) prefOwner
  · intro lookup r pending parentOwner
    rcases (mem_outstanding _ r).mp pending with ⟨rPresent, outsidePool⟩
    rcases attached_requirement_origin tree assignment [] r rPresent with
      ⟨hole, original, originalPresent, same⟩
    have same : r = prefixRequirement (tree.leafAddress hole) original := by simpa using same
    subst r
    have outsidePiece : ¬ HasInternalOwner (events (assignment hole) []) original := by
      rintro ⟨g, hg, equal⟩
      apply outsidePool
      refine ⟨prefixGrant (tree.leafAddress hole) g, ?_, ?_⟩
      · simpa using attached_grant_mem tree assignment [] hole g hg
      · simpa [prefixGrant, prefixRequirement] using equal
    have parentOwner : HasInternalOwner (events tree []) original := by
      rcases parentOwner with ⟨g, hg, equal⟩
      exact ⟨g, hg, by simpa [prefixRequirement] using equal⟩
    apply (parent_exposure_resolves Imp tree hole original).mpr
    exact lookup hole original
      ((mem_outstanding _ original).mpr ⟨originalPresent, outsidePiece⟩) parentOwner

/-- Universal simultaneous native scope partition.  The declaration
freshness hypothesis only separates bottom inventories: references across
pieces remain unrestricted and may fail. The five finite tests retain
existing failures, parent-to-descendant failures, sibling failures, and
actual parent exposure checks (including hidden owners, wrong pack/role). -/
theorem native_scope_partition
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment)
    (fresh : Fresh (events tree []) (attachedEvents tree assignment []).grants) :
    InteriorLegal (events (tree.fillAssignment assignment) []) ↔
      InteriorLegal (events tree []) ∧
      (∀ hole, InteriorLegal (events (assignment hole) [])) ∧
      (∀ r ∈ outstanding (events tree []),
        ¬ HasInternalOwner (attachedEvents tree assignment []) r) ∧
      (∀ hole, ∀ r ∈ outstanding (events (assignment hole) []),
        ¬ HasInternalOwner (attachedEvents tree assignment [])
          (prefixRequirement (tree.leafAddress hole) r)) ∧
      (∀ hole, ∀ r ∈ outstanding (events (assignment hole) []),
        HasInternalOwner (events tree []) r →
          ∃ exposure ∈ (directSummary Imp tree []).exposure,
            MatchesExposure (tree.leafAddress hole) r exposure) := by
  rw [interior_fill_partition, interior_append_iff _ _ fresh,
    attached_interior_iff, parent_to_filling_iff]
  constructor
  · rintro ⟨parentLegal, ⟨pieceLegal, outsideOwners⟩, parentRefs, pieceRefs⟩
    exact ⟨parentLegal, pieceLegal, parentRefs, outsideOwners,
      (filling_to_parent_iff Imp tree assignment outsideOwners).mp pieceRefs⟩
  · rintro ⟨parentLegal, pieceLegal, parentRefs, outsideOwners, lookup⟩
    exact ⟨parentLegal, ⟨pieceLegal, outsideOwners⟩, parentRefs,
      (filling_to_parent_iff Imp tree assignment outsideOwners).mpr lookup⟩

mutual
theorem attachment_holes
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    (assignment : tree.LeafAssignment) → (address : InternalAddress) →
    (attachedSummaries Imp tree assignment address).map Prod.fst = holeRows tree address
  | _, .interface _, _, _ => by simp [attachedSummaries, holeRows, CKTree.leafOrder,
      CKTree.leafAddress, CKTree.leafBoundary]
  | _, .ordinary o children, assignment, address => by
      rw [attachedSummaries, holeRows_ordinary]
      exact attachment_child_holes Imp children assignment address 0

theorem attachment_child_holes
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    (attachedChildSummaries Imp children assignment address slot).map Prod.fst =
      childHoleRows children address slot
  | _, .nil, _, _, _ => rfl
  | _, .cons head tail, assignment, address, slot => by
      rw [attachedChildSummaries, List.map_append, attachment_holes,
        attachment_child_holes, childHoleRows_cons]
end

mutual
theorem filled_hole_rows
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    (assignment : tree.LeafAssignment) → (address : InternalAddress) →
    holeRows (tree.fillAssignment assignment) address =
      (attachedSummaries Imp tree assignment address).flatMap (fun input => input.2.holes)
  | _, .interface _, assignment, address => by
      change holeRows (assignment PUnit.unit) address = _
      simp [attachedSummaries, directSummary, holeRows]
  | _, .ordinary o children, assignment, address => by
      rw [CKTree.fillAssignment, holeRows_ordinary, attachedSummaries]
      exact filled_child_hole_rows Imp children assignment address 0

theorem filled_child_hole_rows
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    childHoleRows (children.fillAssignment assignment) address slot =
      (attachedChildSummaries Imp children assignment address slot).flatMap
        (fun input => input.2.holes)
  | _, .nil, _, _, _ => rfl
  | _, .cons head tail, assignment, address, slot => by
      rw [CKChildren.fillAssignment, childHoleRows_cons, attachedChildSummaries,
        List.flatMap_append, filled_hole_rows, filled_child_hole_rows]
end

theorem sumInventories_append (left right : List (Attachment sigma)) :
    sumInventories (left ++ right) = sumInventories left + sumInventories right := by
  induction left with
  | nil => simp [sumInventories]
  | cons head tail ih =>
      change head.2.inventory + sumInventories (tail ++ right) =
        (head.2.inventory + sumInventories tail) + sumInventories right
      rw [ih]
      rw [Multiset.add_assoc]

theorem sumRequirements_append (left right : List (Attachment sigma)) :
    sumRequirements (left ++ right) = sumRequirements left + sumRequirements right := by
  induction left with
  | nil => simp [sumRequirements]
  | cons head tail ih =>
      change head.2.requirements + sumRequirements (tail ++ right) =
        (head.2.requirements + sumRequirements tail) + sumRequirements right
      rw [ih, Multiset.add_assoc]

theorem inventory_of_input (inputs : List (Attachment sigma))
    (input : Attachment sigma) (present : input ∈ inputs) (uid : Nat)
    (declared : uid ∈ input.2.inventory) : uid ∈ sumInventories inputs := by
  induction inputs with
  | nil => cases present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with equal | inTail
      · subst input
        exact Multiset.mem_add.mpr (.inl declared)
      · exact Multiset.mem_add.mpr (.inr (ih inTail))

theorem hasInternalOwner_inventory
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) (r : Requirement sigma) :
    HasInternalOwner (events tree address) r ↔
      r.owner ∈ (directSummary Imp tree address).inventory := by
  simp [HasInternalOwner, directSummary]

theorem requirements_filter
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) :
    (directSummary Imp tree address).requirements =
      ((events tree address).requirements : Multiset (Requirement sigma)).filter
        (fun r => r.owner ∉ (directSummary Imp tree address).inventory) := by
  classical
  change Multiset.filter (fun r => ¬ HasInternalOwner (events tree address) r)
    ((events tree address).requirements : Multiset (Requirement sigma)) = _
  apply Multiset.filter_congr
  intro r hr
  exact not_congr (hasInternalOwner_inventory Imp tree address r)

/-- Filtering by the final owner inventory discards the same top rows
whether already-internal obligations were removed in the input or not. -/
theorem filter_pending_inside
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) (total : Multiset Nat)
    (within : ∀ uid ∈ (directSummary Imp tree address).inventory, uid ∈ total) :
    ((events tree address).requirements : Multiset (Requirement sigma)).filter
      (fun r => r.owner ∉ total) =
    (directSummary Imp tree address).requirements.filter (fun r => r.owner ∉ total) := by
  classical
  rw [requirements_filter, Multiset.filter_filter]
  apply Multiset.filter_congr
  intro r hr
  exact ⟨fun outside => ⟨outside, fun own => outside (within r.owner own)⟩,
    fun both => both.1⟩

mutual
theorem filter_attached_requirements
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    (assignment : tree.LeafAssignment) → (address : InternalAddress) → (total : Multiset Nat) →
    (∀ input ∈ attachedSummaries Imp tree assignment address,
      ∀ uid ∈ input.2.inventory, uid ∈ total) →
    (attachedRequirements tree assignment address).filter (fun r => r.owner ∉ total) =
      (sumRequirements (attachedSummaries Imp tree assignment address)).filter
        (fun r => r.owner ∉ total)
  | G, .interface _, assignment, address, total, within => by
      have ownWithin := within
        (⟨⟨address, G⟩, directSummary Imp (assignment PUnit.unit) address⟩ : Attachment sigma)
        (by simp [attachedSummaries])
      simpa [attachedRequirements, attachedSummaries, sumRequirements] using
        filter_pending_inside Imp (assignment PUnit.unit) address total ownWithin
  | _, .ordinary _ children, assignment, address, total, within =>
      filter_attached_requirements_children Imp children assignment address 0 total within

theorem filter_attached_requirements_children
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    (total : Multiset Nat) →
    (∀ input ∈ attachedChildSummaries Imp children assignment address slot,
      ∀ uid ∈ input.2.inventory, uid ∈ total) →
    (attachedChildRequirements children assignment address slot).filter (fun r => r.owner ∉ total) =
      (sumRequirements (attachedChildSummaries Imp children assignment address slot)).filter
        (fun r => r.owner ∉ total)
  | _, .nil, _, _, _, _, _ => by
      simp [attachedChildRequirements, attachedChildSummaries, sumRequirements]
  | _, .cons head tail, assignment, address, slot, total, within => by
      have headWithin : ∀ input ∈ attachedSummaries Imp head
          (fun h => assignment (.inl h)) (address ++ [slot]),
          ∀ uid ∈ input.2.inventory, uid ∈ total := by
        intro input present
        exact within input (List.mem_append_left _ present)
      have tailWithin : ∀ input ∈ attachedChildSummaries Imp tail
          (fun h => assignment (.inr h)) address (slot + 1),
          ∀ uid ∈ input.2.inventory, uid ∈ total := by
        intro input present
        exact within input (List.mem_append_right _ present)
      rw [attachedChildRequirements, attachedChildSummaries, sumRequirements_append,
        Multiset.filter_add, Multiset.filter_add,
        filter_attached_requirements Imp head _ _ _ headWithin,
        filter_attached_requirements_children Imp tail _ _ _ _ tailWithin]
end

mutual
theorem attached_inventory
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    (assignment : tree.LeafAssignment) → (address : InternalAddress) →
    sumInventories (attachedSummaries Imp tree assignment address) =
      (attachedGrants tree assignment address).map Grant.uid
  | _, .interface _, assignment, address => by
      simp [attachedSummaries, sumInventories, directSummary, attachedGrants]
  | _, .ordinary _ children, assignment, address =>
      attached_inventory_children Imp children assignment address 0

theorem attached_inventory_children
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    sumInventories (attachedChildSummaries Imp children assignment address slot) =
      (attachedChildGrants children assignment address slot).map Grant.uid
  | _, .nil, _, _, _ => by
      simp [attachedChildSummaries, sumInventories, attachedChildGrants]
  | _, .cons head tail, assignment, address, slot => by
      rw [attachedChildSummaries, sumInventories_append, attached_inventory,
        attached_inventory_children]
      simp [attachedChildGrants, Multiset.map_add]
end

/-- Exact owner inventory transport for arbitrary typed simultaneous native
filling, including malformed scope references.  No freshness hypothesis
is needed for this field; multiplicities reveal duplicate declarations. -/
theorem inventory_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    (directSummary Imp (tree.fillAssignment assignment) address).inventory =
      (composeSummary (directSummary Imp tree address)
        (attachedSummaries Imp tree assignment address)).inventory := by
  have native := (events_fill tree assignment address).2
  change ((events (tree.fillAssignment assignment) address).grants.map Grant.uid : Multiset _) =
    ((events tree address).grants.map Grant.uid : Multiset _) +
      sumInventories (attachedSummaries Imp tree assignment address)
  rw [attached_inventory]
  simpa only [Multiset.map_coe, Multiset.map_add] using congrArg (Multiset.map Grant.uid) native

/-- Exact physical outstanding-demand transport under arbitrary simultaneous
native filling. Newly internal owners disappear from this field even when
their branch/pack check will fail; they never become fictitious external
requirements. Every retained top occurrence keeps its actual address. -/
theorem requirements_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    (directSummary Imp (tree.fillAssignment assignment) address).requirements =
      (composeSummary (directSummary Imp tree address)
        (attachedSummaries Imp tree assignment address)).requirements := by
  classical
  let parent := directSummary Imp tree address
  let inputs := attachedSummaries Imp tree assignment address
  let total := combinedInventory parent inputs
  have parentWithin : ∀ uid ∈ parent.inventory, uid ∈ total := by
    intro uid present
    exact Multiset.mem_add.mpr (.inl present)
  have inputsWithin : ∀ input ∈ inputs, ∀ uid ∈ input.2.inventory, uid ∈ total := by
    intro input present uid declared
    exact Multiset.mem_add.mpr (.inr (inventory_of_input inputs input present uid declared))
  change (directSummary Imp (tree.fillAssignment assignment) address).requirements =
    (parent.requirements + sumRequirements inputs).filter (fun r => r.owner ∉ total)
  rw [requirements_filter, inventory_fill]
  change ((events (tree.fillAssignment assignment) address).requirements :
    Multiset (Requirement sigma)).filter (fun r => r.owner ∉ total) = _
  rw [(events_fill tree assignment address).1, Multiset.filter_add,
    filter_pending_inside Imp tree address total parentWithin,
    filter_attached_requirements Imp tree assignment address total inputsWithin]
  exact (Multiset.filter_add _ _ _).symm

/-- Exact surviving physical-hole order, whole boundaries and absolute
addresses. Inherited Boxes remain typed holes, never coefficient units. -/
theorem holes_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    (directSummary Imp (tree.fillAssignment assignment) address).holes =
      (composeSummary (directSummary Imp tree address)
        (attachedSummaries Imp tree assignment address)).holes :=
  filled_hole_rows Imp tree assignment address

/-- The root boundary is fixed by native typed simultaneous filling. -/
theorem conclusion_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    (directSummary Imp (tree.fillAssignment assignment) address).conclusion =
      (composeSummary (directSummary Imp tree address)
        (attachedSummaries Imp tree assignment address)).conclusion := rfl

theorem hasInternalOwner_prefix_events (path : InternalAddress) (e : Events sigma)
    (r : Requirement sigma) :
    HasInternalOwner (prefixEvents path e) r ↔ HasInternalOwner e r := by
  simp [HasInternalOwner, prefixEvents, prefixGrant]

theorem interior_prefix_events (path : InternalAddress) (e : Events sigma) :
    InteriorLegal (prefixEvents path e) ↔ InteriorLegal e := by
  constructor
  · intro all r present internal
    have inPref : prefixRequirement path r ∈ (prefixEvents path e).requirements :=
      List.mem_map.mpr ⟨r, present, rfl⟩
    have ownPref : HasInternalOwner (prefixEvents path e) (prefixRequirement path r) :=
      (hasInternalOwner_prefix_events _ _ _).mpr internal
    rcases all _ inPref ownPref with ⟨g, hg, valid⟩
    rcases List.mem_map.mp hg with ⟨original, originalPresent, same⟩
    subst g
    exact ⟨original, originalPresent, (compatible_prefix _ _ _).mp valid⟩
  · intro all r present internal
    rcases List.mem_map.mp present with ⟨original, originalPresent, same⟩
    subst r
    have own : HasInternalOwner e original :=
      (hasInternalOwner_prefix_events _ _ _).mp internal
    rcases all original originalPresent own with ⟨g, hg, valid⟩
    exact ⟨prefixGrant path g, List.mem_map.mpr ⟨g, hg, rfl⟩,
      (compatible_prefix _ _ _).mpr valid⟩

theorem ok_at_iff (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) :
    (directSummary Imp tree address).ok ↔ (directSummary Imp tree []).ok := by
  change (ExactTree Imp tree ∧ UniqueOwners (events tree address) ∧
    InteriorLegal (events tree address)) ↔
    (ExactTree Imp tree ∧ UniqueOwners (events tree []) ∧ InteriorLegal (events tree []))
  rw [events_at, interior_prefix_events]
  simp only [UniqueOwners, prefixEvents, List.map_map, Function.comp_def, prefixGrant]

theorem outstanding_prefix_events (path : InternalAddress) (e : Events sigma) :
    outstanding (prefixEvents path e) = (outstanding e).map (prefixRequirement path) := by
  classical
  simp only [outstanding, prefixEvents, List.filter_map]
  congr 1
  apply List.filter_congr
  intro r present
  change decide (¬ HasInternalOwner (prefixEvents path e) (prefixRequirement path r)) =
    decide (¬ HasInternalOwner e r)
  have owner : HasInternalOwner (prefixEvents path e) (prefixRequirement path r) ↔
      HasInternalOwner e r := by
    simpa only [HasInternalOwner, prefixRequirement] using
      hasInternalOwner_prefix_events path e (prefixRequirement path r)
  exact decide_eq_decide.mpr (not_congr owner)

theorem requirements_at (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) :
    (directSummary Imp tree address).requirements =
      (directSummary Imp tree []).requirements.map (prefixRequirement address) := by
  change (outstanding (events tree address) : Multiset (Requirement sigma)) = _
  rw [events_at, outstanding_prefix_events]
  rfl

theorem inventory_at (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) :
    (directSummary Imp tree address).inventory = (directSummary Imp tree []).inventory := by
  change ((events tree address).grants.map Grant.uid : Multiset Nat) = _
  rw [events_at]
  simp [prefixEvents, prefixGrant, List.map_map, Function.comp_def, directSummary]

mutual
theorem attachedSummaries_eq_map
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    (assignment : tree.LeafAssignment) → (address : InternalAddress) →
    attachedSummaries Imp tree assignment address = tree.leafOrder.map (fun hole =>
      (⟨address ++ tree.leafAddress hole, tree.leafBoundary hole⟩,
        directSummary Imp (assignment hole) (address ++ tree.leafAddress hole)))
  | _, .interface _, _, _ => by
      simp [attachedSummaries, CKTree.leafOrder, CKTree.leafAddress, CKTree.leafBoundary]
  | _, .ordinary _ children, assignment, address => by
      simpa [attachedSummaries, CKTree.leafOrder, CKTree.leafAddress,
        CKTree.leafBoundary, offsetFirst_zero] using
          attachedChildSummaries_eq_map Imp children assignment address 0

theorem attachedChildSummaries_eq_map
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    attachedChildSummaries Imp children assignment address slot = children.leafOrder.map (fun hole =>
      (⟨address ++ offsetFirst slot (children.leafAddress hole), children.leafBoundary hole⟩,
        directSummary Imp (assignment hole)
          (address ++ offsetFirst slot (children.leafAddress hole))))
  | _, .nil, _, _, _ => rfl
  | _, .cons head tail, assignment, address, slot => by
      rw [attachedChildSummaries, attachedSummaries_eq_map, attachedChildSummaries_eq_map]
      change _ = List.map
        (fun (hole : head.LeafOccurrence ⊕ tail.LeafOccurrence) =>
          ((⟨address ++ offsetFirst slot ((CKChildren.cons head tail).leafAddress hole),
              (CKChildren.cons head tail).leafBoundary hole⟩ : Hole sigma),
            directSummary Imp (assignment hole)
              (address ++ offsetFirst slot ((CKChildren.cons head tail).leafAddress hole))))
        (head.leafOrder.map Sum.inl ++ tail.leafOrder.map Sum.inr)
      rw [@List.map_append (head.LeafOccurrence ⊕ tail.LeafOccurrence) (Attachment sigma)]
      simp only [List.map_map]
      congr 1
      · apply List.map_congr_left
        intro hole present
        simp [CKChildren.leafAddress, CKChildren.leafBoundary, offsetFirst, List.append_assoc]
      · apply List.map_congr_left
        intro hole present
        simp [CKChildren.leafAddress, CKChildren.leafBoundary, offsetFirst_shift]
end

mutual
theorem attached_summary_forall
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    (assignment : tree.LeafAssignment) → (address : InternalAddress) →
    (property : Attachment sigma → Prop) →
    ((∀ input ∈ attachedSummaries Imp tree assignment address, property input) ↔
      ∀ hole, property (⟨address ++ tree.leafAddress hole, tree.leafBoundary hole⟩,
        directSummary Imp (assignment hole) (address ++ tree.leafAddress hole)))
  | G, .interface _, assignment, address, property => by
      constructor
      · intro all hole
        cases hole
        apply all
        simp [attachedSummaries, CKTree.leafAddress, CKTree.leafBoundary]
      · intro all input present
        have same : input = (⟨address, G⟩, directSummary Imp (assignment PUnit.unit) address) := by
          simpa [attachedSummaries] using present
        subst input
        simpa [CKTree.leafAddress, CKTree.leafBoundary] using all PUnit.unit
  | _, .ordinary _ children, assignment, address, property => by
      simpa [attachedSummaries, CKTree.leafAddress, CKTree.leafBoundary, offsetFirst_zero] using
        attached_child_summary_forall Imp children assignment address 0 property

theorem attached_child_summary_forall
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    (property : Attachment sigma → Prop) →
    ((∀ input ∈ attachedChildSummaries Imp children assignment address slot, property input) ↔
      ∀ hole, property
        (⟨address ++ offsetFirst slot (children.leafAddress hole), children.leafBoundary hole⟩,
          directSummary Imp (assignment hole)
            (address ++ offsetFirst slot (children.leafAddress hole))))
  | _, .nil, _, _, _, _ => by
      constructor
      · intro all hole; exact nomatch hole
      · intro all input present; cases present
  | _, .cons head tail, assignment, address, slot, property => by
      simp only [attachedChildSummaries, List.mem_append, or_imp, forall_and]
      rw [attached_summary_forall Imp head, attached_child_summary_forall Imp tail]
      constructor
      · rintro ⟨onHead, onTail⟩ hole
        cases hole with
        | inl h => simpa [CKChildren.leafAddress, CKChildren.leafBoundary, offsetFirst,
            List.append_assoc] using onHead h
        | inr h => simpa [CKChildren.leafAddress, CKChildren.leafBoundary,
            offsetFirst_shift] using onTail h
      · intro all
        exact ⟨fun h => by simpa [CKChildren.leafAddress, CKChildren.leafBoundary,
            offsetFirst, List.append_assoc] using all (.inl h),
          fun h => by simpa [CKChildren.leafAddress, CKChildren.leafBoundary,
            offsetFirst_shift] using all (.inr h)⟩
end

theorem unique_inventory_iff
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) :
    UniqueOwners (events tree address) ↔ (directSummary Imp tree address).inventory.Nodup := by
  exact Multiset.coe_nodup.symm

theorem sumInventories_nodup_input (inputs : List (Attachment sigma))
    (unique : (sumInventories inputs).Nodup) (input : Attachment sigma)
    (present : input ∈ inputs) : input.2.inventory.Nodup := by
  induction inputs with
  | nil => cases present
  | cons head tail ih =>
      have split := Multiset.nodup_add.mp unique
      rcases List.mem_cons.mp present with same | inTail
      · subst input; exact split.1
      · exact ih split.2.1 inTail

theorem combinedInventory_fresh
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment)
    (unique : (combinedInventory (directSummary Imp tree [])
      (attachedSummaries Imp tree assignment [])).Nodup) :
    Fresh (events tree []) (attachedEvents tree assignment []).grants := by
  have separated := (Multiset.nodup_add.mp unique).2.2
  intro parent parentPresent child childPresent same
  have own : parent.uid ∈ (directSummary Imp tree []).inventory := by
    change parent.uid ∈ ((events tree []).grants.map Grant.uid : Multiset Nat)
    exact List.mem_map.mpr ⟨parent, parentPresent, rfl⟩
  have inserted : child.uid ∈ sumInventories (attachedSummaries Imp tree assignment []) := by
    rw [attached_inventory]
    apply Multiset.mem_map.mpr
    refine ⟨child, ?_, rfl⟩
    rw [← (attached_event_bags tree assignment []).2]
    exact childPresent
  exact Multiset.disjoint_left.mp separated own (by simpa [same] using inserted)

theorem hasInternalOwner_attached_inventory
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (r : Requirement sigma) :
    HasInternalOwner (attachedEvents tree assignment []) r ↔
      r.owner ∈ sumInventories (attachedSummaries Imp tree assignment []) := by
  rw [attached_inventory, ← (attached_event_bags tree assignment []).2]
  simp [HasInternalOwner]

/-- Total native failure-flag refinement at the whole root. Neither local
correctness nor well-scoped cross references are assumed. Duplicate bottom
declarations make both sides fail before any exposure lookup is accepted. -/
theorem ok_fill_root
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) :
    (directSummary Imp (tree.fillAssignment assignment) []).ok ↔
      (composeSummary (directSummary Imp tree [])
        (attachedSummaries Imp tree assignment [])).ok := by
  classical
  let parent := directSummary Imp tree []
  let inputs := attachedSummaries Imp tree assignment []
  let total := combinedInventory parent inputs
  have finalUnique : UniqueOwners (events (tree.fillAssignment assignment) []) ↔ total.Nodup := by
    rw [unique_inventory_iff Imp, inventory_fill]
    rfl
  have inputMember (hole : tree.LeafOccurrence) :
      (⟨tree.leafAddress hole, tree.leafBoundary hole⟩,
        directSummary Imp (assignment hole) (tree.leafAddress hole)) ∈ inputs := by
    change _ ∈ attachedSummaries Imp tree assignment []
    rw [attachedSummaries_eq_map]
    exact List.mem_map.mpr ⟨hole, tree.leaf_mem_leafOrder hole, by simp⟩
  have toPending (hole : tree.LeafOccurrence) (r : Requirement sigma)
      (pending : r ∈ outstanding (events (assignment hole) [])) :
      prefixRequirement (tree.leafAddress hole) r ∈
        (directSummary Imp (assignment hole) (tree.leafAddress hole)).requirements := by
    rw [requirements_at]
    apply Multiset.mem_map.mpr
    exact ⟨r, pending, rfl⟩
  constructor
  · rintro ⟨localFinal, ownersFinal, insideFinal⟩
    have unique : total.Nodup := finalUnique.mp ownersFinal
    have fresh := combinedInventory_fresh Imp tree assignment unique
    rcases (exact_fill Imp tree assignment).mp localFinal with ⟨parentLocal, pieceLocal⟩
    rcases (native_scope_partition Imp tree assignment fresh).mp insideFinal with
      ⟨parentInside, pieceInside, parentNoInserted, pieceNoInserted, lookup⟩
    have split := Multiset.nodup_add.mp unique
    have parentOwners : UniqueOwners (events tree []) :=
      (unique_inventory_iff Imp tree []).mpr split.1
    have pieceOK (hole : tree.LeafOccurrence) :
        (directSummary Imp (assignment hole) (tree.leafAddress hole)).ok := by
      have uniquePiece := sumInventories_nodup_input inputs split.2.1 _ (inputMember hole)
      have localOwners : UniqueOwners (events (assignment hole) []) := by
        apply (unique_inventory_iff Imp (assignment hole) []).mpr
        rw [← inventory_at Imp (assignment hole) (tree.leafAddress hole)]
        exact uniquePiece
      exact (ok_at_iff Imp (assignment hole) _).mpr
        ⟨pieceLocal hole, localOwners, pieceInside hole⟩
    refine ⟨⟨parentLocal, parentOwners, parentInside⟩, ?_, ?_, unique, ?_, ?_⟩
    · apply (attached_summary_forall Imp tree assignment []
        (fun input => input.2.ok ∧ input.1.boundary = input.2.conclusion)).mpr
      intro hole
      simpa using (show (directSummary Imp (assignment hole) (tree.leafAddress hole)).ok ∧
        tree.leafBoundary hole = (directSummary Imp (assignment hole) (tree.leafAddress hole)).conclusion
        from ⟨pieceOK hole, rfl⟩)
    · exact attachment_holes Imp tree assignment []
    · intro r pending owned
      have pending : r ∈ outstanding (events tree []) := pending
      rcases (mem_outstanding _ r).mp pending with ⟨present, outside⟩
      rcases Multiset.mem_add.mp owned with ownParent | ownInserted
      · exact outside ((hasInternalOwner_inventory Imp tree [] r).mpr ownParent)
      · exact parentNoInserted r pending
          ((hasInternalOwner_attached_inventory Imp tree assignment r).mpr ownInserted)
    · apply (attached_summary_forall Imp tree assignment []
        (fun input => ∀ r ∈ input.2.requirements, r.owner ∈ total →
          r.owner ∈ parent.inventory ∧ ∃ exposure ∈ parent.exposure,
            MatchesExposure input.1.address r exposure)).mpr
      intro hole r pending owned
      rw [requirements_at] at pending
      rcases Multiset.mem_map.mp pending with ⟨original, originalPresent, same⟩
      subst r
      have originalPresent : original ∈ outstanding (events (assignment hole) []) := originalPresent
      rcases Multiset.mem_add.mp owned with ownParent | ownInserted
      · have internal := (hasInternalOwner_inventory Imp tree [] original).mpr ownParent
        rcases lookup hole original originalPresent internal with ⟨exposure, hg, matched⟩
        refine ⟨ownParent, exposure, hg, ?_⟩
        simpa [MatchesExposure, prefixRequirement] using matched
      · exact False.elim (pieceNoInserted hole original originalPresent
          ((hasInternalOwner_attached_inventory Imp tree assignment _).mpr ownInserted))
  · rintro ⟨parentOK, pieceFlags, covered, unique, parentNoTotal, pieceChecks⟩
    have fresh := combinedInventory_fresh Imp tree assignment unique
    have pieces : ∀ hole,
        (directSummary Imp (assignment hole) (tree.leafAddress hole)).ok := by
      intro hole
      exact (pieceFlags _ (inputMember hole)).1
    have piecesRoot : ∀ hole, (directSummary Imp (assignment hole) []).ok :=
      fun hole => (ok_at_iff Imp (assignment hole) _).mp (pieces hole)
    refine ⟨(exact_fill Imp tree assignment).mpr
      ⟨parentOK.1, fun hole => (piecesRoot hole).1⟩, finalUnique.mpr unique, ?_⟩
    apply (native_scope_partition Imp tree assignment fresh).mpr
    refine ⟨parentOK.2.2, fun hole => (piecesRoot hole).2.2, ?_, ?_, ?_⟩
    · intro r pending ownInserted
      have inTotal : r.owner ∈ total := Multiset.mem_add.mpr (.inr
        ((hasInternalOwner_attached_inventory Imp tree assignment r).mp ownInserted))
      exact parentNoTotal r pending inTotal
    · intro hole r pending ownInserted
      have uidInserted : (prefixRequirement (tree.leafAddress hole) r).owner ∈
          sumInventories inputs :=
        (hasInternalOwner_attached_inventory Imp tree assignment _).mp ownInserted
      have inTotal : (prefixRequirement (tree.leafAddress hole) r).owner ∈ total :=
        Multiset.mem_add.mpr (.inr uidInserted)
      have namedParent := (pieceChecks _ (inputMember hole) _ (toPending hole r pending) inTotal).1
      exact Multiset.disjoint_left.mp (Multiset.nodup_add.mp unique).2.2 namedParent uidInserted
    · intro hole r pending parentOwner
      have uidParent : (prefixRequirement (tree.leafAddress hole) r).owner ∈ parent.inventory :=
        (hasInternalOwner_inventory Imp tree [] r).mp parentOwner
      have inTotal : (prefixRequirement (tree.leafAddress hole) r).owner ∈ total :=
        Multiset.mem_add.mpr (.inl uidParent)
      rcases (pieceChecks _ (inputMember hole) _ (toPending hole r pending) inTotal).2 with
        ⟨exposure, present, matched⟩
      exact ⟨exposure, present, by simpa [MatchesExposure, prefixRequirement] using matched⟩

#print axioms inventory_fill
#print axioms summary_legality_iff
#print axioms requirements_fill
#print axioms holes_fill
#print axioms conclusion_fill
#print axioms attachment_holes
#print axioms parent_exposure_resolves
#print axioms interior_fill_partition
#print axioms parent_to_filling_iff
#print axioms attached_interior_iff
#print axioms filling_to_parent_iff
#print axioms native_scope_partition
#print axioms compose_failure_persists
#print axioms child_failure_persists
#print axioms newly_internal_not_external
#print axioms ok_at_iff
#print axioms outstanding_prefix_events
#print axioms requirements_at
#print axioms inventory_at
#print axioms attachedSummaries_eq_map
#print axioms ok_fill_root

end Potkin.Research.OpenDischarge

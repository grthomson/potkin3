import Potkin.Research.OpenDischarge
import Potkin.InverseCutGeometry

/-!
# Finite owner inventories and boundary-facing discharge information

The records in this module are metadata of native CK trees.  Demands retain
their physical top occurrence address, whereas an exposure contains only a
hole address, declared owner UID, shared parameters and permitted branch.
Ordinary interior vertices and bottom common sequents are omitted. Owner
inventories, demands and exposure tables are multisets of metadata rows:
their traversal order is not recoverable from a compact summary and is
not part of its contract. A demand still includes its physical occurrence
address, so equal-looking tops and their multiplicities are not collapsed.
The native ordered premise/factor packets remain separate and unchanged.

`Summary.ok` is a proposition about finite data, not a replacement legality
definition: the independent `Legal` predicate remains the actual-tree
checker in `OpenDischarge`.  Executable decision procedures and exact
summary substitution are separate obligations.
-/

namespace Potkin.Research.OpenDischarge

universe u v w
variable {sigma : Signature.{u, v}}

def prefixRequirement (pathPrefix : InternalAddress) (r : Requirement sigma) :
    Requirement sigma := {r with topAddress := pathPrefix ++ r.topAddress}

def prefixGrant (pathPrefix : InternalAddress) (g : Grant sigma) : Grant sigma :=
  {g with address := pathPrefix ++ g.address}

def prefixEvents (pathPrefix : InternalAddress) (e : Events sigma) : Events sigma :=
  ⟨e.requirements.map (prefixRequirement pathPrefix),
    e.grants.map (prefixGrant pathPrefix)⟩

theorem prefixEvents_append (pathPrefix : InternalAddress) (a b : Events sigma) :
    prefixEvents pathPrefix (a.append b) =
      (prefixEvents pathPrefix a).append (prefixEvents pathPrefix b) := by
  simp [prefixEvents, Events.append, List.map_append]

theorem rootEvents_prefix (pathPrefix address : InternalAddress)
    (o : LocalOccurrence sigma (Data sigma)) :
    rootEvents (pathPrefix ++ address) o = prefixEvents pathPrefix (rootEvents address o) := by
  cases h : o.instanceData <;>
    simp [rootEvents, h, prefixEvents, prefixRequirement, prefixGrant]

mutual
theorem events_prefix : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (pathPrefix address : InternalAddress) →
    events tree (pathPrefix ++ address) = prefixEvents pathPrefix (events tree address)
  | _, .interface _, _, _ => rfl
  | _, .ordinary o children, pathPrefix, address => by
      rw [events, rootEvents_prefix, childEvents_prefix, events, prefixEvents_append]

theorem childEvents_prefix : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (pathPrefix address : InternalAddress) → (slot : Nat) →
    childEvents children (pathPrefix ++ address) slot =
      prefixEvents pathPrefix (childEvents children address slot)
  | _, .nil, _, _, _ => rfl
  | _, .cons head tail, pathPrefix, address, slot => by
      simp only [childEvents]
      rw [List.append_assoc, events_prefix, childEvents_prefix, prefixEvents_append]
end

theorem events_at (tree : CKTree sigma (Data sigma) G) (pathPrefix : InternalAddress) :
    events tree pathPrefix = prefixEvents pathPrefix (events tree []) := by
  simpa using events_prefix tree pathPrefix []

theorem compatible_prefix (pathPrefix : InternalAddress)
    (r : Requirement sigma) (g : Grant sigma) :
    Compatible (prefixRequirement pathPrefix r) (prefixGrant pathPrefix g) ↔ Compatible r g := by
  simp only [Compatible, prefixRequirement, prefixGrant]
  constructor
  · rintro ⟨uid, pack, suffix, equal⟩
    refine ⟨uid, pack, suffix, ?_⟩
    apply List.append_cancel_left
    simpa only [List.append_assoc] using equal
  · rintro ⟨uid, pack, suffix, equal⟩
    refine ⟨uid, pack, suffix, ?_⟩
    simpa only [List.append_assoc] using congrArg (pathPrefix ++ ·) equal

/-- A genuine vacancy has no rule vertices at or below it. This uses the
native address classifier, not a semantic-edge or renamed-rule guess. -/
theorem interface_status_append {InstanceData : Type w}
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    {address : InternalAddress} (vacancy : tree.InterfaceAt address)
    (suffix : InternalAddress) :
    tree.statusAt (address ++ suffix) =
      (if suffix = [] then .interface else .missing) := by
  induction vacancy generalizing suffix with
  | root H => cases suffix <;> rfl
  | child o children i below ih =>
      change children.statusAt i.val (_ ++ suffix) = _
      rw [CKChildren.statusAt_get]
      exact ih suffix

theorem hole_not_prefix_vertex {InstanceData : Type w}
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (hole : tree.LeafOccurrence) {address : InternalAddress}
    (vertex : tree.VertexAt address) :
    ¬ AddressPrefix (tree.leafAddress hole) address := by
  rintro ⟨suffix, equal⟩
  have status := vertex.statusAt_eq_ordinary
  rw [← equal, interface_status_append (tree.leafPuncture hole).toInterfaceAt] at status
  split at status <;> cases status

mutual
/-- Only inserted pieces are traversed; the parent contributes no events. -/
def attachedRequirements : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → tree.LeafAssignment →
    InternalAddress → Multiset (Requirement sigma)
  | _, .interface _, assignment, address =>
      (events (assignment PUnit.unit) address).requirements
  | _, .ordinary _ children, assignment, address =>
      attachedChildRequirements children assignment address 0

def attachedChildRequirements : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → children.LeafAssignment →
    InternalAddress → Nat → Multiset (Requirement sigma)
  | _, .nil, _, _, _ => 0
  | _, .cons head tail, assignment, address, slot =>
      attachedRequirements head (fun h => assignment (.inl h)) (address ++ [slot]) +
        attachedChildRequirements tail (fun h => assignment (.inr h)) address (slot + 1)
end

theorem multiset_interleave {α : Type*} (a b c d : Multiset α) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Multiset.add_assoc a b (c + d), ← Multiset.add_assoc b c d,
    Multiset.add_comm b c, Multiset.add_assoc c b d,
    ← Multiset.add_assoc a c (b + d)]

mutual
def attachedGrants : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → tree.LeafAssignment →
    InternalAddress → Multiset (Grant sigma)
  | _, .interface _, assignment, address =>
      (events (assignment PUnit.unit) address).grants
  | _, .ordinary _ children, assignment, address =>
      attachedChildGrants children assignment address 0

def attachedChildGrants : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → children.LeafAssignment →
    InternalAddress → Nat → Multiset (Grant sigma)
  | _, .nil, _, _, _ => 0
  | _, .cons head tail, assignment, address, slot =>
      attachedGrants head (fun h => assignment (.inl h)) (address ++ [slot]) +
        attachedChildGrants tail (fun h => assignment (.inr h)) address (slot + 1)
end

mutual
/-- Physical top and bottom multiplicities survive simultaneous filling.
The bags are metadata views of the native ordered lists, not forest factors.
Native premise order and hole addresses remain on the original witnesses. -/
theorem events_fill : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (assignment : tree.LeafAssignment) →
    (address : InternalAddress) →
    ((events (tree.fillAssignment assignment) address).requirements : Multiset _) =
      ((events tree address).requirements : Multiset (Requirement sigma)) +
        attachedRequirements tree assignment address ∧
    ((events (tree.fillAssignment assignment) address).grants : Multiset _) =
      ((events tree address).grants : Multiset (Grant sigma)) +
        attachedGrants tree assignment address
  | _, .interface _, assignment, address => by
      change ((events (assignment PUnit.unit) address).requirements : Multiset (Requirement sigma)) =
        0 + ((events (assignment PUnit.unit) address).requirements : Multiset (Requirement sigma)) ∧
        ((events (assignment PUnit.unit) address).grants : Multiset (Grant sigma)) =
          0 + ((events (assignment PUnit.unit) address).grants : Multiset (Grant sigma))
      simp
  | _, .ordinary o children, assignment, address => by
      rcases childEvents_fill children assignment address 0 with ⟨hr, hg⟩
      simp only [CKTree.fillAssignment, events, Events.append, ← Multiset.coe_add,
        attachedRequirements, attachedGrants]
      constructor
      · rw [hr, Multiset.add_assoc]
      · rw [hg, Multiset.add_assoc]

theorem childEvents_fill : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    ((childEvents (children.fillAssignment assignment) address slot).requirements : Multiset _) =
      ((childEvents children address slot).requirements : Multiset (Requirement sigma)) +
        attachedChildRequirements children assignment address slot ∧
    ((childEvents (children.fillAssignment assignment) address slot).grants : Multiset _) =
      ((childEvents children address slot).grants : Multiset (Grant sigma)) +
        attachedChildGrants children assignment address slot
  | _, .nil, _, _, _ => by simp [childEvents, CKChildren.fillAssignment,
      attachedChildRequirements, attachedChildGrants]
  | _, .cons head tail, assignment, address, slot => by
      rcases events_fill head (fun h => assignment (.inl h)) (address ++ [slot]) with ⟨hr, hg⟩
      rcases childEvents_fill tail (fun h => assignment (.inr h)) address (slot + 1) with
        ⟨tr, tg⟩
      simp only [CKChildren.fillAssignment, childEvents, Events.append, ← Multiset.coe_add,
        attachedChildRequirements, attachedChildGrants]
      constructor
      · rw [hr, tr]; exact multiset_interleave _ _ _ _
      · rw [hg, tg]; exact multiset_interleave _ _ _ _
end

structure Hole (sigma : Signature.{u, v}) where
  address : InternalAddress
  boundary : Hypersequent sigma

structure Exposure (sigma : Signature.{u, v}) where
  hole : InternalAddress
  owner : Nat
  parameters : Parameters sigma
  role : Fin 2

structure Summary (sigma : Signature.{u, v}) where
  conclusion : Hypersequent sigma
  holes : List (Hole sigma)
  inventory : Multiset Nat
  requirements : Multiset (Requirement sigma)
  exposure : Multiset (Exposure sigma)
  ok : Prop

noncomputable def exposureRows (holes : List (Hole sigma))
    (grants : List (Grant sigma)) : List (Exposure sigma) := by
  classical
  exact holes.flatMap fun h => grants.flatMap fun g =>
    ([0, 1] : List (Fin 2)).filterMap fun role =>
      if ∃ suffix, h.address = g.address ++ [role.val] ++ suffix then
        some ⟨h.address, g.uid, g.parameters, role⟩ else none

noncomputable def directSummary
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress := []) : Summary sigma :=
  let e := events tree address
  let holes := tree.leafOrder.map fun h =>
    (⟨address ++ tree.leafAddress h, tree.leafBoundary h⟩ : Hole sigma)
  ⟨G, holes, e.grants.map Grant.uid, outstanding e,
    exposureRows holes e.grants, ExactTree Imp tree ∧ UniqueOwners e ∧ InteriorLegal e⟩

/-- With no external declarations, independent legality is equivalent to
internal success and no outstanding top occurrence. No certificate is
invented for a typed hole: completeness is a separate required premise
when this theorem is used as correctness of a finished proof. -/
theorem closed_summary_agreement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) :
    Legal Imp tree address [] ↔ (directSummary Imp tree address).ok ∧
      (directSummary Imp tree address).requirements = 0 := by
  have fresh : Fresh (events tree address) [] := by
    intro gi hgi ge hge; cases hge
  rw [Legal, legality_interface_iff _ _ fresh]
  change (ExactTree Imp tree ∧ UniqueOwners (events tree address) ∧
    InteriorLegal (events tree address) ∧ OutstandingLegal (events tree address) []) ↔
    (ExactTree Imp tree ∧ UniqueOwners (events tree address) ∧
      InteriorLegal (events tree address)) ∧
        (outstanding (events tree address) : Multiset (Requirement sigma)) = 0
  have pending : OutstandingLegal (events tree address) [] ↔
      outstanding (events tree address) = [] := by
    simp [OutstandingLegal, List.eq_nil_iff_forall_not_mem]
  rw [pending]
  rw [Multiset.coe_eq_zero]
  constructor
  · rintro ⟨a, b, c, d⟩; exact ⟨⟨a, b, c⟩, d⟩
  · rintro ⟨⟨a, b, c⟩, d⟩; exact ⟨a, b, c, d⟩

theorem hasInternalOwner_append (left right : Events sigma) (r : Requirement sigma) :
    HasInternalOwner (left.append right) r ↔
      HasInternalOwner left r ∨ HasInternalOwner right r := by
  simp only [HasInternalOwner, Events.append, List.mem_append]
  constructor
  · rintro ⟨g, present | present, uid⟩
    · exact Or.inl ⟨g, present, uid⟩
    · exact Or.inr ⟨g, present, uid⟩
  · rintro (⟨g, present, uid⟩ | ⟨g, present, uid⟩)
    · exact ⟨g, Or.inl present, uid⟩
    · exact ⟨g, Or.inr present, uid⟩

noncomputable def excludeOwners (owners : Events sigma)
    (requirements : List (Requirement sigma)) : List (Requirement sigma) := by
  classical
  exact requirements.filter (fun r => decide (¬ HasInternalOwner owners r))

/-- Newly internal owners are removed even when their routing is illegal.
This equality does not assume that cross-piece references are well scoped. -/
theorem outstanding_append (left right : Events sigma) :
    outstanding (left.append right) =
      excludeOwners right (outstanding left) ++
        excludeOwners left (outstanding right) := by
  classical
  simp only [outstanding, excludeOwners, Events.append, List.filter_append, List.filter_filter]
  congr 1
  · apply List.filter_congr
    intro r hr
    change decide (¬ HasInternalOwner (left.append right) r) =
      (decide (¬ HasInternalOwner right r) && decide (¬ HasInternalOwner left r))
    rw [hasInternalOwner_append]
    simp [not_or, Bool.and_comm]
  · apply List.filter_congr
    intro r hr
    change decide (¬ HasInternalOwner (left.append right) r) =
      (decide (¬ HasInternalOwner left r) && decide (¬ HasInternalOwner right r))
    rw [hasInternalOwner_append]
    simp [not_or]

def CrossLegal (source target : Events sigma) : Prop :=
  ∀ r ∈ outstanding source, HasInternalOwner target r →
    ∃ g ∈ target.grants, Compatible r g

/-- An exact finite ownership-partition theorem.  Its tests include wrong
parameters/branch, hidden owners and reverse ownership: `Compatible` still
checks actual physical ancestry.  To replace this finite event computation
by compact per-hole exposure lookups requires a native routing adapter;
that adapter is not assumed or concealed in this statement. -/
theorem interior_append_iff (left right : Events sigma)
    (fresh : Fresh left right.grants) :
    InteriorLegal (left.append right) ↔
      InteriorLegal left ∧ InteriorLegal right ∧
        CrossLegal left right ∧ CrossLegal right left := by
  have freshReverse : Fresh right left.grants := by
    intro gr hgr gl hgl eq
    exact fresh gl hgl gr hgr eq.symm
  constructor
  · intro legal
    have extractInterior : ∀ (first second : Events sigma),
        Fresh first second.grants → InteriorLegal (first.append second) →
        InteriorLegal first := by
      intro first second disjoint all r hr internal
      rcases all r (List.mem_append_left _ hr)
        ((hasInternalOwner_append first second r).mpr (.inl internal)) with ⟨g, hg, valid⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact ⟨g, hg, valid⟩
      · rcases internal with ⟨gi, hgi, uid⟩
        exact False.elim (disjoint gi hgi g hg (uid.trans valid.1))
    have swapped : InteriorLegal (right.append left) := by
      intro r hr internal
      have present : r ∈ (left.append right).requirements := by
        simpa [Events.append, List.mem_append, or_comm] using hr
      have inside : HasInternalOwner (left.append right) r := by
        simpa [hasInternalOwner_append, or_comm] using internal
      rcases legal r present inside with ⟨g, hg, valid⟩
      exact ⟨g, by simpa [Events.append, List.mem_append, or_comm] using hg, valid⟩
    have extractCross : ∀ (first second : Events sigma),
        InteriorLegal (first.append second) → CrossLegal first second := by
      intro first second all r hr internal
      rcases (mem_outstanding first r).mp hr with ⟨present, outside⟩
      rcases all r (List.mem_append_left _ present)
        ((hasInternalOwner_append first second r).mpr (.inr internal)) with ⟨g, hg, valid⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact False.elim (outside ⟨g, hg, valid.1.symm⟩)
      · exact ⟨g, hg, valid⟩
    exact ⟨extractInterior left right fresh legal,
      extractInterior right left freshReverse swapped,
      extractCross left right legal, extractCross right left swapped⟩
  · rintro ⟨leftLegal, rightLegal, leftCross, rightCross⟩ r hr internal
    have route : ∀ (first second : Events sigma),
        InteriorLegal first → CrossLegal first second →
        r ∈ first.requirements →
        HasInternalOwner (first.append second) r →
        ∃ g ∈ (first.append second).grants, Compatible r g := by
      intro first second own cross present inside
      by_cases ownOwner : HasInternalOwner first r
      · rcases own r present ownOwner with ⟨g, hg, valid⟩
        exact ⟨g, List.mem_append_left _ hg, valid⟩
      · have other := (hasInternalOwner_append first second r).mp inside
        have other := other.resolve_left ownOwner
        rcases cross r ((mem_outstanding first r).mpr ⟨present, ownOwner⟩) other with ⟨g, hg, valid⟩
        exact ⟨g, List.mem_append_right _ hg, valid⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact route left right leftLegal leftCross hr internal
    · have swapped : HasInternalOwner (right.append left) r := by
        simpa [hasInternalOwner_append, or_comm] using internal
      rcases route right left rightLegal rightCross hr swapped with ⟨g, hg, valid⟩
      exact ⟨g, by simpa [Events.append, List.mem_append, or_comm] using hg, valid⟩

#print axioms events_prefix
#print axioms compatible_prefix
#print axioms interface_status_append
#print axioms hole_not_prefix_vertex
#print axioms events_fill
#print axioms closed_summary_agreement
#print axioms outstanding_append
#print axioms interior_append_iff

end Potkin.Research.OpenDischarge

import Potkin.Research.OpenDischargeCertificates
import Potkin.Research.DischargeScopeGeometry

/-!
# Soundness of physical scoped discharge certificates

The scope invariant is essential: a matching identifier in an arbitrary
list is not evidence of ancestry.  Every scope entry below records an actual
ancestor and its ordered branch.  The conclusion uses the independently
defined address-based event relation, not success of a summary evaluator.
-/

namespace Potkin.Research.OpenDischargeAgreement

open OpenDischarge OpenDischargeCertificates
open DischargeScopeGeometry
universe u v
variable {sigma : Signature.{u, v}}

def ScopeAnchored (address : InternalAddress) (scope : List (OwnerSlot sigma)) : Prop :=
  ∀ owner ∈ scope, ∃ suffix,
    address = owner.address ++ [owner.role.val] ++ suffix

def ScopeResolves (request : Requirement sigma) (scope : List (OwnerSlot sigma)) : Prop :=
  ∃ owner ∈ scope, request.owner = owner.uid ∧
    request.parameters = owner.parameters ∧ request.role = owner.role ∧
    ∃ suffix, request.topAddress = owner.address ++ [owner.role.val] ++ suffix

def SoundEvents (e : Events sigma) (scope : List (OwnerSlot sigma)) : Prop :=
  ∀ request ∈ e.requirements,
    (∃ owner ∈ e.grants, Compatible request owner) ∨ ScopeResolves request scope

/-- The two elementary address obstructions used by scoped completeness:
different physical premise branches cannot resolve one another's demands. -/
theorem incompatible_sibling_addresses (request : Requirement sigma) (owner : Grant sigma)
    (address : InternalAddress) (left right : Nat) (requestSuffix ownerSuffix : InternalAddress)
    (requestAddress : request.topAddress = address ++ [left] ++ requestSuffix)
    (ownerAddress : owner.address = address ++ [right] ++ ownerSuffix)
    (different : left ≠ right) : ¬ Compatible request owner := by
  rintro ⟨_, _, suffix, equal⟩
  have branches : left :: requestSuffix = right :: (ownerSuffix ++ [request.role.val] ++ suffix) := by
    apply List.append_cancel_left
    simpa only [requestAddress, ownerAddress, List.append_assoc, List.singleton_append] using equal
  exact different (List.cons.inj branches).1

/-- A bottom strictly above a root top in the proof-drawing direction (a
descendant in root-first addresses) cannot discharge that existing root top. -/
theorem incompatible_descendant_owner (request : Requirement sigma) (owner : Grant sigma)
    (address : InternalAddress) (slot : Nat) (ownerSuffix : InternalAddress)
    (requestAddress : request.topAddress = address)
    (ownerAddress : owner.address = address ++ [slot] ++ ownerSuffix) :
    ¬ Compatible request owner := by
  rintro ⟨_, _, suffix, equal⟩
  have lengths := congrArg List.length equal
  simp only [requestAddress, ownerAddress, List.length_append, List.length_singleton] at lengths
  omega

theorem anchored_child (address : InternalAddress) (slot : Nat)
    (scope : List (OwnerSlot sigma)) (anchored : ScopeAnchored address scope) :
    ScopeAnchored (address ++ [slot]) scope := by
  intro owner present
  rcases anchored owner present with ⟨suffix, equal⟩
  refine ⟨suffix ++ [slot], ?_⟩
  simp only [equal, List.append_assoc]

theorem anchored_enter (uid : Nat) (pack : Parameters sigma)
    (address : InternalAddress) (role : Fin 2) (scope : List (OwnerSlot sigma))
    (anchored : ScopeAnchored address scope) :
    ScopeAnchored (address ++ [role.val]) (enterOwner uid pack address role scope) := by
  intro owner present
  rcases List.mem_cons.mp present with equal | present
  · subst owner
    exact ⟨[], by simp⟩
  · exact anchored_child address role.val scope anchored owner present

theorem sound_append (left right : Events sigma) (scope : List (OwnerSlot sigma))
    (leftSound : SoundEvents left scope) (rightSound : SoundEvents right scope) :
    SoundEvents (left.append right) scope := by
  intro request present
  rcases List.mem_append.mp present with present | present
  · rcases leftSound request present with ⟨owner, found, compatible⟩ | resolved
    · exact Or.inl ⟨owner, List.mem_append_left _ found, compatible⟩
    · exact Or.inr resolved
  · rcases rightSound request present with ⟨owner, found, compatible⟩ | resolved
    · exact Or.inl ⟨owner, List.mem_append_right _ found, compatible⟩
    · exact Or.inr resolved

theorem top_resolves (uid : Nat) (pack : Parameters sigma) (role : Fin 2)
    (address : InternalAddress) (rule : Nat) (scope : List (OwnerSlot sigma))
    (anchored : ScopeAnchored address scope)
    (choice : EligibleOwner uid pack role scope) :
    ScopeResolves ⟨uid, address, rule, role, pack⟩ scope := by
  rcases choice with ⟨index, sameUid, samePack, sameRole⟩
  have present : scope.get index ∈ scope := List.get_mem scope index
  refine ⟨scope.get index, present, sameUid.symm, samePack.symm, sameRole.symm, ?_⟩
  exact anchored _ present

theorem resolve_enter (request : Requirement sigma) (uid : Nat)
    (pack : Parameters sigma) (address : InternalAddress) (rule : Nat)
    (role : Fin 2) (scope : List (OwnerSlot sigma))
    (resolved : ScopeResolves request (enterOwner uid pack address role scope)) :
    Compatible request ⟨uid, address, rule, pack⟩ ∨ ScopeResolves request scope := by
  rcases resolved with ⟨owner, present, uidEqual, packEqual, roleEqual, suffix, equal⟩
  rcases List.mem_cons.mp present with ownerEqual | present
  · subst owner
    apply Or.inl
    refine ⟨uidEqual, packEqual, suffix, ?_⟩
    simpa only [roleEqual] using equal
  · exact Or.inr ⟨owner, present, uidEqual, packEqual, roleEqual, suffix, equal⟩

def emptyChildrenProvider {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma (Data sigma) Gs) : ChildrenProvider children :=
  fun _ _ _ => PEmpty

theorem scope_resolves_enter (request : Requirement sigma) (uid : Nat)
    (pack : Parameters sigma) (address : InternalAddress) (role : Fin 2)
    (scope : List (OwnerSlot sigma)) (resolved : ScopeResolves request scope) :
    ScopeResolves request (enterOwner uid pack address role scope) := by
  rcases resolved with ⟨owner, present, uidEqual, packEqual, roleEqual, suffix, equal⟩
  exact ⟨owner, List.mem_cons_of_mem _ present, uidEqual, packEqual, roleEqual, suffix, equal⟩

theorem eligible_of_scope_resolves (uid : Nat) (pack : Parameters sigma) (role : Fin 2)
    (address : InternalAddress) (rule : Nat) (scope : List (OwnerSlot sigma))
    (resolved : ScopeResolves ⟨uid, address, rule, role, pack⟩ scope) :
    Nonempty (EligibleOwner uid pack role scope) := by
  rcases resolved with ⟨owner, present, sameUid, samePack, sameRole, _⟩
  rcases List.get_of_mem present with ⟨index, equal⟩
  refine ⟨⟨index, ?_⟩⟩
  rw [equal]
  exact ⟨sameUid.symm, samePack.symm, sameRole.symm⟩

theorem sound_children_split {G : Hypersequent sigma}
    {Gs : List (Hypersequent sigma)} (head : CKTree sigma (Data sigma) G)
    (tail : CKChildren sigma (Data sigma) Gs) (address : InternalAddress)
    (slot : Nat) (scope : List (OwnerSlot sigma))
    (sound : SoundEvents (childEvents (.cons head tail) address slot) scope) :
    SoundEvents (events head (address ++ [slot])) scope ∧
      SoundEvents (childEvents tail address (slot + 1)) scope := by
  constructor
  · intro request present
    have offered := sound request (List.mem_append_left _ present)
    rcases offered with ⟨owner, found, compatible⟩ | resolved
    · rcases List.mem_append.mp found with own | sibling
      · exact Or.inl ⟨owner, own, compatible⟩
      · rcases (events_vertices head (address ++ [slot])).1 request present with
          ⟨requestSuffix, requestAddress, _⟩
        rcases (childEvents_vertices tail address (slot + 1)).2 owner sibling with
          ⟨index, ownerSuffix, ownerAddress, _⟩
        exact False.elim (incompatible_sibling_addresses request owner address slot
          ((slot + 1) + index.val) requestSuffix ownerSuffix
          (by simpa only [List.append_assoc] using requestAddress) ownerAddress
          (by omega) compatible)
    · exact Or.inr resolved
  · intro request present
    have offered := sound request (List.mem_append_right _ present)
    rcases offered with ⟨owner, found, compatible⟩ | resolved
    · rcases List.mem_append.mp found with sibling | own
      · rcases (childEvents_vertices tail address (slot + 1)).1 request present with
          ⟨index, requestSuffix, requestAddress, _⟩
        rcases (events_vertices head (address ++ [slot])).2 owner sibling with
          ⟨ownerSuffix, ownerAddress, _⟩
        exact False.elim (incompatible_sibling_addresses request owner address
          ((slot + 1) + index.val) slot requestSuffix ownerSuffix requestAddress
          (by simpa only [List.append_assoc] using ownerAddress)
          (by omega) compatible)
      · exact Or.inl ⟨owner, own, compatible⟩
    · exact Or.inr resolved

theorem root_resolution_enters (request : Requirement sigma) (uid : Nat)
    (pack : Parameters sigma) (address : InternalAddress) (rule : Nat)
    (role : Fin 2) (scope : List (OwnerSlot sigma)) (requestSuffix : InternalAddress)
    (requestAddress : request.topAddress = address ++ [role.val] ++ requestSuffix)
    (compatible : Compatible request ⟨uid, address, rule, pack⟩) :
    ScopeResolves request (enterOwner uid pack address role scope) := by
  rcases compatible with ⟨sameUid, samePack, suffix, equal⟩
  have branches : role.val :: requestSuffix = request.role.val :: suffix := by
    apply List.append_cancel_left
    simpa only [requestAddress, List.append_assoc, List.singleton_append] using equal
  have sameRole : request.role = role := Fin.ext (List.cons.inj branches).1.symm
  refine ⟨⟨uid, address, pack, role⟩, List.mem_cons_self, sameUid, samePack,
    sameRole, suffix, ?_⟩
  simpa only [sameRole] using equal

theorem sound_bottom_split {L R : Hypersequent sigma}
    (left : CKTree sigma (Data sigma) L) (right : CKTree sigma (Data sigma) R)
    (address : InternalAddress) (scope : List (OwnerSlot sigma))
    (uid : Nat) (pack : Parameters sigma) (rule : Nat)
    (sound : SoundEvents
      (({ requirements := [], grants := [⟨uid, address, rule, pack⟩] } : Events sigma).append
        (childEvents (.cons left (.cons right .nil)) address 0)) scope) :
    SoundEvents (events left (address ++ [0])) (enterOwner uid pack address 0 scope) ∧
      SoundEvents (events right (address ++ [1])) (enterOwner uid pack address 1 scope) := by
  constructor
  · intro request present
    have offered := sound request (by
      simp only [Events.append, childEvents, List.nil_append, List.append_nil, List.mem_append]
      exact Or.inl present)
    rcases offered with ⟨owner, found, compatible⟩ | resolved
    · have choices : owner = ⟨uid, address, rule, pack⟩ ∨
          owner ∈ (events left (address ++ [0])).grants ∨
          owner ∈ (events right (address ++ [1])).grants := by
        simpa only [Events.append, childEvents, List.append_nil, List.mem_append,
          List.mem_singleton] using found
      rcases choices with rfl | own | sibling
      · rcases (events_vertices left (address ++ [0])).1 request present with
          ⟨suffix, equal, _⟩
        exact Or.inr (root_resolution_enters request uid pack address rule 0 scope suffix
          (by simpa only [List.append_assoc] using equal) compatible)
      · exact Or.inl ⟨owner, own, compatible⟩
      · rcases (events_vertices left (address ++ [0])).1 request present with
          ⟨requestSuffix, requestAddress, _⟩
        rcases (events_vertices right (address ++ [1])).2 owner sibling with
          ⟨ownerSuffix, ownerAddress, _⟩
        exact False.elim (incompatible_sibling_addresses request owner address 0 1
          requestSuffix ownerSuffix requestAddress ownerAddress (by decide) compatible)
    · exact Or.inr (scope_resolves_enter request uid pack address 0 scope resolved)
  · intro request present
    have offered := sound request (by
      simp only [Events.append, childEvents, List.nil_append, List.append_nil, List.mem_append]
      exact Or.inr present)
    rcases offered with ⟨owner, found, compatible⟩ | resolved
    · have choices : owner = ⟨uid, address, rule, pack⟩ ∨
          owner ∈ (events left (address ++ [0])).grants ∨
          owner ∈ (events right (address ++ [1])).grants := by
        simpa only [Events.append, childEvents, List.append_nil, List.mem_append,
          List.mem_singleton] using found
      rcases choices with rfl | sibling | own
      · rcases (events_vertices right (address ++ [1])).1 request present with
          ⟨suffix, equal, _⟩
        exact Or.inr (root_resolution_enters request uid pack address rule 1 scope suffix
          (by simpa only [List.append_assoc] using equal) compatible)
      · rcases (events_vertices right (address ++ [1])).1 request present with
          ⟨requestSuffix, requestAddress, _⟩
        rcases (events_vertices left (address ++ [0])).2 owner sibling with
          ⟨ownerSuffix, ownerAddress, _⟩
        exact False.elim (incompatible_sibling_addresses request owner address 1 0
          requestSuffix ownerSuffix requestAddress ownerAddress (by decide) compatible)
      · exact Or.inl ⟨owner, own, compatible⟩
    · exact Or.inr (scope_resolves_enter request uid pack address 1 scope resolved)

theorem top_children_sound {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma (Data sigma) Gs) (address : InternalAddress)
    (scope : List (OwnerSlot sigma)) (request : Requirement sigma)
    (sound : SoundEvents
      (({ requirements := [request], grants := [] } : Events sigma).append (childEvents children address 0)) scope) :
    SoundEvents (childEvents children address 0) scope := by
  intro childRequest present
  have offered := sound childRequest (List.mem_append_right _ present)
  simpa only [Events.append, List.nil_append] using offered

theorem top_eligible_from_sound {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma (Data sigma) Gs) (address : InternalAddress)
    (scope : List (OwnerSlot sigma)) (uid : Nat) (pack : Parameters sigma)
    (role : Fin 2) (rule : Nat)
    (sound : SoundEvents
      (({ requirements := [⟨uid, address, rule, role, pack⟩], grants := [] } : Events sigma).append
        (childEvents children address 0)) scope) :
    Nonempty (EligibleOwner uid pack role scope) := by
  have offered := sound ⟨uid, address, rule, role, pack⟩
    (List.mem_append_left _ (List.mem_singleton_self _))
  rcases offered with ⟨owner, found, compatible⟩ | resolved
  · have child : owner ∈ (childEvents children address 0).grants := by
      simpa only [Events.append, List.nil_append] using found
    rcases (childEvents_vertices children address 0).2 owner child with
      ⟨index, suffix, equal, _⟩
    exact False.elim (incompatible_descendant_owner
      ⟨uid, address, rule, role, pack⟩ owner address index.val suffix rfl
      (by simpa only [Nat.zero_add] using equal) compatible)
  · exact eligible_of_scope_resolves uid pack role address rule scope resolved

mutual

/-- A kernel witness yields actual designated-owner resolution.  No local
admission assumption is needed for this direction; admission is added by the
headline theorem.  Vacant interfaces cannot supply a closed witness. -/
theorem kernel_sound : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (address : InternalAddress) →
    (scope : List (OwnerSlot sigma)) → ScopeAnchored address scope →
    ClosedKernel tree address scope → SoundEvents (events tree address) scope
  | _, .interface _, _, _, _, certificate => nomatch certificate
  | _, .ordinary o children, address, scope, anchored, certificate => by
      cases label : o.instanceData with
      | top role pack uid gamma pi =>
          simp only [ClosedKernel, Kernel, label] at certificate
          change EligibleOwner uid pack role scope ×
            ChildrenKernel children (emptyProvider (.ordinary o children)) address 0 scope
            at certificate
          apply sound_append
          · intro request present
            have equal : request = ⟨uid, address, o.id, role, pack⟩ := by
              simpa only [rootEvents, label, List.mem_singleton] using present
            subst request
            exact Or.inr (top_resolves uid pack role address o.id scope anchored certificate.1)
          · exact children_sound children address 0 scope anchored certificate.2
      | bottom pack uid conclusion =>
          simp only [ClosedKernel, Kernel, label] at certificate
          simpa only [events, rootEvents, label] using
            bottom_sound children address scope uid pack o.id anchored certificate
      | identity formula =>
          simp only [ClosedKernel, Kernel, label] at certificate
          apply sound_append
          · intro request present
            simp only [rootEvents, label, List.not_mem_nil] at present
          · exact children_sound children address 0 scope anchored certificate
      | weakening formula gamma pi =>
          simp only [ClosedKernel, Kernel, label] at certificate
          apply sound_append
          · intro request present
            simp only [rootEvents, label, List.not_mem_nil] at present
          · exact children_sound children address 0 scope anchored certificate
      | contraction formula gamma pi =>
          simp only [ClosedKernel, Kernel, label] at certificate
          apply sound_append
          · intro request present
            simp only [rootEvents, label, List.not_mem_nil] at present
          · exact children_sound children address 0 scope anchored certificate
      | implicationRight gamma antecedent consequent result =>
          simp only [ClosedKernel, Kernel, label] at certificate
          apply sound_append
          · intro request present
            simp only [rootEvents, label, List.not_mem_nil] at present
          · exact children_sound children address 0 scope anchored certificate

theorem children_sound : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → (address : InternalAddress) →
    (slot : Nat) → (scope : List (OwnerSlot sigma)) → ScopeAnchored address scope →
    ChildrenKernel children (emptyChildrenProvider children) address slot scope →
    SoundEvents (childEvents children address slot) scope
  | _, .nil, _, _, _, _, _ => by
      intro request present
      simp only [childEvents, List.not_mem_nil] at present
  | _, .cons head tail, address, slot, scope, anchored, certificate =>
      sound_append _ _ scope
        (kernel_sound head (address ++ [slot]) scope
          (anchored_child address slot scope anchored) certificate.1)
        (children_sound tail address (slot + 1) scope anchored certificate.2)

theorem bottom_sound : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → (address : InternalAddress) →
    (scope : List (OwnerSlot sigma)) → (uid : Nat) → (pack : Parameters sigma) →
    (rule : Nat) → ScopeAnchored address scope →
    BottomKernel children (emptyChildrenProvider children) uid pack address scope →
    SoundEvents
      (({ requirements := [], grants := [⟨uid, address, rule, pack⟩] } : Events sigma).append
        (childEvents children address 0)) scope
  | _, .nil, _, _, _, _, _, _, certificate => nomatch certificate
  | _, .cons _ .nil, _, _, _, _, _, _, certificate => nomatch certificate
  | _, .cons left (.cons right .nil), address, scope, uid, pack, rule, anchored,
      certificate => by
      have leftSound := kernel_sound left (address ++ [0])
        (enterOwner uid pack address 0 scope) (anchored_enter uid pack address 0 scope anchored)
        certificate.1
      have rightSound := kernel_sound right (address ++ [1])
        (enterOwner uid pack address 1 scope) (anchored_enter uid pack address 1 scope anchored)
        certificate.2
      intro request present
      change request ∈ [] ++
        ((events left (address ++ [0])).requirements ++
          ((events right (address ++ [1])).requirements ++ [])) at present
      simp only [List.nil_append, List.append_nil, List.mem_append] at present
      rcases present with present | present
      · rcases leftSound request present with ⟨owner, found, compatible⟩ | resolved
        · apply Or.inl
          refine ⟨owner, ?_, compatible⟩
          change owner ∈ [⟨uid, address, rule, pack⟩] ++
            ((events left (address ++ [0])).grants ++
              ((events right (address ++ [1])).grants ++ []))
          simp only [List.mem_append, List.mem_singleton]
          exact Or.inr (Or.inl found)
        · rcases resolve_enter request uid pack address rule 0 scope resolved with
              compatible | resolved
          · exact Or.inl ⟨_, List.mem_append_left _ (List.mem_singleton_self _), compatible⟩
          · exact Or.inr resolved
      · rcases rightSound request present with ⟨owner, found, compatible⟩ | resolved
        · apply Or.inl
          refine ⟨owner, ?_, compatible⟩
          change owner ∈ [⟨uid, address, rule, pack⟩] ++
            ((events left (address ++ [0])).grants ++
              ((events right (address ++ [1])).grants ++ []))
          simp only [List.mem_append, List.mem_singleton, List.mem_nil_iff, or_false]
          exact Or.inr (Or.inr found)
        · rcases resolve_enter request uid pack address rule 1 scope resolved with
              compatible | resolved
          · exact Or.inl ⟨_, List.mem_append_left _ (List.mem_singleton_self _), compatible⟩
          · exact Or.inr resolved
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, _, _, certificate => nomatch certificate

end

mutual
/-- A closed certificate never turns an unfilled native `Box` into a proof. -/
theorem kernel_complete : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (address : InternalAddress) →
    (scope : List (OwnerSlot sigma)) → ClosedKernel tree address scope → tree.IsComplete
  | _, .interface _, _, _, certificate => nomatch certificate
  | _, .ordinary o children, address, scope, certificate => by
      cases label : o.instanceData <;>
        simp only [ClosedKernel, Kernel, label] at certificate
      all_goals first
        | exact children_complete children address 0 scope certificate
        | exact children_complete children address 0 scope certificate.2
        | exact bottom_complete children _ _ address scope certificate

theorem children_complete : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → (address : InternalAddress) →
    (slot : Nat) → (scope : List (OwnerSlot sigma)) →
    ChildrenKernel children (emptyChildrenProvider children) address slot scope →
    children.IsComplete
  | _, .nil, _, _, _, _ => trivial
  | _, .cons head tail, address, slot, scope, certificate =>
      ⟨kernel_complete head (address ++ [slot]) scope certificate.1,
        children_complete tail address (slot + 1) scope certificate.2⟩

theorem bottom_complete : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (uid : Nat) → (pack : Parameters sigma) → (address : InternalAddress) →
    (scope : List (OwnerSlot sigma)) →
    BottomKernel children (emptyChildrenProvider children) uid pack address scope →
    children.IsComplete
  | _, .nil, _, _, _, _, certificate => nomatch certificate
  | _, .cons _ .nil, _, _, _, _, certificate => nomatch certificate
  | _, .cons left (.cons right .nil), uid, pack, address, scope, certificate =>
      ⟨kernel_complete left (address ++ [0])
          (enterOwner uid pack address 0 scope) certificate.1,
        kernel_complete right (address ++ [1])
          (enterOwner uid pack address 1 scope) certificate.2, trivial⟩
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, certificate => nomatch certificate
end

mutual

/-- Constructive scoped completeness for the independent actual-event test.
Internal descendants and sibling owners are excluded by native address
geometry; exact admission supplies the genuine bottom's binary arity. -/
theorem kernel_of_sound
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    (address : InternalAddress) → (scope : List (OwnerSlot sigma)) →
    ExactTree Imp tree → tree.IsComplete → SoundEvents (events tree address) scope →
    Nonempty (ClosedKernel tree address scope)
  | _, .interface _, _, _, _, complete, _ => False.elim complete
  | _, .ordinary o children, address, scope, exactLocal, complete, sound => by
      change ExactInstance Imp o ∧ ExactChildren Imp children at exactLocal
      change children.IsComplete at complete
      cases label : o.instanceData with
      | top role pack uid gamma pi =>
          simp only [ClosedKernel, Kernel, label]
          have rootSound : SoundEvents
              (({ requirements := [⟨uid, address, o.id, role, pack⟩], grants := [] } : Events sigma).append
                (childEvents children address 0)) scope := by
            simpa only [events, rootEvents, label] using sound
          rcases top_eligible_from_sound children address scope uid pack role o.id rootSound with
            ⟨choice⟩
          rcases children_of_sound Imp children address 0 scope exactLocal.2 complete
              (top_children_sound children address scope _ rootSound) with ⟨childCertificate⟩
          exact ⟨⟨choice, childCertificate⟩⟩
      | bottom pack uid conclusion =>
          simp only [ClosedKernel, Kernel, label]
          have localInstance := exactLocal.1
          simp only [ExactInstance, label] at localInstance
          have count : o.shape.premises.length = 2 := by
            simpa using congrArg (fun shape : OccurrenceShape sigma => shape.premises.length)
              localInstance.2.2.2
          exact bottom_of_sound Imp children address scope uid pack o.id count exactLocal.2
            complete (by simpa only [events, rootEvents, label] using sound)
      | identity formula =>
          simp only [ClosedKernel, Kernel, label]
          exact children_of_sound Imp children address 0 scope exactLocal.2 complete
            (by simpa only [events, rootEvents, label, Events.append, List.nil_append] using sound)
      | weakening formula gamma pi =>
          simp only [ClosedKernel, Kernel, label]
          exact children_of_sound Imp children address 0 scope exactLocal.2 complete
            (by simpa only [events, rootEvents, label, Events.append, List.nil_append] using sound)
      | contraction formula gamma pi =>
          simp only [ClosedKernel, Kernel, label]
          exact children_of_sound Imp children address 0 scope exactLocal.2 complete
            (by simpa only [events, rootEvents, label, Events.append, List.nil_append] using sound)
      | implicationRight gamma antecedent consequent result =>
          simp only [ClosedKernel, Kernel, label]
          exact children_of_sound Imp children address 0 scope exactLocal.2 complete
            (by simpa only [events, rootEvents, label, Events.append, List.nil_append] using sound)

theorem children_of_sound
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (address : InternalAddress) → (slot : Nat) → (scope : List (OwnerSlot sigma)) →
    ExactChildren Imp children → children.IsComplete →
    SoundEvents (childEvents children address slot) scope →
    Nonempty (ChildrenKernel children (emptyChildrenProvider children) address slot scope)
  | _, .nil, _, _, _, _, _, _ => ⟨PUnit.unit⟩
  | _, .cons head tail, address, slot, scope, exactLocal, complete, sound => by
      have split := sound_children_split head tail address slot scope sound
      rcases kernel_of_sound Imp head (address ++ [slot]) scope exactLocal.1 complete.1
          split.1 with ⟨headCertificate⟩
      rcases children_of_sound Imp tail address (slot + 1) scope exactLocal.2 complete.2
          split.2 with ⟨tailCertificate⟩
      exact ⟨⟨headCertificate, tailCertificate⟩⟩

theorem bottom_of_sound
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (address : InternalAddress) → (scope : List (OwnerSlot sigma)) →
    (uid : Nat) → (pack : Parameters sigma) → (rule : Nat) → Gs.length = 2 →
    ExactChildren Imp children → children.IsComplete →
    SoundEvents
      (({ requirements := [], grants := [⟨uid, address, rule, pack⟩] } : Events sigma).append
        (childEvents children address 0)) scope →
    Nonempty (BottomKernel children (emptyChildrenProvider children) uid pack address scope)
  | _, .nil, _, _, _, _, _, count, _, _, _ => by simp at count
  | _, .cons _ .nil, _, _, _, _, _, count, _, _, _ => by simp at count
  | _, .cons left (.cons right .nil), address, scope, uid, pack, rule, _,
      exactLocal, complete, sound => by
      have split := sound_bottom_split left right address scope uid pack rule sound
      rcases kernel_of_sound Imp left (address ++ [0]) (enterOwner uid pack address 0 scope)
          exactLocal.1 complete.1 split.1 with ⟨leftCertificate⟩
      rcases kernel_of_sound Imp right (address ++ [1]) (enterOwner uid pack address 1 scope)
          exactLocal.2.1 complete.2.1 split.2 with ⟨rightCertificate⟩
      exact ⟨⟨leftCertificate, rightCertificate⟩⟩
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, _, count, _, _, _ => by
      simp only [List.length_cons] at count
      omega

end

/-- Independently checked local schemas and unique declarations turn a closed
kernel witness into the actual tree-event legality relation.  The converse is
a separate completeness obligation, not hidden in this statement. -/
theorem closed_kernel_legal
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (certificate : ClosedKernel tree [] []) : Legal Imp tree [] [] := by
  refine ⟨exactLocal, unique, ?_⟩
  have sound := kernel_sound tree [] [] (by intro owner present; cases present) certificate
  intro request present
  rcases sound request present with ⟨owner, found, compatible⟩ | resolved
  · exact ⟨owner, by simpa using found, compatible⟩
  · rcases resolved with ⟨owner, present, _⟩
    cases present

/-- Existence agreement, not identification of a Type-valued certificate
with a Prop proof. Completeness is explicit because open Boxes are obligations
accepted by local checking, but have no closed kernel witness. -/
theorem closed_kernel_iff_legal
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (complete : tree.IsComplete) :
    Nonempty (ClosedKernel tree [] []) ↔ Legal Imp tree [] [] := by
  constructor
  · rintro ⟨certificate⟩
    exact closed_kernel_legal Imp tree exactLocal unique certificate
  · intro legal
    apply kernel_of_sound Imp tree [] [] exactLocal complete
    intro request present
    rcases legal.2.2 request present with ⟨owner, found, compatible⟩
    exact Or.inl ⟨owner, by simpa using found, compatible⟩

/-- The native cut equivalence is now interpreted by the independently
defined discharge legality relation. Detached factors are evaluated at the
actual vacancies under scopes produced by this same remainder certificate;
they are not required to be independently closed. The branch convention
includes the empty cut, ordinary proper cuts and the separate whole endpoint. -/
theorem closed_legality_cut_gluing
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (complete : tree.IsComplete) (cut : CKBranchCut tree) :
    Legal Imp tree [] [] ↔
      Nonempty (Kernel cut.remainder (branchProvider cut (emptyProvider tree)) [] []) := by
  have agreement := closed_kernel_iff_legal Imp tree exactLocal unique complete
  have gluing := branchEquiv cut (emptyProvider tree) [] []
  constructor
  · intro legal
    rcases agreement.mpr legal with ⟨certificate⟩
    exact ⟨gluing certificate⟩
  · rintro ⟨pieces⟩
    exact agreement.mp ⟨gluing.symm pieces⟩

theorem proper_cut_legality_gluing
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (exactLocal : ExactTree Imp tree) (unique : UniqueOwners (events tree []))
    (complete : tree.IsComplete) (cut : CKCut tree) :
    Legal Imp tree [] [] ↔
      Nonempty (Kernel cut.remainder (remainderProvider cut.plan (emptyProvider tree)) [] []) :=
  closed_legality_cut_gluing Imp tree exactLocal unique complete (.descend cut.plan)

#check @kernel_sound
#check @closed_kernel_legal
#check @kernel_complete
#check @closed_kernel_iff_legal
#check @closed_legality_cut_gluing
#check @proper_cut_legality_gluing
#print axioms kernel_sound
#print axioms closed_kernel_legal
#print axioms kernel_complete
#print axioms kernel_of_sound
#print axioms closed_kernel_iff_legal
#print axioms closed_legality_cut_gluing
#print axioms proper_cut_legality_gluing

end Potkin.Research.OpenDischargeAgreement

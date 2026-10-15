import Potkin.Research.D3SourceAdequacy

/-!
# Physical system occurrences in the source fragment

These are indices and geometry facts over the existing source `Diagram`, not
a new proof, context or cut syntax.  Public occurrences are the native source
event ordinals.  All declarations, including declarations discharging nothing,
and all repeated top applications remain distinct.
-/

namespace Potkin.Research.D3SystemOccurrences
open D3SourceEncoding D3SourceAdequacy

abbrev TopOccurrence {S : D3SourceEncoding.Sequent} (D : Diagram S) :=
  Fin (D3SourceAdequacy.events D []).tops.length
abbrev BottomOccurrence {S : D3SourceEncoding.Sequent} (D : Diagram S) :=
  Fin (D3SourceAdequacy.events D []).bottoms.length

def topEvent {S : D3SourceEncoding.Sequent} (D : Diagram S) (t : TopOccurrence D) : Top :=
  (D3SourceAdequacy.events D []).tops.get t
def bottomEvent {S : D3SourceEncoding.Sequent} (D : Diagram S) (b : BottomOccurrence D) : Bottom :=
  (D3SourceAdequacy.events D []).bottoms.get b
def Eligible {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (t : TopOccurrence D) (b : BottomOccurrence D) : Prop :=
  D3SourceAdequacy.Eligible (topEvent D t) (bottomEvent D b)

/-- All eligible assignments, without imposing a particular owner annotation.
The reverse physical-bottom order includes unused declarations. -/
abbrev RawGrouping {S : D3SourceEncoding.Sequent} (D : Diagram S) :=
  D3DischargeGrouping.Grouping (Eligible D)
    (List.finRange (D3SourceAdequacy.events D []).tops.length)
    (List.finRange (D3SourceAdequacy.events D []).bottoms.length).reverse

mutual
theorem events_top_address : {S : D3SourceEncoding.Sequent} → (D : Diagram S) →
    (address : InternalAddress) → (t : Top) → t ∈ (D3SourceAdequacy.events D address).tops →
      ∃ suffix, t.address = address ++ suffix
  | _, .hole _, _, _, present => by cases present
  | _, .rule key r children, address, t, present => by
      change t ∈ (D3SourceAdequacy.rootEvents address key r).tops ++
        (D3SourceAdequacy.childEvents children address 0).tops at present
      rcases List.mem_append.mp present with root | below
      · cases r <;> simp [D3SourceAdequacy.rootEvents] at root
        subst t
        exact ⟨[], by simp⟩
      · rcases child_events_top_address children address 0 t below with ⟨slot, _, suffix, h⟩
        exact ⟨[slot] ++ suffix, by simpa [List.append_assoc] using h⟩
theorem child_events_top_address : {Ss : List D3SourceEncoding.Sequent} →
    (Ds : Children Ss) → (address : InternalAddress) → (slot : Nat) → (t : Top) →
      t ∈ (D3SourceAdequacy.childEvents Ds address slot).tops →
        ∃ j, slot ≤ j ∧ ∃ suffix, t.address = address ++ [j] ++ suffix
  | _, .nil, _, _, _, present => by cases present
  | _, .cons head tail, address, slot, t, present => by
      change t ∈ (D3SourceAdequacy.events head (address ++ [slot])).tops ++
        (D3SourceAdequacy.childEvents tail address (slot + 1)).tops at present
      rcases List.mem_append.mp present with first | later
      · rcases events_top_address head (address ++ [slot]) t first with ⟨suffix, h⟩
        exact ⟨slot, le_refl _, suffix, h⟩
      · rcases child_events_top_address tail address (slot + 1) t later with ⟨j, hj, suffix, h⟩
        exact ⟨j, Nat.le_trans (Nat.le_succ _) hj, suffix, h⟩
end

mutual
theorem events_bottom_address : {S : D3SourceEncoding.Sequent} → (D : Diagram S) →
    (address : InternalAddress) → (b : Bottom) → b ∈ (D3SourceAdequacy.events D address).bottoms →
      ∃ suffix, b.address = address ++ suffix
  | _, .hole _, _, _, present => by cases present
  | _, .rule key r children, address, b, present => by
      change b ∈ (D3SourceAdequacy.rootEvents address key r).bottoms ++
        (D3SourceAdequacy.childEvents children address 0).bottoms at present
      rcases List.mem_append.mp present with root | below
      · cases r <;> simp [D3SourceAdequacy.rootEvents] at root
        subst b
        exact ⟨[], by simp⟩
      · rcases child_events_bottom_address children address 0 b below with ⟨slot, _, suffix, h⟩
        exact ⟨[slot] ++ suffix, by simpa [List.append_assoc] using h⟩
theorem child_events_bottom_address : {Ss : List D3SourceEncoding.Sequent} →
    (Ds : Children Ss) → (address : InternalAddress) → (slot : Nat) → (b : Bottom) →
      b ∈ (D3SourceAdequacy.childEvents Ds address slot).bottoms →
        ∃ j, slot ≤ j ∧ ∃ suffix, b.address = address ++ [j] ++ suffix
  | _, .nil, _, _, _, present => by cases present
  | _, .cons head tail, address, slot, b, present => by
      change b ∈ (D3SourceAdequacy.events head (address ++ [slot])).bottoms ++
        (D3SourceAdequacy.childEvents tail address (slot + 1)).bottoms at present
      rcases List.mem_append.mp present with first | later
      · rcases events_bottom_address head (address ++ [slot]) b first with ⟨suffix, h⟩
        exact ⟨slot, le_refl _, suffix, h⟩
      · rcases child_events_bottom_address tail address (slot + 1) b later with ⟨j, hj, suffix, h⟩
        exact ⟨j, Nat.le_trans (Nat.le_succ _) hj, suffix, h⟩
end

theorem eligible_address_length (t : Top) (b : Bottom)
    (eligible : D3SourceAdequacy.Eligible t b) : b.address.length < t.address.length := by
  rcases eligible.2 with ⟨suffix, h⟩
  rw [h]
  simp only [List.length_append, List.length_singleton]
  omega

theorem root_top_not_eligible_below (address : InternalAddress) (t : Top) (b : Bottom)
    (root : t.address = address) (below : ∃ suffix, b.address = address ++ suffix) :
    ¬ D3SourceAdequacy.Eligible t b := by
  intro eligible
  have h := eligible_address_length t b eligible
  rcases below with ⟨suffix, hb⟩
  rw [root, hb, List.length_append] at h
  omega

/-- Distinct ordered sibling prefixes cannot have a discharge edge between
them.  This is not a nearest-owner condition: every ancestor is still eligible. -/
theorem eligible_same_child (address : InternalAddress) (i j : Nat)
    (t : Top) (b : Bottom) (ta ba : InternalAddress)
    (ht : t.address = address ++ [i] ++ ta)
    (hb : b.address = address ++ [j] ++ ba)
    (eligible : D3SourceAdequacy.Eligible t b) : i = j := by
  rcases eligible.2 with ⟨suffix, h⟩
  rw [ht, hb] at h
  have heads : i :: ta = j :: (ba ++ [t.role.val] ++ suffix) := by
    exact List.append_cancel_left (as := address) (by simpa [List.append_assoc] using h)
  exact (List.cons.inj heads).1

/-- Geometry transport yields a literal inverse transport of EVERY assignment,
not just equivalence of existence or of a fixed owner annotation. -/
def assignmentEquiv {S T : D3SourceEncoding.Sequent} (D : Diagram S) (E : Diagram T)
    (tops : TopOccurrence D ≃ TopOccurrence E)
    (bottoms : BottomOccurrence D ≃ BottomOccurrence E)
    (geometry : ∀ t b, Eligible D t b ↔ Eligible E (tops t) (bottoms b)) :
    RawGrouping D ≃ RawGrouping E where
  toFun g := ⟨fun t => bottoms (g.assignment (tops.symm t)), by
    apply (D3DischargeGrouping.pendingConstruction_iff _ _ _ _).mpr
    intro t _
    have h := (D3DischargeGrouping.pendingConstruction_iff _ _ _ _).mp
      g.construction (tops.symm t) (by simp)
    refine ⟨by simp, ?_⟩
    simpa using (geometry (tops.symm t) (g.assignment (tops.symm t))).mp h.2⟩
  invFun g := ⟨fun t => bottoms.symm (g.assignment (tops t)), by
    apply (D3DischargeGrouping.pendingConstruction_iff _ _ _ _).mpr
    intro t _
    have h := (D3DischargeGrouping.pendingConstruction_iff _ _ _ _).mp
      g.construction (tops t) (by simp)
    refine ⟨by simp, ?_⟩
    apply (geometry t (bottoms.symm (g.assignment (tops t)))).mpr
    simpa using h.2⟩
  left_inv g := by
    cases g with | mk assignment construction =>
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv g := by
    cases g with | mk assignment construction =>
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

#check @assignmentEquiv
#print axioms events_top_address
#print axioms events_bottom_address
#print axioms eligible_same_child
#print axioms assignmentEquiv
end Potkin.Research.D3SystemOccurrences

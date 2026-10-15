import Potkin.Research.RecursiveSysComSource
import Potkin.Research.D3SystemOccurrences

/-!
# Source-only legality of recursive prepared Sys(com) phases

These results inspect the actual native source diagram independently of any
target interpretation. Fresh owner IDs are declaration identities, not rule
keys. Vacancies remain open; completeness requires actual complete fillers.
-/
namespace Potkin.Research.RecursiveSysComSource
open D3SourceEncoding D3SourceAdequacy

theorem topDiagram_correct (key uid : Nat) (role : Fin 2) (p : Parameters)
    {out : Sequent} (spec : TopSpec role p out) :
    LocallyCorrect (topDiagram key uid role p spec) := by
  apply (PreparedSysComSource.transport_correct _ _).mpr
  exact ⟨spec.single, trivial, trivial⟩

@[simp] theorem topDiagram_events (key uid : Nat) (role : Fin 2) (p : Parameters)
    {out : Sequent} (spec : TopSpec role p out) (address : InternalAddress) :
    events (topDiagram key uid role p spec) address =
      ⟨[⟨uid, address, key, role, p⟩], []⟩ := by
  rw [topDiagram, PreparedSysComSource.transport_events]
  rfl

section DecorationLaws
variable (uid : Nat) (role : Fin 2) (p : Parameters)

mutual
theorem decorate_correct : {S : Sequent} → (D : Diagram S) → (keys : D.Hole → Nat) →
    (specs : (h : D.Hole) → TopSpec role p (D.holeBoundary h)) →
    LocallyCorrect D → LocallyCorrect (decorate uid role p D keys specs)
  | _, .hole _, keys, specs, _ => topDiagram_correct _ _ _ _ _
  | _, .rule _ _ children, keys, specs, correct =>
      ⟨correct.1, decorateChildren_correct children keys specs correct.2⟩
theorem decorateChildren_correct : {Ss : List Sequent} → (Ds : Children Ss) →
    (keys : Ds.Hole → Nat) →
    (specs : (h : Ds.Hole) → TopSpec role p (Ds.holeBoundary h)) →
    ChildrenCorrect Ds → ChildrenCorrect (decorateChildren uid role p Ds keys specs)
  | _, .nil, _, _, _ => trivial
  | _, .cons head tail, keys, specs, correct =>
      ⟨decorate_correct head (fun h => keys (.inl h)) (fun h => specs (.inl h)) correct.1,
       decorateChildren_correct tail (fun h => keys (.inr h))
         (fun h => specs (.inr h)) correct.2⟩
end

mutual
theorem decorate_bottoms : {S : Sequent} → (D : Diagram S) → (keys : D.Hole → Nat) →
    (specs : (h : D.Hole) → TopSpec role p (D.holeBoundary h)) →
    (address : InternalAddress) →
    (events (decorate uid role p D keys specs) address).bottoms = (events D address).bottoms
  | _, .hole _, keys, specs, address => by simp [decorate, events]
  | _, .rule key r children, keys, specs, address => by
      change _ ++ _ = _ ++ _
      exact congrArg ((rootEvents address key r).bottoms ++ ·)
        (decorateChildren_bottoms children keys specs address 0)
theorem decorateChildren_bottoms : {Ss : List Sequent} → (Ds : Children Ss) →
    (keys : Ds.Hole → Nat) →
    (specs : (h : Ds.Hole) → TopSpec role p (Ds.holeBoundary h)) →
    (address : InternalAddress) → (slot : Nat) →
    (childEvents (decorateChildren uid role p Ds keys specs) address slot).bottoms =
      (childEvents Ds address slot).bottoms
  | _, .nil, _, _, _, _ => rfl
  | _, .cons head tail, keys, specs, address, slot => by
      change _ ++ _ = _ ++ _
      rw [decorate_bottoms, decorateChildren_bottoms]
end

/- Old physical top events are retained literally. New top events have the
new phase's exact owner, role and parameters; their rule key is not inferred. -/
mutual
theorem decorate_tops_cases : {S : Sequent} → (D : Diagram S) → (keys : D.Hole → Nat) →
    (specs : (h : D.Hole) → TopSpec role p (D.holeBoundary h)) →
    (address : InternalAddress) → (t : Top) →
    t ∈ (events (decorate uid role p D keys specs) address).tops →
      t ∈ (events D address).tops ∨
        (t.owner = uid ∧ t.role = role ∧ t.parameters = p)
  | _, .hole _, keys, specs, address, t, present => by
      simp only [decorate, topDiagram_events, List.mem_singleton] at present
      subst t
      exact .inr ⟨rfl, rfl, rfl⟩
  | _, .rule key r children, keys, specs, address, t, present => by
      change t ∈ (rootEvents address key r).tops ++ _ at present
      rcases List.mem_append.mp present with root | below
      · exact .inl (List.mem_append_left _ root)
      · rcases decorateChildren_tops_cases children keys specs address 0 t below with old | new
        · exact .inl (List.mem_append_right _ old)
        · exact .inr new
theorem decorateChildren_tops_cases : {Ss : List Sequent} → (Ds : Children Ss) →
    (keys : Ds.Hole → Nat) →
    (specs : (h : Ds.Hole) → TopSpec role p (Ds.holeBoundary h)) →
    (address : InternalAddress) → (slot : Nat) → (t : Top) →
    t ∈ (childEvents (decorateChildren uid role p Ds keys specs) address slot).tops →
      t ∈ (childEvents Ds address slot).tops ∨
        (t.owner = uid ∧ t.role = role ∧ t.parameters = p)
  | _, .nil, _, _, _, _, _, present => by cases present
  | _, .cons head tail, keys, specs, address, slot, t, present => by
      change t ∈ _ ++ _ at present
      rcases List.mem_append.mp present with first | later
      · rcases decorate_tops_cases head (fun h => keys (.inl h)) (fun h => specs (.inl h))
          (address ++ [slot]) t first with old | new
        · exact .inl (List.mem_append_left _ old)
        · exact .inr new
      · rcases decorateChildren_tops_cases tail (fun h => keys (.inr h))
          (fun h => specs (.inr h)) address (slot + 1) t later with old | new
        · exact .inl (List.mem_append_right _ old)
        · exact .inr new
end
end DecorationLaws

theorem Source.localCorrect : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (source : Source S O bounds) → LocallyCorrect source.erase
  | _, _, _, .leaf _ => trivial
  | _, _, _, .iw _ _ _ _ single body => ⟨single, body.localCorrect, trivial⟩
  | _, _, _, .phase _ _ _ _ single left right _ _ _ =>
      ⟨single, decorate_correct _ _ _ _ _ _ left.localCorrect,
        decorate_correct _ _ _ _ _ _ right.localCorrect, trivial⟩

theorem Source.bottomOwnerList : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (source : Source S O bounds) → (address : InternalAddress) →
    ((events source.erase address).bottoms.map Bottom.uid) = source.owners
  | _, _, _, .leaf _, _ => rfl
  | _, _, _, .iw key a gamma pi single body, address => by
      simpa only [Source.erase, Source.native, Native.iw, events, childEvents,
        rootEvents, append, List.nil_append, List.append_nil, Source.owners] using
        body.bottomOwnerList (address ++ [0])
  | _, _, _, .phase key uid p S single left right keys specsL specsR, address => by
      change uid :: ((_ ++ (_ ++ [])).map Bottom.uid) = uid :: (left.owners ++ right.owners)
      rw [List.append_nil, List.map_append]
      congr 1
      exact congrArg₂ (· ++ ·)
        ((congrArg (List.map Bottom.uid) (decorate_bottoms _ _ _ _ _ _ _)).trans
          (left.bottomOwnerList (address ++ [0])))
        ((congrArg (List.map Bottom.uid) (decorate_bottoms _ _ _ _ _ _ _)).trans
          (right.bottomOwnerList (address ++ [1])))

theorem Source.owners_nodup : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (source : Source S O bounds) → WellScoped source → source.owners.Nodup
  | _, _, _, .leaf _, _ => List.nodup_nil
  | _, _, _, .iw _ _ _ _ _ body, hscope => body.owners_nodup hscope
  | _, _, _, .phase _ _ _ _ _ left right _ _ _, hscope =>
      List.nodup_cons.mpr ⟨hscope.2.2.1,
        (left.owners_nodup hscope.1).append (right.owners_nodup hscope.2.1) hscope.2.2.2⟩

theorem Source.resolved : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (source : Source S O bounds) → (address : InternalAddress) → Resolved (events source.erase address)
  | _, _, _, .leaf _, _ => by intro _ present; cases present
  | _, _, _, .iw key a gamma pi single body, address => by
      simpa only [Source.erase, Source.native, Native.iw, events, childEvents, rootEvents,
        append, List.nil_append, List.append_nil] using body.resolved (address ++ [0])
  | _, _, _, .phase key uid p S single left right keys specsL specsR, address => by
      intro t present
      change t ∈ _ ++ (_ ++ []) at present
      rw [List.append_nil] at present
      rcases List.mem_append.mp present with first | second
      · rcases decorate_tops_cases uid 0 p left.native.diagram _ _ (address ++ [0]) t first with old | new
        · rcases left.resolved (address ++ [0]) t old with ⟨b, hb, eligible, owner⟩
          refine ⟨b, ?_, eligible, owner⟩
          change b ∈ _ :: (_ ++ (_ ++ []))
          apply List.mem_cons_of_mem
          apply List.mem_append_left
          dsimp only [Native.decorate]
          rw [decorate_bottoms]
          exact hb
        · rcases D3SystemOccurrences.events_top_address _ (address ++ [0]) t first with ⟨suffix, h⟩
          exact ⟨⟨uid, address, key, p⟩, by simp [Source.erase, Source.native,
            Native.bottom, events, rootEvents, append],
            ⟨new.2.2, suffix, by simpa [new.2.1] using h⟩, new.1⟩
      · rcases decorate_tops_cases uid 1 p right.native.diagram _ _ (address ++ [1]) t second with old | new
        · rcases right.resolved (address ++ [1]) t old with ⟨b, hb, eligible, owner⟩
          refine ⟨b, ?_, eligible, owner⟩
          change b ∈ _ :: (_ ++ (_ ++ []))
          apply List.mem_cons_of_mem
          apply List.mem_append_right
          apply List.mem_append_left
          dsimp only [Native.decorate]
          rw [decorate_bottoms]
          exact hb
        · rcases D3SystemOccurrences.events_top_address _ (address ++ [1]) t second with ⟨suffix, h⟩
          exact ⟨⟨uid, address, key, p⟩, by simp [Source.erase, Source.native,
            Native.bottom, events, rootEvents, append],
            ⟨new.2.2, suffix, by simpa [new.2.1] using h⟩, new.1⟩

theorem Source.correct {S O bounds} (source : Source S O bounds) (hscope : WellScoped source) :
    SourceCorrect source.erase := by
  refine ⟨source.localCorrect, ?_, (grouping_iff_resolved _).mpr (source.resolved [])⟩
  rw [source.bottomOwnerList]
  exact source.owners_nodup hscope

#print axioms Source.localCorrect
#print axioms Source.resolved
#print axioms Source.correct
end Potkin.Research.RecursiveSysComSource

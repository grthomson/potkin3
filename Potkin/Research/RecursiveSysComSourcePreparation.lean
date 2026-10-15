import Potkin.Research.RecursiveSysComSourceLaws

/-!
# Physical preparation of recursive Sys(com) phases

Root-prefix ancestry is opposite the paper's drawing convention. Preparation
is established from physical vacancies and source owner freshness, not from
the success of a target translation.
-/
namespace Potkin.Research.RecursiveSysComSource
open D3SourceEncoding D3SourceAdequacy
open PreparedSysComSource (StrictAncestor Prepared)

section DecorationOrigin
variable (uid : Nat) (role : Fin 2) (p : Parameters)
mutual
theorem decorate_top_origin : {S : Sequent} → (D : Diagram S) → (keys : D.Hole → Nat) →
    (specs : (h : D.Hole) → TopSpec role p (D.holeBoundary h)) →
    (address : InternalAddress) → (t : Top) →
    t ∈ (events (decorate uid role p D keys specs) address).tops →
      t ∈ (events D address).tops ∨
        ∃ h : D.Hole, t.owner = uid ∧ t.role = role ∧ t.parameters = p ∧
          t.address = address ++ D.holeAddress h
  | _, .hole _, keys, specs, address, t, present => by
      simp only [decorate, topDiagram_events, List.mem_singleton] at present
      subst t
      exact .inr ⟨PUnit.unit, rfl, rfl, rfl, by simp [Diagram.holeAddress]⟩
  | _, .rule key r children, keys, specs, address, t, present => by
      change t ∈ (rootEvents address key r).tops ++ _ at present
      rcases List.mem_append.mp present with root | below
      · exact .inl (List.mem_append_left _ root)
      · rcases decorateChildren_top_origin children keys specs address 0 t below with old | new
        · exact .inl (List.mem_append_right _ old)
        · rcases new with ⟨h, owner, role, params, ha⟩
          exact .inr ⟨h, owner, role, params,
            by simpa [Diagram.holeAddress, OpenDischarge.offsetFirst_zero] using ha⟩
theorem decorateChildren_top_origin : {Ss : List Sequent} → (Ds : Children Ss) →
    (keys : Ds.Hole → Nat) →
    (specs : (h : Ds.Hole) → TopSpec role p (Ds.holeBoundary h)) →
    (address : InternalAddress) → (slot : Nat) → (t : Top) →
    t ∈ (childEvents (decorateChildren uid role p Ds keys specs) address slot).tops →
      t ∈ (childEvents Ds address slot).tops ∨
        ∃ h : Ds.Hole, t.owner = uid ∧ t.role = role ∧ t.parameters = p ∧
          t.address = address ++ OpenDischarge.offsetFirst slot (Ds.holeAddress h)
  | _, .nil, _, _, _, _, _, present => by cases present
  | _, .cons head tail, keys, specs, address, slot, t, present => by
      change t ∈ _ ++ _ at present
      rcases List.mem_append.mp present with first | later
      · rcases decorate_top_origin head (fun h => keys (.inl h)) (fun h => specs (.inl h))
          (address ++ [slot]) t first with old | new
        · exact .inl (List.mem_append_left _ old)
        · rcases new with ⟨h, owner, role, params, ha⟩
          exact .inr ⟨Sum.inl h, owner, role, params,
            by simpa [Children.holeAddress, OpenDischarge.offsetFirst, List.append_assoc] using ha⟩
      · rcases decorateChildren_top_origin tail (fun h => keys (.inr h))
          (fun h => specs (.inr h)) address (slot + 1) t later with old | new
        · exact .inl (List.mem_append_right _ old)
        · rcases new with ⟨h, owner, role, params, ha⟩
          exact .inr ⟨Sum.inr h, owner, role, params,
            by simpa [Children.holeAddress, OpenDischarge.offsetFirst_shift] using ha⟩
end
end DecorationOrigin

theorem source_top_vertex {S : Sequent} (D : Diagram S) (address : InternalAddress)
    (t : Top) (present : t ∈ (events D address).tops) :
    ∃ relative, t.address = address ++ relative ∧ (encode D).VertexAt relative := by
  have native : encodeTop t ∈ (OpenDischarge.events (encode D) address).requirements := by
    rw [encode_events]
    exact List.mem_map.mpr ⟨t, present, rfl⟩
  exact DischargeScopeGeometry.events_vertices (encode D) address |>.1 (encodeTop t) native

theorem hole_not_prefix_top {S : Sequent} (D : Diagram S) (address : InternalAddress)
    (h : D.Hole) (t : Top) (present : t ∈ (events D address).tops) :
    ¬ (address ++ D.holeAddress h).IsPrefix t.address := by
  rintro ⟨suffix, equal⟩
  rcases source_top_vertex D address t present with ⟨relative, location, vertex⟩
  have cancel : D.holeAddress h ++ suffix = relative := by
    apply List.append_cancel_left (as := address)
    simpa [List.append_assoc, location] using equal
  apply OpenDischarge.hole_not_prefix_vertex (encode D) (D3SourceEncoding.holeEquiv D h) vertex
  exact ⟨suffix, by simpa [hole_address] using cancel⟩

theorem distinct_hole_addresses_not_prefix {S : Sequent} (D : Diagram S)
    (address : InternalAddress) (h k : D.Hole) (different : h ≠ k) :
    ¬ (address ++ D.holeAddress h).IsPrefix (address ++ D.holeAddress k) := by
  rintro ⟨suffix, equal⟩
  apply DischargeScopeGeometry.distinct_holes_not_prefix (encode D)
    (D3SourceEncoding.holeEquiv D h) (D3SourceEncoding.holeEquiv D k)
    (fun same => different ((D3SourceEncoding.holeEquiv D).injective same))
  refine ⟨suffix, ?_⟩
  rw [hole_address, hole_address]
  apply List.append_cancel_left (as := address)
  simpa [List.append_assoc] using equal

/-- A finite source ranking is only evidence for the paper's preparation
conditions; it is not a proof/cut/context carrier. -/
def Ranked (rank : Nat → Nat) (e : Events) : Prop :=
  ∀ t ∈ e.tops, ∀ u ∈ e.tops, StrictAncestor t.address u.address → rank u.owner < rank t.owner

theorem ranked_prepared {rank : Nat → Nat} {e : Events} (ranked : Ranked rank e) : Prepared e := by
  constructor
  · intro t ht u hu same ancestor
    have smaller := ranked t ht u hu ancestor
    simpa [same] using smaller
  · rintro ⟨t, ht, u, hu, v, hv, w, hw, tv, uw, _, tu, wv⟩
    have one := ranked t ht u hu tu
    have two := ranked w hw v hv wv
    rw [tv, uw] at one
    omega

theorem decorate_ranked (uid : Nat) (role : Fin 2) (p : Parameters)
    {S : Sequent} (D : Diagram S) (keys : D.Hole → Nat)
    (specs : (h : D.Hole) → TopSpec role p (D.holeBoundary h)) (address : InternalAddress)
    (rank : Nat → Nat) (old : Ranked rank (events D address)) (zero : rank uid = 0)
    (positive : ∀ t ∈ (events D address).tops, 0 < rank t.owner) :
    Ranked rank (events (decorate uid role p D keys specs) address) := by
  intro t ht u hu ancestor
  rcases decorate_top_origin uid role p D keys specs address t ht with ht | ⟨h, th, _, _, ta⟩
  · rcases decorate_top_origin uid role p D keys specs address u hu with hu | ⟨k, uk, _, _, ua⟩
    · exact old t ht u hu ancestor
    · simpa [uk, zero] using positive t ht
  · rcases decorate_top_origin uid role p D keys specs address u hu with hu | ⟨k, uk, _, _, ua⟩
    · exact False.elim (hole_not_prefix_top D address h u hu (ta ▸ ancestor.2))
    · by_cases same : h = k
      · subst k
        exact False.elim (ancestor.1 (ta.trans ua.symm))
      · exact False.elim (distinct_hole_addresses_not_prefix D address h k same
          (by simpa [ta, ua] using ancestor.2))

def phaseRank (uid : Nat) (leftOwners : List Nat) (left right : Nat → Nat) (owner : Nat) : Nat :=
  if owner = uid then 0 else if owner ∈ leftOwners then left owner + 1 else right owner + 1

theorem phaseRank_left {uid owner : Nat} {leftOwners rightOwners : List Nat}
    (left right : Nat → Nat) (fresh : uid ∉ leftOwners ++ rightOwners)
    (present : owner ∈ leftOwners) :
    phaseRank uid leftOwners left right owner = left owner + 1 := by
  have different : owner ≠ uid := by
    intro same
    exact fresh (List.mem_append_left _ (same ▸ present))
  simp [phaseRank, different, present]

theorem phaseRank_right {uid owner : Nat} {leftOwners rightOwners : List Nat}
    (left right : Nat → Nat) (fresh : uid ∉ leftOwners ++ rightOwners)
    (disjoint : List.Disjoint leftOwners rightOwners) (present : owner ∈ rightOwners) :
    phaseRank uid leftOwners left right owner = right owner + 1 := by
  have different : owner ≠ uid := by
    intro same
    exact fresh (List.mem_append_right _ (same ▸ present))
  have absent : owner ∉ leftOwners := fun old => disjoint old present
  simp [phaseRank, different, absent]

def Source.rank : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → Nat → Nat
  | _, _, _, .leaf _ => fun _ => 0
  | _, _, _, .iw _ _ _ _ _ body => body.rank
  | _, _, _, .phase _ uid _ _ _ left right _ _ _ =>
      phaseRank uid left.owners left.rank right.rank

theorem Source.topOwner_mem : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (source : Source S O bounds) → (address : InternalAddress) →
    (t : Top) → t ∈ (events source.erase address).tops → t.owner ∈ source.owners
  | _, _, _, .leaf _, _, _, present => by cases present
  | _, _, _, .iw key a gamma pi single body, address, t, present => by
      apply body.topOwner_mem (address ++ [0]) t
      simpa only [Source.erase, Source.native, Native.iw, events, childEvents,
        rootEvents, append, List.nil_append, List.append_nil] using present
  | _, _, _, .phase key uid p S single left right keys specsL specsR, address, t, present => by
      change t ∈ _ ++ (_ ++ []) at present
      rw [List.append_nil] at present
      rcases List.mem_append.mp present with first | second
      · rcases decorate_tops_cases uid 0 p left.native.diagram _ _ (address ++ [0]) t first with old | new
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (left.topOwner_mem _ t old))
        · exact new.1.symm ▸ List.mem_cons_self
      · rcases decorate_tops_cases uid 1 p right.native.diagram _ _ (address ++ [1]) t second with old | new
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (right.topOwner_mem _ t old))
        · exact new.1.symm ▸ List.mem_cons_self

theorem separate_premise_tops {S T : Sequent} (D : Diagram S) (E : Diagram T)
    (address : InternalAddress) (i j : Nat) (different : i ≠ j)
    (t : Top) (ht : t ∈ (events D (address ++ [i])).tops)
    (u : Top) (hu : u ∈ (events E (address ++ [j])).tops) :
    ¬ t.address.IsPrefix u.address := by
  rintro ⟨suffix, equal⟩
  rcases D3SystemOccurrences.events_top_address D _ t ht with ⟨left, tl⟩
  rcases D3SystemOccurrences.events_top_address E _ u hu with ⟨right, ur⟩
  have tails : i :: (left ++ suffix) = j :: right := by
    apply List.append_cancel_left (as := address)
    simpa [tl, ur, List.append_assoc] using equal
  exact different (List.cons.inj tails).1

theorem Source.ranked : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (source : Source S O bounds) → WellScoped source →
    (address : InternalAddress) → Ranked source.rank (events source.erase address)
  | _, _, _, .leaf _, _, _ => by intro _ present; cases present
  | _, _, _, .iw key a gamma pi single body, hscope, address => by
      simpa only [Source.erase, Source.native, Native.iw, events, childEvents,
        rootEvents, append, List.nil_append, List.append_nil, Source.rank] using
        body.ranked hscope (address ++ [0])
  | _, _, _, .phase key uid p S single left right keys specsL specsR, hscope, address => by
      let rank := phaseRank uid left.owners left.rank right.rank
      have leftRank : ∀ t ∈ (events left.erase (address ++ [0])).tops,
          rank t.owner = left.rank t.owner + 1 := by
        intro t ht
        exact phaseRank_left _ _ hscope.2.2.1 (left.topOwner_mem _ t ht)
      have rightRank : ∀ t ∈ (events right.erase (address ++ [1])).tops,
          rank t.owner = right.rank t.owner + 1 := by
        intro t ht
        exact phaseRank_right _ _ hscope.2.2.1 hscope.2.2.2 (right.topOwner_mem _ t ht)
      have leftOld : Ranked rank (events left.erase (address ++ [0])) := by
        intro t ht u hu ancestor
        rw [leftRank t ht, leftRank u hu]
        exact Nat.add_lt_add_right (left.ranked hscope.1 _ t ht u hu ancestor) 1
      have rightOld : Ranked rank (events right.erase (address ++ [1])) := by
        intro t ht u hu ancestor
        rw [rightRank t ht, rightRank u hu]
        exact Nat.add_lt_add_right (right.ranked hscope.2.1 _ t ht u hu ancestor) 1
      have leftNew : Ranked rank (events
          (left.native.decorate uid 0 p (fun o => keys (.inl o)) specsL).diagram
          (address ++ [0])) := by
        apply decorate_ranked uid 0 p left.native.diagram _ _ _ rank leftOld
        · simp [rank, phaseRank]
        · intro t ht
          rw [leftRank t ht]
          omega
      have rightNew : Ranked rank (events
          (right.native.decorate uid 1 p (fun o => keys (.inr o)) specsR).diagram
          (address ++ [1])) := by
        apply decorate_ranked uid 1 p right.native.diagram _ _ _ rank rightOld
        · simp [rank, phaseRank]
        · intro t ht
          rw [rightRank t ht]
          omega
      intro t ht u hu ancestor
      change t ∈ _ ++ (_ ++ []) at ht
      change u ∈ _ ++ (_ ++ []) at hu
      rw [List.append_nil] at ht hu
      rcases List.mem_append.mp ht with tl | tr
      · rcases List.mem_append.mp hu with ul | ur
        · exact leftNew t tl u ul ancestor
        · exact False.elim (separate_premise_tops _ _ address 0 1 (by decide) t tl u ur ancestor.2)
      · rcases List.mem_append.mp hu with ul | ur
        · exact False.elim (separate_premise_tops _ _ address 1 0 (by decide) t tr u ul ancestor.2)
        · exact rightNew t tr u ur ancestor

theorem Source.prepared {S O bounds} (source : Source S O bounds) (hscope : WellScoped source)
    (address : InternalAddress := []) : Prepared (events source.erase address) :=
  ranked_prepared (source.ranked hscope address)

#print axioms decorate_top_origin
#print axioms Source.prepared
end Potkin.Research.RecursiveSysComSource

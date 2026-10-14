import Potkin.Research.OpenDischargeComposition
import Potkin.Research.DischargeSummaryCongruence

/-!
# Exact simultaneous composition of native discharge summaries

All sums below are finite multisets of metadata over existing native physical
holes and rule occurrences. They are not a proof, cut, context or forest
carrier. In particular repeated owner/role rows are never deduplicated.
-/

namespace Potkin.Research.OpenDischarge

open Potkin.Research.DischargeScopeGeometry

universe u v w
variable {sigma : Signature.{u, v}}

def prefixExposure (path : InternalAddress) (e : Exposure sigma) : Exposure sigma :=
  {e with hole := path ++ e.hole}

def prefixHole (path : InternalAddress) (h : Hole sigma) : Hole sigma :=
  {h with address := path ++ h.address}

noncomputable def exposureCell (address : InternalAddress) (g : Grant sigma) :
    Multiset (Exposure sigma) := by
  classical
  exact (([0, 1] : List (Fin 2)) : Multiset (Fin 2)).bind fun role =>
    if ∃ suffix, address = g.address ++ [role.val] ++ suffix then
      {⟨address, g.uid, g.parameters, role⟩} else 0

noncomputable def exposureBag (holes : Multiset (Hole sigma))
    (grants : Multiset (Grant sigma)) : Multiset (Exposure sigma) :=
  holes.bind fun h => grants.bind fun g => exposureCell h.address g

private theorem filterMap_if_bag {alpha : Type u} {beta : Type v}
    (items : List alpha) (P : alpha → Prop) (f : alpha → beta) [DecidablePred P] :
    (items.filterMap (fun a => if P a then some (f a) else none) : Multiset beta) =
      (items : Multiset alpha).bind (fun a => if P a then {f a} else 0) := by
  induction items with
  | nil => simp
  | cons a tail ih =>
      by_cases present : P a <;> simp [List.filterMap, present, ih, ← Multiset.cons_coe]

theorem exposureRows_asBag (holes : List (Hole sigma)) (grants : List (Grant sigma)) :
    (exposureRows holes grants : Multiset (Exposure sigma)) =
      exposureBag holes grants := by
  classical
  unfold exposureRows exposureBag
  rw [← Multiset.coe_bind]
  apply Multiset.bind_congr
  intro hole present
  rw [← Multiset.coe_bind]
  apply Multiset.bind_congr
  intro grant present
  exact filterMap_if_bag ([0, 1] : List (Fin 2))
    (fun role : Fin 2 => ∃ suffix, hole.address = grant.address ++ [role.val] ++ suffix)
    (fun role => (⟨hole.address, grant.uid, grant.parameters, role⟩ : Exposure sigma))

theorem cell_prefix (path address : InternalAddress) (g : Grant sigma) :
    exposureCell (path ++ address) (prefixGrant path g) =
      (exposureCell address g).map (prefixExposure path) := by
  classical
  simp only [exposureCell, Multiset.map_bind]
  apply Multiset.bind_congr
  intro role present
  have condition :
      (∃ suffix, path ++ address = (prefixGrant path g).address ++ [role.val] ++ suffix) ↔
      ∃ suffix, address = g.address ++ [role.val] ++ suffix := by
    constructor
    · rintro ⟨suffix, equal⟩
      exact ⟨suffix, List.append_cancel_left (as := path)
        (by simpa [prefixGrant, List.append_assoc] using equal)⟩
    · rintro ⟨suffix, equal⟩
      exact ⟨suffix, by simpa [prefixGrant, List.append_assoc] using
        (congrArg (List.append path) equal)⟩
  rw [propext condition]
  split_ifs <;> simp [prefixExposure, prefixGrant]

theorem exposureBag_prefix (path : InternalAddress) (holes : Multiset (Hole sigma))
    (grants : Multiset (Grant sigma)) :
    exposureBag (holes.map (prefixHole path)) (grants.map (prefixGrant path)) =
      (exposureBag holes grants).map (prefixExposure path) := by
  simp only [exposureBag, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr
  intro hole present
  apply Multiset.bind_congr
  intro grant present
  exact cell_prefix path hole.address grant

theorem exposure_at (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) :
    (directSummary Imp tree address).exposure =
      (directSummary Imp tree []).exposure.map (prefixExposure address) := by
  change (exposureRows (holeRows tree address) (events tree address).grants :
    Multiset (Exposure sigma)) = _
  rw [exposureRows_asBag, events_at]
  have holes : (holeRows tree address : Multiset (Hole sigma)) =
      (holeRows tree [] : Multiset (Hole sigma)).map (prefixHole address) := by
    simp [holeRows, Multiset.map_coe, List.map_map, Function.comp_def, prefixHole]
  rw [holes]
  change exposureBag _ (((events tree []).grants : Multiset (Grant sigma)).map
    (prefixGrant address)) = _
  rw [exposureBag_prefix]
  congr 1
  exact (exposureRows_asBag _ _).symm

private theorem bind_single_index {alpha : Type u} {beta : Type v}
    (items : Multiset alpha) (unique : items.Nodup) (a : alpha) (present : a ∈ items)
    (f : alpha → Multiset beta)
    (others : ∀ b ∈ items, b ≠ a → f b = 0) : items.bind f = f a := by
  induction items using Multiset.induction_on with
  | empty => cases present
  | @cons head tail ih =>
      rcases Multiset.nodup_cons.mp unique with ⟨outside, tailUnique⟩
      by_cases same : head = a
      · subst head
        have vanished : tail.bind f = 0 := by
          calc
            tail.bind f = tail.bind (fun _ => 0) := by
              apply Multiset.bind_congr
              intro b hb
              exact others b (Multiset.mem_cons_of_mem hb) (fun equal => outside (equal ▸ hb))
            _ = 0 := by simp
        simp [vanished]
      · have inTail : a ∈ tail := (Multiset.mem_cons.mp present).resolve_left
          (fun equal => same equal.symm)
        have headZero := others head (by simp) same
        rw [Multiset.cons_bind, headZero, zero_add]
        exact ih tailUnique inTail (fun b hb different =>
          others b (Multiset.mem_cons_of_mem hb) different)

theorem cell_filter_address (address selected : InternalAddress) (g : Grant sigma) :
    (exposureCell address g).filter (fun e => e.hole = selected) =
      if address = selected then exposureCell address g else 0 := by
  classical
  by_cases same : address = selected
  · subst selected
    rw [if_pos rfl]
    simp only [exposureCell, Multiset.filter_bind]
    apply Multiset.bind_congr
    intro role present
    split_ifs <;> simp
  · simp only [exposureCell, Multiset.filter_bind, if_neg same]
    calc
      _ = (([0, 1] : List (Fin 2)) : Multiset (Fin 2)).bind (fun _ => 0) := by
        apply Multiset.bind_congr
        intro role present
        split_ifs <;> simp [same]
      _ = 0 := by simp

theorem cell_under_native_hole {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (hole : tree.LeafOccurrence)
    (payload address : InternalAddress) (g : Grant sigma)
    (ownerPresent : g ∈ (events tree address).grants) :
    exposureCell ((address ++ tree.leafAddress hole) ++ payload) g =
      (exposureCell (address ++ tree.leafAddress hole) g).map
        (fun e => {e with hole := (address ++ tree.leafAddress hole) ++ payload}) := by
  classical
  rw [events_at] at ownerPresent
  rcases List.mem_map.mp ownerPresent with ⟨original, originalPresent, same⟩
  subst g
  simp only [exposureCell, Multiset.map_bind]
  apply Multiset.bind_congr
  intro role present
  have condition :
      (∃ suffix, (address ++ tree.leafAddress hole) ++ payload =
        (prefixGrant address original).address ++ [role.val] ++ suffix) ↔
      ∃ suffix, address ++ tree.leafAddress hole =
        (prefixGrant address original).address ++ [role.val] ++ suffix := by
    let request : Requirement sigma := ⟨original.uid, payload, 0, role, original.parameters⟩
    constructor
    · rintro ⟨suffix, equal⟩
      have routedLocal : Compatible (prefixRequirement (tree.leafAddress hole) request) original :=
        ⟨rfl, rfl, suffix, List.append_cancel_left (as := address)
          (by simpa [request, prefixRequirement, prefixGrant, List.append_assoc] using equal)⟩
      rcases (compatible_through_hole tree hole request original originalPresent).mp routedLocal with
        ⟨_, _, suffix, path⟩
      exact ⟨suffix, by simpa [prefixGrant, List.append_assoc] using
        (congrArg (List.append address) path.symm)⟩
    · rintro ⟨suffix, equal⟩
      have path : AddressPrefix (original.address ++ [role.val]) (tree.leafAddress hole) :=
        ⟨suffix, (List.append_cancel_left (as := address)
          (by simpa [prefixGrant, List.append_assoc] using equal)).symm⟩
      rcases (compatible_through_hole tree hole request original originalPresent).mpr
        ⟨rfl, rfl, path⟩ with ⟨_, _, suffix, routed⟩
      exact ⟨suffix, by simpa [request, prefixRequirement, prefixGrant, List.append_assoc] using
        (congrArg (List.append address) routed)⟩
  rw [propext condition]
  split_ifs <;> simp

theorem cell_cross_holes {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (left right : tree.LeafOccurrence)
    (different : left ≠ right) (payload address : InternalAddress) (g : Grant sigma) :
    exposureCell ((address ++ tree.leafAddress left) ++ payload)
      (prefixGrant (address ++ tree.leafAddress right) g) = 0 := by
  classical
  unfold exposureCell
  calc
    _ = (([0, 1] : List (Fin 2)) : Multiset (Fin 2)).bind (fun _ => 0) := by
      apply Multiset.bind_congr
      intro role present
      have blocked : ¬ ∃ suffix, (address ++ tree.leafAddress left) ++ payload =
          (prefixGrant (address ++ tree.leafAddress right) g).address ++ [role.val] ++ suffix := by
        rintro ⟨suffix, equal⟩
        let request : Requirement sigma := ⟨g.uid, payload, 0, role, g.parameters⟩
        apply incompatible_different_hole_fillings tree left right different request g
        refine ⟨rfl, rfl, suffix, ?_⟩
        apply List.append_cancel_left (as := address)
        simpa [request, prefixRequirement, prefixGrant, List.append_assoc] using equal
      rw [if_neg blocked]
    _ = 0 := by simp

mutual
theorem attached_grants_bind : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (assignment : tree.LeafAssignment) →
    (address : InternalAddress) →
    attachedGrants tree assignment address = (tree.leafOrder : Multiset _).bind
      (fun hole => ((events (assignment hole) (address ++ tree.leafAddress hole)).grants :
        Multiset (Grant sigma)))
  | _, .interface _, _, _ => by
      simp [attachedGrants, CKTree.leafOrder, CKTree.leafAddress]
  | _, .ordinary _ children, assignment, address => by
      simpa [attachedGrants, CKTree.leafOrder, CKTree.leafAddress, offsetFirst_zero] using
        attached_child_grants_bind children assignment address 0

theorem attached_child_grants_bind : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) → (address : InternalAddress) → (slot : Nat) →
    attachedChildGrants children assignment address slot = (children.leafOrder : Multiset _).bind
      (fun hole => ((events (assignment hole)
        (address ++ offsetFirst slot (children.leafAddress hole))).grants : Multiset (Grant sigma)))
  | _, .nil, _, _, _ => by simp [attachedChildGrants, CKChildren.leafOrder]
  | _, .cons head tail, assignment, address, slot => by
      rw [attachedChildGrants, attached_grants_bind, attached_child_grants_bind]
      change _ = ((head.leafOrder.map Sum.inl ++ tail.leafOrder.map Sum.inr :
        List (head.LeafOccurrence ⊕ tail.LeafOccurrence)) :
          Multiset (head.LeafOccurrence ⊕ tail.LeafOccurrence)).bind
          (fun hole => ((events (assignment hole)
            (address ++ offsetFirst slot ((CKChildren.cons head tail).leafAddress hole))).grants :
              Multiset (Grant sigma)))
      rw [← Multiset.coe_add, ← Multiset.map_coe, ← Multiset.map_coe,
        Multiset.add_bind, Multiset.bind_map, Multiset.bind_map]
      congr 1
      · apply Multiset.bind_congr
        intro hole present
        simp [CKChildren.leafAddress, offsetFirst, List.append_assoc]
        exact List.Perm.refl _
      · apply Multiset.bind_congr
        intro hole present
        simp [CKChildren.leafAddress, offsetFirst_shift]
        exact List.Perm.refl _
end

theorem filled_holes_bind
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    (holeRows (tree.fillAssignment assignment) address : Multiset (Hole sigma)) =
      (tree.leafOrder : Multiset _).bind (fun hole =>
        (holeRows (assignment hole) (address ++ tree.leafAddress hole) : Multiset (Hole sigma))) := by
  have ordered := filled_hole_rows Imp tree assignment address
  rw [attachedSummaries_eq_map, List.flatMap_map] at ordered
  change (holeRows (tree.fillAssignment assignment) address : Multiset (Hole sigma)) = _
  rw [ordered, ← Multiset.coe_bind]
  rfl

theorem exposure_native_bind
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) :
    (directSummary Imp tree address).exposure =
      (tree.leafOrder : Multiset _).bind fun hole =>
        ((events tree address).grants : Multiset (Grant sigma)).bind fun grant =>
          exposureCell (address ++ tree.leafAddress hole) grant := by
  change (exposureRows (holeRows tree address) (events tree address).grants :
    Multiset (Exposure sigma)) = _
  rw [exposureRows_asBag]
  unfold exposureBag holeRows
  rw [← Multiset.map_coe, Multiset.bind_map]

theorem exposure_filter_native_hole
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (hole : tree.LeafOccurrence) (address : InternalAddress) :
    (directSummary Imp tree address).exposure.filter
        (fun e => e.hole = address ++ tree.leafAddress hole) =
      ((events tree address).grants : Multiset (Grant sigma)).bind
        (exposureCell (address ++ tree.leafAddress hole)) := by
  classical
  rw [exposure_native_bind, Multiset.filter_bind]
  let f : tree.LeafOccurrence → Multiset (Exposure sigma) := fun other =>
    (((events tree address).grants : Multiset (Grant sigma)).bind
      (exposureCell (address ++ tree.leafAddress other))).filter
        (fun e => e.hole = address ++ tree.leafAddress hole)
  change (tree.leafOrder : Multiset _).bind f = _
  have only : (tree.leafOrder : Multiset _).bind f = f hole := by
    apply bind_single_index _ (Multiset.coe_nodup.mpr tree.leafOrder_nodup)
      hole (tree.leaf_mem_leafOrder hole)
    intro other present different
    have addresses : address ++ tree.leafAddress other ≠ address ++ tree.leafAddress hole := by
      intro same
      exact different (tree.leafAddress_injective (List.append_cancel_left same))
    simp only [f, Multiset.filter_bind, cell_filter_address, if_neg addresses]
    simp
  rw [only]
  simp [f, Multiset.filter_bind, cell_filter_address]

theorem inheritedExposure_bind (parent : Summary sigma) (input : Attachment sigma) :
    inheritedExposure parent input = (input.2.holes : Multiset (Hole sigma)).bind
      (fun hole => (parent.exposure.filter (fun e => e.hole = input.1.address)).map
        (fun e => {e with hole := hole.address})) := by
  classical
  unfold inheritedExposure
  induction input.2.holes with
  | nil => simp
  | cons head tail ih => simp only [List.foldr_cons, ← Multiset.cons_coe, Multiset.cons_bind, ih]

theorem inherited_exposure_native
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (hole : tree.LeafOccurrence)
    (address : InternalAddress) :
    inheritedExposure (directSummary Imp tree address)
        (⟨address ++ tree.leafAddress hole, tree.leafBoundary hole⟩,
          directSummary Imp (assignment hole) (address ++ tree.leafAddress hole)) =
      (holeRows (assignment hole) (address ++ tree.leafAddress hole) : Multiset (Hole sigma)).bind
        (fun newHole => ((events tree address).grants : Multiset (Grant sigma)).bind
          (exposureCell newHole.address)) := by
  rw [inheritedExposure_bind, exposure_filter_native_hole]
  change (holeRows (assignment hole) (address ++ tree.leafAddress hole) :
    Multiset (Hole sigma)).bind _ = _
  apply Multiset.bind_congr
  intro newHole present
  rcases List.mem_map.mp present with ⟨inner, innerPresent, same⟩
  subst newHole
  rw [Multiset.map_bind]
  apply Multiset.bind_congr
  intro grant ownerPresent
  exact (cell_under_native_hole tree hole ((assignment hole).leafAddress inner)
    address grant ownerPresent).symm

theorem attached_cells_at_hole
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (hole : tree.LeafOccurrence)
    (payload address : InternalAddress) :
    (attachedGrants tree assignment address).bind
      (exposureCell ((address ++ tree.leafAddress hole) ++ payload)) =
      ((events (assignment hole) (address ++ tree.leafAddress hole)).grants :
        Multiset (Grant sigma)).bind
          (exposureCell ((address ++ tree.leafAddress hole) ++ payload)) := by
  rw [attached_grants_bind, Multiset.bind_assoc]
  apply bind_single_index _ (Multiset.coe_nodup.mpr tree.leafOrder_nodup)
    hole (tree.leaf_mem_leafOrder hole)
  intro other present different
  calc
    _ = (((events (assignment other) (address ++ tree.leafAddress other)).grants :
        Multiset (Grant sigma))).bind (fun _ => 0) := by
      apply Multiset.bind_congr
      intro g ownerPresent
      change g ∈ (events (assignment other) (address ++ tree.leafAddress other)).grants at ownerPresent
      rw [events_at] at ownerPresent
      rcases List.mem_map.mp ownerPresent with ⟨original, originalPresent, same⟩
      subst g
      exact cell_cross_holes tree hole other different.symm payload address original
    _ = 0 := by simp

theorem compose_exposure_bind (parent : Summary sigma) (inputs : List (Attachment sigma)) :
    (composeSummary parent inputs).exposure = (inputs : Multiset (Attachment sigma)).bind
      (fun input => input.2.exposure + inheritedExposure parent input) := by
  change inputs.foldr _ 0 = _
  induction inputs with
  | nil => simp
  | cons head tail ih => simp only [List.foldr_cons, ← Multiset.cons_coe, Multiset.cons_bind, ih]

/-- Exact exposure multiplicity under simultaneous native filling, including
equal owner/role rows and arbitrary malformed or ill-scoped rule data. -/
theorem exposure_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    (directSummary Imp (tree.fillAssignment assignment) address).exposure =
      (composeSummary (directSummary Imp tree address)
        (attachedSummaries Imp tree assignment address)).exposure := by
  change (exposureRows (holeRows (tree.fillAssignment assignment) address)
    (events (tree.fillAssignment assignment) address).grants : Multiset (Exposure sigma)) = _
  rw [exposureRows_asBag, exposureBag, filled_holes_bind Imp,
    (events_fill tree assignment address).2, Multiset.bind_assoc,
    compose_exposure_bind, attachedSummaries_eq_map, ← Multiset.map_coe,
    Multiset.bind_map]
  apply Multiset.bind_congr
  intro hole holePresent
  simp only [Multiset.add_bind, Multiset.bind_add]
  rw [← inherited_exposure_native Imp tree assignment hole address]
  have own : (holeRows (assignment hole) (address ++ tree.leafAddress hole) :
      Multiset (Hole sigma)).bind
      (fun newHole => (attachedGrants tree assignment address).bind (exposureCell newHole.address)) =
      (directSummary Imp (assignment hole) (address ++ tree.leafAddress hole)).exposure := by
    change _ = (exposureRows (holeRows (assignment hole) (address ++ tree.leafAddress hole))
      (events (assignment hole) (address ++ tree.leafAddress hole)).grants :
        Multiset (Exposure sigma))
    rw [exposureRows_asBag]
    apply Multiset.bind_congr
    intro newHole present
    rcases List.mem_map.mp present with ⟨inner, innerPresent, same⟩
    subst newHole
    exact attached_cells_at_hole tree assignment hole ((assignment hole).leafAddress inner) address
  rw [own]
  exact Multiset.add_comm _ _

theorem exposureAt_prefix_map (exposures : Multiset (Exposure sigma))
    (pathPrefix address : InternalAddress) :
    ((exposures.map (prefixExposure pathPrefix)).filter
      (fun e => e.hole = pathPrefix ++ address)).map eraseExposure =
      (exposures.filter (fun e => e.hole = address)).map eraseExposure := by
  classical
  rw [Multiset.filter_map]
  simp only [Function.comp_def]
  have filtered : exposures.filter (fun e => (prefixExposure pathPrefix e).hole = pathPrefix ++ address) =
      exposures.filter (fun e => e.hole = address) := by
    apply Multiset.filter_congr
    intro e present
    change (pathPrefix ++ e.hole = pathPrefix ++ address) ↔ e.hole = address
    exact ⟨List.append_cancel_left, fun equal => congrArg (List.append pathPrefix) equal⟩
  rw [filtered, Multiset.map_map]
  congr 1

theorem exposureAt_at (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (pathPrefix address : InternalAddress) :
    exposureAt (directSummary Imp tree pathPrefix) (pathPrefix ++ address) =
      exposureAt (directSummary Imp tree []) address := by
  classical
  unfold exposureAt
  rw [exposure_at]
  exact exposureAt_prefix_map _ pathPrefix address

theorem summaryRootAgreement_at
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (sourceAddress targetAddress : InternalAddress) :
    RootAgreement (directSummary Imp tree sourceAddress)
      (directSummary Imp tree targetAddress) := by
  refine ⟨rfl, (inventory_at Imp tree sourceAddress).trans
    (inventory_at Imp tree targetAddress).symm, ?_,
    (ok_at_iff Imp tree sourceAddress).trans (ok_at_iff Imp tree targetAddress).symm⟩
  rw [requirements_at Imp tree sourceAddress, requirements_at Imp tree targetAddress,
    Multiset.map_map, Multiset.map_map]
  congr 1

theorem attachments_at_agreement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    List.Forall₂ (AttachmentAgreement (directSummary Imp tree address) (directSummary Imp tree []))
      (attachedSummaries Imp tree assignment address) (attachedSummaries Imp tree assignment []) := by
  rw [attachedSummaries_eq_map, attachedSummaries_eq_map]
  simp only [List.nil_append]
  induction tree.leafOrder with
  | nil => exact .nil
  | cons hole tail ih =>
      apply List.Forall₂.cons _ ih
      exact ⟨rfl, summaryRootAgreement_at Imp (assignment hole)
        (address ++ tree.leafAddress hole) (tree.leafAddress hole),
        exposureAt_at Imp tree address (tree.leafAddress hole)⟩

/-- Full failure-flag reflection at every actual absolute address. This
does not assume input legality, freshness, or successful local checking. -/
theorem ok_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    (directSummary Imp (tree.fillAssignment assignment) address).ok ↔
      (composeSummary (directSummary Imp tree address)
        (attachedSummaries Imp tree assignment address)).ok := by
  have agree := compose_rootAgreement (summaryRootAgreement_at Imp tree address [])
    (attachments_at_agreement Imp tree assignment address)
    (attachment_holes Imp tree assignment address) (attachment_holes Imp tree assignment [])
  exact (ok_at_iff Imp (tree.fillAssignment assignment) address).trans
    ((ok_fill_root Imp tree assignment).trans agree.ok.symm)

theorem summary_fields_ext {source target : Summary sigma}
    (conclusion : source.conclusion = target.conclusion)
    (holes : source.holes = target.holes)
    (inventory : source.inventory = target.inventory)
    (requirements : source.requirements = target.requirements)
    (exposure : source.exposure = target.exposure) (ok : source.ok ↔ target.ok) :
    source = target := by
  cases source
  cases target
  simp only at conclusion holes inventory requirements exposure ok
  subst_vars
  cases propext ok
  rfl

/-- Exact full finite-summary composition for arbitrary native typed
simultaneous fillings, including failure flags and every exposure copy. -/
theorem directSummary_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) (address : InternalAddress) :
    directSummary Imp (tree.fillAssignment assignment) address =
      composeSummary (directSummary Imp tree address)
        (attachedSummaries Imp tree assignment address) := by
  apply summary_fields_ext
  · exact conclusion_fill _ _ _ _
  · exact holes_fill _ _ _ _
  · exact inventory_fill _ _ _ _
  · exact requirements_fill _ _ _ _
  · exact exposure_fill _ _ _ _
  · exact ok_fill _ _ _ _

/-- Associativity on realizable summaries, under the existing canonical
physical-hole and boundary reindexing of simultaneous native filling.
No law on arbitrary unrealizable summary records is asserted. -/
theorem composeSummary_realizable_assoc
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (first : tree.LeafAssignment)
    (second : (tree.fillAssignment first).LeafAssignment) (address : InternalAddress) :
    composeSummary
      (composeSummary (directSummary Imp tree address) (attachedSummaries Imp tree first address))
      (attachedSummaries Imp (tree.fillAssignment first) second address) =
        composeSummary (directSummary Imp tree address)
          (attachedSummaries Imp tree (tree.composeLeafAssignment first second) address) := by
  calc
    _ = directSummary Imp ((tree.fillAssignment first).fillAssignment second) address := by
      rw [← directSummary_fill]
      exact (directSummary_fill Imp (tree.fillAssignment first) second address).symm
    _ = directSummary Imp (tree.fillAssignment (tree.composeLeafAssignment first second)) address :=
      congrArg (fun t => directSummary Imp t address) (tree.fillAssignment_assoc first second)
    _ = _ := directSummary_fill Imp tree (tree.composeLeafAssignment first second) address

#check @exposure_fill
#check @ok_fill
#check @directSummary_fill
#check @composeSummary_realizable_assoc
#print axioms exposure_fill
#print axioms exposure_at
#print axioms ok_fill
#print axioms directSummary_fill
#print axioms composeSummary_realizable_assoc

end Potkin.Research.OpenDischarge

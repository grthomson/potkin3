import Potkin.Research.OpenDischargeComposition

/-!
# Fixed-owner congruence of compact discharge summaries

These relations compare metadata of the existing native trees.  They are not
proof, context, cut, or forest carriers.  The rooted observer forgets only the
local suffix of a pending top's physical address; owner IDs, exact top-rule
IDs, parameters, ordered roles and multiplicities remain.  Actual addresses
and physical-hole matching are retained separately by the native adapters.

Composition preserves this observer whenever each pair of physical attachment
sites has the same typed boundary and normalized parent exposure.  No freshness
or successful-input premise is imposed: equal combined inventories reject the
same declaration collisions, and all cached failure flags are retained.
-/

namespace Potkin.Research.OpenDischarge

universe u v
variable {sigma : Signature.{u, v}}

def eraseRequirement (r : Requirement sigma) : Requirement sigma :=
  {r with topAddress := []}

def eraseExposure (e : Exposure sigma) : Exposure sigma :=
  {e with hole := []}

/-- A finite rooted observation of existing summary metadata. -/
structure RootAgreement (source target : Summary sigma) : Prop where
  conclusion : source.conclusion = target.conclusion
  inventory : source.inventory = target.inventory
  requirements : source.requirements.map eraseRequirement =
    target.requirements.map eraseRequirement
  ok : source.ok ↔ target.ok

noncomputable def exposureAt (parent : Summary sigma) (address : InternalAddress) :
    Multiset (Exposure sigma) := by
  classical
  exact (parent.exposure.filter (fun e => e.hole = address)).map eraseExposure

/-- Compare two explicitly paired physical attachments, not equal-looking
logical ports.  The hole's actual address is used before normalization. -/
structure AttachmentAgreement (sourceParent targetParent : Summary sigma)
    (source target : Attachment sigma) : Prop where
  boundary : source.1.boundary = target.1.boundary
  root : RootAgreement source.2 target.2
  exposure : exposureAt sourceParent source.1.address =
    exposureAt targetParent target.1.address

theorem rootAgreement_refl (summary : Summary sigma) : RootAgreement summary summary :=
  ⟨rfl, rfl, rfl, Iff.rfl⟩

theorem rootAgreement_symm {source target : Summary sigma}
    (agree : RootAgreement source target) : RootAgreement target source :=
  ⟨agree.conclusion.symm, agree.inventory.symm,
    agree.requirements.symm, agree.ok.symm⟩

theorem rootAgreement_of_eq {source target : Summary sigma}
    (same : source = target) : RootAgreement source target := by
  subst target
  exact rootAgreement_refl source

/-- Literal whole-summary equality provides a matching native physical hole,
not just a displayed sequent.  Vacant addresses are unique in native trees. -/
theorem fullSummary_hole_exists
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {source target : CKTree sigma (Data sigma) G}
    (same : directSummary Imp source [] = directSummary Imp target [])
    (hole : source.LeafOccurrence) :
    ∃ other : target.LeafOccurrence,
      source.leafAddress hole = target.leafAddress other ∧
        source.leafBoundary hole = target.leafBoundary other := by
  have present : (⟨source.leafAddress hole, source.leafBoundary hole⟩ : Hole sigma) ∈
      (directSummary Imp source []).holes := by
    exact List.mem_map.mpr ⟨hole, source.leaf_mem_leafOrder hole, rfl⟩
  rw [same] at present
  change (⟨source.leafAddress hole, source.leafBoundary hole⟩ : Hole sigma) ∈
    target.leafOrder.map
      (fun other => (⟨target.leafAddress other, target.leafBoundary other⟩ : Hole sigma))
    at present
  rcases List.mem_map.mp present with ⟨other, member, equal⟩
  exact ⟨other, (congrArg Hole.address equal).symm,
    (congrArg Hole.boundary equal).symm⟩

/-- Canonical address matching extracted from equality of existing summaries.
Choice selects the unique native vacancy at that address, not a new context. -/
noncomputable def fullSummary_holeEquiv
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {source target : CKTree sigma (Data sigma) G}
    (same : directSummary Imp source [] = directSummary Imp target []) :
    source.LeafOccurrence ≃ target.LeafOccurrence where
  toFun hole := Classical.choose (fullSummary_hole_exists Imp same hole)
  invFun hole := Classical.choose (fullSummary_hole_exists Imp same.symm hole)
  left_inv hole := by
    apply source.leafAddress_injective
    exact (Classical.choose_spec (fullSummary_hole_exists Imp same.symm
      (Classical.choose (fullSummary_hole_exists Imp same hole)))).1.symm.trans
        (Classical.choose_spec (fullSummary_hole_exists Imp same hole)).1.symm
  right_inv hole := by
    apply target.leafAddress_injective
    exact (Classical.choose_spec (fullSummary_hole_exists Imp same
      (Classical.choose (fullSummary_hole_exists Imp same.symm hole)))).1.symm.trans
        (Classical.choose_spec (fullSummary_hole_exists Imp same.symm hole)).1.symm

theorem fullSummary_holeEquiv_address
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {source target : CKTree sigma (Data sigma) G}
    (same : directSummary Imp source [] = directSummary Imp target [])
    (hole : source.LeafOccurrence) :
    source.leafAddress hole = target.leafAddress (fullSummary_holeEquiv Imp same hole) :=
  (Classical.choose_spec (fullSummary_hole_exists Imp same hole)).1

theorem fullSummary_holeEquiv_boundary
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {source target : CKTree sigma (Data sigma) G}
    (same : directSummary Imp source [] = directSummary Imp target [])
    (hole : source.LeafOccurrence) :
    source.leafBoundary hole = target.leafBoundary (fullSummary_holeEquiv Imp same hole) :=
  (Classical.choose_spec (fullSummary_hole_exists Imp same hole)).2

theorem fullSummary_holeEquiv_order
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {source target : CKTree sigma (Data sigma) G}
    (same : directSummary Imp source [] = directSummary Imp target []) :
    source.leafOrder.map (fullSummary_holeEquiv Imp same) = target.leafOrder := by
  have rows := congrArg (List.map Hole.address) (congrArg Summary.holes same)
  have orderedAddresses : source.leafOrder.map source.leafAddress =
      target.leafOrder.map target.leafAddress := by
    simpa only [directSummary, List.nil_append, List.map_map] using rows
  apply target.leafAddress_injective.list_map
  calc
    (source.leafOrder.map (fullSummary_holeEquiv Imp same)).map target.leafAddress =
        source.leafOrder.map source.leafAddress := by
      rw [List.map_map]
      apply List.map_congr_left
      intro hole member
      exact (fullSummary_holeEquiv_address Imp same hole).symm
    _ = target.leafOrder.map target.leafAddress := orderedAddresses

theorem forall_paired_iff {left right : List (Attachment sigma)}
    {relation : Attachment sigma → Attachment sigma → Prop}
    (paired : List.Forall₂ relation left right)
    (P Q : Attachment sigma → Prop)
    (agree : ∀ a b, relation a b → (P a ↔ Q b)) :
    (∀ a ∈ left, P a) ↔ ∀ b ∈ right, Q b := by
  induction paired with
  | nil => simp
  | @cons a b left right pair tail ih =>
      constructor
      · intro all other present
        rcases List.mem_cons.mp present with same | present
        · subst other
          exact (agree a b pair).mp (all a (by simp))
        · exact ih.mp (fun item member => all item (List.mem_cons_of_mem _ member))
            other present
      · intro all other present
        rcases List.mem_cons.mp present with same | present
        · subst other
          exact (agree a b pair).mpr (all b (by simp))
        · exact ih.mpr (fun item member => all item (List.mem_cons_of_mem _ member))
            other present

/-- Universal conditions transport through the actual multiset map.  This
preserves every occurrence multiplicity even though the condition is a Prop. -/
theorem forall_erased_requirements_iff
    {left right : Multiset (Requirement sigma)}
    (same : left.map eraseRequirement = right.map eraseRequirement)
    (P Q : Requirement sigma → Prop)
    (agree : ∀ a b, eraseRequirement a = eraseRequirement b → (P a ↔ Q b)) :
    (∀ a ∈ left, P a) ↔ ∀ b ∈ right, Q b := by
  constructor
  · intro all b present
    have mapped := Multiset.mem_map_of_mem eraseRequirement present
    rw [← same] at mapped
    rcases Multiset.mem_map.mp mapped with ⟨a, member, equal⟩
    exact (agree a b equal).mp (all a member)
  · intro all a present
    have mapped := Multiset.mem_map_of_mem eraseRequirement present
    rw [same] at mapped
    rcases Multiset.mem_map.mp mapped with ⟨b, member, equal⟩
    exact (agree a b equal.symm).mpr (all b member)

theorem sumInventories_eq {sourceParent targetParent : Summary sigma}
    {source target : List (Attachment sigma)}
    (paired : List.Forall₂ (AttachmentAgreement sourceParent targetParent) source target) :
    sumInventories source = sumInventories target := by
  induction paired with
  | nil => rfl
  | cons pair tail ih =>
      change _ + sumInventories _ = _ + sumInventories _
      rw [pair.root.inventory, ih]

theorem erase_sumRequirements_eq {sourceParent targetParent : Summary sigma}
    {source target : List (Attachment sigma)}
    (paired : List.Forall₂ (AttachmentAgreement sourceParent targetParent) source target) :
    (sumRequirements source).map eraseRequirement =
      (sumRequirements target).map eraseRequirement := by
  induction paired with
  | nil => rfl
  | cons pair tail ih =>
      change ( _ + sumRequirements _).map eraseRequirement =
        (_ + sumRequirements _).map eraseRequirement
      rw [Multiset.map_add, Multiset.map_add, pair.root.requirements, ih]

theorem exposureAt_lookup (parent : Summary sigma) (address : InternalAddress)
    (r : Requirement sigma) :
    (∃ e ∈ parent.exposure, MatchesExposure address r e) ↔
      ∃ e ∈ exposureAt parent address,
        e.owner = r.owner ∧ e.parameters = r.parameters ∧ e.role = r.role := by
  classical
  constructor
  · rintro ⟨e, present, hole, owner, pack, role⟩
    refine ⟨eraseExposure e, ?_, owner, pack, role⟩
    apply Multiset.mem_map_of_mem
    exact Multiset.mem_filter.mpr ⟨present, hole⟩
  · rintro ⟨e, present, owner, pack, role⟩
    rcases Multiset.mem_map.mp present with ⟨original, selected, same⟩
    rcases Multiset.mem_filter.mp selected with ⟨member, hole⟩
    subst e
    exact ⟨original, member, hole, owner, pack, role⟩

theorem exposure_lookup_transport {sourceParent targetParent : Summary sigma}
    {source target : Attachment sigma}
    (paired : AttachmentAgreement sourceParent targetParent source target)
    {a b : Requirement sigma} (equal : eraseRequirement a = eraseRequirement b) :
    (∃ e ∈ sourceParent.exposure, MatchesExposure source.1.address a e) ↔
      ∃ e ∈ targetParent.exposure, MatchesExposure target.1.address b e := by
  have owner : a.owner = b.owner := by
    simpa only [eraseRequirement] using
      congrArg (fun r : Requirement sigma => r.owner) equal
  have pack : a.parameters = b.parameters := by
    simpa only [eraseRequirement] using
      congrArg (fun r : Requirement sigma => r.parameters) equal
  have role : a.role = b.role := by
    simpa only [eraseRequirement] using
      congrArg (fun r : Requirement sigma => r.role) equal
  rw [exposureAt_lookup, exposureAt_lookup, paired.exposure, owner, pack, role]

theorem compositionOK_iff {sourceParent targetParent : Summary sigma}
    (parents : RootAgreement sourceParent targetParent)
    {source target : List (Attachment sigma)}
    (paired : List.Forall₂ (AttachmentAgreement sourceParent targetParent) source target)
    (sourceCoverage : source.map Prod.fst = sourceParent.holes)
    (targetCoverage : target.map Prod.fst = targetParent.holes) :
    compositionOK sourceParent source ↔ compositionOK targetParent target := by
  have inventory : combinedInventory sourceParent source =
      combinedInventory targetParent target := by
    unfold combinedInventory
    rw [parents.inventory, sumInventories_eq paired]
  have children :
      (∀ input ∈ source, input.2.ok ∧ input.1.boundary = input.2.conclusion) ↔
        ∀ input ∈ target, input.2.ok ∧ input.1.boundary = input.2.conclusion := by
    apply forall_paired_iff paired
    intro a b pair
    rw [pair.root.ok, pair.boundary, pair.root.conclusion]
  have parentDemands :
      (∀ r ∈ sourceParent.requirements, r.owner ∉ combinedInventory sourceParent source) ↔
        ∀ r ∈ targetParent.requirements,
          r.owner ∉ combinedInventory targetParent target := by
    apply forall_erased_requirements_iff parents.requirements
    intro a b equal
    have owner : a.owner = b.owner := by
      simpa only [eraseRequirement] using
        congrArg (fun r : Requirement sigma => r.owner) equal
    rw [inventory, owner]
  have childDemands :
      (∀ input ∈ source, ∀ r ∈ input.2.requirements,
        r.owner ∈ combinedInventory sourceParent source →
          r.owner ∈ sourceParent.inventory ∧
            ∃ e ∈ sourceParent.exposure, MatchesExposure input.1.address r e) ↔
      ∀ input ∈ target, ∀ r ∈ input.2.requirements,
        r.owner ∈ combinedInventory targetParent target →
          r.owner ∈ targetParent.inventory ∧
            ∃ e ∈ targetParent.exposure, MatchesExposure input.1.address r e := by
    apply forall_paired_iff paired
    intro input other pair
    apply forall_erased_requirements_iff pair.root.requirements
    intro a b equal
    have owner : a.owner = b.owner := by
      simpa only [eraseRequirement] using
        congrArg (fun r : Requirement sigma => r.owner) equal
    rw [inventory, parents.inventory, owner,
      exposure_lookup_transport pair equal]
  constructor
  · rintro ⟨parentOK, childOK, covered, unique, parentLegal, childLegal⟩
    exact ⟨parents.ok.mp parentOK, children.mp childOK, targetCoverage,
      inventory ▸ unique, parentDemands.mp parentLegal, childDemands.mp childLegal⟩
  · rintro ⟨parentOK, childOK, covered, unique, parentLegal, childLegal⟩
    exact ⟨parents.ok.mpr parentOK, children.mpr childOK, sourceCoverage,
      inventory.symm ▸ unique, parentDemands.mpr parentLegal, childDemands.mpr childLegal⟩

theorem erase_filter_owners (rows : Multiset (Requirement sigma))
    (owners : Multiset Nat) :
    (rows.filter (fun r => r.owner ∉ owners)).map eraseRequirement =
      (rows.map eraseRequirement).filter (fun r => r.owner ∉ owners) := by
  classical
  rw [Multiset.filter_map]
  rfl

/-- The compact compositional operation preserves rooted observations under
paired native attachments, including bad fillers and owner collisions. -/
theorem compose_rootAgreement {sourceParent targetParent : Summary sigma}
    (parents : RootAgreement sourceParent targetParent)
    {source target : List (Attachment sigma)}
    (paired : List.Forall₂ (AttachmentAgreement sourceParent targetParent) source target)
    (sourceCoverage : source.map Prod.fst = sourceParent.holes)
    (targetCoverage : target.map Prod.fst = targetParent.holes) :
    RootAgreement (composeSummary sourceParent source) (composeSummary targetParent target) := by
  have inventory : combinedInventory sourceParent source =
      combinedInventory targetParent target := by
    unfold combinedInventory
    rw [parents.inventory, sumInventories_eq paired]
  refine ⟨parents.conclusion, inventory, ?_,
    compositionOK_iff parents paired sourceCoverage targetCoverage⟩
  change (remainingRequirements sourceParent source).map eraseRequirement =
    (remainingRequirements targetParent target).map eraseRequirement
  unfold remainingRequirements
  rw [erase_filter_owners, erase_filter_owners, Multiset.map_add, Multiset.map_add,
    parents.requirements, erase_sumRequirements_eq paired, inventory]

#check @compositionOK_iff
#check @compose_rootAgreement
#check @fullSummary_holeEquiv
#print axioms fullSummary_holeEquiv
#print axioms fullSummary_holeEquiv_order
#print axioms compositionOK_iff
#print axioms compose_rootAgreement

end Potkin.Research.OpenDischarge

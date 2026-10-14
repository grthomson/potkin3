import Potkin.OriginCuts
import Potkin.NestedCoherence

/-!
# Staged native opening with persistent origins

Relative native sites restrict the original annotations, never renaming on
re-rooting. Lower data are decoded within their actual middle component before
the middle forest fills the root. The grouping is the existing native family
of relative cuts, not a new proof, forest or schedule carrier.

This establishes staged reconstruction and its native projection, not an
equality of enriched schedule coefficient triples or a linear coaction law.
-/

namespace Potkin
universe u v w z
variable {sigma : Signature.{u, v}} {InstanceData : Type w} {Origin : Type z}

mutual
def CKCutPlan.originDetached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    tree.OriginNames Origin → (site : cut.Site) → (cut.detached site).OriginNames Origin
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ cuts, names, site => cuts.originDetached names.2 site
def CKChildCuts.originDetached : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    children.OriginNames Origin → (site : cuts.Site) → (cuts.detached site).OriginNames Origin
  | _, _, .nil, _ => fun site => nomatch site
  | _, _, .cons _ _ head tail, names => fun site =>
      match site with
      | Sum.inl site => head.originDetached names.1 site
      | Sum.inr site => tail.originDetached names.2 site
def CKBranchCut.originDetached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    tree.OriginNames Origin → (site : cut.Site) → (cut.detached site).OriginNames Origin
  | _, _, .detach _, names, _ => names
  | _, _, .descend cut, names, site => cut.originDetached names site
end

mutual
theorem CKCutPlan.originDetached_sublist : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (names : tree.OriginNames Origin) → (site : cut.Site) →
    List.Sublist ((cut.detached site).originList (cut.originDetached names site))
      (tree.originList names)
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ cuts, names, site =>
      (cuts.originDetached_sublist names.2 site).cons names.1
theorem CKChildCuts.originDetached_sublist : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (names : children.OriginNames Origin) → (site : cuts.Site) →
    List.Sublist ((cuts.detached site).originList (cuts.originDetached names site))
      (children.originList names)
  | _, _, .nil, _, site => nomatch site
  | _, _, .cons head tail headCut tailCuts, names, site => by
      cases site with
      | inl site =>
          simpa using (headCut.originDetached_sublist names.1 site).append
            (List.nil_sublist (tail.originList names.2))
      | inr site =>
          simpa using (List.nil_sublist (head.originList names.1)).append
            (tailCuts.originDetached_sublist names.2 site)
theorem CKBranchCut.originDetached_sublist : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (names : tree.OriginNames Origin) → (site : cut.Site) →
    List.Sublist ((cut.detached site).originList (cut.originDetached names site))
      (tree.originList names)
  | _, _, .detach _, _, _ => List.Sublist.refl _
  | _, _, .descend cut, names, site => cut.originDetached_sublist names site
end

mutual
theorem CKCutPlan.originFactors_siteOrder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (names : tree.OriginNames Origin) →
    cut.originFactors names = cut.siteOrder.map (fun site =>
      (⟨⟨cut.siteBoundary site, cut.detached site, cut.detachedOrdinary site⟩,
        cut.originDetached names site⟩ : OriginComponent sigma InstanceData Origin))
  | _, _, .interface _, _ => rfl
  | _, _, .ordinary _ _ cuts, names => cuts.originFactors_siteOrder names.2
theorem CKChildCuts.originFactors_siteOrder : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (names : children.OriginNames Origin) →
    cuts.originFactors names = cuts.siteOrder.map (fun site =>
      (⟨⟨cuts.siteBoundary site, cuts.detached site, cuts.detachedOrdinary site⟩,
        cuts.originDetached names site⟩ : OriginComponent sigma InstanceData Origin))
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _ h t, names => by
      rw [CKChildCuts.originFactors,
        h.originFactors_siteOrder names.1, t.originFactors_siteOrder names.2]
      simp only [CKChildCuts.siteOrder, CKChildCuts.Site]
      rw [List.map_append, List.map_map, List.map_map]
      rfl
theorem CKBranchCut.originFactors_siteOrder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (names : tree.OriginNames Origin) →
    cut.originFactors names = cut.siteOrder.map (fun site =>
      (⟨⟨cut.siteBoundary site, cut.detached site, cut.detachedOrdinary site⟩,
        cut.originDetached names site⟩ : OriginComponent sigma InstanceData Origin))
  | _, _, .detach _, _ => rfl
  | _, _, .descend cut, names => cut.originFactors_siteOrder names
end

def OriginTree.asComponent {G : Hypersequent sigma}
    (tree : OriginTree sigma InstanceData Origin G) (ordinary : tree.native.IsOrdinary) :
    OriginComponent sigma InstanceData Origin := ⟨⟨G, tree.native, ordinary⟩, tree.names⟩

theorem OriginTree.asComponent_congr {G : Hypersequent sigma}
    {x y : OriginTree sigma InstanceData Origin G} (equal : x = y)
    (hx : x.native.IsOrdinary) (hy : y.native.IsOrdinary) :
    x.asComponent hx = y.asComponent hy := by cases equal; rfl

namespace CKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Admission remains relative to exactly the original presentation. This
does not construct a private checked node or assert admission of raw data. -/
theorem decode_collected_locallyAdmitted {T : ProofTheory sigma InstanceData}
    {P : EquippedPresentation T} (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) (admitted : LocallyAdmittedTree P tree) :
    LocallyAdmittedTree P
      (OriginTree.decode (cut.originForest names) cut.remainder
        (cut.plan.originRemainder names)).native := by
  have equal := congrArg OriginTree.native (cut.decode_collected names fresh)
  change (OriginTree.decode (cut.originForest names) cut.remainder
    (cut.plan.originRemainder names)).native = tree at equal
  rwa [equal]

/-- The output is the actual decoder result, not a stored original source. -/
noncomputable def reassembledFactor (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) : OriginComponent sigma InstanceData Origin :=
  (OriginTree.decode (cut.originForest names) cut.remainder
    (cut.plan.originRemainder names)).asComponent (by
      have equal := congrArg OriginTree.native (cut.decode_collected names fresh)
      change (OriginTree.decode (cut.originForest names) cut.remainder
        (cut.plan.originRemainder names)).native = tree at equal
      rw [equal]
      exact cut.sourceOrdinary)

theorem reassembledFactor_eq (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) :
    cut.reassembledFactor names fresh =
      (⟨⟨G, tree, cut.sourceOrdinary⟩, names⟩ : OriginComponent sigma InstanceData Origin) :=
  OriginTree.asComponent_congr (cut.decode_collected names fresh) _ _

/-- Each actual detached component is opened and its collected inner data
decoded before its packet is returned to the commutative outer forest. -/
noncomputable def stagedOriginForest (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup)
    (inner : (outer : cut.Site) → CKCut (cut.plan.detached outer)) :
    OriginForest sigma InstanceData Origin :=
  Multiset.ofList (cut.orderedSites.map fun outer =>
    (inner outer).reassembledFactor (cut.plan.originDetached names outer)
      (fresh.sublist (cut.plan.originDetached_sublist names outer)))

theorem stagedOriginForest_eq (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup)
    (inner : (outer : cut.Site) → CKCut (cut.plan.detached outer)) :
    cut.stagedOriginForest names fresh inner = cut.originForest names := by
  unfold stagedOriginForest originForest
  rw [cut.plan.originFactors_siteOrder names]
  apply congrArg Multiset.ofList
  apply List.map_congr_left
  intro outer _
  exact (inner outer).reassembledFactor_eq _ _

theorem decode_twoStage (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup)
    (inner : (outer : cut.Site) → CKCut (cut.plan.detached outer)) :
    OriginTree.decode (cut.stagedOriginForest names fresh inner)
      cut.remainder (cut.plan.originRemainder names) =
        (⟨tree, names⟩ : OriginTree sigma InstanceData Origin G) := by
  rw [cut.stagedOriginForest_eq names fresh inner]
  exact cut.decode_collected names fresh

end CKCut

namespace CanonicalTwoStageWitness

/-- For an actual existing canonical noncrossing decomposition, forgetting
staged enriched reconstruction gives its exact native composed filling.
The native schedule-region theorem itself is reused, not re-proved here. -/
theorem CanonicalThreeRegionDecomposition.originDecode_forget
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    {first second : ValidAddressCut tree} {witness : CanonicalTwoStageWitness first second}
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (names : tree.OriginNames Origin) (fresh : (tree.originList names).Nodup) :
    (OriginTree.decode
      (witness.finalCut.toCut.stagedOriginForest names fresh
        (fun outer => (decomposition.innerCut outer).toCut))
      witness.finalCut.toCut.remainder
      (witness.finalCut.toCut.plan.originRemainder names)).native =
        decomposition.composedFilling := by
  have equal := congrArg OriginTree.native (witness.finalCut.toCut.decode_twoStage
    names fresh (fun outer => (decomposition.innerCut outer).toCut))
  exact equal.trans decomposition.composedFilling_reconstructs.symm

end CanonicalTwoStageWitness

end Potkin

#print axioms Potkin.CKCut.decode_twoStage
#print axioms Potkin.CKCut.decode_collected_locallyAdmitted
#print axioms Potkin.CanonicalTwoStageWitness.CanonicalThreeRegionDecomposition.originDecode_forget

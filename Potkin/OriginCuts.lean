import Potkin.MaterialDegree
import Potkin.RealizedCut

/-!
# Persistent origins on native CK extraction

These are dependent annotations of existing native trees, not another proof
syntax. A name labels every physical ordinary vertex and every old interface.
The collected coefficients remain a multiset of positive native components.
The decoder receives only that multiset and the enriched remainder.

Names are immutable birth identifiers, not current addresses or rule IDs.
Freshness includes interfaces. Re-rooting restricts annotations without
renaming them; a new vacancy inherits the opened root's name.
-/

namespace Potkin
universe u v w z
variable {sigma : Signature.{u, v}} {InstanceData : Type w} {Origin : Type z}

mutual
def CKTree.OriginNames (Origin : Type z) : {G : Hypersequent sigma} →
    CKTree sigma InstanceData G → Type z
  | _, .interface _ => Origin
  | _, .ordinary _ children => Origin × children.OriginNames Origin
def CKChildren.OriginNames (Origin : Type z) :
    {Gs : List (Hypersequent sigma)} → CKChildren sigma InstanceData Gs → Type z
  | _, .nil => PUnit
  | _, .cons head tail => head.OriginNames Origin × tail.OriginNames Origin
end

mutual
def CKTree.originList : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → tree.OriginNames Origin → List Origin
  | _, .interface _, name => [name]
  | _, .ordinary _ children, names => names.1 :: children.originList names.2
def CKChildren.originList : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) →
    children.OriginNames Origin → List Origin
  | _, .nil, _ => []
  | _, .cons head tail, names => head.originList names.1 ++ tail.originList names.2
end

def CKTree.rootOrigin : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → tree.OriginNames Origin → Origin
  | _, .interface _, name => name
  | _, .ordinary _ _, names => names.1

structure OriginTree (sigma : Signature.{u, v}) (InstanceData : Type w)
    (Origin : Type z) (G : Hypersequent sigma) where
  native : CKTree sigma InstanceData G
  names : native.OriginNames Origin

structure OriginChildren (sigma : Signature.{u, v}) (InstanceData : Type w)
    (Origin : Type z) (Gs : List (Hypersequent sigma)) where
  native : CKChildren sigma InstanceData Gs
  names : native.OriginNames Origin

def OriginChildren.cons {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
    (head : OriginTree sigma InstanceData Origin G)
    (tail : OriginChildren sigma InstanceData Origin Gs) :
    OriginChildren sigma InstanceData Origin (G :: Gs) :=
  ⟨.cons head.native tail.native, (head.names, tail.names)⟩

def OriginTree.Fresh {G : Hypersequent sigma}
    (tree : OriginTree sigma InstanceData Origin G) : Prop :=
  (tree.native.originList tree.names).Nodup

structure OriginComponent (sigma : Signature.{u, v}) (InstanceData : Type w)
    (Origin : Type z) where
  native : CKComponent sigma InstanceData
  names : native.tree.OriginNames Origin

abbrev OriginForest (sigma : Signature.{u, v}) (InstanceData : Type w)
    (Origin : Type z) := Multiset (OriginComponent sigma InstanceData Origin)

def OriginComponent.rootOrigin (c : OriginComponent sigma InstanceData Origin) : Origin :=
  c.native.tree.rootOrigin c.names

def OriginComponent.asTree (c : OriginComponent sigma InstanceData Origin) :
    OriginTree sigma InstanceData Origin c.native.boundary := ⟨c.native.tree, c.names⟩

namespace OriginForest

/-- Lookup is defined on the multiset itself, never on a recovered order.
Fresh root keys make the choice unique on valid extraction data. -/
noncomputable def lookup (F : OriginForest sigma InstanceData Origin) (name : Origin) :
    Option (OriginComponent sigma InstanceData Origin) := by
  classical
  exact if h : ∃ c, c ∈ F ∧ c.rootOrigin = name then some (Classical.choose h) else none

theorem lookup_none (F : OriginForest sigma InstanceData Origin) (name : Origin)
    (absent : ∀ c ∈ F, c.rootOrigin ≠ name) : lookup F name = none := by
  classical
  simp only [lookup]
  split_ifs with h
  · obtain ⟨c, member, equal⟩ := h
    exact (absent c member equal).elim
  · rfl

theorem lookup_some (F : OriginForest sigma InstanceData Origin)
    (c : OriginComponent sigma InstanceData Origin) (member : c ∈ F)
    (unique : ∀ d ∈ F, d.rootOrigin = c.rootOrigin → d = c) :
    lookup F c.rootOrigin = some c := by
  classical
  unfold lookup
  split_ifs with h
  · congr 1
    exact unique _ (Classical.choose_spec h).1 (Classical.choose_spec h).2
  · exact (h ⟨c, member, rfl⟩).elim

theorem lookup_add_right (F E : OriginForest sigma InstanceData Origin)
    (fresh : (F.map OriginComponent.rootOrigin).Nodup) (name : Origin)
    (absent : ∀ c ∈ E, c.rootOrigin ≠ name) :
    lookup (F + E) name = lookup F name := by
  classical
  by_cases h : ∃ c, c ∈ F ∧ c.rootOrigin = name
  · obtain ⟨c, member, equal⟩ := h
    have unique : ∀ d ∈ F, d.rootOrigin = c.rootOrigin → d = c := by
      intro d hd he
      exact Multiset.inj_on_of_nodup_map fresh d hd c member he
    have uniqueSum : ∀ d ∈ F + E, d.rootOrigin = c.rootOrigin → d = c := by
      intro d hd he
      rcases Multiset.mem_add.mp hd with hd | hd
      · exact unique d hd he
      · exact (absent d hd (he.trans equal)).elim
    rw [← equal, lookup_some _ c (Multiset.mem_add.mpr (Or.inl member)) uniqueSum,
      lookup_some _ c member unique]
  · have absentF : ∀ c ∈ F, c.rootOrigin ≠ name := by
      intro c hc he
      exact h ⟨c, hc, he⟩
    rw [lookup_none F name absentF, lookup_none (F + E) name]
    intro c hc
    rcases Multiset.mem_add.mp hc with hc | hc
    · exact absentF c hc
    · exact absent c hc

end OriginForest

mutual
noncomputable def OriginTree.decode (F : OriginForest sigma InstanceData Origin) :
    {G : Hypersequent sigma} → (tree : CKTree sigma InstanceData G) →
    tree.OriginNames Origin → OriginTree sigma InstanceData Origin G
  | _, .interface G, name => by
      classical
      exact match F.lookup name with
      | none => ⟨.interface G, name⟩
      | some c => if h : c.native.boundary = G then h ▸ c.asTree else ⟨.interface G, name⟩
  | _, .ordinary o children, names =>
      let result := OriginChildren.decode F children names.2
      ⟨.ordinary o result.native, (names.1, result.names)⟩
noncomputable def OriginChildren.decode (F : OriginForest sigma InstanceData Origin) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma InstanceData Gs) →
    children.OriginNames Origin → OriginChildren sigma InstanceData Origin Gs
  | _, .nil, _ => ⟨.nil, PUnit.unit⟩
  | _, .cons head tail, names =>
      let h := OriginTree.decode F head names.1
      let t := OriginChildren.decode F tail names.2
      ⟨.cons h.native t.native, (h.names, t.names)⟩
end

mutual
theorem OriginTree.decode_congr (F E : OriginForest sigma InstanceData Origin) :
    {G : Hypersequent sigma} → (tree : CKTree sigma InstanceData G) →
    (names : tree.OriginNames Origin) →
    (∀ name ∈ tree.originList names, F.lookup name = E.lookup name) →
    OriginTree.decode F tree names = OriginTree.decode E tree names
  | _, .interface _, names, equal => by
      simp only [OriginTree.decode, equal names (by simp [CKTree.originList])]
  | _, .ordinary o children, names, equal => by
      have h := OriginChildren.decode_congr F E children names.2
        (fun name member => equal name (List.mem_cons_of_mem _ member))
      exact congrArg (fun result : OriginChildren sigma InstanceData Origin _ =>
        (⟨.ordinary o result.native, (names.1, result.names)⟩ :
          OriginTree sigma InstanceData Origin _)) h
theorem OriginChildren.decode_congr (F E : OriginForest sigma InstanceData Origin) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma InstanceData Gs) →
    (names : children.OriginNames Origin) →
    (∀ name ∈ children.originList names, F.lookup name = E.lookup name) →
    OriginChildren.decode F children names = OriginChildren.decode E children names
  | _, .nil, _, _ => rfl
  | _, .cons head tail, names, equal => by
      have h := OriginTree.decode_congr F E head names.1
        (fun name member => equal name (List.mem_append_left _ member))
      have t := OriginChildren.decode_congr F E tail names.2
        (fun name member => equal name (List.mem_append_right _ member))
      exact congrArg₂ OriginChildren.cons h t
end

mutual
def CKCutPlan.originRemainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    tree.OriginNames Origin → cut.remainder.OriginNames Origin
  | _, _, .interface _, names => names
  | _, _, .ordinary _ _ cuts, names => (names.1, cuts.originRemainder names.2)
def CKChildCuts.originRemainder : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    children.OriginNames Origin → cuts.remainder.OriginNames Origin
  | _, _, .nil, _ => PUnit.unit
  | _, _, .cons _ _ h t, names => (h.originRemainder names.1, t.originRemainder names.2)
def CKBranchCut.originRemainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    tree.OriginNames Origin → cut.remainder.OriginNames Origin
  | _, tree, .detach _, names => tree.rootOrigin names
  | _, _, .descend cut, names => cut.originRemainder names
end

mutual
def CKCutPlan.originFactors : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    tree.OriginNames Origin → List (OriginComponent sigma InstanceData Origin)
  | _, _, .interface _, _ => []
  | _, _, .ordinary _ _ cuts, names => cuts.originFactors names.2
def CKChildCuts.originFactors : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    children.OriginNames Origin → List (OriginComponent sigma InstanceData Origin)
  | _, _, .nil, _ => []
  | _, _, .cons _ _ h t, names => h.originFactors names.1 ++ t.originFactors names.2
def CKBranchCut.originFactors : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    tree.OriginNames Origin → List (OriginComponent sigma InstanceData Origin)
  | G, tree, .detach ordinary, names => [⟨⟨G, tree, ordinary⟩, names⟩]
  | _, _, .descend cut, names => cut.originFactors names
end

mutual
theorem CKCutPlan.originRemainder_sublist : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (names : tree.OriginNames Origin) →
    List.Sublist (cut.remainder.originList (cut.originRemainder names)) (tree.originList names)
  | _, _, .interface _, _ => List.Sublist.refl _
  | _, _, .ordinary _ _ cuts, names =>
      (cuts.originRemainder_sublist names.2).cons₂ names.1
theorem CKChildCuts.originRemainder_sublist : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (names : children.OriginNames Origin) →
    List.Sublist (cuts.remainder.originList (cuts.originRemainder names)) (children.originList names)
  | _, _, .nil, _ => List.Sublist.refl _
  | _, _, .cons _ _ h t, names =>
      (h.originRemainder_sublist names.1).append (t.originRemainder_sublist names.2)
theorem CKBranchCut.originRemainder_sublist : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (names : tree.OriginNames Origin) →
    List.Sublist (cut.remainder.originList (cut.originRemainder names)) (tree.originList names)
  | _, tree, .detach _, names => by
      cases tree with
      | interface _ => exact List.Sublist.refl _
      | ordinary _ children => exact (List.nil_sublist _).cons₂ names.1
  | _, _, .descend cut, names => cut.originRemainder_sublist names
end

mutual
theorem CKCutPlan.originRoots_sublist : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (names : tree.OriginNames Origin) →
    List.Sublist ((cut.originFactors names).map OriginComponent.rootOrigin) (tree.originList names)
  | _, _, .interface _, _ => List.nil_sublist _
  | _, _, .ordinary _ _ cuts, names => (cuts.originRoots_sublist names.2).cons names.1
theorem CKChildCuts.originRoots_sublist : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (names : children.OriginNames Origin) →
    List.Sublist ((cuts.originFactors names).map OriginComponent.rootOrigin) (children.originList names)
  | _, _, .nil, _ => List.Sublist.refl _
  | _, _, .cons _ _ h t, names => by
      simpa [CKChildCuts.originFactors, List.map_append] using
        (h.originRoots_sublist names.1).append (t.originRoots_sublist names.2)
theorem CKBranchCut.originRoots_sublist : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (names : tree.OriginNames Origin) →
    List.Sublist ((cut.originFactors names).map OriginComponent.rootOrigin) (tree.originList names)
  | _, tree, .detach _, names => by
      cases tree with
      | interface _ => exact List.Sublist.refl _
      | ordinary _ children => exact (List.nil_sublist _).cons₂ names.1
  | _, _, .descend cut, names => cut.originRoots_sublist names
end

private theorem decode_ignore_right (F E : OriginForest sigma InstanceData Origin)
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (names : tree.OriginNames Origin) (fresh : (F.map OriginComponent.rootOrigin).Nodup)
    (outside : ∀ c ∈ E, ∀ name ∈ tree.originList names, c.rootOrigin ≠ name) :
    OriginTree.decode (F + E) tree names = OriginTree.decode F tree names := by
  apply OriginTree.decode_congr
  intro name member
  exact OriginForest.lookup_add_right F E fresh name (fun c hc => outside c hc name member)

private theorem decodeChildren_ignore_right (F E : OriginForest sigma InstanceData Origin)
    {Gs : List (Hypersequent sigma)} (children : CKChildren sigma InstanceData Gs)
    (names : children.OriginNames Origin) (fresh : (F.map OriginComponent.rootOrigin).Nodup)
    (outside : ∀ c ∈ E, ∀ name ∈ children.originList names, c.rootOrigin ≠ name) :
    OriginChildren.decode (F + E) children names = OriginChildren.decode F children names := by
  apply OriginChildren.decode_congr
  intro name member
  exact OriginForest.lookup_add_right F E fresh name (fun c hc => outside c hc name member)

mutual
theorem CKCutPlan.decode_originExtraction : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (names : tree.OriginNames Origin) → (tree.originList names).Nodup →
    OriginTree.decode (Multiset.ofList (cut.originFactors names))
      cut.remainder (cut.originRemainder names) = ⟨tree, names⟩
  | _, _, .interface G, names, _ => by
      simp [OriginTree.decode, CKCutPlan.originFactors, CKCutPlan.originRemainder,
        CKCutPlan.remainder, OriginForest.lookup]
  | _, _, .ordinary o children cuts, names, fresh => by
      have hc := cuts.decode_originExtraction names.2 (List.nodup_cons.mp fresh).2
      exact congrArg (fun result : OriginChildren sigma InstanceData Origin _ =>
        (⟨.ordinary o result.native, (names.1, result.names)⟩ :
          OriginTree sigma InstanceData Origin _)) hc
theorem CKChildCuts.decode_originExtraction : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (names : children.OriginNames Origin) → (children.originList names).Nodup →
    OriginChildren.decode (Multiset.ofList (cuts.originFactors names))
      cuts.remainder (cuts.originRemainder names) = ⟨children, names⟩
  | _, _, .nil, names, _ => by cases names; rfl
  | _, _, .cons head tail h t, names, fresh => by
      have facts := List.nodup_append'.mp fresh
      have disjoint := List.disjoint_left.mp facts.2.2
      let F := Multiset.ofList (h.originFactors names.1)
      let E := Multiset.ofList (t.originFactors names.2)
      have hfresh : (F.map OriginComponent.rootOrigin).Nodup := by
        simpa [F] using facts.1.sublist (h.originRoots_sublist names.1)
      have efresh : (E.map OriginComponent.rootOrigin).Nodup := by
        simpa [E] using facts.2.1.sublist (t.originRoots_sublist names.2)
      have hdecode : OriginTree.decode (F + E) h.remainder (h.originRemainder names.1) =
          OriginTree.decode F h.remainder (h.originRemainder names.1) := by
        apply decode_ignore_right _ _ _ _ hfresh
        intro c hc name hn equal
        have ce : c.rootOrigin ∈ tail.originList names.2 :=
          (t.originRoots_sublist names.2).subset
            (List.mem_map.mpr ⟨c, by simpa [E] using hc, rfl⟩)
        have nh : name ∈ head.originList names.1 :=
          (h.originRemainder_sublist names.1).subset hn
        exact disjoint nh (equal ▸ ce)
      have tdecode : OriginChildren.decode (F + E) t.remainder (t.originRemainder names.2) =
          OriginChildren.decode E t.remainder (t.originRemainder names.2) := by
        rw [Multiset.add_comm F E]
        apply decodeChildren_ignore_right _ _ _ _ efresh
        intro c hc name hn equal
        have ch : c.rootOrigin ∈ head.originList names.1 :=
          (h.originRoots_sublist names.1).subset
            (List.mem_map.mpr ⟨c, by simpa [F] using hc, rfl⟩)
        have nt : name ∈ tail.originList names.2 :=
          (t.originRemainder_sublist names.2).subset hn
        exact disjoint ch (equal.symm ▸ nt)
      have hi := h.decode_originExtraction names.1 facts.1
      have ti := t.decode_originExtraction names.2 facts.2.1
      exact congrArg₂ OriginChildren.cons (hdecode.trans hi) (tdecode.trans ti)
theorem CKBranchCut.decode_originExtraction : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (names : tree.OriginNames Origin) → (tree.originList names).Nodup →
    OriginTree.decode (Multiset.ofList (cut.originFactors names))
      cut.remainder (cut.originRemainder names) = ⟨tree, names⟩
  | G, tree, .detach ordinary, names, _ => by
      let c : OriginComponent sigma InstanceData Origin := ⟨⟨G, tree, ordinary⟩, names⟩
      have found : OriginForest.lookup ({c} : OriginForest sigma InstanceData Origin)
          c.rootOrigin = some c :=
        OriginForest.lookup_some _ c (by simp) (by intro d hd _; simpa using hd)
      change OriginTree.decode ({c} : OriginForest sigma InstanceData Origin)
        (.interface G) c.rootOrigin = _
      simp [OriginTree.decode, found, c, OriginComponent.asTree]
  | _, _, .descend cut, names, fresh => cut.decode_originExtraction names fresh
end

mutual
theorem CKCutPlan.originFactors_forget : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (names : tree.OriginNames Origin) →
    (cut.originFactors names).map OriginComponent.native =
      cut.siteOrder.map (fun site =>
        (⟨cut.siteBoundary site, cut.detached site, cut.detachedOrdinary site⟩ :
          CKComponent sigma InstanceData))
  | _, _, .interface _, _ => rfl
  | _, _, .ordinary _ _ cuts, names => cuts.originFactors_forget names.2
theorem CKChildCuts.originFactors_forget : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (names : children.OriginNames Origin) →
    (cuts.originFactors names).map OriginComponent.native =
      cuts.siteOrder.map (fun site =>
        (⟨cuts.siteBoundary site, cuts.detached site, cuts.detachedOrdinary site⟩ :
          CKComponent sigma InstanceData))
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _ h t, names => by
      rw [CKChildCuts.originFactors, List.map_append,
        h.originFactors_forget names.1, t.originFactors_forget names.2]
      simp only [CKChildCuts.siteOrder, CKChildCuts.Site]
      rw [List.map_append, List.map_map, List.map_map]
      rfl
theorem CKBranchCut.originFactors_forget : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (names : tree.OriginNames Origin) →
    (cut.originFactors names).map OriginComponent.native =
      cut.siteOrder.map (fun site =>
        (⟨cut.siteBoundary site, cut.detached site, cut.detachedOrdinary site⟩ :
          CKComponent sigma InstanceData))
  | _, _, .detach _, _ => rfl
  | _, _, .descend cut, names => cut.originFactors_forget names
end

mutual
/-- Complete typed vacancy keys, including inherited interfaces. -/
def CKTree.originHoleKeys : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → tree.OriginNames Origin →
    List (Origin × Hypersequent sigma)
  | G, .interface _, name => [(name, G)]
  | _, .ordinary _ children, names => children.originHoleKeys names.2
def CKChildren.originHoleKeys : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → children.OriginNames Origin →
    List (Origin × Hypersequent sigma)
  | _, .nil, _ => []
  | _, .cons head tail, names =>
      head.originHoleKeys names.1 ++ tail.originHoleKeys names.2
end

def OriginComponent.holeKey (c : OriginComponent sigma InstanceData Origin) :
    Origin × Hypersequent sigma := (c.rootOrigin, c.native.boundary)

mutual
/-- Every collected factor has a same-origin, same-complete-boundary vacancy;
freshness later ensures this matching is once-only. -/
theorem CKCutPlan.originFactors_match_holes : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (names : tree.OriginNames Origin) →
    List.Sublist ((cut.originFactors names).map OriginComponent.holeKey)
      (cut.remainder.originHoleKeys (cut.originRemainder names))
  | _, _, .interface _, _ => List.nil_sublist _
  | _, _, .ordinary _ _ cuts, names => cuts.originFactors_match_holes names.2
theorem CKChildCuts.originFactors_match_holes : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (names : children.OriginNames Origin) →
    List.Sublist ((cuts.originFactors names).map OriginComponent.holeKey)
      (cuts.remainder.originHoleKeys (cuts.originRemainder names))
  | _, _, .nil, _ => List.Sublist.refl _
  | _, _, .cons _ _ h t, names => by
      simpa [CKChildCuts.originFactors, CKChildCuts.originRemainder, CKChildCuts.remainder,
        CKChildren.originHoleKeys, List.map_append] using
        (h.originFactors_match_holes names.1).append (t.originFactors_match_holes names.2)
theorem CKBranchCut.originFactors_match_holes : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (names : tree.OriginNames Origin) →
    List.Sublist ((cut.originFactors names).map OriginComponent.holeKey)
      (cut.remainder.originHoleKeys (cut.originRemainder names))
  | _, _, .detach _, _ => List.Sublist.refl _
  | _, _, .descend cut, names => cut.originFactors_match_holes names
end

mutual
theorem CKTree.originHoleKeys_origins_sublist : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (names : tree.OriginNames Origin) →
    List.Sublist ((tree.originHoleKeys names).map Prod.fst) (tree.originList names)
  | _, .interface _, _ => List.Sublist.refl _
  | _, .ordinary _ children, names =>
      (children.originHoleKeys_origins_sublist names.2).cons names.1
theorem CKChildren.originHoleKeys_origins_sublist : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (names : children.OriginNames Origin) →
    List.Sublist ((children.originHoleKeys names).map Prod.fst) (children.originList names)
  | _, .nil, _ => List.Sublist.refl _
  | _, .cons head tail, names => by
      simpa [CKChildren.originHoleKeys, List.map_append] using
        (head.originHoleKeys_origins_sublist names.1).append
          (tail.originHoleKeys_origins_sublist names.2)
end

namespace CKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

def originForest (cut : CKCut tree) (names : tree.OriginNames Origin) :
    OriginForest sigma InstanceData Origin := Multiset.ofList (cut.plan.originFactors names)

def enrichedRemainder (cut : CKCut tree) (names : tree.OriginNames Origin) :
    OriginTree sigma InstanceData Origin G := ⟨cut.remainder, cut.plan.originRemainder names⟩

@[simp] theorem enrichedRemainder_forget (cut : CKCut tree)
    (names : tree.OriginNames Origin) : (cut.enrichedRemainder names).native = cut.remainder := rfl

theorem originForest_forget (cut : CKCut tree) (names : tree.OriginNames Origin) :
    (cut.originForest names).map OriginComponent.native = cut.detachedForest := by
  simp only [originForest, Multiset.map_coe, cut.plan.originFactors_forget names,
    detachedForest, detachedTuple, orderedSites, List.map_map]
  rfl

theorem originForest_card (cut : CKCut tree) (names : tree.OriginNames Origin) :
    (cut.originForest names).card = cut.detachedForest.card := by
  rw [← cut.originForest_forget names, Multiset.card_map]

theorem originFactors_typedMatching (cut : CKCut tree) (names : tree.OriginNames Origin)
    (c : OriginComponent sigma InstanceData Origin) (member : c ∈ cut.originForest names) :
    c.holeKey ∈ cut.remainder.originHoleKeys (cut.plan.originRemainder names) := by
  apply (cut.plan.originFactors_match_holes names).subset
  exact List.mem_map.mpr ⟨c, by simpa [originForest] using member, rfl⟩

/-- Actual collected-data decoding; no source, cut, or ordered tuple is a
decoder argument. This applies to every native cut, including the empty cut. -/
theorem decode_collected (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) :
    OriginTree.decode (cut.originForest names) (cut.enrichedRemainder names).native
      (cut.enrichedRemainder names).names = (⟨tree, names⟩ : OriginTree sigma InstanceData Origin G) :=
  cut.plan.decode_originExtraction names fresh

theorem originRoots_nodup (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) :
    ((cut.originForest names).map OriginComponent.rootOrigin).Nodup := by
  simpa [originForest] using fresh.sublist (cut.plan.originRoots_sublist names)

theorem enrichedRemainder_fresh (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) : (cut.enrichedRemainder names).Fresh :=
  fresh.sublist (cut.plan.originRemainder_sublist names)

theorem remainder_holeOrigins_nodup (cut : CKCut tree) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) :
    ((cut.remainder.originHoleKeys (cut.plan.originRemainder names)).map Prod.fst).Nodup :=
  (cut.enrichedRemainder_fresh names fresh).sublist
    (cut.remainder.originHoleKeys_origins_sublist (cut.plan.originRemainder names))

/-- Equal collected enriched data determine the source across different
native trees. This is not equality defined by comparing all cuts. -/
theorem collected_injective {other : CKTree sigma InstanceData G}
    (cut : CKCut tree) (otherCut : CKCut other)
    (names : tree.OriginNames Origin) (otherNames : other.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) (otherFresh : (other.originList otherNames).Nodup)
    (remainder : cut.enrichedRemainder names = otherCut.enrichedRemainder otherNames)
    (forest : cut.originForest names = otherCut.originForest otherNames) :
    (⟨tree, names⟩ : OriginTree sigma InstanceData Origin G) = ⟨other, otherNames⟩ := by
  rw [← cut.decode_collected names fresh, ← otherCut.decode_collected otherNames otherFresh]
  rw [forest, remainder]

end CKCut

/-- Specialization reuses the already mechanized maximum; no downward-closure
hypothesis or interpretation of material kind as an arbitrary selector. -/
theorem CKTree.decode_maximalMaterialCut {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (notPure : ¬ tree.AllVerticesMaterial) (names : tree.OriginNames Origin)
    (fresh : (tree.originList names).Nodup) :
    let cut := tree.maximalMaterialCut ordinary notPure
    OriginTree.decode (cut.originForest names) cut.remainder (cut.plan.originRemainder names) =
      (⟨tree, names⟩ : OriginTree sigma InstanceData Origin G) :=
  (tree.maximalMaterialCut ordinary notPure).decode_collected names fresh

/-- Separate whole-opening module data, not a fabricated CK root cut or the
algebraic forest unit. The right object is a named typed vacancy. -/
theorem OriginTree.decode_wholeOpening {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (names : tree.OriginNames Origin) (fresh : (tree.originList names).Nodup) :
    OriginTree.decode ({⟨⟨G, tree, ordinary⟩, names⟩} : OriginForest sigma InstanceData Origin)
      (.interface G) (tree.rootOrigin names) = ⟨tree, names⟩ := by
  exact (CKBranchCut.detach ordinary).decode_originExtraction names fresh

end Potkin

#print axioms Potkin.CKCut.decode_collected
#print axioms Potkin.CKCut.collected_injective
#print axioms Potkin.CKTree.decode_maximalMaterialCut
#print axioms Potkin.CKCut.originForest_forget
#print axioms Potkin.CKCut.originRoots_nodup
#print axioms Potkin.CKCut.remainder_holeOrigins_nodup
#print axioms Potkin.CKCut.originFactors_typedMatching

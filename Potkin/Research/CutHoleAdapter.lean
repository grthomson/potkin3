import Potkin.AllHoleFilling

/-!
# Complete-source cut-created interface adapter

These maps index the existing native typed remainder; they do not introduce
another cut, proof, or context carrier.  Completeness is essential for the
inverse: an inherited interface is not a selected site.  A full branch's
`detach` remains separate from the root-excluding public `CKCut` plan.
-/

namespace Potkin
universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual

/-- A selected site creates one physical typed remainder interface. -/
def CKCutPlan.siteToLeaf : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    cut.Site → cut.remainder.LeafOccurrence
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary _ _ cuts, site => cuts.siteToLeaf site

def CKChildCuts.siteToLeaf : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    cuts.Site → cuts.remainder.LeafOccurrence
  | _, _, .nil, site => nomatch site
  | _, _, .cons _ _ head tail, site =>
      match site with
      | .inl site => .inl (head.siteToLeaf site)
      | .inr site => .inr (tail.siteToLeaf site)

def CKBranchCut.siteToLeaf : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    cut.Site → cut.remainder.LeafOccurrence
  | _, _, .detach _, _ => PUnit.unit
  | _, _, .descend cut, site => cut.siteToLeaf site

end

mutual

/-- Every remainder hole is cut-created only when the source is complete. -/
def CKCutPlan.leafToSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    tree.IsComplete → cut.remainder.LeafOccurrence → cut.Site
  | _, _, .interface _, complete, _ => False.elim complete
  | _, _, .ordinary _ _ cuts, complete, hole => cuts.leafToSite complete hole

def CKChildCuts.leafToSite : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    children.IsComplete → cuts.remainder.LeafOccurrence → cuts.Site
  | _, _, .nil, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, complete, hole =>
      match hole with
      | .inl hole => .inl (head.leafToSite complete.1 hole)
      | .inr hole => .inr (tail.leafToSite complete.2 hole)

def CKBranchCut.leafToSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    tree.IsComplete → cut.remainder.LeafOccurrence → cut.Site
  | _, _, .detach _, _, _ => PUnit.unit
  | _, _, .descend cut, complete, hole => cut.leafToSite complete hole

end

mutual

theorem CKCutPlan.leafToSite_siteToLeaf : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (complete : tree.IsComplete) → (site : cut.Site) →
    cut.leafToSite complete (cut.siteToLeaf site) = site
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ cuts, complete, site =>
      cuts.leafToSite_siteToLeaf complete site

theorem CKChildCuts.leafToSite_siteToLeaf : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (complete : children.IsComplete) → (site : cuts.Site) →
    cuts.leafToSite complete (cuts.siteToLeaf site) = site
  | _, _, .nil, _, site => nomatch site
  | _, _, .cons _ _ head tail, complete, site => by
      cases site with
      | inl site => exact congrArg Sum.inl (head.leafToSite_siteToLeaf complete.1 site)
      | inr site => exact congrArg Sum.inr (tail.leafToSite_siteToLeaf complete.2 site)

theorem CKBranchCut.leafToSite_siteToLeaf : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (complete : tree.IsComplete) → (site : cut.Site) →
    cut.leafToSite complete (cut.siteToLeaf site) = site
  | _, _, .detach _, _, site => by cases site; rfl
  | _, _, .descend cut, complete, site => cut.leafToSite_siteToLeaf complete site

end

mutual

theorem CKCutPlan.siteToLeaf_leafToSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (complete : tree.IsComplete) → (hole : cut.remainder.LeafOccurrence) →
    cut.siteToLeaf (cut.leafToSite complete hole) = hole
  | _, _, .interface _, complete, _ => False.elim complete
  | _, _, .ordinary _ _ cuts, complete, hole =>
      cuts.siteToLeaf_leafToSite complete hole

theorem CKChildCuts.siteToLeaf_leafToSite : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (complete : children.IsComplete) → (hole : cuts.remainder.LeafOccurrence) →
    cuts.siteToLeaf (cuts.leafToSite complete hole) = hole
  | _, _, .nil, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, complete, hole => by
      cases hole with
      | inl hole => exact congrArg Sum.inl (head.siteToLeaf_leafToSite complete.1 hole)
      | inr hole => exact congrArg Sum.inr (tail.siteToLeaf_leafToSite complete.2 hole)

theorem CKBranchCut.siteToLeaf_leafToSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (complete : tree.IsComplete) → (hole : cut.remainder.LeafOccurrence) →
    cut.siteToLeaf (cut.leafToSite complete hole) = hole
  | _, _, .detach _, _, hole => by cases hole; rfl
  | _, _, .descend cut, complete, hole => cut.siteToLeaf_leafToSite complete hole

end

/-- Actual remainder holes and selected sites are equivalent, not merely
equal in number.  The hypothesis excludes inherited source interfaces. -/
def CKCutPlan.completeHoleEquiv {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCutPlan tree)
    (complete : tree.IsComplete) : cut.remainder.LeafOccurrence ≃ cut.Site where
  toFun := cut.leafToSite complete
  invFun := cut.siteToLeaf
  left_inv := cut.siteToLeaf_leafToSite complete
  right_inv := cut.leafToSite_siteToLeaf complete

def CKBranchCut.completeHoleEquiv {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree)
    (complete : tree.IsComplete) : cut.remainder.LeafOccurrence ≃ cut.Site where
  toFun := cut.leafToSite complete
  invFun := cut.siteToLeaf
  left_inv := cut.siteToLeaf_leafToSite complete
  right_inv := cut.leafToSite_siteToLeaf complete

def CKCut.completeHoleEquiv {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCut tree)
    (complete : tree.IsComplete) : cut.remainder.LeafOccurrence ≃ cut.Site :=
  cut.plan.completeHoleEquiv complete

mutual

theorem CKCutPlan.siteToLeaf_boundary : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (site : cut.Site) →
    cut.remainder.leafBoundary (cut.siteToLeaf site) = cut.siteBoundary site
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary _ _ cuts, site => cuts.siteToLeaf_boundary site

theorem CKChildCuts.siteToLeaf_boundary : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (site : cuts.Site) →
    cuts.remainder.leafBoundary (cuts.siteToLeaf site) = cuts.siteBoundary site
  | _, _, .nil, site => nomatch site
  | _, _, .cons _ _ head tail, site => by
      cases site with
      | inl site => exact head.siteToLeaf_boundary site
      | inr site => exact tail.siteToLeaf_boundary site

theorem CKBranchCut.siteToLeaf_boundary : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (site : cut.Site) →
    cut.remainder.leafBoundary (cut.siteToLeaf site) = cut.siteBoundary site
  | _, _, .detach _, _ => rfl
  | _, _, .descend cut, site => cut.siteToLeaf_boundary site

end

mutual

theorem CKCutPlan.siteToLeaf_address : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (site : cut.Site) →
    cut.remainder.leafAddress (cut.siteToLeaf site) = cut.address site
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary _ _ cuts, site => cuts.siteToLeaf_address site

theorem CKChildCuts.siteToLeaf_address : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (site : cuts.Site) →
    cuts.remainder.leafAddress (cuts.siteToLeaf site) = cuts.address site
  | _, _, .nil, site => nomatch site
  | _, _, .cons _ _ head tail, site => by
      cases site with
      | inl site => exact congrArg (List.cons 0) (head.siteToLeaf_address site)
      | inr site => exact congrArg InternalAddress.shiftHead (tail.siteToLeaf_address site)

theorem CKBranchCut.siteToLeaf_address : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (site : cut.Site) →
    cut.remainder.leafAddress (cut.siteToLeaf site) = cut.relativeAddress site
  | _, _, .detach _, _ => rfl
  | _, _, .descend cut, site => cut.siteToLeaf_address site

end

theorem CKCutPlan.leafToSite_boundary {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCutPlan tree)
    (complete : tree.IsComplete) (hole : cut.remainder.LeafOccurrence) :
    cut.remainder.leafBoundary hole = cut.siteBoundary (cut.leafToSite complete hole) := by
  simpa only [cut.siteToLeaf_leafToSite complete hole] using
    cut.siteToLeaf_boundary (cut.leafToSite complete hole)

theorem CKBranchCut.leafToSite_boundary {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree)
    (complete : tree.IsComplete) (hole : cut.remainder.LeafOccurrence) :
    cut.remainder.leafBoundary hole = cut.siteBoundary (cut.leafToSite complete hole) := by
  simpa only [cut.siteToLeaf_leafToSite complete hole] using
    cut.siteToLeaf_boundary (cut.leafToSite complete hole)

theorem CKBranchCut.leafToSite_address {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree)
    (complete : tree.IsComplete) (hole : cut.remainder.LeafOccurrence) :
    cut.remainder.leafAddress hole = cut.relativeAddress (cut.leafToSite complete hole) := by
  simpa only [cut.siteToLeaf_leafToSite complete hole] using
    cut.siteToLeaf_address (cut.leafToSite complete hole)

mutual

/-- The original detached family viewed at native physical remainder holes.
This definition is constructor-wise, avoiding arbitrary boundary casts. -/
def CKCutPlan.detachedLeafAssignment : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    tree.IsComplete → cut.remainder.LeafAssignment
  | _, _, .interface _, complete, _ => False.elim complete
  | _, _, .ordinary _ _ cuts, complete, hole => cuts.detachedLeafAssignment complete hole

def CKChildCuts.detachedLeafAssignment : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    children.IsComplete → cuts.remainder.LeafAssignment
  | _, _, .nil, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, complete, hole =>
      match hole with
      | .inl hole => head.detachedLeafAssignment complete.1 hole
      | .inr hole => tail.detachedLeafAssignment complete.2 hole

def CKBranchCut.detachedLeafAssignment : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    tree.IsComplete → cut.remainder.LeafAssignment
  | _, tree, .detach _, _, _ => tree
  | _, _, .descend cut, complete, hole => cut.detachedLeafAssignment complete hole

end

mutual

/-- The assignment is the actual aligned native factor, not a collected forest. -/
theorem CKCutPlan.detachedLeafAssignment_atSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (complete : tree.IsComplete) → (site : cut.Site) →
    HEq (cut.detachedLeafAssignment complete (cut.siteToLeaf site)) (cut.detached site)
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ cuts, complete, site =>
      cuts.detachedLeafAssignment_atSite complete site

theorem CKChildCuts.detachedLeafAssignment_atSite : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (complete : children.IsComplete) → (site : cuts.Site) →
    HEq (cuts.detachedLeafAssignment complete (cuts.siteToLeaf site)) (cuts.detached site)
  | _, _, .nil, _, site => nomatch site
  | _, _, .cons _ _ head tail, complete, site => by
      cases site with
      | inl site => exact head.detachedLeafAssignment_atSite complete.1 site
      | inr site => exact tail.detachedLeafAssignment_atSite complete.2 site

theorem CKBranchCut.detachedLeafAssignment_atSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (complete : tree.IsComplete) → (site : cut.Site) →
    HEq (cut.detachedLeafAssignment complete (cut.siteToLeaf site)) (cut.detached site)
  | _, _, .detach _, _, _ => HEq.rfl
  | _, _, .descend cut, complete, site => cut.detachedLeafAssignment_atSite complete site

end

mutual

/-- Simultaneous native all-hole filling reconstructs the literal source. -/
theorem CKCutPlan.fillAssignment_detached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (complete : tree.IsComplete) →
    cut.remainder.fillAssignment (cut.detachedLeafAssignment complete) = tree
  | _, _, .interface _, complete => False.elim complete
  | _, _, .ordinary o _ cuts, complete =>
      congrArg (CKTree.ordinary o) (cuts.fillAssignment_detached complete)

theorem CKChildCuts.fillAssignment_detached : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (complete : children.IsComplete) →
    cuts.remainder.fillAssignment (cuts.detachedLeafAssignment complete) = children
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail headCut tailCuts, complete => by
      change CKChildren.cons
        (headCut.remainder.fillAssignment (headCut.detachedLeafAssignment complete.1))
        (tailCuts.remainder.fillAssignment (tailCuts.detachedLeafAssignment complete.2)) =
          CKChildren.cons head tail
      rw [headCut.fillAssignment_detached complete.1, tailCuts.fillAssignment_detached complete.2]

theorem CKBranchCut.fillAssignment_detached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (complete : tree.IsComplete) →
    cut.remainder.fillAssignment (cut.detachedLeafAssignment complete) = tree
  | _, _, .detach _, _ => rfl
  | _, _, .descend cut, complete => cut.fillAssignment_detached complete

end

theorem CKCut.fillAssignment_detached {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCut tree)
    (complete : tree.IsComplete) :
    cut.remainder.fillAssignment (cut.plan.detachedLeafAssignment complete) = tree :=
  cut.plan.fillAssignment_detached complete

mutual

theorem CKCutPlan.detached_isComplete : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    tree.IsComplete → (site : cut.Site) → (cut.detached site).IsComplete
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ cuts, complete, site => cuts.detached_isComplete complete site

theorem CKChildCuts.detached_isComplete : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    children.IsComplete → (site : cuts.Site) → (cuts.detached site).IsComplete
  | _, _, .nil, _, site => nomatch site
  | _, _, .cons _ _ head tail, complete, site => by
      cases site with
      | inl site => exact head.detached_isComplete complete.1 site
      | inr site => exact tail.detached_isComplete complete.2 site

theorem CKBranchCut.detached_isComplete : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    tree.IsComplete → (site : cut.Site) → (cut.detached site).IsComplete
  | _, _, .detach _, complete, _ => complete
  | _, _, .descend cut, complete, site => cut.detached_isComplete complete site

end

/-! ## Native interfaces of a simultaneously filled open tree

Unlike the complete-source cut adapter above, these occurrence maps allow
arbitrary open sources and open fillers.  An interface in the filled tree is
indexed by its original physical hole and its physical occurrence inside that
hole's filler.  This is the native reindexing required by nested gluing.
-/

mutual

def CKTree.fillLeafSplit : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
    (tree.fillAssignment assignment).LeafOccurrence →
      (Σ hole : tree.LeafOccurrence, (assignment hole).LeafOccurrence)
  | G, .interface _, _, inner =>
      ⟨(PUnit.unit : (CKTree.interface G : CKTree sigma InstanceData G).LeafOccurrence), inner⟩
  | _, .ordinary _ children, assignment, inner => children.fillLeafSplit assignment inner

def CKChildren.fillLeafSplit : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (assignment : children.LeafAssignment) →
    (children.fillAssignment assignment).LeafOccurrence →
      (Σ hole : children.LeafOccurrence, (assignment hole).LeafOccurrence)
  | _, .nil, _, inner => nomatch inner
  | _, .cons head tail, assignment, inner =>
      match inner with
      | .inl inner =>
          let pair := head.fillLeafSplit (fun h => assignment (.inl h)) inner
          ⟨.inl pair.1, pair.2⟩
      | .inr inner =>
          let pair := tail.fillLeafSplit (fun h => assignment (.inr h)) inner
          ⟨.inr pair.1, pair.2⟩

end

mutual

def CKTree.fillLeafJoin : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
    (Σ hole : tree.LeafOccurrence, (assignment hole).LeafOccurrence) →
      (tree.fillAssignment assignment).LeafOccurrence
  | _, .interface _, _, pair => by
      rcases pair with ⟨hole, inner⟩
      cases hole
      exact inner
  | _, .ordinary _ children, assignment, pair => children.fillLeafJoin assignment pair

def CKChildren.fillLeafJoin : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (assignment : children.LeafAssignment) →
    (Σ hole : children.LeafOccurrence, (assignment hole).LeafOccurrence) →
      (children.fillAssignment assignment).LeafOccurrence
  | _, .nil, _, ⟨hole, _⟩ => nomatch hole
  | _, .cons head tail, assignment, ⟨hole, inner⟩ =>
      match hole with
      | .inl hole => .inl (head.fillLeafJoin (fun h => assignment (.inl h)) ⟨hole, inner⟩)
      | .inr hole => .inr (tail.fillLeafJoin (fun h => assignment (.inr h)) ⟨hole, inner⟩)

end

mutual

theorem CKTree.fillLeafJoin_split : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
    (inner : (tree.fillAssignment assignment).LeafOccurrence) →
    tree.fillLeafJoin assignment (tree.fillLeafSplit assignment inner) = inner
  | _, .interface _, _, _ => rfl
  | _, .ordinary _ children, assignment, inner => children.fillLeafJoin_split assignment inner

theorem CKChildren.fillLeafJoin_split : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (assignment : children.LeafAssignment) →
    (inner : (children.fillAssignment assignment).LeafOccurrence) →
    children.fillLeafJoin assignment (children.fillLeafSplit assignment inner) = inner
  | _, .nil, _, inner => nomatch inner
  | _, .cons head tail, assignment, inner => by
      cases inner with
      | inl inner =>
          exact congrArg Sum.inl (head.fillLeafJoin_split (fun h => assignment (.inl h)) inner)
      | inr inner =>
          exact congrArg Sum.inr (tail.fillLeafJoin_split (fun h => assignment (.inr h)) inner)

end

mutual

theorem CKTree.fillLeafSplit_join : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
    (pair : Σ hole : tree.LeafOccurrence, (assignment hole).LeafOccurrence) →
    tree.fillLeafSplit assignment (tree.fillLeafJoin assignment pair) = pair
  | _, .interface _, _, ⟨hole, inner⟩ => by cases hole; rfl
  | _, .ordinary _ children, assignment, pair => children.fillLeafSplit_join assignment pair

theorem CKChildren.fillLeafSplit_join : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (assignment : children.LeafAssignment) →
    (pair : Σ hole : children.LeafOccurrence, (assignment hole).LeafOccurrence) →
    children.fillLeafSplit assignment (children.fillLeafJoin assignment pair) = pair
  | _, .nil, _, ⟨hole, _⟩ => nomatch hole
  | _, .cons head tail, assignment, ⟨hole, inner⟩ => by
      cases hole with
      | inl hole =>
          let embed := fun (pair : Σ h : head.LeafOccurrence,
              (assignment (.inl h)).LeafOccurrence) =>
            (⟨Sum.inl pair.1, pair.2⟩ :
              Σ h : head.LeafOccurrence ⊕ tail.LeafOccurrence,
                (assignment h).LeafOccurrence)
          change embed (head.fillLeafSplit (fun h => assignment (.inl h))
            (head.fillLeafJoin (fun h => assignment (.inl h)) ⟨hole, inner⟩)) =
              embed ⟨hole, inner⟩
          exact congrArg embed
            (head.fillLeafSplit_join (fun h => assignment (.inl h)) ⟨hole, inner⟩)
      | inr hole =>
          let embed := fun (pair : Σ h : tail.LeafOccurrence,
              (assignment (.inr h)).LeafOccurrence) =>
            (⟨Sum.inr pair.1, pair.2⟩ :
              Σ h : head.LeafOccurrence ⊕ tail.LeafOccurrence,
                (assignment h).LeafOccurrence)
          change embed (tail.fillLeafSplit (fun h => assignment (.inr h))
            (tail.fillLeafJoin (fun h => assignment (.inr h)) ⟨hole, inner⟩)) =
              embed ⟨hole, inner⟩
          exact congrArg embed
            (tail.fillLeafSplit_join (fun h => assignment (.inr h)) ⟨hole, inner⟩)

end

def CKTree.filledLeafEquiv {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) (assignment : tree.LeafAssignment) :
    (tree.fillAssignment assignment).LeafOccurrence ≃
      (Σ hole : tree.LeafOccurrence, (assignment hole).LeafOccurrence) where
  toFun := tree.fillLeafSplit assignment
  invFun := tree.fillLeafJoin assignment
  left_inv := tree.fillLeafJoin_split assignment
  right_inv := tree.fillLeafSplit_join assignment

def CKChildren.filledLeafEquiv {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData Gs) (assignment : children.LeafAssignment) :
    (children.fillAssignment assignment).LeafOccurrence ≃
      (Σ hole : children.LeafOccurrence, (assignment hole).LeafOccurrence) where
  toFun := children.fillLeafSplit assignment
  invFun := children.fillLeafJoin assignment
  left_inv := children.fillLeafJoin_split assignment
  right_inv := children.fillLeafSplit_join assignment

mutual

theorem CKTree.fillLeafJoin_boundary : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
    (hole : tree.LeafOccurrence) → (inner : (assignment hole).LeafOccurrence) →
    (tree.fillAssignment assignment).leafBoundary (tree.fillLeafJoin assignment ⟨hole, inner⟩) =
      (assignment hole).leafBoundary inner
  | _, .interface _, _, hole, _ => by cases hole; rfl
  | _, .ordinary _ children, assignment, hole, inner =>
      children.fillLeafJoin_boundary assignment hole inner

theorem CKChildren.fillLeafJoin_boundary : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (assignment : children.LeafAssignment) →
    (hole : children.LeafOccurrence) → (inner : (assignment hole).LeafOccurrence) →
    (children.fillAssignment assignment).leafBoundary (children.fillLeafJoin assignment ⟨hole, inner⟩) =
      (assignment hole).leafBoundary inner
  | _, .nil, _, hole, _ => nomatch hole
  | _, .cons head tail, assignment, hole, inner => by
      cases hole with
      | inl hole => exact head.fillLeafJoin_boundary (fun h => assignment (.inl h)) hole inner
      | inr hole => exact tail.fillLeafJoin_boundary (fun h => assignment (.inr h)) hole inner

end

theorem CKChildren.leafAddress_ne_nil : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (hole : children.LeafOccurrence) →
    children.leafAddress hole ≠ []
  | _, .nil, hole => nomatch hole
  | _, .cons _ tail, hole => by
      cases hole with
      | inl hole => simp [CKChildren.leafAddress]
      | inr hole =>
          have nonempty := tail.leafAddress_ne_nil hole
          cases equation : tail.leafAddress hole with
          | nil => exact False.elim (nonempty equation)
          | cons slot rest => simp [CKChildren.leafAddress, equation,
              InternalAddress.shiftHead_cons]

mutual

/-- Absolute inner addresses retain the original physical interface prefix. -/
theorem CKTree.fillLeafJoin_address : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
    (hole : tree.LeafOccurrence) → (inner : (assignment hole).LeafOccurrence) →
    (tree.fillAssignment assignment).leafAddress (tree.fillLeafJoin assignment ⟨hole, inner⟩) =
      tree.leafAddress hole ++ (assignment hole).leafAddress inner
  | _, .interface _, _, hole, _ => by cases hole; rfl
  | _, .ordinary _ children, assignment, hole, inner =>
      children.fillLeafJoin_address assignment hole inner

theorem CKChildren.fillLeafJoin_address : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (assignment : children.LeafAssignment) →
    (hole : children.LeafOccurrence) → (inner : (assignment hole).LeafOccurrence) →
    (children.fillAssignment assignment).leafAddress (children.fillLeafJoin assignment ⟨hole, inner⟩) =
      children.leafAddress hole ++ (assignment hole).leafAddress inner
  | _, .nil, _, hole, _ => nomatch hole
  | _, .cons head tail, assignment, hole, inner => by
      cases hole with
      | inl hole =>
          exact congrArg (List.cons 0)
            (head.fillLeafJoin_address (fun h => assignment (.inl h)) hole inner)
      | inr hole =>
          change InternalAddress.shiftHead
            ((tail.fillAssignment (fun h => assignment (.inr h))).leafAddress
              (tail.fillLeafJoin (fun h => assignment (.inr h)) ⟨hole, inner⟩)) =
            InternalAddress.shiftHead (tail.leafAddress hole) ++
              (assignment (.inr hole)).leafAddress inner
          rw [tail.fillLeafJoin_address]
          exact InternalAddress.shiftHead_append_of_ne_nil _ _ (tail.leafAddress_ne_nil hole)

end

/-- The actual native boundary-aligned second filling after reindexing its
physical holes; no address is reconstructed from collected coefficients. -/
def CKTree.composeLeafAssignment {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) (first : tree.LeafAssignment)
    (second : (tree.fillAssignment first).LeafAssignment) : tree.LeafAssignment :=
  fun hole => (first hole).fillAssignment (fun inner =>
    Eq.mp (congrArg (CKTree sigma InstanceData) (tree.fillLeafJoin_boundary first hole inner))
      (second (tree.fillLeafJoin first ⟨hole, inner⟩)))

def CKChildren.composeLeafAssignment {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData Gs) (first : children.LeafAssignment)
    (second : (children.fillAssignment first).LeafAssignment) : children.LeafAssignment :=
  fun hole => (first hole).fillAssignment (fun inner =>
    Eq.mp (congrArg (CKTree sigma InstanceData) (children.fillLeafJoin_boundary first hole inner))
      (second (children.fillLeafJoin first ⟨hole, inner⟩)))

mutual

/-- Literal native filling associativity, using the preceding occurrence
equivalence rather than an assumed or coefficient-level composition law. -/
theorem CKTree.fillAssignment_assoc : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (first : tree.LeafAssignment) →
    (second : (tree.fillAssignment first).LeafAssignment) →
    (tree.fillAssignment first).fillAssignment second =
      tree.fillAssignment (tree.composeLeafAssignment first second)
  | _, .interface _, _, _ => rfl
  | _, .ordinary o children, first, second =>
      congrArg (CKTree.ordinary o) (children.fillAssignment_assoc first second)

theorem CKChildren.fillAssignment_assoc : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (first : children.LeafAssignment) →
    (second : (children.fillAssignment first).LeafAssignment) →
    (children.fillAssignment first).fillAssignment second =
      children.fillAssignment (children.composeLeafAssignment first second)
  | _, .nil, _, _ => rfl
  | _, .cons head tail, first, second => by
      change CKChildren.cons
        ((head.fillAssignment (fun h => first (.inl h))).fillAssignment (fun h => second (.inl h)))
        ((tail.fillAssignment (fun h => first (.inr h))).fillAssignment (fun h => second (.inr h))) =
        CKChildren.cons
          (head.fillAssignment (head.composeLeafAssignment (fun h => first (.inl h))
            (fun h => second (.inl h))))
          (tail.fillAssignment (tail.composeLeafAssignment (fun h => first (.inr h))
            (fun h => second (.inr h))))
      rw [head.fillAssignment_assoc, tail.fillAssignment_assoc]

end

end Potkin

#check Potkin.CKCut.completeHoleEquiv
#check Potkin.CKBranchCut.completeHoleEquiv
#print axioms Potkin.CKCutPlan.completeHoleEquiv
#print axioms Potkin.CKBranchCut.completeHoleEquiv
#print axioms Potkin.CKCutPlan.siteToLeaf_boundary
#print axioms Potkin.CKBranchCut.siteToLeaf_address
#print axioms Potkin.CKBranchCut.detachedLeafAssignment_atSite
#print axioms Potkin.CKCut.fillAssignment_detached
#check Potkin.CKTree.filledLeafEquiv
#print axioms Potkin.CKTree.filledLeafEquiv
#print axioms Potkin.CKTree.fillLeafJoin_boundary
#print axioms Potkin.CKTree.fillLeafJoin_address
#print axioms Potkin.CKTree.fillAssignment_assoc
#print axioms Potkin.CKBranchCut.detached_isComplete

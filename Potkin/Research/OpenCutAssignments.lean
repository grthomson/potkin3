import Potkin.Research.CutHoleAdapter

/-!
# Native cut reconstruction with inherited interfaces

The complete-source adapter is not applicable to an arbitrary open derivation:
an inherited interface need not be a selected cut site.  This additive adapter
fills cut-created vacancies by their aligned factors and leaves inherited
vacancies as the same typed `Box`.  All carriers are the existing native ones.
-/

namespace Potkin

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual

/-- Whether this remainder interface was created by the cut.  `none` means
an inherited source interface, not an unaddressed selected vertex. -/
def CKCutPlan.remainderLeafOrigin : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    cut.remainder.LeafOccurrence → Option cut.Site
  | _, _, .interface _, _ => none
  | _, _, .ordinary _ _ cuts, hole => cuts.remainderLeafOrigin hole

def CKChildCuts.remainderLeafOrigin : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    cuts.remainder.LeafOccurrence → Option cuts.Site
  | _, _, .nil, hole => nomatch hole
  | _, _, .cons _ _ head tail, hole =>
      match hole with
      | .inl hole => (head.remainderLeafOrigin hole).map Sum.inl
      | .inr hole => (tail.remainderLeafOrigin hole).map Sum.inr

def CKBranchCut.remainderLeafOrigin : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    cut.remainder.LeafOccurrence → Option cut.Site
  | _, _, .detach _, _ => some PUnit.unit
  | _, _, .descend cut, hole => cut.remainderLeafOrigin hole

end

mutual

/-- An open reconstruction assignment retains inherited typed holes. -/
def CKCutPlan.openDetachedAssignment : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    cut.remainder.LeafAssignment
  | G, _, .interface _, _ => .interface G
  | _, _, .ordinary _ _ cuts, hole => cuts.openDetachedAssignment hole

def CKChildCuts.openDetachedAssignment : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    cuts.remainder.LeafAssignment
  | _, _, .nil, hole => nomatch hole
  | _, _, .cons _ _ head tail, hole =>
      match hole with
      | .inl hole => head.openDetachedAssignment hole
      | .inr hole => tail.openDetachedAssignment hole

def CKBranchCut.openDetachedAssignment : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    cut.remainder.LeafAssignment
  | _, tree, .detach _, _ => tree
  | _, _, .descend cut, hole => cut.openDetachedAssignment hole

end

mutual

theorem CKCutPlan.remainderLeafOrigin_atSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (site : cut.Site) → cut.remainderLeafOrigin (cut.siteToLeaf site) = some site
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary _ _ cuts, site => cuts.remainderLeafOrigin_atSite site

theorem CKChildCuts.remainderLeafOrigin_atSite : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (site : cuts.Site) → cuts.remainderLeafOrigin (cuts.siteToLeaf site) = some site
  | _, _, .nil, site => nomatch site
  | _, _, .cons _ _ head tail, site => by
      cases site with
      | inl site =>
          change (head.remainderLeafOrigin (head.siteToLeaf site)).map Sum.inl = _
          rw [head.remainderLeafOrigin_atSite]
          rfl
      | inr site =>
          change (tail.remainderLeafOrigin (tail.siteToLeaf site)).map Sum.inr = _
          rw [tail.remainderLeafOrigin_atSite]
          rfl

theorem CKBranchCut.remainderLeafOrigin_atSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (site : cut.Site) → cut.remainderLeafOrigin (cut.siteToLeaf site) = some site
  | _, _, .detach _, site => by cases site; rfl
  | _, _, .descend cut, site => cut.remainderLeafOrigin_atSite site

end

mutual

/-- The selected-site callback is exactly its native ordered factor. -/
theorem CKCutPlan.openDetachedAssignment_atSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (site : cut.Site) →
    HEq (cut.openDetachedAssignment (cut.siteToLeaf site)) (cut.detached site)
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary _ _ cuts, site => cuts.openDetachedAssignment_atSite site

theorem CKChildCuts.openDetachedAssignment_atSite : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (site : cuts.Site) →
    HEq (cuts.openDetachedAssignment (cuts.siteToLeaf site)) (cuts.detached site)
  | _, _, .nil, site => nomatch site
  | _, _, .cons _ _ head tail, site => by
      cases site with
      | inl site => exact head.openDetachedAssignment_atSite site
      | inr site => exact tail.openDetachedAssignment_atSite site

theorem CKBranchCut.openDetachedAssignment_atSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (site : cut.Site) →
    HEq (cut.openDetachedAssignment (cut.siteToLeaf site)) (cut.detached site)
  | _, _, .detach _, _ => HEq.rfl
  | _, _, .descend cut, site => cut.openDetachedAssignment_atSite site

end

mutual

/-- Literal native reconstruction, with no completeness assumption. -/
theorem CKCutPlan.fillAssignment_openDetached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    cut.remainder.fillAssignment cut.openDetachedAssignment = tree
  | _, _, .interface _ => rfl
  | _, _, .ordinary o _ cuts =>
      congrArg (CKTree.ordinary o) cuts.fillAssignment_openDetached

theorem CKChildCuts.fillAssignment_openDetached : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    cuts.remainder.fillAssignment cuts.openDetachedAssignment = children
  | _, _, .nil => rfl
  | _, _, .cons head tail headCut tailCuts => by
      change CKChildren.cons
        (headCut.remainder.fillAssignment headCut.openDetachedAssignment)
        (tailCuts.remainder.fillAssignment tailCuts.openDetachedAssignment) =
          CKChildren.cons head tail
      rw [headCut.fillAssignment_openDetached, tailCuts.fillAssignment_openDetached]

theorem CKBranchCut.fillAssignment_openDetached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    cut.remainder.fillAssignment cut.openDetachedAssignment = tree
  | _, _, .detach _ => rfl
  | _, _, .descend cut => cut.fillAssignment_openDetached

end

/- Inherited vacancies are left as their native typed `Box`, not replaced by
a proof or by an algebraic unit. -/
mutual

theorem CKCutPlan.openDetachedAssignment_inherited : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    (hole : cut.remainder.LeafOccurrence) → cut.remainderLeafOrigin hole = none →
    cut.openDetachedAssignment hole = .interface (cut.remainder.leafBoundary hole)
  | _, _, .interface _, _, _ => rfl
  | _, _, .ordinary _ _ cuts, hole, inherited =>
      cuts.openDetachedAssignment_inherited hole inherited

theorem CKChildCuts.openDetachedAssignment_inherited : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    (hole : cuts.remainder.LeafOccurrence) → cuts.remainderLeafOrigin hole = none →
    cuts.openDetachedAssignment hole = .interface (cuts.remainder.leafBoundary hole)
  | _, _, .nil, hole, _ => nomatch hole
  | _, _, .cons _ _ head tail, hole, inherited => by
      cases hole with
      | inl hole =>
          apply head.openDetachedAssignment_inherited hole
          change (head.remainderLeafOrigin hole).map Sum.inl = none at inherited
          cases origin : head.remainderLeafOrigin hole with
          | none => rfl
          | some site => simp [origin] at inherited
      | inr hole =>
          apply tail.openDetachedAssignment_inherited hole
          change (tail.remainderLeafOrigin hole).map Sum.inr = none at inherited
          cases origin : tail.remainderLeafOrigin hole with
          | none => rfl
          | some site => simp [origin] at inherited

theorem CKBranchCut.openDetachedAssignment_inherited : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    (hole : cut.remainder.LeafOccurrence) → cut.remainderLeafOrigin hole = none →
    cut.openDetachedAssignment hole = .interface (cut.remainder.leafBoundary hole)
  | _, _, .detach _, _, inherited => by cases inherited
  | _, _, .descend cut, hole, inherited =>
      cut.openDetachedAssignment_inherited hole inherited

end

theorem CKCut.fillAssignment_openDetached {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCut tree) :
    cut.remainder.fillAssignment cut.plan.openDetachedAssignment = tree :=
  cut.plan.fillAssignment_openDetached

end Potkin

#check Potkin.CKBranchCut.fillAssignment_openDetached
#print axioms Potkin.CKBranchCut.fillAssignment_openDetached
#print axioms Potkin.CKBranchCut.openDetachedAssignment_atSite
#print axioms Potkin.CKBranchCut.remainderLeafOrigin_atSite
#print axioms Potkin.CKBranchCut.openDetachedAssignment_inherited

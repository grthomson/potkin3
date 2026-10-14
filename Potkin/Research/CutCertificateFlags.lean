import Potkin.Research.CutHoleAdapter
import Potkin.CompositeCutExpansion

/-!
# Native compatible inside-factor cut flags

The first cut is an existing native installation. A second full branch cut is
given in each addressed detached factor. Retained outer vertices are traversed
without selecting an ancestor. The choices below are the existing composite
cut expansion index, not another cut or hierarchy carrier.

The one-shot cut lives on the actual installed source `first.fill first.detached`,
whose literal equality with the original source is already proved natively.
Whole selections are still `CKBranchCut.detach`, never fabricated public root
cuts. This scope is nested inside-factor flags, not all arbitrary noncrossing
two-cut schedules.
-/

namespace Potkin
universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual

def CKCutPlan.insideChoices : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    ((site : first.Site) → CKBranchCut (first.detached site)) →
      first.ExpansionChoices first.detached
  | _, _, .interface _, _ => PUnit.unit
  | _, _, .ordinary _ _ children, lower => children.insideChoices lower

def CKChildCuts.insideChoices : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    ((site : first.Site) → CKBranchCut (first.detached site)) →
      first.ExpansionChoices first.detached
  | _, _, .nil, _ => PUnit.unit
  | _, _, .cons _ _ head tail, lower =>
      (head.insideChoices (fun i => lower (.inl i)),
        tail.insideChoices (fun i => lower (.inr i)))

def CKBranchCut.insideChoices : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    ((site : first.Site) → CKBranchCut (first.detached site)) →
      first.ExpansionChoices first.detached
  | _, _, .detach _, lower => lower PUnit.unit
  | _, _, .descend plan, lower => by
      cases plan with
      | interface _ => exact PUnit.unit
      | ordinary _ _ children => exact .inr (children.insideChoices lower)

end

def CKCutPlan.insideCombined {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (first : CKCutPlan tree)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    CKCutPlan (first.fill first.detached) :=
  first.expandCut first.detached (first.insideChoices lower)

def CKChildCuts.insideCombined {Gs : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData Gs} (first : CKChildCuts children)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    CKChildCuts (first.fill first.detached) :=
  first.expandCut first.detached (first.insideChoices lower)

def CKBranchCut.insideCombined {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (first : CKBranchCut tree)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    CKBranchCut (first.fill first.detached) :=
  first.expandCut first.detached (first.insideChoices lower)

/-- The actual native composite-cut equivalence, with the concrete flag
choices as its inverse input; no coherence is postulated here. -/
theorem CKCutPlan.insideCombined_nativeEquiv {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (first : CKCutPlan tree)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    (first.compositeCutEquiv first.detached).symm (first.insideChoices lower) =
      first.insideCombined lower := rfl

theorem CKCutPlan.insideCombined_decompose {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (first : CKCutPlan tree)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    first.decomposeCut first.detached (first.insideCombined lower) =
      first.insideChoices lower :=
  first.decompose_expand first.detached (first.insideChoices lower)

mutual

/-- The one-shot remainder is the first remainder filled with the actual
open middle remainders, including every inherited interface. -/
theorem CKCutPlan.insideCombined_remainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (first.insideCombined lower).remainder = first.fill (fun i => (lower i).remainder)
  | _, _, .interface _, _ => rfl
  | _, _, .ordinary o _ children, lower =>
      congrArg (CKTree.ordinary o) (children.insideCombined_remainder lower)

theorem CKChildCuts.insideCombined_remainder : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (first.insideCombined lower).remainder = first.fill (fun i => (lower i).remainder)
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail headCut tailCuts, lower => by
      change CKChildren.cons
        ((headCut.insideCombined (fun i => lower (.inl i))).remainder)
        ((tailCuts.insideCombined (fun i => lower (.inr i))).remainder) =
        CKChildren.cons
          (headCut.fill (fun i => (lower (.inl i)).remainder))
          (tailCuts.fill (fun i => (lower (.inr i)).remainder))
      rw [headCut.insideCombined_remainder, tailCuts.insideCombined_remainder] <;> rfl

theorem CKBranchCut.insideCombined_remainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (first.insideCombined lower).remainder = first.fill (fun i => (lower i).remainder)
  | _, _, .detach _, _ => rfl
  | _, _, .descend plan, lower => by
      cases plan with
      | interface _ => rfl
      | ordinary o children cuts =>
          exact congrArg (CKTree.ordinary o) (cuts.insideCombined_remainder lower)

end

mutual

def CKCutPlan.insideSiteSplit : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (first.insideCombined lower).Site → (Σ i : first.Site, (lower i).Site)
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ children, lower, site => children.insideSiteSplit lower site

def CKChildCuts.insideSiteSplit : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (first.insideCombined lower).Site → (Σ i : first.Site, (lower i).Site)
  | _, _, .nil, _, site => nomatch site
  | _, _, .cons _ _ head tail, lower, site =>
      match site with
      | .inl site =>
          let pair := head.insideSiteSplit (fun i => lower (.inl i)) site
          ⟨.inl pair.1, pair.2⟩
      | .inr site =>
          let pair := tail.insideSiteSplit (fun i => lower (.inr i)) site
          ⟨.inr pair.1, pair.2⟩

def CKBranchCut.insideSiteSplit : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (first.insideCombined lower).Site → (Σ i : first.Site, (lower i).Site)
  | _, _, .detach _, _, site => ⟨PUnit.unit, site⟩
  | _, _, .descend plan, lower, site => by
      cases plan with
      | interface _ => exact nomatch site
      | ordinary _ _ children => exact children.insideSiteSplit lower site

end

mutual

def CKCutPlan.insideSiteJoin : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (Σ i : first.Site, (lower i).Site) → (first.insideCombined lower).Site
  | _, _, .interface _, _, ⟨site, _⟩ => nomatch site
  | _, _, .ordinary _ _ children, lower, pair => children.insideSiteJoin lower pair

def CKChildCuts.insideSiteJoin : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (Σ i : first.Site, (lower i).Site) → (first.insideCombined lower).Site
  | _, _, .nil, _, ⟨site, _⟩ => nomatch site
  | _, _, .cons _ _ head tail, lower, ⟨site, inner⟩ =>
      match site with
      | .inl site => .inl (head.insideSiteJoin (fun i => lower (.inl i)) ⟨site, inner⟩)
      | .inr site => .inr (tail.insideSiteJoin (fun i => lower (.inr i)) ⟨site, inner⟩)

def CKBranchCut.insideSiteJoin : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (Σ i : first.Site, (lower i).Site) → (first.insideCombined lower).Site
  | _, _, .detach _, _, pair => by
      rcases pair with ⟨site, inner⟩
      cases site
      exact inner
  | _, _, .descend plan, lower, pair => by
      cases plan with
      | interface _ => exact nomatch pair.1
      | ordinary _ _ children => exact children.insideSiteJoin lower pair

end

mutual

theorem CKCutPlan.insideSiteJoin_split : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : (first.insideCombined lower).Site) →
    first.insideSiteJoin lower (first.insideSiteSplit lower site) = site
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ children, lower, site => children.insideSiteJoin_split lower site

theorem CKChildCuts.insideSiteJoin_split : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : (first.insideCombined lower).Site) →
    first.insideSiteJoin lower (first.insideSiteSplit lower site) = site
  | _, _, .nil, _, site => nomatch site
  | _, _, .cons _ _ head tail, lower, site => by
      cases site with
      | inl site => exact congrArg Sum.inl (head.insideSiteJoin_split (fun i => lower (.inl i)) site)
      | inr site => exact congrArg Sum.inr (tail.insideSiteJoin_split (fun i => lower (.inr i)) site)

theorem CKBranchCut.insideSiteJoin_split : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : (first.insideCombined lower).Site) →
    first.insideSiteJoin lower (first.insideSiteSplit lower site) = site
  | _, _, .detach _, _, _ => rfl
  | _, _, .descend plan, lower, site => by
      cases plan with
      | interface _ => exact nomatch site
      | ordinary _ _ children => exact children.insideSiteJoin_split lower site

end

mutual

theorem CKCutPlan.insideSiteSplit_join : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (pair : Σ i : first.Site, (lower i).Site) →
    first.insideSiteSplit lower (first.insideSiteJoin lower pair) = pair
  | _, _, .interface _, _, ⟨site, _⟩ => nomatch site
  | _, _, .ordinary _ _ children, lower, pair => children.insideSiteSplit_join lower pair

theorem CKChildCuts.insideSiteSplit_join : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (pair : Σ i : first.Site, (lower i).Site) →
    first.insideSiteSplit lower (first.insideSiteJoin lower pair) = pair
  | _, _, .nil, _, ⟨site, _⟩ => nomatch site
  | _, _, .cons _ _ head tail, lower, ⟨site, inner⟩ => by
      cases site with
      | inl site =>
          let embed := fun (pair : Σ i : head.Site, (lower (.inl i)).Site) =>
            (⟨Sum.inl pair.1, pair.2⟩ : Σ i : head.Site ⊕ tail.Site, (lower i).Site)
          change embed (head.insideSiteSplit (fun i => lower (.inl i))
            (head.insideSiteJoin (fun i => lower (.inl i)) ⟨site, inner⟩)) = embed ⟨site, inner⟩
          exact congrArg embed (head.insideSiteSplit_join (fun i => lower (.inl i)) ⟨site, inner⟩)
      | inr site =>
          let embed := fun (pair : Σ i : tail.Site, (lower (.inr i)).Site) =>
            (⟨Sum.inr pair.1, pair.2⟩ : Σ i : head.Site ⊕ tail.Site, (lower i).Site)
          change embed (tail.insideSiteSplit (fun i => lower (.inr i))
            (tail.insideSiteJoin (fun i => lower (.inr i)) ⟨site, inner⟩)) = embed ⟨site, inner⟩
          exact congrArg embed (tail.insideSiteSplit_join (fun i => lower (.inr i)) ⟨site, inner⟩)

theorem CKBranchCut.insideSiteSplit_join : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (pair : Σ i : first.Site, (lower i).Site) →
    first.insideSiteSplit lower (first.insideSiteJoin lower pair) = pair
  | _, _, .detach _, _, ⟨site, _⟩ => by cases site; rfl
  | _, _, .descend plan, lower, pair => by
      cases plan with
      | interface _ => exact nomatch pair.1
      | ordinary _ _ children => exact children.insideSiteSplit_join lower pair

end

/-- Occurrence-resolved, multiplicity-preserving reindexing of the actual
one-shot cut into first sites and their ordered lower-cut sites. -/
def CKCutPlan.insideSiteEquiv {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (first : CKCutPlan tree)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    (first.insideCombined lower).Site ≃ (Σ i : first.Site, (lower i).Site) where
  toFun := first.insideSiteSplit lower
  invFun := first.insideSiteJoin lower
  left_inv := first.insideSiteJoin_split lower
  right_inv := first.insideSiteSplit_join lower

mutual

theorem CKCutPlan.insideSiteJoin_address : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    (first.insideCombined lower).address (first.insideSiteJoin lower ⟨site, inner⟩) =
      first.address site ++ (lower site).relativeAddress inner
  | _, _, .interface _, _, site, _ => nomatch site
  | _, _, .ordinary _ _ children, lower, site, inner =>
      children.insideSiteJoin_address lower site inner

theorem CKChildCuts.insideSiteJoin_address : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    (first.insideCombined lower).address (first.insideSiteJoin lower ⟨site, inner⟩) =
      first.address site ++ (lower site).relativeAddress inner
  | _, _, .nil, _, site, _ => nomatch site
  | _, _, .cons _ _ head tail, lower, site, inner => by
      cases site with
      | inl site =>
          exact congrArg (List.cons 0) (head.insideSiteJoin_address (fun i => lower (.inl i)) site inner)
      | inr site =>
          change InternalAddress.shiftHead
            ((tail.insideCombined (fun i => lower (.inr i))).address
              (tail.insideSiteJoin (fun i => lower (.inr i)) ⟨site, inner⟩)) =
            InternalAddress.shiftHead (tail.address site) ++ (lower (.inr site)).relativeAddress inner
          rw [tail.insideSiteJoin_address]
          exact InternalAddress.shiftHead_append_of_ne_nil _ _ (tail.address_nonroot site)

theorem CKBranchCut.insideSiteJoin_address : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    (first.insideCombined lower).relativeAddress (first.insideSiteJoin lower ⟨site, inner⟩) =
      first.relativeAddress site ++ (lower site).relativeAddress inner
  | _, _, .detach _, _, site, _ => by cases site; rfl
  | _, _, .descend plan, lower, site, inner => by
      cases plan with
      | interface _ => exact nomatch site
      | ordinary _ _ children => exact children.insideSiteJoin_address lower site inner

end

mutual

theorem CKCutPlan.insideSiteJoin_boundary : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    (first.insideCombined lower).siteBoundary (first.insideSiteJoin lower ⟨site, inner⟩) =
      (lower site).siteBoundary inner
  | _, _, .interface _, _, site, _ => nomatch site
  | _, _, .ordinary _ _ children, lower, site, inner => children.insideSiteJoin_boundary lower site inner

theorem CKChildCuts.insideSiteJoin_boundary : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    (first.insideCombined lower).siteBoundary (first.insideSiteJoin lower ⟨site, inner⟩) =
      (lower site).siteBoundary inner
  | _, _, .nil, _, site, _ => nomatch site
  | _, _, .cons _ _ head tail, lower, site, inner => by
      cases site with
      | inl site => exact head.insideSiteJoin_boundary (fun i => lower (.inl i)) site inner
      | inr site => exact tail.insideSiteJoin_boundary (fun i => lower (.inr i)) site inner

theorem CKBranchCut.insideSiteJoin_boundary : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    (first.insideCombined lower).siteBoundary (first.insideSiteJoin lower ⟨site, inner⟩) =
      (lower site).siteBoundary inner
  | _, _, .detach _, _, site, _ => by cases site; rfl
  | _, _, .descend plan, lower, site, inner => by
      cases plan with
      | interface _ => exact nomatch site
      | ordinary _ _ children => exact children.insideSiteJoin_boundary lower site inner

end

mutual

theorem CKCutPlan.insideSiteJoin_detached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    HEq ((first.insideCombined lower).detached (first.insideSiteJoin lower ⟨site, inner⟩))
      ((lower site).detached inner)
  | _, _, .interface _, _, site, _ => nomatch site
  | _, _, .ordinary _ _ children, lower, site, inner => children.insideSiteJoin_detached lower site inner

theorem CKChildCuts.insideSiteJoin_detached : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    HEq ((first.insideCombined lower).detached (first.insideSiteJoin lower ⟨site, inner⟩))
      ((lower site).detached inner)
  | _, _, .nil, _, site, _ => nomatch site
  | _, _, .cons _ _ head tail, lower, site, inner => by
      cases site with
      | inl site => exact head.insideSiteJoin_detached (fun i => lower (.inl i)) site inner
      | inr site => exact tail.insideSiteJoin_detached (fun i => lower (.inr i)) site inner

theorem CKBranchCut.insideSiteJoin_detached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) →
    (site : first.Site) → (inner : (lower site).Site) →
    HEq ((first.insideCombined lower).detached (first.insideSiteJoin lower ⟨site, inner⟩))
      ((lower site).detached inner)
  | _, _, .detach _, _, site, _ => by cases site; rfl
  | _, _, .descend plan, lower, site, inner => by
      cases plan with
      | interface _ => exact nomatch site
      | ordinary _ _ children => exact children.insideSiteJoin_detached lower site inner

end

/-! ## All-hole intermediate filling for complete first sources -/

mutual

def CKCutPlan.siteFillersToLeaves : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    tree.IsComplete →
    ((site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
      first.remainder.LeafAssignment
  | _, _, .interface _, complete, _, _ => False.elim complete
  | _, _, .ordinary _ _ children, complete, fillers, hole =>
      children.siteFillersToLeaves complete fillers hole

def CKChildCuts.siteFillersToLeaves : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    children.IsComplete →
    ((site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
      first.remainder.LeafAssignment
  | _, _, .nil, _, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, complete, fillers, hole =>
      match hole with
      | .inl hole => head.siteFillersToLeaves complete.1 (fun i => fillers (.inl i)) hole
      | .inr hole => tail.siteFillersToLeaves complete.2 (fun i => fillers (.inr i)) hole

def CKBranchCut.siteFillersToLeaves : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    tree.IsComplete →
    ((site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
      first.remainder.LeafAssignment
  | _, _, .detach _, _, fillers, _ => fillers PUnit.unit
  | _, _, .descend plan, complete, fillers, hole => plan.siteFillersToLeaves complete fillers hole

end

mutual

theorem CKCutPlan.siteFillersToLeaves_atSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (complete : tree.IsComplete) →
    (fillers : (site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
    (site : first.Site) →
    HEq (first.siteFillersToLeaves complete fillers (first.siteToLeaf site)) (fillers site)
  | _, _, .interface _, _, _, site => nomatch site
  | _, _, .ordinary _ _ children, complete, fillers, site =>
      children.siteFillersToLeaves_atSite complete fillers site

theorem CKChildCuts.siteFillersToLeaves_atSite : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (complete : children.IsComplete) →
    (fillers : (site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
    (site : first.Site) →
    HEq (first.siteFillersToLeaves complete fillers (first.siteToLeaf site)) (fillers site)
  | _, _, .nil, _, _, site => nomatch site
  | _, _, .cons _ _ head tail, complete, fillers, site => by
      cases site with
      | inl site => exact head.siteFillersToLeaves_atSite complete.1 (fun i => fillers (.inl i)) site
      | inr site => exact tail.siteFillersToLeaves_atSite complete.2 (fun i => fillers (.inr i)) site

theorem CKBranchCut.siteFillersToLeaves_atSite : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (complete : tree.IsComplete) →
    (fillers : (site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
    (site : first.Site) →
    HEq (first.siteFillersToLeaves complete fillers (first.siteToLeaf site)) (fillers site)
  | _, _, .detach _, _, _, site => by cases site; rfl
  | _, _, .descend plan, complete, fillers, site => plan.siteFillersToLeaves_atSite complete fillers site

end

mutual

theorem CKCutPlan.siteFillersToLeaves_detached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (complete : tree.IsComplete) →
    first.siteFillersToLeaves complete first.detached = first.detachedLeafAssignment complete
  | _, _, .interface _, complete => False.elim complete
  | _, _, .ordinary _ _ children, complete => children.siteFillersToLeaves_detached complete

theorem CKChildCuts.siteFillersToLeaves_detached : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (complete : children.IsComplete) →
    first.siteFillersToLeaves complete first.detached = first.detachedLeafAssignment complete
  | _, _, .nil, _ => by funext hole; exact nomatch hole
  | _, _, .cons _ _ head tail, complete => by
      funext hole
      cases hole with
      | inl hole => exact congrFun (head.siteFillersToLeaves_detached complete.1) hole
      | inr hole => exact congrFun (tail.siteFillersToLeaves_detached complete.2) hole

theorem CKBranchCut.siteFillersToLeaves_detached : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (complete : tree.IsComplete) →
    first.siteFillersToLeaves complete first.detached = first.detachedLeafAssignment complete
  | _, _, .detach _, _ => rfl
  | _, _, .descend plan, complete => plan.siteFillersToLeaves_detached complete

end

mutual

theorem CKCutPlan.fillAssignment_siteFillers : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKCutPlan tree) →
    (complete : tree.IsComplete) →
    (fillers : (site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
    first.remainder.fillAssignment (first.siteFillersToLeaves complete fillers) = first.fill fillers
  | _, _, .interface _, complete, _ => False.elim complete
  | _, _, .ordinary o _ children, complete, fillers =>
      congrArg (CKTree.ordinary o) (children.fillAssignment_siteFillers complete fillers)

theorem CKChildCuts.fillAssignment_siteFillers : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (first : CKChildCuts children) →
    (complete : children.IsComplete) →
    (fillers : (site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
    first.remainder.fillAssignment (first.siteFillersToLeaves complete fillers) = first.fill fillers
  | _, _, .nil, _, _ => rfl
  | _, _, .cons _ _ head tail, complete, fillers => by
      change CKChildren.cons
        (head.remainder.fillAssignment (head.siteFillersToLeaves complete.1 (fun i => fillers (.inl i))))
        (tail.remainder.fillAssignment (tail.siteFillersToLeaves complete.2 (fun i => fillers (.inr i)))) =
        CKChildren.cons (head.fill (fun i => fillers (.inl i))) (tail.fill (fun i => fillers (.inr i)))
      rw [head.fillAssignment_siteFillers, tail.fillAssignment_siteFillers]

theorem CKBranchCut.fillAssignment_siteFillers : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (first : CKBranchCut tree) →
    (complete : tree.IsComplete) →
    (fillers : (site : first.Site) → CKTree sigma InstanceData (first.siteBoundary site)) →
    first.remainder.fillAssignment (first.siteFillersToLeaves complete fillers) = first.fill fillers
  | _, _, .detach _, _, _ => rfl
  | _, _, .descend plan, complete, fillers => plan.fillAssignment_siteFillers complete fillers

end

theorem CKCutPlan.insideCombined_remainder_allHoles {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (first : CKCutPlan tree)
    (complete : tree.IsComplete)
    (lower : (site : first.Site) → CKBranchCut (first.detached site)) :
    (first.insideCombined lower).remainder =
      first.remainder.fillAssignment
        (first.siteFillersToLeaves complete (fun i => (lower i).remainder)) :=
  (first.insideCombined_remainder lower).trans
    (first.fillAssignment_siteFillers complete (fun i => (lower i).remainder)).symm

end Potkin

#check Potkin.CKCutPlan.insideSiteEquiv
#check Potkin.CKCutPlan.insideCombined_remainder_allHoles
#print axioms Potkin.CKCutPlan.insideCombined_nativeEquiv
#print axioms Potkin.CKCutPlan.insideCombined_decompose
#print axioms Potkin.CKCutPlan.insideSiteEquiv
#print axioms Potkin.CKCutPlan.insideSiteJoin_address
#print axioms Potkin.CKCutPlan.insideSiteJoin_boundary
#print axioms Potkin.CKCutPlan.insideSiteJoin_detached
#print axioms Potkin.CKCutPlan.insideCombined_remainder_allHoles
#print axioms Potkin.CKCutPlan.siteFillersToLeaves_atSite
#print axioms Potkin.CKCutPlan.siteFillersToLeaves_detached

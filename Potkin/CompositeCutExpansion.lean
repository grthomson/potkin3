import Potkin.GeneralFilling
import Potkin.OriginCutCoherence

/-!
# Actual CK cuts after installation of composite payloads

An installation is an existing native cut plan. Its remainder is the typed
template and its site-indexed fillers are the installed modules. The expansion
index below consists only of products and sums of independent choices and
existing native payload cuts; it is not another tree, cut, forest or context
carrier. An old selected ancestor has no choices below it. At an opened site
all choices are actual branch cuts of the full payload, including its root.
-/

namespace Potkin
universe u v w z
variable {sigma : Signature.{u, v}} {InstanceData : Type w} {Origin : Type z}

def CKCutPlan.contents : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → CKCutPlan tree →
      match tree with
      | .interface _ => PUnit.{max (max u v) w + 1}
      | .ordinary _ children => CKChildCuts children
  | _, _, .interface _ => PUnit.unit
  | _, _, .ordinary _ _ cuts => cuts

def CKChildCuts.contents : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → CKChildCuts children →
      match children with
      | .nil => PUnit.{max (max u v) w + 1}
      | .cons head tail => CKBranchCut head × CKChildCuts tail
  | _, _, .nil => PUnit.unit
  | _, _, .cons _ _ head tail => (head, tail)

def CKBranchCut.rootChoice {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} : CKBranchCut tree →
      PUnit.{max (max u v) w + 1} ⊕ CKCutPlan tree
  | .detach _ => .inl PUnit.unit
  | .descend cut => .inr cut

theorem CKCutPlan.contents_reconstructs : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
      (match tree, cut.contents with
      | .interface G, _ => CKCutPlan.interface G
      | .ordinary o children, cuts => CKCutPlan.ordinary o children cuts) = cut
  | _, _, .interface _ => rfl
  | _, _, .ordinary _ _ _ => rfl

theorem CKChildCuts.contents_reconstructs : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cut : CKChildCuts children) →
      (match children, cut.contents with
      | .nil, _ => CKChildCuts.nil
      | .cons head tail, pair => CKChildCuts.cons head tail pair.1 pair.2) = cut
  | _, _, .nil => rfl
  | _, _, .cons _ _ _ _ => rfl

theorem CKBranchCut.rootChoice_reconstructs {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (ordinary : tree.IsOrdinary)
    (cut : CKBranchCut tree) :
    (match cut.rootChoice with
    | .inl _ => CKBranchCut.detach ordinary
    | .inr plan => CKBranchCut.descend plan) = cut := by
  cases cut <;> rfl

theorem CKBranchCut.interface_unique {G : Hypersequent sigma}
    (cut : CKBranchCut (.interface G : CKTree sigma InstanceData G)) :
    cut = .descend (.interface G) := by
  cases cut with
  | detach impossible => exact False.elim impossible
  | descend cut => cases cut; rfl

mutual
def CKCutPlan.ExpansionChoices : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    ((site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → Type (max (max u v) w)
  | _, _, .interface _, _ => PUnit.{max (max u v) w + 1}
  | _, _, .ordinary _ _ children, fillers => children.ExpansionChoices fillers
def CKChildCuts.ExpansionChoices : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    ((site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → Type (max (max u v) w)
  | _, _, .nil, _ => PUnit.{max (max u v) w + 1}
  | _, _, .cons _ _ head tail, fillers =>
      head.ExpansionChoices (fun s => fillers (.inl s)) ×
        tail.ExpansionChoices (fun s => fillers (.inr s))
def CKBranchCut.ExpansionChoices : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    ((site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → Type (max (max u v) w)
  | _, _, .detach _, fillers => CKBranchCut (fillers PUnit.unit)
  | _, _, .descend plan, fillers =>
      match plan with
      | .interface _ => PUnit.{max (max u v) w + 1}
      | .ordinary _ _ children =>
          PUnit.{max (max u v) w + 1} ⊕ children.ExpansionChoices fillers
end

mutual
def CKCutPlan.expandCut : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      CKCutPlan (installation.fill fillers)
  | _, _, .interface G, _, _ => .interface G
  | _, _, .ordinary o _ children, fillers, choices =>
      .ordinary o _ (children.expandCut fillers choices)
def CKChildCuts.expandCut : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      CKChildCuts (installation.fill fillers)
  | _, _, .nil, _, _ => .nil
  | _, _, .cons _ _ head tail, fillers, choices =>
      .cons _ _ (head.expandCut (fun s => fillers (.inl s)) choices.1)
        (tail.expandCut (fun s => fillers (.inr s)) choices.2)
def CKBranchCut.expandCut : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      CKBranchCut (installation.fill fillers)
  | _, _, .detach _, _, choices => choices
  | _, _, .descend plan, fillers, choices => by
      cases plan with
      | interface _ => exact .descend (.interface _)
      | ordinary o children cuts =>
          exact match choices with
          | .inl _ => .detach trivial
          | .inr choices =>
              .descend (.ordinary o _ (cuts.expandCut fillers choices))
end

mutual
def CKCutPlan.decomposeCut : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → CKCutPlan (installation.fill fillers) →
      installation.ExpansionChoices fillers
  | _, _, .interface _, _, _ => PUnit.unit
  | _, _, .ordinary _ _ children, fillers, cut =>
      children.decomposeCut fillers cut.contents
def CKChildCuts.decomposeCut : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → CKChildCuts (installation.fill fillers) →
      installation.ExpansionChoices fillers
  | _, _, .nil, _, _ => PUnit.unit
  | _, _, .cons _ _ head tail, fillers, cut =>
      (head.decomposeCut (fun s => fillers (.inl s)) cut.contents.1,
        tail.decomposeCut (fun s => fillers (.inr s)) cut.contents.2)
def CKBranchCut.decomposeCut : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → CKBranchCut (installation.fill fillers) →
      installation.ExpansionChoices fillers
  | _, _, .detach _, _, cut => cut
  | _, _, .descend plan, fillers, cut => by
      cases plan with
      | interface G => exact PUnit.unit
      | ordinary o children cuts =>
          exact match cut.rootChoice with
          | .inl _ => .inl PUnit.unit
          | .inr cut => .inr (cuts.decomposeCut fillers cut.contents)
end

mutual
theorem CKCutPlan.expand_decompose : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (cut : CKCutPlan (installation.fill fillers)) →
      installation.expandCut fillers (installation.decomposeCut fillers cut) = cut
  | _, _, .interface _, _, cut => by cases cut; rfl
  | _, _, .ordinary o _ children, fillers, cut => by
      change CKCutPlan.ordinary o _
        (children.expandCut fillers (children.decomposeCut fillers cut.contents)) = cut
      rw [children.expand_decompose fillers cut.contents]
      exact cut.contents_reconstructs
theorem CKChildCuts.expand_decompose : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (cut : CKChildCuts (installation.fill fillers)) →
      installation.expandCut fillers (installation.decomposeCut fillers cut) = cut
  | _, _, .nil, _, cut => by cases cut; rfl
  | _, _, .cons _ _ head tail, fillers, cut => by
      change CKChildCuts.cons _ _
        (head.expandCut (fun s => fillers (.inl s))
          (head.decomposeCut (fun s => fillers (.inl s)) cut.contents.1))
        (tail.expandCut (fun s => fillers (.inr s))
          (tail.decomposeCut (fun s => fillers (.inr s)) cut.contents.2)) = cut
      rw [head.expand_decompose, tail.expand_decompose]
      exact cut.contents_reconstructs
theorem CKBranchCut.expand_decompose : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (cut : CKBranchCut (installation.fill fillers)) →
      installation.expandCut fillers (installation.decomposeCut fillers cut) = cut
  | _, _, .detach _, _, _ => rfl
  | _, _, .descend plan, fillers, cut => by
      cases plan with
      | interface G =>
          exact cut.interface_unique.symm
      | ordinary o children cuts =>
          have reassemble := cut.rootChoice_reconstructs (by trivial)
          generalize equal : cut.rootChoice = choice at *
          cases choice with
          | inl value => simpa [CKBranchCut.expandCut, CKBranchCut.decomposeCut,
              equal] using reassemble
          | inr childCut =>
              simp only [CKBranchCut.expandCut, CKBranchCut.decomposeCut, equal]
              rw [cuts.expand_decompose fillers childCut.contents]
              have childEq : CKCutPlan.ordinary o (cuts.fill fillers)
                  childCut.contents = childCut := childCut.contents_reconstructs
              exact (congrArg CKBranchCut.descend childEq).trans reassemble
end

mutual
theorem CKCutPlan.decompose_expand : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
      installation.decomposeCut fillers (installation.expandCut fillers choices) = choices
  | _, _, .interface _, _, choices => by cases choices; rfl
  | _, _, .ordinary _ _ children, fillers, choices =>
      children.decompose_expand fillers choices
theorem CKChildCuts.decompose_expand : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
      installation.decomposeCut fillers (installation.expandCut fillers choices) = choices
  | _, _, .nil, _, choices => by cases choices; rfl
  | _, _, .cons _ _ head tail, fillers, choices => by
      cases choices with
      | mk h t =>
          simp only [CKChildCuts.expandCut, CKChildCuts.decomposeCut,
            CKChildCuts.contents,
            head.decompose_expand (fun s => fillers (.inl s)) h,
            tail.decompose_expand (fun s => fillers (.inr s)) t]
theorem CKBranchCut.decompose_expand : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
      installation.decomposeCut fillers (installation.expandCut fillers choices) = choices
  | _, _, .detach _, _, _ => rfl
  | _, _, .descend plan, fillers, choices => by
      cases plan with
      | interface G => cases choices; rfl
      | ordinary o children cuts =>
          cases choices with
          | inl value => cases value; rfl
          | inr choices =>
              simp only [CKBranchCut.expandCut, CKBranchCut.decomposeCut,
                CKBranchCut.rootChoice, CKCutPlan.contents,
                cuts.decompose_expand fillers choices]
end

/-- Every actual cut of the installed native proof has one and only one
old-ancestor / unswallowed-payload expansion. -/
def CKCutPlan.compositeCutEquiv {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (installation : CKCutPlan tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) :
    CKCutPlan (installation.fill fillers) ≃ installation.ExpansionChoices fillers where
  toFun := installation.decomposeCut fillers
  invFun := installation.expandCut fillers
  left_inv := installation.expand_decompose fillers
  right_inv := installation.decompose_expand fillers

mutual
/-- The actual old-vertex outer cut, on the existing typed remainder. -/
def CKCutPlan.expansionOuterCut : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      CKCutPlan installation.remainder
  | _, _, .interface G, _, _ => .interface G
  | _, _, .ordinary o _ children, fillers, choices =>
      .ordinary o _ (children.expansionOuterCut fillers choices)
def CKChildCuts.expansionOuterCut : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      CKChildCuts installation.remainder
  | _, _, .nil, _, _ => .nil
  | _, _, .cons _ _ head tail, fillers, choices =>
      .cons _ _ (head.expansionOuterCut (fun s => fillers (.inl s)) choices.1)
        (tail.expansionOuterCut (fun s => fillers (.inr s)) choices.2)
def CKBranchCut.expansionOuterCut : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      CKBranchCut installation.remainder
  | _, _, .detach _, _, _ => .descend (.interface _)
  | _, _, .descend plan, fillers, choices => by
      cases plan with
      | interface _ => exact .descend (.interface _)
      | ordinary o children cuts =>
          exact match choices with
          | .inl _ => .detach trivial
          | .inr choices =>
              .descend (.ordinary o _ (cuts.expansionOuterCut fillers choices))
end

mutual
/-- None precisely denotes suppression at a chosen old ancestor; otherwise
the result is an actual native branch cut of the entire installed payload. -/
def CKCutPlan.expansionPayloadCut : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      (site : installation.Site) → Option (CKBranchCut (fillers site))
  | _, _, .interface _, _, _, site => nomatch site
  | _, _, .ordinary _ _ children, fillers, choices, site =>
      children.expansionPayloadCut fillers choices site
def CKChildCuts.expansionPayloadCut : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      (site : installation.Site) → Option (CKBranchCut (fillers site))
  | _, _, .nil, _, _, site => nomatch site
  | _, _, .cons _ _ head tail, fillers, choices, site =>
      match site with
      | .inl s => head.expansionPayloadCut (fun s => fillers (.inl s)) choices.1 s
      | .inr s => tail.expansionPayloadCut (fun s => fillers (.inr s)) choices.2 s
def CKBranchCut.expansionPayloadCut : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
      (site : installation.Site) → Option (CKBranchCut (fillers site))
  | _, _, .detach _, _, choices, site => by cases site; exact some choices
  | _, _, .descend plan, fillers, choices, site => by
      cases plan with
      | interface _ => exact nomatch site
      | ordinary o children cuts =>
          exact match choices with
          | .inl _ => none
          | .inr choices => cuts.expansionPayloadCut fillers choices site
end

mutual
/-- Origin annotations are transported through the native fill; existing
old roots retain their names and payload roots keep their supplied names. -/
def CKCutPlan.fillOriginNames : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → tree.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      (installation.fill fillers).OriginNames Origin
  | _, _, .interface _, _, names, _ => names
  | _, _, .ordinary _ _ children, fillers, names, innerNames =>
      (names.1, children.fillOriginNames fillers names.2 innerNames)
def CKChildCuts.fillOriginNames : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → children.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      (installation.fill fillers).OriginNames Origin
  | _, _, .nil, _, _, _ => PUnit.unit
  | _, _, .cons _ _ head tail, fillers, names, innerNames =>
      (head.fillOriginNames (fun s => fillers (.inl s)) names.1
        (fun s => innerNames (.inl s)),
       tail.fillOriginNames (fun s => fillers (.inr s)) names.2
        (fun s => innerNames (.inr s)))
def CKBranchCut.fillOriginNames : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → tree.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      (installation.fill fillers).OriginNames Origin
  | _, _, .detach _, _, _, innerNames => innerNames PUnit.unit
  | _, _, .descend plan, fillers, names, innerNames =>
      plan.fillOriginNames fillers names innerNames
end

mutual
/-- Independent complete residual constructor: this definition does not
call expandCut or inspect a completed proof's cut enumeration. -/
def CKCutPlan.expansionOriginRemainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
    tree.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      OriginTree sigma InstanceData Origin G
  | _, _, .interface G, _, _, names, _ => ⟨.interface G, names⟩
  | _, _, .ordinary o _ children, fillers, choices, names, innerNames =>
      let residual := children.expansionOriginRemainder fillers choices names.2 innerNames
      ⟨.ordinary o residual.native, (names.1, residual.names)⟩
def CKChildCuts.expansionOriginRemainder : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
    children.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      OriginChildren sigma InstanceData Origin Gs
  | _, _, .nil, _, _, _, _ => ⟨.nil, PUnit.unit⟩
  | _, _, .cons _ _ head tail, fillers, choices, names, innerNames =>
      OriginChildren.cons
        (head.expansionOriginRemainder (fun s => fillers (.inl s)) choices.1 names.1
          (fun s => innerNames (.inl s)))
        (tail.expansionOriginRemainder (fun s => fillers (.inr s)) choices.2 names.2
          (fun s => innerNames (.inr s)))
def CKBranchCut.expansionOriginRemainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
    tree.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      OriginTree sigma InstanceData Origin G
  | _, _, .detach _, _, cut, _, innerNames =>
      ⟨cut.remainder, cut.originRemainder (innerNames PUnit.unit)⟩
  | _, _, .descend plan, fillers, choices, names, innerNames => by
      cases plan with
      | interface _ => exact ⟨.interface _, names⟩
      | ordinary o children cuts =>
          exact match choices with
          | .inl _ => ⟨.interface _, names.1⟩
          | .inr choices =>
              let residual := cuts.expansionOriginRemainder fillers choices names.2 innerNames
              ⟨.ordinary o residual.native, (names.1, residual.names)⟩
end

mutual
/-- The coefficient constructor keeps whole composite factors, not a
primitive inventory. Its list is collected commutatively only afterwards. -/
def CKCutPlan.expansionOriginFactors : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
    tree.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      List (OriginComponent sigma InstanceData Origin)
  | _, _, .interface _, _, _, _, _ => []
  | _, _, .ordinary _ _ children, fillers, choices, names, innerNames =>
      children.expansionOriginFactors fillers choices names.2 innerNames
def CKChildCuts.expansionOriginFactors : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
    children.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      List (OriginComponent sigma InstanceData Origin)
  | _, _, .nil, _, _, _, _ => []
  | _, _, .cons _ _ head tail, fillers, choices, names, innerNames =>
      head.expansionOriginFactors (fun s => fillers (.inl s)) choices.1 names.1
        (fun s => innerNames (.inl s)) ++
      tail.expansionOriginFactors (fun s => fillers (.inr s)) choices.2 names.2
        (fun s => innerNames (.inr s))
def CKBranchCut.expansionOriginFactors : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers →
    tree.OriginNames Origin →
    ((site : installation.Site) → (fillers site).OriginNames Origin) →
      List (OriginComponent sigma InstanceData Origin)
  | _, _, .detach _, _, cut, _, innerNames =>
      cut.originFactors (innerNames PUnit.unit)
  | _, _, .descend plan, fillers, choices, names, innerNames => by
      cases plan with
      | interface _ => exact []
      | ordinary o children cuts =>
          exact match choices with
          | .inl _ =>
              [⟨⟨_, .ordinary o (cuts.fill fillers), trivial⟩,
                (names.1, cuts.fillOriginNames fillers names.2 innerNames)⟩]
          | .inr choices => cuts.expansionOriginFactors fillers choices names.2 innerNames
end

mutual
theorem CKCutPlan.expand_originRemainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
    (names : tree.OriginNames Origin) →
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) →
      (⟨(installation.expandCut fillers choices).remainder,
        (installation.expandCut fillers choices).originRemainder
          (installation.fillOriginNames fillers names innerNames)⟩ :
        OriginTree sigma InstanceData Origin G) =
        installation.expansionOriginRemainder fillers choices names innerNames
  | _, _, .interface _, _, _, _, _ => rfl
  | _, _, .ordinary o _ children, fillers, choices, names, innerNames => by
      have equal := children.expand_originRemainder fillers choices names.2 innerNames
      exact congrArg (fun residual : OriginChildren sigma InstanceData Origin o.shape.premises =>
        (⟨.ordinary o residual.native, (names.1, residual.names)⟩ :
          OriginTree sigma InstanceData Origin o.shape.conclusion)) equal
theorem CKChildCuts.expand_originRemainder : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
    (names : children.OriginNames Origin) →
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) →
      (⟨(installation.expandCut fillers choices).remainder,
        (installation.expandCut fillers choices).originRemainder
          (installation.fillOriginNames fillers names innerNames)⟩ :
        OriginChildren sigma InstanceData Origin Gs) =
        installation.expansionOriginRemainder fillers choices names innerNames
  | _, _, .nil, _, _, _, _ => rfl
  | _, _, .cons _ _ head tail, fillers, choices, names, innerNames => by
      exact congrArg₂ OriginChildren.cons
        (head.expand_originRemainder (fun s => fillers (.inl s)) choices.1 names.1
          (fun s => innerNames (.inl s)))
        (tail.expand_originRemainder (fun s => fillers (.inr s)) choices.2 names.2
          (fun s => innerNames (.inr s)))
theorem CKBranchCut.expand_originRemainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
    (names : tree.OriginNames Origin) →
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) →
      (⟨(installation.expandCut fillers choices).remainder,
        (installation.expandCut fillers choices).originRemainder
          (installation.fillOriginNames fillers names innerNames)⟩ :
        OriginTree sigma InstanceData Origin G) =
        installation.expansionOriginRemainder fillers choices names innerNames
  | _, _, .detach _, _, _, _, _ => rfl
  | _, _, .descend plan, fillers, choices, names, innerNames => by
      cases plan with
      | interface _ => rfl
      | ordinary o children cuts =>
          cases choices with
          | inl _ => rfl
          | inr choices =>
              have equal := cuts.expand_originRemainder fillers choices names.2 innerNames
              exact congrArg
                (fun residual : OriginChildren sigma InstanceData Origin o.shape.premises =>
                  (⟨.ordinary o residual.native, (names.1, residual.names)⟩ :
                    OriginTree sigma InstanceData Origin o.shape.conclusion)) equal
end

mutual
theorem CKCutPlan.expand_originFactors : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
    (names : tree.OriginNames Origin) →
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) →
      (installation.expandCut fillers choices).originFactors
        (installation.fillOriginNames fillers names innerNames) =
        installation.expansionOriginFactors fillers choices names innerNames
  | _, _, .interface _, _, _, _, _ => rfl
  | _, _, .ordinary _ _ children, fillers, choices, names, innerNames =>
      children.expand_originFactors fillers choices names.2 innerNames
theorem CKChildCuts.expand_originFactors : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
    (names : children.OriginNames Origin) →
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) →
      (installation.expandCut fillers choices).originFactors
        (installation.fillOriginNames fillers names innerNames) =
        installation.expansionOriginFactors fillers choices names innerNames
  | _, _, .nil, _, _, _, _ => rfl
  | _, _, .cons _ _ head tail, fillers, choices, names, innerNames =>
      congrArg₂ List.append
        (head.expand_originFactors (fun s => fillers (.inl s)) choices.1 names.1
          (fun s => innerNames (.inl s)))
        (tail.expand_originFactors (fun s => fillers (.inr s)) choices.2 names.2
          (fun s => innerNames (.inr s)))
theorem CKBranchCut.expand_originFactors : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
    (names : tree.OriginNames Origin) →
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) →
      (installation.expandCut fillers choices).originFactors
        (installation.fillOriginNames fillers names innerNames) =
        installation.expansionOriginFactors fillers choices names innerNames
  | _, _, .detach _, _, _, _, _ => rfl
  | _, _, .descend plan, fillers, choices, names, innerNames => by
      cases plan with
      | interface _ => rfl
      | ordinary o children cuts =>
          cases choices with
          | inl _ => rfl
          | inr choices => exact cuts.expand_originFactors fillers choices names.2 innerNames
end

mutual
/-- The expansion index carries no hidden cut information: the actual outer
native cut and the compatible per-site native inner cuts determine it. -/
theorem CKCutPlan.expansion_outer_inner_injective : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (left right : installation.ExpansionChoices fillers) →
    installation.expansionOuterCut fillers left =
      installation.expansionOuterCut fillers right →
    (∀ site, installation.expansionPayloadCut fillers left site =
      installation.expansionPayloadCut fillers right site) → left = right
  | _, _, .interface _, _, left, right, _, _ => by cases left; cases right; rfl
  | _, _, .ordinary _ _ children, fillers, left, right, outer, inner =>
      children.expansion_outer_inner_injective fillers left right
        (congrArg CKCutPlan.contents outer) inner
theorem CKChildCuts.expansion_outer_inner_injective : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (left right : installation.ExpansionChoices fillers) →
    installation.expansionOuterCut fillers left =
      installation.expansionOuterCut fillers right →
    (∀ site, installation.expansionPayloadCut fillers left site =
      installation.expansionPayloadCut fillers right site) → left = right
  | _, _, .nil, _, left, right, _, _ => by cases left; cases right; rfl
  | _, _, .cons _ _ head tail, fillers, left, right, outer, inner => by
      have tupleEq := congrArg CKChildCuts.contents outer
      have headEq := head.expansion_outer_inner_injective
        (fun s => fillers (.inl s)) left.1 right.1 (congrArg Prod.fst tupleEq)
        (fun s => inner (.inl s))
      have tailEq := tail.expansion_outer_inner_injective
        (fun s => fillers (.inr s)) left.2 right.2 (congrArg Prod.snd tupleEq)
        (fun s => inner (.inr s))
      exact Prod.ext headEq tailEq
theorem CKBranchCut.expansion_outer_inner_injective : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (left right : installation.ExpansionChoices fillers) →
    installation.expansionOuterCut fillers left =
      installation.expansionOuterCut fillers right →
    (∀ site, installation.expansionPayloadCut fillers left site =
      installation.expansionPayloadCut fillers right site) → left = right
  | _, _, .detach _, _, left, right, _, inner =>
      Option.some.inj (inner PUnit.unit)
  | _, _, .descend plan, fillers, left, right, outer, inner => by
      cases plan with
      | interface _ => cases left; cases right; rfl
      | ordinary o children cuts =>
          cases left with
          | inl leftUnit =>
              cases right with
              | inl rightUnit => cases leftUnit; cases rightUnit; rfl
              | inr right =>
                  have impossible := congrArg CKBranchCut.rootChoice outer
                  cases impossible
          | inr left =>
              cases right with
              | inl rightUnit =>
                  have impossible := congrArg CKBranchCut.rootChoice outer
                  cases impossible
              | inr right =>
                  have planEq := Sum.inr.inj (congrArg CKBranchCut.rootChoice outer)
                  have childrenEq := congrArg CKCutPlan.contents planEq
                  exact congrArg Sum.inr
                    (cuts.expansion_outer_inner_injective fillers left right childrenEq inner)
end

/-- Every completed native cut is uniquely determined by its explicit actual
outer cut and its optional actual payload cuts. -/
theorem CKCutPlan.installed_outer_inner_injective {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (installation : CKCutPlan tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site))
    (left right : CKCutPlan (installation.fill fillers))
    (outer : installation.expansionOuterCut fillers (installation.decomposeCut fillers left) =
      installation.expansionOuterCut fillers (installation.decomposeCut fillers right))
    (inner : ∀ site,
      installation.expansionPayloadCut fillers (installation.decomposeCut fillers left) site =
      installation.expansionPayloadCut fillers (installation.decomposeCut fillers right) site) :
    left = right :=
  (installation.compositeCutEquiv fillers).injective
    (installation.expansion_outer_inner_injective fillers _ _ outer inner)

namespace CKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- The expansion is a native cut of the native checked-sector fill. In
particular its root is never selectable and the whole endpoint stays separate. -/
def expandedCut (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choices : installation.plan.ExpansionChoices fillers) :
    CKCut (installation.fill fillers) :=
  ⟨installation.fill_isOrdinary fillers, installation.plan.expandCut fillers choices⟩

/-- The public native wrapper retains the intrinsic witness bijection.
This does not assert the separate unresolved address-set injectivity of
legacy plans or count a deduplicated extensional enumeration. -/
def installedCutEquiv (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site)) :
    CKCut (installation.fill fillers) ≃ installation.plan.ExpansionChoices fillers where
  toFun := fun cut => installation.plan.decomposeCut fillers cut.plan
  invFun := installation.expandedCut fillers
  left_inv := by
    intro cut
    cases cut with
    | mk ordinary plan =>
        unfold expandedCut
        rw [installation.plan.expand_decompose fillers plan]
  right_inv := installation.plan.decompose_expand fillers

/-- Exact factor and residual comparison BEFORE any coefficient collection;
the collected forest equality therefore retains occurrence multiplicity. -/
theorem expanded_originObservation (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choices : installation.plan.ExpansionChoices fillers)
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    ((installation.expandedCut fillers choices).enrichedRemainder
        (installation.plan.fillOriginNames fillers names innerNames),
      (installation.expandedCut fillers choices).originForest
        (installation.plan.fillOriginNames fillers names innerNames)) =
    (installation.plan.expansionOriginRemainder fillers choices names innerNames,
      Multiset.ofList
        (installation.plan.expansionOriginFactors fillers choices names innerNames)) := by
  apply Prod.ext
  · exact installation.plan.expand_originRemainder fillers choices names innerNames
  · exact congrArg Multiset.ofList
      (installation.plan.expand_originFactors fillers choices names innerNames)

/-- A typed composite installation and EVERY selected expansion occurrence
stay in the same exact equipped presentation, with no provenance cast. -/
theorem expanded_locallyAdmitted {T : ProofTheory sigma InstanceData}
    {P : EquippedPresentation T} (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choices : installation.plan.ExpansionChoices fillers)
    (sourceAdmitted : LocallyAdmittedTree P tree)
    (fillersAdmitted : ∀ site, LocallyAdmittedTree P (fillers site)) :
    LocallyAdmittedTree P (installation.fill fillers) ∧
    LocallyAdmittedTree P (installation.expandedCut fillers choices).remainder ∧
    (∀ site, LocallyAdmittedTree P
      ((installation.expandedCut fillers choices).plan.detached site)) := by
  have admitted := installation.fill_locallyAdmitted fillers sourceAdmitted fillersAdmitted
  exact ⟨admitted,
    (installation.expandedCut fillers choices).remainder_locallyAdmitted admitted,
    (installation.expandedCut fillers choices).detached_locallyAdmitted admitted⟩

/-- The independently assembled expansion term reconstructs the installed
native source. No completed-proof enumeration appears in this construction. -/
theorem decode_expansion (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choices : installation.plan.ExpansionChoices fillers)
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (fresh : ((installation.fill fillers).originList
      (installation.plan.fillOriginNames fillers names innerNames)).Nodup) :
    OriginTree.decode
      (Multiset.ofList
        (installation.plan.expansionOriginFactors fillers choices names innerNames))
      (installation.plan.expansionOriginRemainder fillers choices names innerNames).native
      (installation.plan.expansionOriginRemainder fillers choices names innerNames).names =
      (⟨installation.fill fillers,
        installation.plan.fillOriginNames fillers names innerNames⟩ :
        OriginTree sigma InstanceData Origin G) := by
  have residual := installation.plan.expand_originRemainder fillers choices names innerNames
  have factors := installation.plan.expand_originFactors fillers choices names innerNames
  rw [← factors, ← residual]
  exact (installation.expandedCut fillers choices).decode_collected _ fresh

/-- Additional native extractions inside the ACTUAL full composite factors
reassemble first. Their staged forest is precisely the independent expansion
forest, not a flattened primitive-leaf inventory. -/
theorem expansion_stagedForest (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choices : installation.plan.ExpansionChoices fillers)
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (fresh : ((installation.fill fillers).originList
      (installation.plan.fillOriginNames fillers names innerNames)).Nodup)
    (lower : (site : (installation.expandedCut fillers choices).Site) →
      CKCut ((installation.expandedCut fillers choices).plan.detached site)) :
    (installation.expandedCut fillers choices).stagedOriginForest
      (installation.plan.fillOriginNames fillers names innerNames) fresh lower =
      Multiset.ofList
        (installation.plan.expansionOriginFactors fillers choices names innerNames) := by
  rw [(installation.expandedCut fillers choices).stagedOriginForest_eq _ fresh lower]
  exact congrArg Multiset.ofList
    (installation.plan.expand_originFactors fillers choices names innerNames)

/-- Lower-then-middle reconstruction for arbitrary typed composite modules
is compatible with the precise native cut-expansion residual. This is a
tree/forest opening theorem, not an asserted linear coaction equation. -/
theorem decode_expansion_twoStage (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choices : installation.plan.ExpansionChoices fillers)
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (fresh : ((installation.fill fillers).originList
      (installation.plan.fillOriginNames fillers names innerNames)).Nodup)
    (lower : (site : (installation.expandedCut fillers choices).Site) →
      CKCut ((installation.expandedCut fillers choices).plan.detached site)) :
    OriginTree.decode
      ((installation.expandedCut fillers choices).stagedOriginForest
        (installation.plan.fillOriginNames fillers names innerNames) fresh lower)
      (installation.plan.expansionOriginRemainder fillers choices names innerNames).native
      (installation.plan.expansionOriginRemainder fillers choices names innerNames).names =
      (⟨installation.fill fillers,
        installation.plan.fillOriginNames fillers names innerNames⟩ :
        OriginTree sigma InstanceData Origin G) := by
  rw [installation.expansion_stagedForest fillers choices names innerNames fresh lower]
  exact installation.decode_expansion fillers choices names innerNames fresh

end CKCut

/-- An intact payload root is a full positive coefficient, including its
positive-arity interior and inherited holes; it is not a primitive count. -/
theorem CKBranchCut.wholePayload_factor {G : Hypersequent sigma}
    {probe : CKTree sigma InstanceData G} (probeOrdinary : probe.IsOrdinary)
    (payload : CKTree sigma InstanceData G) (payloadOrdinary : payload.IsOrdinary)
    (names : probe.OriginNames Origin) (payloadNames : payload.OriginNames Origin) :
    (CKBranchCut.detach probeOrdinary).expansionOriginFactors (fun _ => payload)
      (CKBranchCut.detach payloadOrdinary) names (fun _ => payloadNames) =
      [⟨⟨G, payload, payloadOrdinary⟩, payloadNames⟩] := rfl

/-- Suppression is not an informal compatibility hypothesis: the constructor
selecting an old ancestor yields no independent cut for ANY site below it. -/
theorem CKBranchCut.oldAncestor_suppresses (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (installation : CKChildCuts children)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) (site : installation.Site) :
    (CKBranchCut.descend (.ordinary o children installation)).expansionPayloadCut
      fillers (.inl PUnit.unit) site = none := rfl

/-- The factor at a swallowed old ancestor carries the WHOLE filled subtree.
The formula retains every module and its physical annotations below it. -/
theorem CKBranchCut.oldAncestor_fullFactor (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (installation : CKChildCuts children)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site))
    (names : (CKTree.ordinary o children).OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    (CKBranchCut.descend (.ordinary o children installation)).expansionOriginFactors
      fillers (.inl PUnit.unit) names innerNames =
      [⟨⟨o.shape.conclusion, .ordinary o (installation.fill fillers), trivial⟩,
        (names.1, installation.fillOriginNames fillers names.2 innerNames)⟩] := rfl

end Potkin

#print axioms Potkin.CKCutPlan.compositeCutEquiv
#print axioms Potkin.CKCutPlan.installed_outer_inner_injective
#print axioms Potkin.CKCut.installedCutEquiv
#print axioms Potkin.CKCutPlan.expand_originFactors
#print axioms Potkin.CKCutPlan.expand_originRemainder
#print axioms Potkin.CKCut.expanded_originObservation
#print axioms Potkin.CKCut.expanded_locallyAdmitted
#print axioms Potkin.CKCut.decode_expansion
#print axioms Potkin.CKCut.decode_expansion_twoStage

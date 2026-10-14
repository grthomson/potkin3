import Potkin.Research.ContextCutAction
import Potkin.CompositeCutExpansion

/-!
# Two bracketings of native CK extraction

`BranchInside` chooses an outer full branch cut, then a full branch cut in
each actual detached factor. `BranchRemainder` first chooses a full branch
cut, then a full branch cut of its literal typed remainder. These are witness
metadata over the installed native carriers, not new proof or cut carriers.

The full endpoint remains a branch adapter, never a proper root cut. In the
coefficient projection only an interface middle remainder contributes no
positive component; its typed Box remains present in the witness data.
-/

namespace Potkin.Research.RemainderExtractionFlags

open ContextCutPackets ContextCutAction

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

abbrev PlanInside {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :=
  Σ upper : CKCutPlan tree, (site : upper.Site) → CKBranchCut (upper.detached site)

abbrev ChildrenInside {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData Gs) :=
  Σ upper : CKChildCuts children, (site : upper.Site) → CKBranchCut (upper.detached site)

abbrev BranchInside {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :=
  Σ upper : CKBranchCut tree, (site : upper.Site) → CKBranchCut (upper.detached site)

abbrev PlanRemainder {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :=
  Σ lower : CKCutPlan tree, CKCutPlan lower.remainder

abbrev ChildrenRemainder {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData Gs) :=
  Σ lower : CKChildCuts children, CKChildCuts lower.remainder

abbrev BranchRemainder {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :=
  Σ lower : CKBranchCut tree, CKBranchCut lower.remainder

theorem plan_remainder_ordinary {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCutPlan tree)
    (ordinary : tree.IsOrdinary) : cut.remainder.IsOrdinary := by
  cases cut with
  | interface _ => exact False.elim ordinary
  | ordinary _ _ _ => trivial

theorem plan_source_ordinary {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCutPlan tree)
    (ordinary : cut.remainder.IsOrdinary) : tree.IsOrdinary := by
  cases cut with
  | interface _ => exact False.elim ordinary
  | ordinary _ _ _ => trivial

/-- Full outer selection is reassociated without manufacturing a root cut. -/
def rootPair {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) : BranchRemainder tree :=
  match lower with
  | .detach h => ⟨.detach h, .descend (.interface _)⟩
  | .descend cut => ⟨.descend cut, .detach (plan_remainder_ordinary cut ordinary)⟩

theorem rootPair_first {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) :
    (rootPair ordinary lower).1 = lower := by cases lower <;> rfl

theorem rootPair_remainder {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) :
    (rootPair ordinary lower).2.remainder = CKTree.interface G := by cases lower <;> rfl

mutual

def toRemainderPlan : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKCutPlan tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → PlanRemainder tree
  | _, _, .interface G, _ => ⟨.interface G, .interface G⟩
  | _, _, .ordinary o children cuts, inner =>
      let result := toRemainderChildren cuts inner
      ⟨.ordinary o children result.1, .ordinary o result.1.remainder result.2⟩

def toRemainderChildren : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (upper : CKChildCuts children) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → ChildrenRemainder children
  | _, _, .nil, _ => ⟨.nil, .nil⟩
  | _, _, .cons head tail h t, inner =>
      let first := toRemainderBranch h (fun i => inner (.inl i))
      let rest := toRemainderChildren t (fun i => inner (.inr i))
      ⟨.cons head tail first.1 rest.1,
        .cons first.1.remainder rest.1.remainder first.2 rest.2⟩

def toRemainderBranch : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKBranchCut tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → BranchRemainder tree
  | _, _, .detach ordinary, inner =>
      rootPair ordinary (inner PUnit.unit)
  | _, _, .descend cut, inner =>
      let result := toRemainderPlan cut inner
      ⟨.descend result.1, .descend result.2⟩

end

mutual

def fromRemainderPlan : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (lower : CKCutPlan tree) →
    CKCutPlan lower.remainder → PlanInside tree
  | _, _, .interface G, _ => ⟨.interface G, fun i => nomatch i⟩
  | _, _, .ordinary o children cuts, upper =>
      let result := fromRemainderChildren cuts upper.contents
      ⟨.ordinary o children result.1, result.2⟩

def fromRemainderChildren : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (lower : CKChildCuts children) →
    CKChildCuts lower.remainder → ChildrenInside children
  | _, _, .nil, _ => ⟨.nil, fun i => nomatch i⟩
  | _, _, .cons head tail h t, upper =>
      let first := fromRemainderBranch h upper.contents.1
      let rest := fromRemainderChildren t upper.contents.2
      ⟨.cons head tail first.1 rest.1,
        fun i => match i with
        | .inl i => first.2 i
        | .inr i => rest.2 i⟩

def fromRemainderBranch : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (lower : CKBranchCut tree) →
    CKBranchCut lower.remainder → BranchInside tree
  | _, _, .detach ordinary, _ => ⟨.detach ordinary, fun _ => .detach ordinary⟩
  | _, _, .descend cut, upper =>
      match upper with
      | .detach ordinary => ⟨.detach (plan_source_ordinary cut ordinary), fun _ => .descend cut⟩
      | .descend upper =>
          let result := fromRemainderPlan cut upper
          ⟨.descend result.1, result.2⟩

end

theorem from_rootPair {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) :
    fromRemainderBranch (rootPair ordinary lower).1 (rootPair ordinary lower).2 =
      ⟨CKBranchCut.detach ordinary, fun _ => lower⟩ := by
  cases lower <;> rfl

mutual

theorem from_to_plan : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    fromRemainderPlan (toRemainderPlan upper inner).1 (toRemainderPlan upper inner).2 =
      ⟨upper, inner⟩
  | _, _, .interface G, inner => by
      apply congrArg (Sigma.mk (CKCutPlan.interface G))
      funext i
      exact nomatch i
  | _, _, .ordinary o children cuts, inner => by
      simpa only [toRemainderPlan, fromRemainderPlan, CKCutPlan.contents] using
        congrArg (fun result : ChildrenInside children =>
          (⟨CKCutPlan.ordinary o children result.1, result.2⟩ : PlanInside (.ordinary o children)))
          (from_to_children cuts inner)

theorem from_to_children : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (upper : CKChildCuts children) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    fromRemainderChildren (toRemainderChildren upper inner).1 (toRemainderChildren upper inner).2 =
      ⟨upper, inner⟩
  | _, _, .nil, inner => by
      apply congrArg (Sigma.mk (CKChildCuts.nil : CKChildCuts (.nil : CKChildren sigma InstanceData [])))
      funext i
      exact nomatch i
  | _, _, .cons head tail h t, inner => by
      have first := from_to_branch h (fun i => inner (.inl i))
      have rest := from_to_children t (fun i => inner (.inr i))
      let combine : BranchInside head → ChildrenInside tail → ChildrenInside (.cons head tail) :=
        fun x y => ⟨.cons head tail x.1 y.1,
          fun i => match i with | .inl i => x.2 i | .inr i => y.2 i⟩
      have equal := congrArg₂ combine first rest
      apply Eq.trans equal
      apply congrArg (Sigma.mk (CKChildCuts.cons head tail h t))
      funext i
      cases i <;> rfl

theorem from_to_branch : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    fromRemainderBranch (toRemainderBranch upper inner).1 (toRemainderBranch upper inner).2 =
      ⟨upper, inner⟩
  | _, tree, .detach ordinary, inner => by
      have equal := from_rootPair ordinary (inner PUnit.unit)
      apply Eq.trans equal
      apply congrArg (Sigma.mk (CKBranchCut.detach ordinary))
      funext i
      cases i
      rfl
  | _, tree, .descend cut, inner => by
      exact congrArg (fun result : PlanInside tree =>
        (⟨CKBranchCut.descend result.1, result.2⟩ : BranchInside tree)) (from_to_plan cut inner)

end

mutual

theorem to_from_plan : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (lower : CKCutPlan tree) →
    (upper : CKCutPlan lower.remainder) →
    toRemainderPlan (fromRemainderPlan lower upper).1 (fromRemainderPlan lower upper).2 =
      ⟨lower, upper⟩
  | _, _, .interface G, upper => by cases upper; rfl
  | _, _, .ordinary o children cuts, upper => by
      let encode : ChildrenRemainder children → PlanRemainder (.ordinary o children) :=
        fun result => ⟨CKCutPlan.ordinary o children result.1,
          CKCutPlan.ordinary o result.1.remainder result.2⟩
      have equal := congrArg encode (to_from_children cuts upper.contents)
      apply Eq.trans equal
      exact congrArg (fun second => (⟨CKCutPlan.ordinary o children cuts, second⟩ :
        PlanRemainder (.ordinary o children))) upper.contents_reconstructs

theorem to_from_children : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (lower : CKChildCuts children) →
    (upper : CKChildCuts lower.remainder) →
    toRemainderChildren (fromRemainderChildren lower upper).1 (fromRemainderChildren lower upper).2 =
      ⟨lower, upper⟩
  | _, _, .nil, upper => by cases upper; rfl
  | _, _, .cons head tail h t, upper => by
      cases upper with
      | cons _ _ uh ut =>
          let combine : BranchRemainder head → ChildrenRemainder tail → ChildrenRemainder (.cons head tail) :=
            fun x y => ⟨.cons head tail x.1 y.1,
              .cons x.1.remainder y.1.remainder x.2 y.2⟩
          simpa only [toRemainderChildren, fromRemainderChildren, CKChildCuts.contents,
            combine] using congrArg₂ combine (to_from_branch h uh) (to_from_children t ut)

theorem to_from_branch : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (lower : CKBranchCut tree) →
    (upper : CKBranchCut lower.remainder) →
    toRemainderBranch (fromRemainderBranch lower upper).1 (fromRemainderBranch lower upper).2 =
      ⟨lower, upper⟩
  | _, _, .detach ordinary, upper => by
      have unique := upper.interface_unique
      cases unique
      rfl
  | _, tree, .descend cut, upper => by
      cases upper with
      | detach ordinary => rfl
      | descend upper =>
          exact congrArg (fun result : PlanRemainder tree =>
            (⟨CKBranchCut.descend result.1, CKBranchCut.descend result.2⟩ :
              BranchRemainder tree)) (to_from_plan cut upper)

end

/-- Universal extraction reassociation on physical native witnesses,
including cuts of the previously punctured remainder and both endpoints. -/
def branchFlagEquiv {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    BranchInside tree ≃ BranchRemainder tree where
  toFun flag := toRemainderBranch flag.1 flag.2
  invFun flag := fromRemainderBranch flag.1 flag.2
  left_inv flag := from_to_branch flag.1 flag.2
  right_inv flag := to_from_branch flag.1 flag.2

/-- Prefix a retained physical occurrence address; no decoration changes. -/
def prefixEntry (pathPrefix : InternalAddress) (entry : CKCutEntry sigma InstanceData) :
    CKCutEntry sigma InstanceData := { entry with address := pathPrefix ++ entry.address }

/-- Move an ordered child-tail address to its actual premise slot. -/
def shiftEntry (entry : CKCutEntry sigma InstanceData) : CKCutEntry sigma InstanceData :=
  { entry with address := InternalAddress.shiftHead entry.address }

def childrenPacket {Gs : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData Gs} (cut : CKChildCuts children) :
    List (CKCutEntry sigma InstanceData) :=
  cut.siteOrder.map fun site =>
    ⟨cut.address site, cut.siteBoundary site, cut.detached site, cut.detachedOrdinary site⟩

theorem childrenPacket_cons {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
    {head : CKTree sigma InstanceData G} {tail : CKChildren sigma InstanceData Gs}
    (h : CKBranchCut head) (t : CKChildCuts tail) :
    childrenPacket (.cons head tail h t) =
      (orderedPacket h).map (prefixEntry [0]) ++ (childrenPacket t).map shiftEntry := by
  let encode : (CKChildCuts.cons head tail h t).Site → CKCutEntry sigma InstanceData :=
    fun site => ⟨(CKChildCuts.cons head tail h t).address site,
      (CKChildCuts.cons head tail h t).siteBoundary site,
      (CKChildCuts.cons head tail h t).detached site,
      (CKChildCuts.cons head tail h t).detachedOrdinary site⟩
  have distribution := List.map_append (f := encode)
    (l₁ := h.siteOrder.map Sum.inl) (l₂ := t.siteOrder.map Sum.inr)
  have composition := congrArg₂ List.append
    (List.map_map (g := encode) (f := Sum.inl) (l := h.siteOrder))
    (List.map_map (g := encode) (f := Sum.inr) (l := t.siteOrder))
  have finalComposition := congrArg₂ List.append
    (List.map_map (g := prefixEntry [0])
      (f := fun i => (⟨h.relativeAddress i, h.siteBoundary i, h.detached i,
        h.detachedOrdinary i⟩ : CKCutEntry sigma InstanceData)) (l := h.siteOrder))
    (List.map_map (g := shiftEntry)
      (f := fun i => (⟨t.address i, t.siteBoundary i, t.detached i,
        t.detachedOrdinary i⟩ : CKCutEntry sigma InstanceData)) (l := t.siteOrder))
  exact (distribution.trans composition).trans finalComposition.symm

theorem orderedPacket_ordinary (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises) (cuts : CKChildCuts children) :
    orderedPacket (.descend (.ordinary o children cuts)) = childrenPacket cuts := rfl

/-- A positive-root coefficient packet, with its actual typed tree. An
interface contributes no coefficient component, not an untyped proof unit. -/
def positivePacket {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    List (CKCutEntry sigma InstanceData) :=
  match tree with
  | .interface _ => []
  | .ordinary o children => [⟨[], o.shape.conclusion, .ordinary o children, by trivial⟩]

theorem orderedPacket_detach {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) : orderedPacket (.detach ordinary) = positivePacket tree := by
  cases tree with
  | interface _ => exact False.elim ordinary
  | ordinary _ _ => rfl

theorem rootPair_middlePacket {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (ordinary : tree.IsOrdinary) (lower : CKBranchCut tree) :
    orderedPacket (rootPair ordinary lower).2 = positivePacket lower.remainder := by
  cases lower with
  | detach _ => rfl
  | descend cut => exact orderedPacket_detach _ (plan_remainder_ordinary cut ordinary)

mutual

def insideLowerPlan : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKCutPlan tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → List (CKCutEntry sigma InstanceData)
  | _, _, .interface _, _ => []
  | _, _, .ordinary _ _ cuts, inner => insideLowerChildren cuts inner

def insideLowerChildren : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (upper : CKChildCuts children) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → List (CKCutEntry sigma InstanceData)
  | _, _, .nil, _ => []
  | _, _, .cons _ _ h t, inner =>
      (insideLowerPacket h (fun i => inner (.inl i))).map (prefixEntry [0]) ++
        (insideLowerChildren t (fun i => inner (.inr i))).map shiftEntry

def insideLowerPacket : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKBranchCut tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → List (CKCutEntry sigma InstanceData)
  | _, _, .detach _, inner => orderedPacket (inner PUnit.unit)
  | _, _, .descend cut, inner => insideLowerPlan cut inner

end

mutual

def insideMiddlePlan : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKCutPlan tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → List (CKCutEntry sigma InstanceData)
  | _, _, .interface _, _ => []
  | _, _, .ordinary _ _ cuts, inner => insideMiddleChildren cuts inner

def insideMiddleChildren : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (upper : CKChildCuts children) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → List (CKCutEntry sigma InstanceData)
  | _, _, .nil, _ => []
  | _, _, .cons _ _ h t, inner =>
      (insideMiddlePacket h (fun i => inner (.inl i))).map (prefixEntry [0]) ++
        (insideMiddleChildren t (fun i => inner (.inr i))).map shiftEntry

def insideMiddlePacket : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKBranchCut tree) →
    ((site : upper.Site) → CKBranchCut (upper.detached site)) → List (CKCutEntry sigma InstanceData)
  | _, _, .detach _, inner => positivePacket (inner PUnit.unit).remainder
  | _, _, .descend cut, inner => insideMiddlePlan cut inner

end

def insideRemainder {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (upper : CKBranchCut tree) (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) :
    CKTree sigma InstanceData G := upper.remainder

mutual

theorem toRemainderPlan_lowerPacket : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    orderedPacket (.descend (toRemainderPlan upper inner).1) = insideLowerPlan upper inner
  | _, _, .interface _, _ => rfl
  | _, _, .ordinary o children cuts, inner => by
      exact toRemainderChildren_lowerPacket cuts inner

theorem toRemainderChildren_lowerPacket : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (upper : CKChildCuts children) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    childrenPacket (toRemainderChildren upper inner).1 = insideLowerChildren upper inner
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _ h t, inner => by
      simp only [toRemainderChildren, childrenPacket_cons]
      rw [
        toRemainderBranch_lowerPacket h (fun i => inner (.inl i)),
        toRemainderChildren_lowerPacket t (fun i => inner (.inr i))]
      rfl

theorem toRemainderBranch_lowerPacket : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    orderedPacket (toRemainderBranch upper inner).1 = insideLowerPacket upper inner
  | _, _, .detach ordinary, inner => by
      exact congrArg orderedPacket (rootPair_first ordinary (inner PUnit.unit))
  | _, _, .descend cut, inner => toRemainderPlan_lowerPacket cut inner

end

mutual

theorem toRemainderPlan_middlePacket : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    orderedPacket (.descend (toRemainderPlan upper inner).2) = insideMiddlePlan upper inner
  | _, _, .interface _, _ => rfl
  | _, _, .ordinary o children cuts, inner => toRemainderChildren_middlePacket cuts inner

theorem toRemainderChildren_middlePacket : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (upper : CKChildCuts children) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    childrenPacket (toRemainderChildren upper inner).2 = insideMiddleChildren upper inner
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _ h t, inner => by
      have expand := childrenPacket_cons
        (toRemainderBranch h (fun i => inner (.inl i))).2
        (toRemainderChildren t (fun i => inner (.inr i))).2
      apply expand.trans
      exact congrArg₂ List.append
        (congrArg (fun packet => packet.map (prefixEntry [0]))
          (toRemainderBranch_middlePacket h (fun i => inner (.inl i))))
        (congrArg (fun packet => packet.map shiftEntry)
          (toRemainderChildren_middlePacket t (fun i => inner (.inr i))))

theorem toRemainderBranch_middlePacket : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    orderedPacket (toRemainderBranch upper inner).2 = insideMiddlePacket upper inner
  | _, _, .detach ordinary, inner => by
      exact rootPair_middlePacket ordinary (inner PUnit.unit)
  | _, _, .descend cut, inner => toRemainderPlan_middlePacket cut inner

end

mutual

theorem toRemainderPlan_remainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (toRemainderPlan upper inner).2.remainder = upper.remainder
  | _, _, .interface _, _ => rfl
  | _, _, .ordinary o children cuts, inner =>
      congrArg (CKTree.ordinary o) (toRemainderChildren_remainder cuts inner)

theorem toRemainderChildren_remainder : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (upper : CKChildCuts children) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (toRemainderChildren upper inner).2.remainder = upper.remainder
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _ h t, inner =>
      congrArg₂ CKChildren.cons
        (toRemainderBranch_remainder h (fun i => inner (.inl i)))
        (toRemainderChildren_remainder t (fun i => inner (.inr i)))

theorem toRemainderBranch_remainder : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (toRemainderBranch upper inner).2.remainder = insideRemainder upper inner
  | _, _, .detach ordinary, inner => by
      exact rootPair_remainder ordinary (inner PUnit.unit)
  | _, _, .descend cut, inner => toRemainderPlan_remainder cut inner

end

/-- Literal three-output equality before commutative forest collection. -/
theorem branchFlag_outputs {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (flag : BranchInside tree) :
    (orderedPacket ((branchFlagEquiv tree flag).1),
      orderedPacket ((branchFlagEquiv tree flag).2),
      (branchFlagEquiv tree flag).2.remainder) =
    (insideLowerPacket flag.1 flag.2, insideMiddlePacket flag.1 flag.2,
      insideRemainder flag.1 flag.2) := by
  change (orderedPacket (toRemainderBranch flag.1 flag.2).1,
    orderedPacket (toRemainderBranch flag.1 flag.2).2,
    (toRemainderBranch flag.1 flag.2).2.remainder) = _
  rw [toRemainderBranch_lowerPacket, toRemainderBranch_middlePacket,
    toRemainderBranch_remainder]

mutual

theorem toRemainderPlan_intermediate : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKCutPlan tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (toRemainderPlan upper inner).1.remainder = upper.fill (fun i => (inner i).remainder)
  | _, _, .interface _, _ => rfl
  | _, _, .ordinary o children cuts, inner =>
      congrArg (CKTree.ordinary o) (toRemainderChildren_intermediate cuts inner)

theorem toRemainderChildren_intermediate : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (upper : CKChildCuts children) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (toRemainderChildren upper inner).1.remainder = upper.fill (fun i => (inner i).remainder)
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _ h t, inner =>
      congrArg₂ CKChildren.cons
        (toRemainderBranch_intermediate h (fun i => inner (.inl i)))
        (toRemainderChildren_intermediate t (fun i => inner (.inr i)))

theorem toRemainderBranch_intermediate : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (upper : CKBranchCut tree) →
    (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) →
    (toRemainderBranch upper inner).1.remainder = upper.fill (fun i => (inner i).remainder)
  | _, _, .detach ordinary, inner => by
      exact congrArg CKBranchCut.remainder (rootPair_first ordinary (inner PUnit.unit))
  | _, _, .descend cut, inner => toRemainderPlan_intermediate cut inner

end

/-- Both staged fillings recover the literal original native proof. -/
theorem inside_refill {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (upper : CKBranchCut tree) (inner : (site : upper.Site) → CKBranchCut (upper.detached site)) :
    upper.fill (fun i => (inner i).fill (inner i).detached) = tree := by
  have factors : (fun i => (inner i).fill (inner i).detached) = upper.detached := by
    funext i
    exact (inner i).fill_detached_reconstructs
  rw [factors, upper.fill_detached_reconstructs]

theorem remainder_refill {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (flag : BranchRemainder tree) :
    flag.2.fill flag.2.detached = flag.1.remainder ∧ flag.1.fill flag.1.detached = tree :=
  ⟨flag.2.fill_detached_reconstructs, flag.1.fill_detached_reconstructs⟩

end Potkin.Research.RemainderExtractionFlags

#check Potkin.Research.RemainderExtractionFlags.branchFlagEquiv
#print axioms Potkin.Research.RemainderExtractionFlags.branchFlagEquiv
#check Potkin.Research.RemainderExtractionFlags.branchFlag_outputs
#print axioms Potkin.Research.RemainderExtractionFlags.branchFlag_outputs
#print axioms Potkin.Research.RemainderExtractionFlags.inside_refill
#print axioms Potkin.Research.RemainderExtractionFlags.remainder_refill
#print axioms Potkin.Research.RemainderExtractionFlags.toRemainderBranch_intermediate

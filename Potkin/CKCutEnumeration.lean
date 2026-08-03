import Mathlib.Data.List.ProdSigma
import Potkin.CKCut

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual

/-- Constructor-recursive enumeration of every cut plan below one root. -/
def CKCutPlan.enumerate : {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) -> List (CKCutPlan tree)
  | _, .interface G => [.interface G]
  | _, .ordinary o children =>
      children.enumerateCuts.map (CKCutPlan.ordinary o children)

/-- Cartesian product of the independent choices in every ordered premise.
The tail is the outer loop, so the earlier premise slot varies fastest, as in
the operational reference. -/
def CKChildren.enumerateCuts : {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
      List (CKChildCuts children)
  | _, .nil => [.nil]
  | _, .cons head tail =>
      (tail.enumerateCuts.product head.enumerateBranchCuts).map
        (fun pair => .cons head tail pair.2 pair.1)

/-- One child contributes either its whole ordinary root or one cut strictly
below that root.  An interface has only the empty descending choice. -/
def CKTree.enumerateBranchCuts : {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) -> List (CKBranchCut tree)
  | _, .interface G => [.descend (.interface G)]
  | _, .ordinary o children =>
      let plans := children.enumerateCuts.map (CKCutPlan.ordinary o children)
      (plans.filter fun plan => plan.siteOrder.isEmpty).map CKBranchCut.descend ++
        [.detach (by trivial)] ++
        (plans.filter fun plan => !plan.siteOrder.isEmpty).map CKBranchCut.descend

end

mutual

/-- A constructor-only measure used to justify recursive enumeration proofs
without comparing dependent tree indices. -/
@[simp] def CKCutPlan.cutWeight : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> CKCutPlan tree -> Nat
  | _, _, .interface _ => 1
  | _, _, .ordinary _ _ cuts => cuts.cutWeight + 1

@[simp] def CKChildCuts.cutWeight : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
      CKChildCuts children -> Nat
  | _, _, .nil => 1
  | _, _, .cons _ _ headCut tailCuts =>
      headCut.cutWeight + tailCuts.cutWeight + 1

@[simp] def CKBranchCut.cutWeight : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> CKBranchCut tree -> Nat
  | _, _, .detach _ => 1
  | _, _, .descend cut => cut.cutWeight + 1

end

mutual

/-- The recursive plan enumeration contains no duplicate constructor plans. -/
theorem CKCutPlan.enumerate_nodup {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) :
    (CKCutPlan.enumerate tree).Nodup := by
  cases tree with
  | interface G => simp [CKCutPlan.enumerate]
  | ordinary o children =>
      apply children.enumerateCuts_nodup.map
      intro a b h
      injection h

/-- Unique ordered branch decomposition makes the child Cartesian product
duplicate-free. -/
theorem CKChildren.enumerateCuts_nodup
    {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries) :
    children.enumerateCuts.Nodup := by
  cases children with
  | nil => simp [CKChildren.enumerateCuts]
  | cons head tail =>
      apply (tail.enumerateCuts_nodup.product head.enumerateBranchCuts_nodup).map
      intro a b h
      cases a with
      | mk tailA headA =>
          cases b with
          | mk tailB headB =>
              cases h
              rfl

/-- The whole-root and strict-descendant alternatives are disjoint, and each
strict-descendant plan occurs once. -/
theorem CKTree.enumerateBranchCuts_nodup {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) :
    tree.enumerateBranchCuts.Nodup := by
  cases tree with
  | interface G => simp [CKTree.enumerateBranchCuts]
  | ordinary o children =>
      let plans := children.enumerateCuts.map (CKCutPlan.ordinary o children)
      have plansNodup : plans.Nodup := by
        apply children.enumerateCuts_nodup.map
        intro a b h
        injection h
      have emptyNodup :
          ((plans.filter fun plan => plan.siteOrder.isEmpty).map
            CKBranchCut.descend).Nodup := by
        apply (plansNodup.filter _).map
        intro a b h
        injection h
      have properNodup :
          ((plans.filter fun plan => !plan.siteOrder.isEmpty).map
            CKBranchCut.descend).Nodup := by
        apply (plansNodup.filter _).map
        intro a b h
        injection h
      have rightNodup :
          (CKBranchCut.detach (by trivial) ::
            (plans.filter fun plan => !plan.siteOrder.isEmpty).map
              CKBranchCut.descend).Nodup := by
        apply List.nodup_cons.mpr
        constructor
        · intro member
          rcases List.mem_map.mp member with ⟨plan, _, impossible⟩
          cases impossible
        · exact properNodup
      rw [CKTree.enumerateBranchCuts]
      rw [List.append_assoc]
      apply emptyNodup.append rightNodup
      rw [List.disjoint_left]
      intro branch inEmpty inRight
      rcases List.mem_map.mp inEmpty with ⟨emptyPlan, emptyMember, rfl⟩
      rcases List.mem_cons.mp inRight with impossible | inProper
      · cases impossible
      · rcases List.mem_map.mp inProper with
          ⟨properPlan, properMember, sameBranch⟩
        injection sameBranch with samePlan
        subst properPlan
        have emptyTest := (List.mem_filter.mp emptyMember).2
        have properTest := (List.mem_filter.mp properMember).2
        simp_all

end

mutual

/-- Every structural plan appears in the recursive enumeration. -/
theorem CKCutPlan.mem_enumerate : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> (cut : CKCutPlan tree) ->
      cut ∈ CKCutPlan.enumerate tree
  | _, _, .interface G => by simp [CKCutPlan.enumerate]
  | _, _, .ordinary o children cuts =>
      List.mem_map.mpr ⟨cuts, cuts.mem_enumerate, rfl⟩
termination_by _ _ cut => CKCutPlan.cutWeight cut
decreasing_by
  all_goals
    simp only [CKCutPlan.cutWeight]
    omega

/-- The Cartesian enumeration contains every exact ordered child-choice
tuple. -/
theorem CKChildCuts.mem_enumerate :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> cuts ∈ children.enumerateCuts
  | _, _, .nil => by simp [CKChildren.enumerateCuts]
  | _, _, .cons head tail headCut tailCuts => by
      apply List.mem_map.mpr
      exact ⟨(tailCuts, headCut),
        List.mem_product.mpr
          ⟨tailCuts.mem_enumerate, headCut.mem_enumerate⟩, rfl⟩
termination_by _ _ cuts => CKChildCuts.cutWeight cuts
decreasing_by
  all_goals
    simp only [CKChildCuts.cutWeight]
    omega

/-- Root-detach and strict-descent alternatives exhaust one child branch. -/
theorem CKBranchCut.mem_enumerate : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> (cut : CKBranchCut tree) ->
      cut ∈ tree.enumerateBranchCuts
  | _, tree, .detach ordinary => by
      cases tree with
      | interface => exact False.elim ordinary
      | ordinary o children => simp [CKTree.enumerateBranchCuts]
  | _, tree, .descend plan => by
      have planMember : plan ∈ CKCutPlan.enumerate tree :=
        plan.mem_enumerate
      cases tree with
      | interface G =>
          simp [CKCutPlan.enumerate] at planMember
          subst plan
          simp [CKTree.enumerateBranchCuts]
      | ordinary o children =>
          by_cases h : plan.siteOrder = []
          · rw [CKTree.enumerateBranchCuts]
            apply List.mem_append.mpr
            left
            apply List.mem_append.mpr
            left
            apply List.mem_map.mpr
            exact ⟨plan, List.mem_filter.mpr ⟨planMember, by simp [h]⟩, rfl⟩
          · rw [CKTree.enumerateBranchCuts]
            apply List.mem_append.mpr
            right
            apply List.mem_map.mpr
            exact ⟨plan, List.mem_filter.mpr ⟨planMember, by simp [h]⟩, rfl⟩
termination_by _ _ cut => cut.cutWeight
decreasing_by
  all_goals
    simp only [CKBranchCut.cutWeight]
    omega

end

namespace CKCut

variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Every finite recursive address antichain of a positive source. -/
def enumerate (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) : List (CKCut tree) :=
  (CKCutPlan.enumerate tree).map (fun plan =>
    { sourceOrdinary := ordinary
      plan := plan })

/-- The CK-cut enumerator is duplicate-free as occurrence witnesses, before
any forest projection. -/
theorem enumerate_nodup (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) : (enumerate tree ordinary).Nodup := by
  apply (CKCutPlan.enumerate_nodup tree).map
  intro a b h
  injection h

/-- Completeness for the intrinsic finite prefix-free nonroot cut type. -/
theorem mem_enumerate (cut : CKCut tree) :
    cut ∈ enumerate tree cut.sourceOrdinary := by
  cases cut with
  | mk sourceOrdinary plan =>
      exact List.mem_map.mpr ⟨plan, plan.mem_enumerate, rfl⟩

/-- Every enumerated cut retains the intrinsic CK-cut soundness guarantees:
each selected site is an existing nonroot ordinary vertex, and distinct sites
are prefix-incomparable. -/
theorem enumerate_sound (ordinary : tree.IsOrdinary) {cut : CKCut tree}
    (_member : cut ∈ enumerate tree ordinary) :
    (∀ site : cut.Site,
      tree.VertexAt (cut.plan.address site) ∧ cut.plan.address site ≠ []) ∧
      (∀ {p q : cut.Site}, p ≠ q →
        PrefixIncomparable (cut.plan.address p) (cut.plan.address q)) := by
  constructor
  · intro site
    exact ⟨cut.address_exists site, cut.address_nonroot site⟩
  · intro p q different
    exact cut.addresses_prefixFree different

/-- Insert one address into an already canonical request.  This transparent
helper keeps executable fixtures reducible under ordinary `decide`. -/
private def insertAddress (address : InternalAddress) :
    List InternalAddress -> List InternalAddress
  | [] => [address]
  | head :: tail =>
      if address < head then
        address :: head :: tail
      else
        head :: insertAddress address tail

/-- Canonical lexicographic presentation of a requested internal-address
antichain.  Sorting deliberately preserves duplicates so malformed repeated
occurrences still fail to match an intrinsic cut. -/
private def canonicalAddresses : List InternalAddress -> List InternalAddress
  | [] => []
  | head :: tail => insertAddress head (canonicalAddresses tail)

/-- Executable validation against the canonical internal address list.
Malformed, root, duplicate, nonvertex, and prefix-comparable requests have no
structural cut and therefore return `none`. -/
def validateAddresses (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) (requested : List InternalAddress) :
    Option (CKCut tree) :=
  (enumerate tree ordinary).find? (fun cut =>
    cut.orderedAddresses == canonicalAddresses requested)

/-- Validation in the positive one-based interchange convention. -/
def validateRacketAddresses (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) (requested : List RacketAddress) :
    Option (CKCut tree) :=
  (enumerate tree ordinary).find? (fun cut =>
    cut.orderedAddresses ==
      canonicalAddresses (requested.map RacketAddress.toInternal))

/-- Proper cuts are obtained by discarding the unique all-descend empty plan. -/
def enumerateProper (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) : List (ProperCKCut tree) :=
  (enumerate tree ordinary).filterMap (fun cut =>
    match cut.orderedSites with
    | [] => none
    | site :: _ => some ⟨cut, ⟨site⟩⟩)

end CKCut

end Potkin

import Potkin.CKCutValidity
import Potkin.RealizedCut

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

local instance decidableAddressPrefixPruning
    (left right : InternalAddress) : Decidable (AddressPrefix left right) := by
  unfold AddressPrefix
  infer_instance

/-- Homogeneous equality embeds into heterogeneous equality. -/
theorem heqOfEq {alpha : Sort u} {left right : alpha}
    (equal : left = right) : HEq left right := by
  cases equal
  rfl

namespace CKTree

/-- Replace every selected source address by an interface, retaining every
unselected occurrence decoration and ordered premise literally.  This total
source-address operation is independent of a recursive cut certificate. -/
def pruneAddresses : {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) -> Finset InternalAddress ->
      CKTree sigma InstanceData G
  | _, .interface G, _ => .interface G
  | _, .ordinary o children, addresses =>
      if [] ∈ addresses then
        .interface o.shape.conclusion
      else
        .ordinaryFn o (fun i =>
          pruneAddresses (children.get i)
            (CKAddressAntichain.stripSlot i.1 addresses))
termination_by _ tree _ => tree.degree
decreasing_by
  exact CKChildren.degree_get_lt_parent children i

@[simp]
theorem pruneAddresses_interface (G : Hypersequent sigma)
    (addresses : Finset InternalAddress) :
    (CKTree.interface G : CKTree sigma InstanceData G).pruneAddresses
      addresses = .interface G := by
  simp [pruneAddresses]

@[simp]
theorem pruneAddresses_ordinary_root_selected
    (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (addresses : Finset InternalAddress) (root : [] ∈ addresses) :
    (CKTree.ordinary o children).pruneAddresses addresses =
      .interface o.shape.conclusion := by
  simp [pruneAddresses, root]

@[simp]
theorem pruneAddresses_ordinary_root_absent
    (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (addresses : Finset InternalAddress) (root : [] ∉ addresses) :
    (CKTree.ordinary o children).pruneAddresses addresses =
      .ordinaryFn o (fun i =>
        (children.get i).pruneAddresses
          (CKAddressAntichain.stripSlot i.1 addresses)) := by
  simp [pruneAddresses, root]

end CKTree

mutual

/-- Total data-valued lookup of an exact positive decorated subtree.  Unlike
`VertexAt`, this computational function can eliminate into `CKComponent`. -/
def CKTree.componentAt? : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> InternalAddress ->
      Option (CKComponent sigma InstanceData)
  | _, .interface _, _ => none
  | _, .ordinary o children, [] =>
      some { boundary := o.shape.conclusion
             tree := .ordinary o children
             ordinary := trivial }
  | _, .ordinary _ children, slot :: rest =>
      children.componentAtAddress? (slot :: rest)

/-- Ordered-child implementation of total decorated-subtree lookup. -/
def CKChildren.componentAtAddress? :
    {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries -> InternalAddress ->
      Option (CKComponent sigma InstanceData)
  | _, .nil, _ => none
  | _, .cons _ _, [] => none
  | _, .cons head _, 0 :: rest => head.componentAt? rest
  | _, .cons _ tail, (slot + 1) :: rest =>
      tail.componentAtAddress? (slot :: rest)

end

namespace CKChildren

/-- In-range ordered-child lookup agrees with dependent `get`. -/
theorem componentAtAddress?_eq_get
    {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries)
    (i : Fin boundaries.length) (rest : InternalAddress) :
    children.componentAtAddress? (i.1 :: rest) =
      (children.get i).componentAt? rest := by
  induction boundaries with
  | nil => exact Fin.elim0 i
  | cons G Gs ih =>
      cases children with
      | cons head tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simpa [CKChildren.componentAtAddress?, CKChildren.get] using
                ih tail i

/-- An out-of-range ordered premise selector has no decorated subtree. -/
theorem componentAtAddress?_eq_none_of_length_le
    {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries)
    {slot : Nat} (outOfRange : boundaries.length ≤ slot)
    (rest : InternalAddress) :
    children.componentAtAddress? (slot :: rest) = none := by
  induction boundaries generalizing slot with
  | nil => cases children; rfl
  | cons G Gs ih =>
      cases children with
      | cons head tail =>
          cases slot with
          | zero =>
              have impossible : ¬ (List.length (G :: Gs) ≤ 0) := by simp
              exact False.elim (impossible outOfRange)
          | succ slot =>
              have tailOutOfRange : Gs.length ≤ slot := by
                exact Nat.le_of_succ_le_succ (by simpa using outOfRange)
              exact ih tail tailOutOfRange

/-- Lookup in children assembled by `ofFn` returns the exact supplied child. -/
theorem componentAtAddress?_ofFn
    {boundaries : List (Hypersequent sigma)}
    (children : (i : Fin boundaries.length) →
      CKTree sigma InstanceData (boundaries.get i))
    (i : Fin boundaries.length) (rest : InternalAddress) :
    (CKChildren.ofFn children).componentAtAddress? (i.1 :: rest) =
      (children i).componentAt? rest := by
  rw [componentAtAddress?_eq_get, CKChildren.get_ofFn]

end CKChildren

namespace CKCutPlan

def detachedComponent {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCutPlan tree)
    (site : cut.Site) : CKComponent sigma InstanceData :=
  { boundary := cut.siteBoundary site
    tree := cut.detached site
    ordinary := cut.detachedOrdinary site }

end CKCutPlan

namespace CKChildCuts

def detachedComponent {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (cuts : CKChildCuts children) (site : cuts.Site) :
    CKComponent sigma InstanceData :=
  { boundary := cuts.siteBoundary site
    tree := cuts.detached site
    ordinary := cuts.detachedOrdinary site }

end CKChildCuts

namespace CKBranchCut

def detachedComponent {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree)
    (site : cut.Site) : CKComponent sigma InstanceData :=
  { boundary := cut.siteBoundary site
    tree := cut.detached site
    ordinary := cut.detachedOrdinary site }

end CKBranchCut

mutual

/-- Looking up a plan site in its source returns its actual detached component. -/
theorem CKCutPlan.componentAt?_address_eq_detachedComponent :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (site : cut.Site) ->
    tree.componentAt? (cut.address site) =
      some (cut.detachedComponent site)
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary _ children cuts, site => by
      have nonempty := cuts.address_nonroot site
      cases addressEq : cuts.address site with
      | nil => exact (nonempty addressEq).elim
      | cons slot rest =>
          change (CKTree.ordinary _ children).componentAt?
              (cuts.address site) =
            some (cuts.detachedComponent site)
          rw [addressEq]
          change children.componentAtAddress? (slot :: rest) =
            some (cuts.detachedComponent site)
          have recursive :=
            cuts.componentAt?_address_eq_detachedComponent site
          rw [addressEq] at recursive
          exact recursive

theorem CKChildCuts.componentAt?_address_eq_detachedComponent :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (site : cuts.Site) ->
    children.componentAtAddress? (cuts.address site) =
      some (cuts.detachedComponent site)
  | _, _, .nil, site => nomatch site
  | _, _, .cons head tail headCut tailCuts, site => by
      change Sum headCut.Site tailCuts.Site at site
      cases site with
      | inl site =>
          change head.componentAt? (headCut.relativeAddress site) =
            some (headCut.detachedComponent site)
          exact headCut.componentAt?_address_eq_detachedComponent site
      | inr site =>
          have nonempty := tailCuts.address_nonroot site
          cases addressEq : tailCuts.address site with
          | nil => exact (nonempty addressEq).elim
          | cons slot rest =>
              change (CKChildren.cons head tail).componentAtAddress?
                  (InternalAddress.shiftHead (tailCuts.address site)) =
                some (tailCuts.detachedComponent site)
              rw [addressEq]
              change tail.componentAtAddress? (slot :: rest) =
                some (tailCuts.detachedComponent site)
              have recursive :=
                tailCuts.componentAt?_address_eq_detachedComponent site
              rw [addressEq] at recursive
              exact recursive

theorem CKBranchCut.componentAt?_address_eq_detachedComponent :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (site : cut.Site) ->
    tree.componentAt? (cut.relativeAddress site) =
      some (cut.detachedComponent site)
  | _, tree, .detach ordinary, site => by
      change PUnit at site
      cases site
      cases tree with
      | interface => exact False.elim ordinary
      | ordinary o children => rfl
  | _, _, .descend cut, site =>
      cut.componentAt?_address_eq_detachedComponent site

end

namespace CKCut

/-- Exact detached occurrence as a boundary-packaged connected component. -/
def detachedComponent {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCut tree)
    (site : cut.Site) : CKComponent sigma InstanceData :=
  cut.plan.detachedComponent site

/-- Positive source component of a public cut. -/
def sourceComponent {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCut tree) :
    CKComponent sigma InstanceData :=
  { boundary := G
    tree := tree
    ordinary := cut.sourceOrdinary }

/-- Positive retained remainder as a boundary-packaged component. -/
def remainderComponent {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCut tree) :
    CKComponent sigma InstanceData :=
  { boundary := G
    tree := cut.remainder
    ordinary := cut.remainder_isOrdinary }

/-- Any two cuts selecting the same source address detach the same actual
decorated component, irrespective of their proof certificates. -/
theorem detachedComponent_eq_of_address_eq
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (left right : CKCut tree) (leftSite : left.Site)
    (rightSite : right.Site)
    (addressEq : left.plan.address leftSite =
      right.plan.address rightSite) :
    left.detachedComponent leftSite = right.detachedComponent rightSite := by
  have leftLookup :=
    left.plan.componentAt?_address_eq_detachedComponent leftSite
  have rightLookup :=
    right.plan.componentAt?_address_eq_detachedComponent rightSite
  have equalSome : some (left.detachedComponent leftSite) =
      some (right.detachedComponent rightSite) := by
    change some (left.plan.detachedComponent leftSite) =
      some (right.plan.detachedComponent rightSite)
    rw [← leftLookup, ← rightLookup, addressEq]
  exact Option.some.inj equalSome

/-- Exact occurrence-site/address bijection for one recursive cut. -/
noncomputable def siteAddressEquiv
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCut tree) :
    cut.Site ≃ {address // address ∈ cut.plan.addressFinset} where
  toFun site := ⟨cut.plan.address site,
    (cut.plan.mem_addressFinset_iff _).mpr ⟨site, rfl⟩⟩
  invFun occurrence := Classical.choose
    ((cut.plan.mem_addressFinset_iff occurrence.1).mp occurrence.2)
  left_inv := by
    intro site
    apply cut.address_injective
    exact (Classical.choose_spec
      ((cut.plan.mem_addressFinset_iff _).mp
        ((cut.plan.mem_addressFinset_iff _).mpr ⟨site, rfl⟩)))
  right_inv := by
    intro occurrence
    apply Subtype.ext
    exact Classical.choose_spec
      ((cut.plan.mem_addressFinset_iff occurrence.1).mp occurrence.2)

@[simp]
theorem siteAddressEquiv_apply_val
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCut tree) (site : cut.Site) :
    (cut.siteAddressEquiv site).1 = cut.plan.address site := rfl

end CKCut

namespace CKChildCuts

/-- The retained child at an exact ordered slot is the remainder of the
branch selected at that slot. -/
theorem get_remainder_eq_branchAt_remainder
    {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (cuts : CKChildCuts children) (i : Fin boundaries.length) :
    cuts.remainder.get i = (cuts.branchAt i).remainder := by
  induction boundaries with
  | nil => exact Fin.elim0 i
  | cons G Gs ih =>
      cases children with
      | cons head tail =>
          cases cuts with
          | cons _ _ headCut tailCuts =>
              cases i using Fin.cases with
              | zero => rfl
              | succ i =>
                  simpa [CKChildCuts.remainder, CKChildren.get,
                    CKChildCuts.branchAt] using ih tailCuts i

/-- Remainders commute with assembling independent ordered branch choices. -/
theorem remainder_ofFn
    {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries)
    (branches : (i : Fin boundaries.length) ->
      CKBranchCut (children.get i)) :
    (CKChildCuts.ofFn children branches).remainder =
      CKChildren.ofFn (fun i => (branches i).remainder) := by
  apply CKChildren.ext
  intro i
  rw [CKChildren.get_ofFn,
    get_remainder_eq_branchAt_remainder,
    CKChildCuts.branchAt_ofFn]

end CKChildCuts

mutual

/-- The recursively compiled plan has exactly the occurrence-preserving
source-address remainder computed by `pruneAddresses`. -/
theorem CKNonrootAddressAntichain.toPlan_remainder_eq_pruneAddresses :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (family : CKNonrootAddressAntichain tree) ->
      family.toPlan.1.remainder =
        tree.pruneAddresses family.addresses
  | _, .interface G, family => by
      rw [CKNonrootAddressAntichain.toPlan]
      change CKTree.interface G =
        (CKTree.interface G : CKTree sigma InstanceData G).pruneAddresses
          family.addresses
      symm
      exact CKTree.pruneAddresses_interface G family.addresses
  | _, .ordinary o children, family => by
      have rootAbsent : [] ∉ family.addresses := by
        intro rootMember
        exact family.address_nonroot rootMember rfl
      rw [CKTree.pruneAddresses_ordinary_root_absent _ _ _ rootAbsent]
      rw [CKNonrootAddressAntichain.toPlan]
      change CKTree.ordinary o
          ((CKChildCuts.ofFn children (fun i =>
            (family.toCKAddressAntichain.atChild i).toBranch |>.1)).remainder) =
        CKTree.ordinary o (CKChildren.ofFn (fun i =>
          (children.get i).pruneAddresses
            (CKAddressAntichain.stripSlot i.1 family.addresses)))
      apply congrArg (CKTree.ordinary o)
      rw [CKChildCuts.remainder_ofFn]
      apply CKChildren.ofFn_congr
      intro i
      exact CKAddressAntichain.toBranch_remainder_eq_pruneAddresses
        (family.toCKAddressAntichain.atChild i)
termination_by _ tree _ => 2 * tree.degree
decreasing_by
  all_goals
    exact CKChildren.branchMeasure_lt_parent children _

/-- The relative branch compiler is the root-selecting case of the same
source-address pruning operation. -/
theorem CKAddressAntichain.toBranch_remainder_eq_pruneAddresses :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (family : CKAddressAntichain tree) ->
      family.toBranch.1.remainder =
        tree.pruneAddresses family.addresses
  | _, tree, family => by
      by_cases rootMember : [] ∈ family.addresses
      · have rootOrdinary := CKTree.isOrdinary_of_vertexAt_root
          (family.address_vertex rootMember)
        have pruneEq : tree.pruneAddresses family.addresses =
            CKTree.interface tree.rootBoundary := by
          cases tree with
          | interface G => exact False.elim rootOrdinary
          | ordinary o children =>
              exact CKTree.pruneAddresses_ordinary_root_selected
                o children family.addresses rootMember
        rw [CKAddressAntichain.toBranch]
        simp only [rootMember, ↓reduceDIte, CKBranchCut.remainder]
        exact pruneEq.symm
      · rw [CKAddressAntichain.toBranch]
        simp only [rootMember, ↓reduceDIte, CKBranchCut.remainder]
        exact CKNonrootAddressAntichain.toPlan_remainder_eq_pruneAddresses
          (family.withoutRoot rootMember)
termination_by _ tree _ => 2 * tree.degree + 1
decreasing_by simp_wf

end

namespace ValidAddressCut

/-- A public extensional cut's actual decorated remainder is computed solely
from its source tree and exact address set.  No cut-proof equality is used. -/
theorem remainder_eq_pruneAddresses
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : ValidAddressCut tree) :
    cut.toCut.remainder = tree.pruneAddresses cut.addresses :=
  CKNonrootAddressAntichain.toPlan_remainder_eq_pruneAddresses
    cut.toCKNonrootAddressAntichain

end ValidAddressCut

namespace AddressSelection

/-- A selected source address lies weakly above `address`. -/
def Dominates (selected : Finset InternalAddress)
    (address : InternalAddress) : Prop :=
  ∃ anchor ∈ selected, AddressPrefix anchor address

/-- Selected suffixes weakly below one exact source address.  The recursive
definition keeps selector arithmetic aligned with `CKTree` descent. -/
def belowRelative : Finset InternalAddress → InternalAddress →
    Finset InternalAddress
  | selected, [] => selected
  | selected, slot :: rest =>
      belowRelative (CKAddressAntichain.stripSlot slot selected) rest

@[simp]
theorem mem_belowRelative_iff (selected : Finset InternalAddress)
    (anchor relative : InternalAddress) :
    relative ∈ belowRelative selected anchor ↔
      anchor ++ relative ∈ selected := by
  induction anchor generalizing selected with
  | nil => rfl
  | cons slot rest ih =>
      rw [belowRelative, ih, CKAddressAntichain.mem_stripSlot]
      rfl

/-- If no selected address dominates an anchor, the relative family below
that anchor cannot select its root. -/
theorem belowRelative_root_absent {selected : Finset InternalAddress}
    {anchor : InternalAddress} (outside : ¬ Dominates selected anchor) :
    [] ∉ belowRelative selected anchor := by
  intro member
  have anchorMember : anchor ∈ selected := by
    simpa using (mem_belowRelative_iff selected anchor []).mp member
  exact outside ⟨anchor, anchorMember, by simp [AddressPrefix]⟩

/-- Source-nearest members of an arbitrary finite address family. -/
def frontier (selected : Finset InternalAddress) :
    Finset InternalAddress :=
  selected.filter fun address =>
    ¬ ∃ outer ∈ selected,
      AddressPrefix outer address ∧ address ≠ outer

/-- Removing dominated finite addresses preserves exactly the same weakly
dominated source region.  The terminating ascent chooses a strict prefix at
each step, so no global order or cut certificate is involved. -/
theorem dominates_frontier_iff (selected : Finset InternalAddress)
    (address : InternalAddress) :
    Dominates (frontier selected) address ↔ Dominates selected address := by
  constructor
  · rintro ⟨anchor, anchorMember, anchorPrefix⟩
    exact ⟨anchor, (Finset.mem_filter.mp anchorMember).1, anchorPrefix⟩
  · rintro ⟨initial, initialMember, initialPrefix⟩
    let rec ascend (current : InternalAddress)
        (currentMember : current ∈ selected)
        (currentPrefix : AddressPrefix current address) :
        ∃ anchor ∈ frontier selected,
          AddressPrefix anchor address := by
      by_cases currentFrontier : current ∈ frontier selected
      · exact ⟨current, currentFrontier, currentPrefix⟩
      · have hasOuter : ∃ outer ∈ selected,
            AddressPrefix outer current ∧ current ≠ outer := by
          by_contra noOuter
          exact currentFrontier
            (Finset.mem_filter.mpr ⟨currentMember, noOuter⟩)
        rcases hasOuter with
          ⟨outer, outerMember, outerPrefix, currentNeOuter⟩
        have lengthNe : outer.length ≠ current.length := by
          intro lengthEq
          have outerEqCurrent : outer = current :=
            outerPrefix.eq_of_length_le (by omega)
          exact currentNeOuter outerEqCurrent.symm
        have lengthLt : outer.length < current.length := by
          have lengthLe := outerPrefix.length_le
          omega
        exact ascend outer outerMember
          (outerPrefix.trans currentPrefix)
    termination_by current.length
    decreasing_by exact lengthLt
    exact ascend initial initialMember initialPrefix

/-- Retain exactly those selected source addresses which are not weakly below
any address in the barrier family. -/
def retainedAfter (barrier selected : Finset InternalAddress) :
    Finset InternalAddress :=
  selected.filter fun source =>
    ∀ anchor ∈ barrier, ¬ AddressPrefix anchor source

@[simp]
theorem mem_retainedAfter {barrier selected : Finset InternalAddress}
    {source : InternalAddress} :
    source ∈ retainedAfter barrier selected ↔
      source ∈ selected ∧
        ∀ anchor ∈ barrier, ¬ AddressPrefix anchor source := by
  simp [retainedAfter]

/-- Restricting retained addresses to one ordered child commutes with
retention, provided the barrier does not select the current root. -/
theorem stripSlot_retainedAfter (slot : Nat)
    (barrier selected : Finset InternalAddress)
    (rootAbsent : [] ∉ barrier) :
    CKAddressAntichain.stripSlot slot (retainedAfter barrier selected) =
      retainedAfter (CKAddressAntichain.stripSlot slot barrier)
        (CKAddressAntichain.stripSlot slot selected) := by
  ext relative
  rw [CKAddressAntichain.mem_stripSlot, mem_retainedAfter,
    mem_retainedAfter, CKAddressAntichain.mem_stripSlot]
  constructor
  · rintro ⟨selectedMember, outside⟩
    refine ⟨selectedMember, ?_⟩
    intro anchor anchorMember anchorPrefix
    exact outside (slot :: anchor)
      (CKAddressAntichain.mem_stripSlot.mp anchorMember)
      (by simpa [AddressPrefix] using anchorPrefix)
  · rintro ⟨selectedMember, outside⟩
    refine ⟨selectedMember, ?_⟩
    intro anchor anchorMember anchorPrefix
    cases anchor with
    | nil => exact rootAbsent anchorMember
    | cons head tail =>
        have data : head = slot ∧ AddressPrefix tail relative := by
          simpa [AddressPrefix] using anchorPrefix
        exact outside tail
          (CKAddressAntichain.mem_stripSlot.mpr (by
            simpa [data.1] using anchorMember)) data.2

/-- Child restriction distributes over union of source-address families. -/
theorem stripSlot_union (slot : Nat)
    (left right : Finset InternalAddress) :
    CKAddressAntichain.stripSlot slot (left ∪ right) =
      CKAddressAntichain.stripSlot slot left ∪
        CKAddressAntichain.stripSlot slot right := by
  ext relative
  simp only [CKAddressAntichain.mem_stripSlot, Finset.mem_union]

/-- Below one ordered child, weak source domination is exactly domination by
the child-restricted family, unless the current root was itself selected. -/
theorem dominates_stripSlot_iff (slot : Nat)
    (selected : Finset InternalAddress) (relative : InternalAddress)
    (rootAbsent : [] ∉ selected) :
    Dominates (CKAddressAntichain.stripSlot slot selected) relative ↔
      Dominates selected (slot :: relative) := by
  constructor
  · rintro ⟨anchor, anchorMember, anchorPrefix⟩
    exact ⟨slot :: anchor,
      CKAddressAntichain.mem_stripSlot.mp anchorMember,
      by simpa [AddressPrefix] using anchorPrefix⟩
  · rintro ⟨anchor, anchorMember, anchorPrefix⟩
    cases anchor with
    | nil => exact (rootAbsent anchorMember).elim
    | cons head tail =>
        have data : head = slot ∧ AddressPrefix tail relative := by
          simpa [AddressPrefix] using anchorPrefix
        refine ⟨tail, ?_, data.2⟩
        apply CKAddressAntichain.mem_stripSlot.mpr
        simpa [data.1] using anchorMember

end AddressSelection

namespace CKTree

/-- Sequentially pruning a family and then precisely the selected addresses
which survive that pruning is the direct source-address pruning by their
union.  Every retained occurrence decoration and premise position is literal. -/
theorem pruneAddresses_retainedAfter :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    (barrier selected : Finset InternalAddress) ->
    (tree.pruneAddresses barrier).pruneAddresses
        (AddressSelection.retainedAfter barrier selected) =
      tree.pruneAddresses (barrier ∪ selected)
  | _, .interface G, barrier, selected => by
      simp [CKTree.pruneAddresses]
  | _, .ordinary o children, barrier, selected => by
      by_cases barrierRoot : [] ∈ barrier
      · have unionRoot : [] ∈ barrier ∪ selected :=
          Finset.mem_union_left selected barrierRoot
        rw [CKTree.pruneAddresses_ordinary_root_selected
          o children barrier barrierRoot]
        rw [CKTree.pruneAddresses_interface]
        exact (CKTree.pruneAddresses_ordinary_root_selected
          o children (barrier ∪ selected) unionRoot).symm
      · by_cases selectedRoot : [] ∈ selected
        · have retainedRoot : [] ∈
              AddressSelection.retainedAfter barrier selected := by
            apply AddressSelection.mem_retainedAfter.mpr
            refine ⟨selectedRoot, ?_⟩
            intro anchor anchorMember anchorPrefix
            have anchorRoot : anchor = [] := by
              simpa [AddressPrefix] using anchorPrefix
            exact barrierRoot (anchorRoot ▸ anchorMember)
          have unionRoot : [] ∈ barrier ∪ selected :=
            Finset.mem_union_right barrier selectedRoot
          rw [CKTree.pruneAddresses_ordinary_root_absent
            o children barrier barrierRoot]
          simp only [CKTree.ordinaryFn]
          rw [CKTree.pruneAddresses_ordinary_root_selected _ _ _ retainedRoot]
          exact (CKTree.pruneAddresses_ordinary_root_selected
            o children (barrier ∪ selected) unionRoot).symm
        · have retainedRoot : [] ∉
              AddressSelection.retainedAfter barrier selected := by
            intro member
            exact selectedRoot
              (AddressSelection.mem_retainedAfter.mp member).1
          have unionRoot : [] ∉ barrier ∪ selected := by
            simp [barrierRoot, selectedRoot]
          rw [CKTree.pruneAddresses_ordinary_root_absent
            o children barrier barrierRoot]
          simp only [CKTree.ordinaryFn]
          rw [CKTree.pruneAddresses_ordinary_root_absent _ _ _ retainedRoot]
          rw [CKTree.pruneAddresses_ordinary_root_absent
            o children (barrier ∪ selected) unionRoot]
          apply CKTree.ordinaryFn_congr
          intro i
          simp only [CKChildren.get_ofFn]
          rw [AddressSelection.stripSlot_retainedAfter
            i.1 barrier selected barrierRoot]
          rw [AddressSelection.stripSlot_union]
          exact pruneAddresses_retainedAfter (children.get i)
            (CKAddressAntichain.stripSlot i.1 barrier)
            (CKAddressAntichain.stripSlot i.1 selected)
termination_by _ tree _ _ => tree.degree
decreasing_by
  exact CKChildren.degree_get_lt_parent children i

/-- Source-address pruning depends only on the weakly dominated address
region.  The proof retains ordinary occurrences and ordered children
constructor by constructor. -/
theorem pruneAddresses_eq_of_dominates_iff :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    (left right : Finset InternalAddress) ->
    (∀ address, AddressSelection.Dominates left address ↔
      AddressSelection.Dominates right address) ->
    tree.pruneAddresses left = tree.pruneAddresses right
  | _, .interface G, left, right, equivalent => by
      simp [CKTree.pruneAddresses]
  | _, .ordinary o children, left, right, equivalent => by
      have rootEquivalent : [] ∈ left ↔ [] ∈ right := by
        simpa [AddressSelection.Dominates, AddressPrefix] using equivalent []
      by_cases leftRoot : [] ∈ left
      · have rightRoot : [] ∈ right := rootEquivalent.mp leftRoot
        rw [CKTree.pruneAddresses_ordinary_root_selected
          o children left leftRoot]
        rw [CKTree.pruneAddresses_ordinary_root_selected
          o children right rightRoot]
      · have rightRoot : [] ∉ right := by
          intro member
          exact leftRoot (rootEquivalent.mpr member)
        rw [CKTree.pruneAddresses_ordinary_root_absent
          o children left leftRoot]
        rw [CKTree.pruneAddresses_ordinary_root_absent
          o children right rightRoot]
        apply CKTree.ordinaryFn_congr
        intro i
        apply pruneAddresses_eq_of_dominates_iff
        intro relative
        rw [AddressSelection.dominates_stripSlot_iff
          i.1 left relative leftRoot]
        rw [AddressSelection.dominates_stripSlot_iff
          i.1 right relative rightRoot]
        exact equivalent (i.1 :: relative)
termination_by _ tree _ _ _ => tree.degree
decreasing_by
  exact CKChildren.degree_get_lt_parent children i

/-- Dominated selections are semantically redundant: pruning the finite
source-nearest frontier gives the same decorated tree as pruning the entire
family. -/
theorem pruneAddresses_frontier (tree : CKTree sigma InstanceData G)
    (selected : Finset InternalAddress) :
    tree.pruneAddresses (AddressSelection.frontier selected) =
      tree.pruneAddresses selected :=
  pruneAddresses_eq_of_dominates_iff tree _ _
    (AddressSelection.dominates_frontier_iff selected)

/-- A nonroot pruning family preserves a positive ordinary root. -/
def pruneAddresses_isOrdinary {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (ordinary : tree.IsOrdinary)
    (selected : Finset InternalAddress) (rootAbsent : [] ∉ selected) :
    (tree.pruneAddresses selected).IsOrdinary := by
  cases tree with
  | interface => exact False.elim ordinary
  | ordinary o children =>
      rw [pruneAddresses_ordinary_root_absent
        o children selected rootAbsent]
      trivial

end CKTree

namespace CKComponent

/-- Boundary and actual decorated-tree equality determine a component;
ordinary-root certificates are proof-irrelevant. -/
@[ext]
theorem ext {left right : CKComponent sigma InstanceData}
    (boundaryEq : left.boundary = right.boundary)
    (treeEq : HEq left.tree right.tree) : left = right := by
  cases left with
  | mk leftBoundary leftTree leftOrdinary =>
      cases right with
      | mk rightBoundary rightTree rightOrdinary =>
          cases boundaryEq
          have equalTree : leftTree = rightTree := eq_of_heq treeEq
          cases equalTree
          rfl

/-- Equality of packaged components transports their dependent decorated
trees through any equal finite pruning family. -/
theorem pruneAddresses_tree_heq_of_eq
    {left right : CKComponent sigma InstanceData}
    (componentEq : left = right)
    {leftSelected rightSelected : Finset InternalAddress}
    (selectedEq : leftSelected = rightSelected) :
    HEq (left.tree.pruneAddresses leftSelected)
      (right.tree.pruneAddresses rightSelected) := by
  cases componentEq
  cases selectedEq
  rfl

/-- Prune strictly below a positive component root. -/
def pruneNonroot (component : CKComponent sigma InstanceData)
    (selected : Finset InternalAddress) (rootAbsent : [] ∉ selected) :
    CKComponent sigma InstanceData :=
  { boundary := component.boundary
    tree := component.tree.pruneAddresses selected
    ordinary := CKTree.pruneAddresses_isOrdinary component.ordinary
      selected rootAbsent }

end CKComponent

namespace ValidAddressCut

/-- Component-packaged form of exact source pruning. -/
theorem remainderComponent_eq_pruneNonroot
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : ValidAddressCut tree) :
    cut.toCut.remainderComponent =
      cut.toCut.sourceComponent.pruneNonroot cut.addresses
        (by
          intro rootMember
          exact cut.address_nonroot rootMember rfl) := by
  apply CKComponent.ext
  · rfl
  · exact heqOfEq (remainder_eq_pruneAddresses cut)

end ValidAddressCut

namespace CKTree

/-- Looking up a surviving source occurrence after pruning returns its exact
source component pruned by precisely the selected relative descendants. -/
theorem componentAt?_pruneAddresses :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    (selected : Finset InternalAddress) -> (anchor : InternalAddress) ->
    (outside : ¬ AddressSelection.Dominates selected anchor) ->
    (tree.pruneAddresses selected).componentAt? anchor =
      (tree.componentAt? anchor).map fun component =>
        component.pruneNonroot
          (AddressSelection.belowRelative selected anchor)
          (AddressSelection.belowRelative_root_absent outside)
  | _, .interface G, selected, anchor, outside => by
      simp [CKTree.pruneAddresses, CKTree.componentAt?]
  | _, .ordinary o children, selected, [], outside => by
      have rootAbsent : [] ∉ selected := by
        intro rootMember
        exact outside ⟨[], rootMember, by simp [AddressPrefix]⟩
      simp [CKTree.pruneAddresses, rootAbsent, CKTree.componentAt?,
        CKComponent.pruneNonroot, AddressSelection.belowRelative,
        CKTree.ordinaryFn]
  | _, .ordinary o children, selected, slot :: rest, outside => by
      have rootAbsent : [] ∉ selected := by
        intro rootMember
        exact outside ⟨[], rootMember, by simp [AddressPrefix]⟩
      rw [CKTree.pruneAddresses_ordinary_root_absent
        o children selected rootAbsent]
      by_cases inRange : slot < o.shape.premises.length
      · let i : Fin o.shape.premises.length := ⟨slot, inRange⟩
        have childOutside : ¬ AddressSelection.Dominates
            (CKAddressAntichain.stripSlot slot selected) rest := by
          rw [AddressSelection.dominates_stripSlot_iff
            slot selected rest rootAbsent]
          exact outside
        change (CKChildren.ofFn (fun i =>
            (children.get i).pruneAddresses
              (CKAddressAntichain.stripSlot i.1 selected))).componentAtAddress?
                (slot :: rest) =
          (children.componentAtAddress? (slot :: rest)).map
            (fun component => component.pruneNonroot
              (AddressSelection.belowRelative
                (CKAddressAntichain.stripSlot slot selected) rest)
              (AddressSelection.belowRelative_root_absent childOutside))
        rw [CKChildren.componentAtAddress?_ofFn _ i rest]
        rw [CKChildren.componentAtAddress?_eq_get children i rest]
        have recursive := componentAt?_pruneAddresses
          (children.get i)
          (CKAddressAntichain.stripSlot i.1 selected) rest childOutside
        simpa [i] using recursive
      · have outOfRange : o.shape.premises.length ≤ slot := by omega
        change (CKChildren.ofFn (fun i =>
            (children.get i).pruneAddresses
              (CKAddressAntichain.stripSlot i.1 selected))).componentAtAddress?
                (slot :: rest) =
          (children.componentAtAddress? (slot :: rest)).map _
        rw [CKChildren.componentAtAddress?_eq_none_of_length_le _
          outOfRange]
        rw [children.componentAtAddress?_eq_none_of_length_le
          outOfRange]
        simp
termination_by _ tree _ _ _ => tree.degree
decreasing_by
  exact CKChildren.degree_get_lt_parent children i

/-- Decorated-subtree lookup composes by literal address prefixing. -/
theorem componentAt?_append_of_eq :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    (outer inner : InternalAddress) ->
    (component : CKComponent sigma InstanceData) ->
    tree.componentAt? outer = some component ->
    component.tree.componentAt? inner =
      tree.componentAt? (outer ++ inner)
  | _, .interface G, outer, inner, component, lookup => by
      simp [CKTree.componentAt?] at lookup
  | _, .ordinary o children, [], inner, component, lookup => by
      have componentEq :
          ({ boundary := o.shape.conclusion
             tree := CKTree.ordinary o children
             ordinary := trivial } : CKComponent sigma InstanceData) =
          component := Option.some.inj lookup
      cases componentEq
      rfl
  | _, .ordinary o children, slot :: rest, inner, component, lookup => by
      by_cases inRange : slot < o.shape.premises.length
      · let i : Fin o.shape.premises.length := ⟨slot, inRange⟩
        have childLookup : (children.get i).componentAt? rest =
            some component := by
          rw [← children.componentAtAddress?_eq_get i rest]
          exact lookup
        have recursive := componentAt?_append_of_eq
          (children.get i) rest inner component childLookup
        change component.tree.componentAt? inner =
          children.componentAtAddress? (slot :: (rest ++ inner))
        rw [show slot = i.1 from rfl]
        rw [children.componentAtAddress?_eq_get i (rest ++ inner)]
        exact recursive
      · have outOfRange : o.shape.premises.length ≤ slot := by omega
        have lookupNone :
            (CKTree.ordinary o children).componentAt? (slot :: rest) =
              none := by
          change children.componentAtAddress? (slot :: rest) = none
          exact children.componentAtAddress?_eq_none_of_length_le
            outOfRange rest
        have impossible : none = some component := lookupNone.symm.trans lookup
        contradiction
termination_by _ tree _ _ _ _ => tree.degree
decreasing_by
  exact CKChildren.degree_get_lt_parent children i

end CKTree

namespace CKCut

/-- A relative detachment inside one outer detached factor is the exact
global source component at the prefixed address. -/
theorem nestedDetachedComponent_globalLookup
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (outerCut : CKCut tree) (outer : outerCut.Site)
    (innerCut : CKCut (outerCut.plan.detached outer))
    (inner : innerCut.Site) :
    tree.componentAt?
        (outerCut.plan.address outer ++ innerCut.plan.address inner) =
      some (innerCut.detachedComponent inner) := by
  have outerLookup :=
    outerCut.plan.componentAt?_address_eq_detachedComponent outer
  have innerLookup :=
    innerCut.plan.componentAt?_address_eq_detachedComponent inner
  have composed := CKTree.componentAt?_append_of_eq tree
    (outerCut.plan.address outer) (innerCut.plan.address inner)
    (outerCut.detachedComponent outer) outerLookup
  exact composed.symm.trans innerLookup

end CKCut

end Potkin

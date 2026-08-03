import Mathlib.Data.Finset.Image
import Potkin.CKCutEnumeration
import Potkin.CKCutPuncture

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/--
An extensional finite family of ordinary vertex addresses in one exact open
CK tree.  Root exclusion is deliberately not part of this helper: relative
families below a premise may select that premise root.
-/
structure CKAddressAntichain {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) where
  addresses : Finset InternalAddress
  address_vertex : forall {address}, address ∈ addresses ->
    tree.VertexAt address
  prefixFree : forall {p q}, p ∈ addresses -> q ∈ addresses -> p ≠ q ->
    PrefixIncomparable p q

/-- An address antichain which does not select the root of its current tree. -/
structure CKNonrootAddressAntichain {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G)
    extends CKAddressAntichain tree where
  address_nonroot : forall {address}, address ∈ addresses -> address ≠ []

/--
The independent finite-address presentation of a public CK cut: the source
is positive, every selected address is an existing nonroot ordinary vertex,
and distinct selected addresses are prefix-incomparable.
-/
structure ValidAddressCut {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G)
    extends CKNonrootAddressAntichain tree where
  sourceOrdinary : tree.IsOrdinary

namespace CKAddressAntichain

@[ext]
theorem ext {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    {left right : CKAddressAntichain tree}
    (addresses : left.addresses = right.addresses) : left = right := by
  cases left
  cases right
  cases addresses
  rfl

/-- Remove one fixed zero-based premise selector from a finite address set. -/
def stripSlot (slot : Nat) (addresses : Finset InternalAddress) :
    Finset InternalAddress :=
  (addresses.filter fun address => address.head? = some slot).image List.tail

@[simp]
theorem mem_stripSlot {slot : Nat} {addresses : Finset InternalAddress}
    {tail : InternalAddress} :
    tail ∈ stripSlot slot addresses ↔ slot :: tail ∈ addresses := by
  constructor
  · intro member
    rcases Finset.mem_image.mp member with
      ⟨address, addressMember, tailEq⟩
    have sourceMember := (Finset.mem_filter.mp addressMember).1
    have selectedSlot := (Finset.mem_filter.mp addressMember).2
    cases address with
    | nil => simp at selectedSlot
    | cons head rest =>
        have same : head = slot := by simpa using selectedSlot
        have restEq : rest = tail := by simpa using tailEq
        subst head
        subst rest
        exact sourceMember
  · intro member
    apply Finset.mem_image.mpr
    exact ⟨slot :: tail, Finset.mem_filter.mpr ⟨member, by simp⟩, rfl⟩

end CKAddressAntichain

namespace CKTree

/-- A root vertex witness is exactly the positivity needed by a branch cut. -/
def isOrdinary_of_vertexAt_root {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (vertex : tree.VertexAt []) :
    tree.IsOrdinary := by
  cases vertex
  trivial

/-- Dependent child projection agrees with prefixing its exact slot. -/
theorem vertexAt_cons_iff {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (i : Fin o.shape.premises.length) (address : InternalAddress) :
    (CKTree.ordinary o children).VertexAt (i.1 :: address) ↔
      (children.get i).VertexAt address := by
  rw [CKTree.vertexAt_iff_statusAt_eq_ordinary,
    CKTree.vertexAt_iff_statusAt_eq_ordinary]
  change children.statusAt i.1 address = CKAddressStatus.ordinary ↔ _
  rw [CKChildren.statusAt_get]

/-- A selected nonroot vertex necessarily begins with an in-range slot. -/
theorem slot_lt_of_vertexAt_cons {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    {slot : Nat} {address : InternalAddress}
    (vertex : (CKTree.ordinary o children).VertexAt (slot :: address)) :
    slot < o.shape.premises.length := by
  have status := vertex.statusAt_eq_ordinary
  change children.statusAt slot address = CKAddressStatus.ordinary at status
  rcases children.vertexAt_of_statusAt_eq_ordinary slot address status with
    ⟨i, valueEq, _⟩
  simpa [valueEq] using i.isLt

end CKTree

namespace CKAddressAntichain

/-- Restrict an antichain below one exact ordered premise slot. -/
def atChild {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (family : CKAddressAntichain (CKTree.ordinary o children))
    (i : Fin o.shape.premises.length) :
    CKAddressAntichain (children.get i) where
  addresses := stripSlot i.1 family.addresses
  address_vertex := by
    intro address member
    apply (CKTree.vertexAt_cons_iff i address).mp
    exact family.address_vertex (mem_stripSlot.mp member)
  prefixFree := by
    intro p q pMember qMember different
    have fullDifferent : i.1 :: p ≠ i.1 :: q := by
      intro equal
      exact different (List.cons.inj equal).2
    have full := family.prefixFree
      (mem_stripSlot.mp pMember) (mem_stripSlot.mp qMember) fullDifferent
    simpa [PrefixIncomparable, AddressPrefix] using full

/-- If the relative root is absent, an antichain is a nonroot plan family. -/
def withoutRoot {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (family : CKAddressAntichain tree) (rootAbsent : [] ∉ family.addresses) :
    CKNonrootAddressAntichain tree where
  toCKAddressAntichain := family
  address_nonroot := by
    intro address member equal
    subst address
    exact rootAbsent member

/-- Prefix-freeness forces any antichain containing the root to be a singleton. -/
theorem addresses_eq_singleton_of_root_mem {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (family : CKAddressAntichain tree) (rootMember : [] ∈ family.addresses) :
    family.addresses = {[]} := by
  ext address
  constructor
  · intro member
    have addressEq : address = [] := by
      by_contra nonroot
      have incomparable := family.prefixFree rootMember member
        (fun equal => nonroot equal.symm)
      exact incomparable.1 (by simp [AddressPrefix])
    simp [addressEq]
  · intro member
    have addressEq : address = [] := by simpa using member
    subst address
    exact rootMember

end CKAddressAntichain

namespace CKNonrootAddressAntichain

@[ext]
theorem ext {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    {left right : CKNonrootAddressAntichain tree}
    (addresses : left.addresses = right.addresses) : left = right := by
  cases left with
  | mk leftFamily leftNonroot =>
      cases right with
      | mk rightFamily rightNonroot =>
          have familyEq : leftFamily = rightFamily :=
            CKAddressAntichain.ext addresses
          cases familyEq
          rfl

end CKNonrootAddressAntichain

namespace ValidAddressCut

@[ext]
theorem ext {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    {left right : ValidAddressCut tree}
    (addresses : left.addresses = right.addresses) : left = right := by
  cases left with
  | mk leftFamily leftOrdinary =>
      cases right with
      | mk rightFamily rightOrdinary =>
          have familyEq : leftFamily = rightFamily :=
            CKNonrootAddressAntichain.ext addresses
          cases familyEq
          rfl

end ValidAddressCut

namespace CKChildren

/-- The degree of one child is bounded by the degree of its whole tuple. -/
theorem degree_get_le {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries)
    (i : Fin boundaries.length) :
    (children.get i).degree ≤ children.degree := by
  induction boundaries with
  | nil => exact Fin.elim0 i
  | cons G Gs ih =>
      cases children with
      | cons head tail =>
          cases i using Fin.cases with
          | zero =>
              change head.degree ≤ head.degree + tail.degree
              omega
          | succ i =>
              have below := ih tail i
              change (tail.get i).degree ≤ head.degree + tail.degree
              omega

/-- Every exact child has strictly smaller degree than its ordinary parent. -/
theorem degree_get_lt_parent {o : LocalOccurrence sigma InstanceData}
    (children : CKChildren sigma InstanceData o.shape.premises)
    (i : Fin o.shape.premises.length) :
    (children.get i).degree < (CKTree.ordinary o children).degree := by
  have bounded := degree_get_le children i
  simp only [CKTree.degree]
  omega

/-- The alternating plan/branch recursion decreases at every child call. -/
theorem branchMeasure_lt_parent {o : LocalOccurrence sigma InstanceData}
    (children : CKChildren sigma InstanceData o.shape.premises)
    (i : Fin o.shape.premises.length) :
    2 * (children.get i).degree + 1 <
      2 * (CKTree.ordinary o children).degree := by
  have bounded := degree_get_le children i
  simp only [CKTree.degree]
  omega

end CKChildren

namespace CKChildCuts

/-- Recover the branch choice at one exact ordered child slot. -/
def branchAt : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    CKChildCuts children -> (i : Fin boundaries.length) ->
      CKBranchCut (children.get i)
  | _ :: _, _, .cons _ _ headCut _, ⟨0, _⟩ => headCut
  | _ :: _, _, .cons _ _ _ tailCuts, ⟨n + 1, h⟩ =>
      tailCuts.branchAt ⟨n, Nat.lt_of_succ_lt_succ h⟩

/-- Assemble exact ordered branch choices into one child-cut tuple. -/
def ofFn : {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    ((i : Fin boundaries.length) -> CKBranchCut (children.get i)) ->
      CKChildCuts children
  | [], .nil, _ => .nil
  | _ :: _, .cons head tail, branches =>
      .cons head tail (branches ⟨0, by simp⟩)
        (ofFn tail (fun i => branches i.succ))

@[simp]
theorem branchAt_ofFn {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries)
    (branches : (i : Fin boundaries.length) ->
      CKBranchCut (children.get i)) (i : Fin boundaries.length) :
    (ofFn children branches).branchAt i = branches i := by
  induction boundaries with
  | nil => exact Fin.elim0 i
  | cons G Gs ih =>
      cases children with
      | cons head tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simpa [ofFn, branchAt] using
                ih tail (fun j => branches j.succ) i

/-- A child tuple is determined by its exact branch at every premise slot. -/
theorem ext_branchAt {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    {left right : CKChildCuts children}
    (equal : forall i, left.branchAt i = right.branchAt i) : left = right := by
  induction boundaries with
  | nil => cases left; cases right; rfl
  | cons G Gs ih =>
      cases children with
      | cons head tail =>
          cases left with
          | cons _ _ leftHead leftTail =>
              cases right with
              | cons _ _ rightHead rightTail =>
                  have headEq : leftHead = rightHead :=
                    equal ⟨0, by simp⟩
                  have tailEq : leftTail = rightTail :=
                    ih (fun i => equal i.succ)
                  cases headEq
                  cases tailEq
                  rfl

end CKChildCuts

mutual

/-- Finite extensional address set selected by one recursive plan. -/
def CKCutPlan.addressFinset : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> CKCutPlan tree ->
      Finset InternalAddress
  | _, _, .interface _ => ∅
  | _, _, .ordinary _ _ cuts => cuts.addressFinset

/-- Address set selected across one exact ordered child tuple. -/
def CKChildCuts.addressFinset : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
      CKChildCuts children -> Finset InternalAddress
  | _, _, .nil => ∅
  | _, _, .cons _ _ headCut tailCuts =>
      headCut.relativeAddressFinset.image (fun address => 0 :: address) ∪
        tailCuts.addressFinset.image InternalAddress.shiftHead

/-- Relative selected-address set in one premise branch. -/
def CKBranchCut.relativeAddressFinset : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> CKBranchCut tree ->
      Finset InternalAddress
  | _, _, .detach _ => {[]}
  | _, _, .descend cut => cut.addressFinset

end

mutual

/-- Finset membership is exactly existence of one intrinsic plan site. -/
theorem CKCutPlan.mem_addressFinset_iff : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> (cut : CKCutPlan tree) ->
    (address : InternalAddress) ->
    address ∈ cut.addressFinset ↔
      ∃ site : cut.Site, cut.address site = address
  | _, _, .interface _, address => by
      simp [CKCutPlan.addressFinset, CKCutPlan.Site]
  | _, _, .ordinary _ _ cuts, address =>
      cuts.mem_addressFinset_iff address

/-- Finset membership is exactly existence of one child-tuple site. -/
theorem CKChildCuts.mem_addressFinset_iff :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (address : InternalAddress) ->
    address ∈ cuts.addressFinset ↔
      ∃ site : cuts.Site, cuts.address site = address
  | _, _, .nil, address => by
      simp [CKChildCuts.addressFinset, CKChildCuts.Site]
  | _, _, .cons _ _ headCut tailCuts, address => by
      constructor
      · intro member
        rcases Finset.mem_union.mp member with headMember | tailMember
        · rcases Finset.mem_image.mp headMember with
            ⟨relative, relativeMember, addressEq⟩
          rcases (headCut.mem_relativeAddressFinset_iff relative).mp relativeMember with
            ⟨site, siteEq⟩
          refine ⟨Sum.inl site, ?_⟩
          simpa [CKChildCuts.address, siteEq] using addressEq
        · rcases Finset.mem_image.mp tailMember with
            ⟨relative, relativeMember, addressEq⟩
          rcases (tailCuts.mem_addressFinset_iff relative).mp relativeMember with
            ⟨site, siteEq⟩
          refine ⟨Sum.inr site, ?_⟩
          simpa [CKChildCuts.address, siteEq] using addressEq
      · rintro ⟨site, siteEq⟩
        change Sum headCut.Site tailCuts.Site at site
        cases site with
        | inl site =>
            apply Finset.mem_union_left
            apply Finset.mem_image.mpr
            refine ⟨headCut.relativeAddress site, ?_, ?_⟩
            · exact (headCut.mem_relativeAddressFinset_iff _).mpr ⟨site, rfl⟩
            · simpa [CKChildCuts.address] using siteEq
        | inr site =>
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            refine ⟨tailCuts.address site, ?_, ?_⟩
            · exact (tailCuts.mem_addressFinset_iff _).mpr ⟨site, rfl⟩
            · simpa [CKChildCuts.address] using siteEq

/-- Finset membership is exactly existence of one relative branch site. -/
theorem CKBranchCut.mem_relativeAddressFinset_iff :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> (cut : CKBranchCut tree) ->
    (address : InternalAddress) ->
    address ∈ cut.relativeAddressFinset ↔
      ∃ site : cut.Site, cut.relativeAddress site = address
  | _, _, .detach _, address => by
      simp [CKBranchCut.relativeAddressFinset, CKBranchCut.Site,
        CKBranchCut.relativeAddress]
  | _, _, .descend cut, address => cut.mem_addressFinset_iff address

end

/-- Plan address finsets are the extensional image of the canonical site walk. -/
theorem CKCutPlan.addressFinset_eq_siteOrder_toFinset
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCutPlan tree) :
    cut.addressFinset = (cut.siteOrder.map cut.address).toFinset := by
  ext address
  constructor
  · intro member
    rcases (cut.mem_addressFinset_iff address).mp member with ⟨site, rfl⟩
    exact List.mem_toFinset.mpr <|
      List.mem_map.mpr ⟨site, cut.site_mem_siteOrder site, rfl⟩
  · intro member
    rcases List.mem_map.mp (List.mem_toFinset.mp member) with
      ⟨site, _, rfl⟩
    exact (cut.mem_addressFinset_iff _).mpr ⟨site, rfl⟩

/-- Every plan address is nonroot, including for an empty interface plan. -/
theorem CKCutPlan.address_nonroot : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} -> (cut : CKCutPlan tree) ->
    (site : cut.Site) -> cut.address site ≠ []
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary _ _ cuts, site => cuts.address_nonroot site

/-- Every member of a plan's extensional set is an exact source vertex. -/
theorem CKCutPlan.vertex_of_mem_addressFinset
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCutPlan tree) {address : InternalAddress}
    (member : address ∈ cut.addressFinset) : tree.VertexAt address := by
  rcases (cut.mem_addressFinset_iff address).mp member with ⟨site, rfl⟩
  exact cut.address_vertexAt site

/-- Every member of a plan's extensional set is nonroot. -/
theorem CKCutPlan.nonroot_of_mem_addressFinset
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCutPlan tree) {address : InternalAddress}
    (member : address ∈ cut.addressFinset) : address ≠ [] := by
  rcases (cut.mem_addressFinset_iff address).mp member with ⟨site, rfl⟩
  exact cut.address_nonroot site

/-- Forget an intrinsic plan to its independent finite address antichain. -/
def CKCutPlan.validAddresses
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCutPlan tree) : CKNonrootAddressAntichain tree where
  addresses := cut.addressFinset
  address_vertex := cut.vertex_of_mem_addressFinset
  address_nonroot := cut.nonroot_of_mem_addressFinset
  prefixFree := by
    intro p q pMember qMember different
    rcases (cut.mem_addressFinset_iff p).mp pMember with ⟨pSite, pEq⟩
    rcases (cut.mem_addressFinset_iff q).mp qMember with ⟨qSite, qEq⟩
    have sitesDifferent : pSite ≠ qSite := by
      intro equal
      subst qSite
      exact different (pEq.symm.trans qEq)
    simpa [pEq, qEq] using
      cut.addresses_prefixIncomparable sitesDifferent

/-- Forget a public recursive cut to its independent valid address family. -/
def CKCut.validAddressCut
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCut tree) : ValidAddressCut tree where
  toCKNonrootAddressAntichain := cut.plan.validAddresses
  sourceOrdinary := cut.sourceOrdinary

namespace CKChildCuts

/-- Membership under a fixed premise prefix recovers exactly that branch. -/
theorem mem_addressFinset_branchAt_iff :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (i : Fin boundaries.length) ->
    (address : InternalAddress) ->
    i.1 :: address ∈ cuts.addressFinset ↔
      address ∈ (cuts.branchAt i).relativeAddressFinset
  | _ :: _, _, .cons _ _ headCut tailCuts, ⟨0, _⟩, address => by
      change 0 :: address ∈
          (CKChildCuts.cons _ _ headCut tailCuts).addressFinset ↔
        address ∈ headCut.relativeAddressFinset
      rw [headCut.mem_relativeAddressFinset_iff]
      constructor
      · intro member
        rcases (CKChildCuts.mem_addressFinset_iff _ _).mp member with
          ⟨site, siteEq⟩
        change Sum headCut.Site tailCuts.Site at site
        cases site with
        | inl site =>
            have prefixed :
                0 :: headCut.relativeAddress site = 0 :: address := by
              simpa [CKChildCuts.address] using siteEq
            exact ⟨site, (List.cons.inj prefixed).2⟩
        | inr site =>
            have nonempty := tailCuts.address_nonroot site
            cases tailAddressEq : tailCuts.address site with
            | nil => exact (nonempty tailAddressEq).elim
            | cons slot rest =>
                simp [CKChildCuts.address, tailAddressEq,
                  InternalAddress.shiftHead] at siteEq
      · rintro ⟨site, siteEq⟩
        apply (CKChildCuts.mem_addressFinset_iff _ _).mpr
        exact ⟨Sum.inl site, by simp [CKChildCuts.address, siteEq]⟩
  | _ :: _, _, .cons _ _ headCut tailCuts, ⟨slot + 1, h⟩, address => by
      let tailIndex : Fin _ := ⟨slot, Nat.lt_of_succ_lt_succ h⟩
      change (slot + 1) :: address ∈
          (CKChildCuts.cons _ _ headCut tailCuts).addressFinset ↔
        address ∈ (tailCuts.branchAt tailIndex).relativeAddressFinset
      have tailMembership :
          slot :: address ∈ tailCuts.addressFinset ↔
            address ∈ (tailCuts.branchAt tailIndex).relativeAddressFinset := by
        simpa [tailIndex] using
          tailCuts.mem_addressFinset_branchAt_iff tailIndex address
      rw [← tailMembership]
      constructor
      · intro member
        rcases (CKChildCuts.mem_addressFinset_iff _ _).mp member with
          ⟨site, siteEq⟩
        change Sum headCut.Site tailCuts.Site at site
        cases site with
        | inl site =>
            simp [CKChildCuts.address] at siteEq
        | inr site =>
            apply (CKChildCuts.mem_addressFinset_iff _ _).mpr
            refine ⟨site, ?_⟩
            have nonempty := tailCuts.address_nonroot site
            cases tailAddressEq : tailCuts.address site with
            | nil => exact (nonempty tailAddressEq).elim
            | cons head rest =>
                have shifted :
                    (head + 1) :: rest = (slot + 1) :: address := by
                  simpa [CKChildCuts.address, tailAddressEq,
                    InternalAddress.shiftHead] using siteEq
                have parts := List.cons.inj shifted
                have headEq : head = slot :=
                  Nat.add_right_cancel parts.1
                have restEq : rest = address := parts.2
                simp [headEq, restEq]
      · intro member
        rcases (CKChildCuts.mem_addressFinset_iff _ _).mp member with
          ⟨site, siteEq⟩
        apply (CKChildCuts.mem_addressFinset_iff _ _).mpr
        refine ⟨Sum.inr site, ?_⟩
        simp [CKChildCuts.address, siteEq,
          InternalAddress.shiftHead]

end CKChildCuts

mutual

/--
Constructor-recursive inverse from a nonroot address antichain to a cut plan.
The returned equality is the extensional half of the witness bijection.
-/
def CKNonrootAddressAntichain.toPlan :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (family : CKNonrootAddressAntichain tree) ->
      {cut : CKCutPlan tree // cut.addressFinset = family.addresses}
  | _, .interface G, family => by
      refine ⟨.interface G, ?_⟩
      symm
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro address member
      exact nomatch family.address_vertex member
  | _, .ordinary o children, family => by
      let branches : (i : Fin o.shape.premises.length) ->
          CKBranchCut (children.get i) := fun i =>
        (family.toCKAddressAntichain.atChild i).toBranch |>.1
      let cuts := CKChildCuts.ofFn children branches
      refine ⟨.ordinary o children cuts, ?_⟩
      ext address
      cases address with
      | nil =>
          constructor
          · intro member
            exact (CKCutPlan.nonroot_of_mem_addressFinset _ member rfl).elim
          · intro member
            exact (family.address_nonroot member rfl).elim
      | cons slot rest =>
          by_cases inRange : slot < o.shape.premises.length
          · let i : Fin o.shape.premises.length := ⟨slot, inRange⟩
            change slot :: rest ∈ cuts.addressFinset ↔
              slot :: rest ∈ family.addresses
            rw [show slot = i.1 from rfl,
              CKChildCuts.mem_addressFinset_branchAt_iff cuts i rest,
              CKChildCuts.branchAt_ofFn]
            change rest ∈
                ((family.toCKAddressAntichain.atChild i).toBranch |>.1).relativeAddressFinset ↔ _
            rw [(family.toCKAddressAntichain.atChild i).toBranch.property]
            exact CKAddressAntichain.mem_stripSlot
          · constructor
            · intro member
              have vertex := CKCutPlan.vertex_of_mem_addressFinset
                (CKCutPlan.ordinary o children cuts) member
              exact (inRange (CKTree.slot_lt_of_vertexAt_cons vertex)).elim
            · intro member
              have vertex := family.address_vertex member
              exact (inRange (CKTree.slot_lt_of_vertexAt_cons vertex)).elim
termination_by _ tree _ => 2 * tree.degree
decreasing_by
  all_goals
    exact CKChildren.branchMeasure_lt_parent children _

/--
Constructor-recursive inverse for one relative premise branch.  Selecting its
root forces detachment; otherwise recursion stays strictly below that root.
-/
def CKAddressAntichain.toBranch :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (family : CKAddressAntichain tree) ->
      {cut : CKBranchCut tree //
        cut.relativeAddressFinset = family.addresses}
  | _, tree, family => by
      by_cases rootMember : [] ∈ family.addresses
      · let ordinary := CKTree.isOrdinary_of_vertexAt_root
          (family.address_vertex rootMember)
        refine ⟨.detach ordinary, ?_⟩
        simpa [CKBranchCut.relativeAddressFinset] using
          (family.addresses_eq_singleton_of_root_mem rootMember).symm
      · let built := (family.withoutRoot rootMember).toPlan
        exact ⟨.descend built.1, by
          simpa [CKBranchCut.relativeAddressFinset] using built.2⟩
termination_by _ tree _ => 2 * tree.degree + 1
decreasing_by simp_wf

end

namespace ValidAddressCut

/-- Recursively construct an intrinsic CK cut represented by a valid family. -/
def toCut {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (family : ValidAddressCut tree) :
    CKCut tree where
  sourceOrdinary := family.sourceOrdinary
  plan := family.toCKNonrootAddressAntichain.toPlan.1

@[simp]
theorem toCut_addressFinset {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (family : ValidAddressCut tree) :
    family.toCut.plan.addressFinset = family.addresses :=
  family.toCKNonrootAddressAntichain.toPlan.2

end ValidAddressCut

namespace CKCut

variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Public cut addresses as a finite set agree with the canonical list. -/
theorem addressFinset_eq_orderedAddresses_toFinset (cut : CKCut tree) :
    cut.plan.addressFinset = cut.orderedAddresses.toFinset := by
  simpa [orderedAddresses, orderedSites] using
    cut.plan.addressFinset_eq_siteOrder_toFinset

/-- External completeness for every finite valid nonroot address antichain. -/
theorem exists_mem_enumerate_with_addressFinset
    (family : ValidAddressCut tree) :
    ∃ cut ∈ enumerate tree family.sourceOrdinary,
      cut.plan.addressFinset = family.addresses := by
  refine ⟨family.toCut, ?_, family.toCut_addressFinset⟩
  exact family.toCut.mem_enumerate

end CKCut

end Potkin

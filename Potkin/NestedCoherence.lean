import Potkin.CKCutValidity
import Potkin.RealizedCut
import Potkin.GeneralFilling
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

/-!
# Source-addressed nested CK-cut transport and partial coherence

This file keeps the comparison of successive cuts at occurrence level.  In
particular, all relations below are relations on addresses in one fixed source
tree; relative addresses used after transport are accompanied by the equation
which recovers their source address.

The current results are deliberately partial. They do not identify actual
transported region components or detached tree entries, compose a two-stage
fill from the further-cut root, prove equality of sequential remainders, or
encode arbitrary finite iterated cut schedules.
-/

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

local instance decidableAddressPrefix
    (left right : InternalAddress) : Decidable (AddressPrefix left right) := by
  unfold AddressPrefix
  infer_instance

/-- `inner` is strictly below `outer` in the premise-address tree. -/
def StrictlyInside (inner outer : InternalAddress) : Prop :=
  AddressPrefix outer inner ∧ inner ≠ outer

local instance decidableStrictlyInside
    (inner outer : InternalAddress) : Decidable (StrictlyInside inner outer) := by
  unfold StrictlyInside
  infer_instance

namespace StrictlyInside

theorem irrefl (address : InternalAddress) :
    ¬ StrictlyInside address address := by
  simp [StrictlyInside]

theorem trans {lower middle upper : InternalAddress}
    (lowerMiddle : StrictlyInside lower middle)
    (middleUpper : StrictlyInside middle upper) :
    StrictlyInside lower upper := by
  rcases lowerMiddle with ⟨lowerPrefix, lowerNe⟩
  rcases middleUpper with ⟨middlePrefix, middleNe⟩
  refine ⟨middlePrefix.trans lowerPrefix, ?_⟩
  intro equal
  subst lower
  exact middleNe (lowerPrefix.eq_of_length_le middlePrefix.length_le)

end StrictlyInside

/-- Some address in `inner` lies strictly inside an address in `outer`. -/
def HasInsideAddresses (inner outer : Finset InternalAddress) : Prop :=
  ∃ innerAddress ∈ inner, ∃ outerAddress ∈ outer,
    StrictlyInside innerAddress outerAddress

local instance decidableHasInsideAddresses
    (inner outer : Finset InternalAddress) :
    Decidable (HasInsideAddresses inner outer) := by
  unfold HasInsideAddresses
  infer_instance

/-- The source-independent part of the manuscript's noncrossing relation. -/
def AddressFamiliesNoncrossing
    (first second : Finset InternalAddress) : Prop :=
  Disjoint first second ∧
    ¬ (HasInsideAddresses first second ∧
      HasInsideAddresses second first)

local instance decidableAddressFamiliesNoncrossing
    (first second : Finset InternalAddress) :
    Decidable (AddressFamiliesNoncrossing first second) := by
  unfold AddressFamiliesNoncrossing
  infer_instance

/-- Some selected occurrence of `innerCut` lies strictly inside a selected
occurrence of `outerCut`.  Both cuts are read in one exact source tree. -/
def HasInsidePair {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (innerCut outerCut : ValidAddressCut tree) : Prop :=
  HasInsideAddresses innerCut.addresses outerCut.addresses

/--
The manuscript's two-level noncrossing condition, with the necessary
set-disjointness made explicit.  Comparable cross-pairs may point in only one
strict-prefix orientation; incomparable branches impose no orientation.
-/
structure Noncrossing {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) : Prop where
  disjoint : Disjoint first.addresses second.addresses
  noMixedOrientation :
    ¬ (HasInsidePair first second ∧ HasInsidePair second first)

theorem noncrossing_iff_addressFamilies {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) :
    Noncrossing first second ↔
      AddressFamiliesNoncrossing first.addresses second.addresses := by
  constructor
  · intro witness
    exact ⟨witness.disjoint, witness.noMixedOrientation⟩
  · rintro ⟨disjoint, noMixedOrientation⟩
    exact ⟨disjoint, noMixedOrientation⟩

namespace Noncrossing

theorem symm {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {first second : ValidAddressCut tree}
    (noncrossing : Noncrossing first second) :
    Noncrossing second first := by
  refine ⟨noncrossing.disjoint.symm, ?_⟩
  intro mixed
  exact noncrossing.noMixedOrientation ⟨mixed.2, mixed.1⟩

/-- A mixed pair of opposite nestings is rejected literally. -/
theorem rejects_mixed {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {first second : ValidAddressCut tree}
    (noncrossing : Noncrossing first second)
    (firstInsideSecond : HasInsidePair first second) :
    ¬ HasInsidePair second first := by
  intro secondInsideFirst
  exact noncrossing.noMixedOrientation
    ⟨firstInsideSecond, secondInsideFirst⟩

/-- If every cross-pair is prefix-incomparable, the cuts are noncrossing.
This is the genuinely independent-branch case. -/
theorem of_cross_incomparable {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {first second : ValidAddressCut tree}
    (incomparable : ∀ p ∈ first.addresses, ∀ q ∈ second.addresses,
      PrefixIncomparable p q) :
    Noncrossing first second := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro address firstMember secondMember
    exact (incomparable address firstMember address secondMember).1
      (by simp [AddressPrefix])
  · rintro ⟨⟨p, pMember, q, qMember, pInside⟩, _⟩
    exact (incomparable p pMember q qMember).2 pInside.1

end Noncrossing

namespace ValidAddressCut

/-- Prefix-freeness makes the selected anchor above a source address unique. -/
theorem prefix_anchor_unique {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (cut : ValidAddressCut tree) {source left right : InternalAddress}
    (leftMember : left ∈ cut.addresses)
    (rightMember : right ∈ cut.addresses)
    (leftPrefix : AddressPrefix left source)
    (rightPrefix : AddressPrefix right source) : left = right := by
  by_contra different
  have incomparable := cut.prefixFree leftMember rightMember different
  rcases List.prefix_or_prefix_of_prefix leftPrefix rightPrefix with
    leftRight | rightLeft
  · exact incomparable.1 leftRight
  · exact incomparable.2 rightLeft

end ValidAddressCut

/-- The location of a second-cut occurrence after a first cut.  A retained
address is unchanged.  A detached address records its unique first-cut source
anchor and a relative address whose prefix equation recovers the original
source address. -/
inductive CutAddressDestination {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first : ValidAddressCut tree) (source : InternalAddress) : Type where
  | retained
      (outside : ∀ anchor ∈ first.addresses,
        ¬ AddressPrefix anchor source) :
      CutAddressDestination first source
  | detached
      (anchor : InternalAddress) (anchorMember : anchor ∈ first.addresses)
      (relative : InternalAddress)
      (source_eq : anchor ++ relative = source) :
      CutAddressDestination first source

namespace CutAddressDestination

/-- Canonical source-addressed location.  When a selected first-cut address
prefixes `source`, `drop` supplies its relative address; otherwise the address
stays in the retained component. -/
noncomputable def locate {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first : ValidAddressCut tree) (source : InternalAddress) :
    CutAddressDestination first source := by
  classical
  by_cases prefixed : ∃ anchor ∈ first.addresses,
      AddressPrefix anchor source
  · let anchor := Classical.choose prefixed
    have rest := Classical.choose_spec prefixed
    exact .detached anchor rest.1 (source.drop anchor.length)
      (List.prefix_append_drop rest.2).symm
  · exact .retained (by
      intro anchor member isPrefix
      exact prefixed ⟨anchor, member, isPrefix⟩)

/-- Relative address in the destination carrier. -/
def relative {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {first : ValidAddressCut tree} {source : InternalAddress} :
    CutAddressDestination first source → InternalAddress
  | .retained _ => source
  | .detached _ _ relative _ => relative

/-- Optional source address of the detached carrier; `none` denotes the
retained root component. -/
def anchor? {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {first : ValidAddressCut tree} {source : InternalAddress} :
    CutAddressDestination first source → Option InternalAddress
  | .retained _ => none
  | .detached anchor _ _ _ => some anchor

/-- Every destination retains a literal equation back to the source. -/
theorem source_equation {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {first : ValidAddressCut tree} {source : InternalAddress}
    (destination : CutAddressDestination first source) :
    match destination.anchor? with
    | none => destination.relative = source
    | some anchor => anchor ++ destination.relative = source := by
  cases destination with
  | retained => rfl
  | detached _ _ _ source_eq => exact source_eq

/-- A valid first-cut antichain gives each source address at most one
destination, including its detached anchor and relative suffix. -/
theorem unique {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {first : ValidAddressCut tree} {source : InternalAddress}
    (left right : CutAddressDestination first source) : left = right := by
  cases left with
  | retained leftOutside =>
      cases right with
      | retained rightOutside => rfl
      | detached anchor anchorMember relative sourceEq =>
          exact False.elim <| leftOutside anchor anchorMember
            ⟨relative, sourceEq⟩
  | detached leftAnchor leftMember leftRelative leftEq =>
      cases right with
      | retained rightOutside =>
          exact False.elim <| rightOutside leftAnchor leftMember
            ⟨leftRelative, leftEq⟩
      | detached rightAnchor rightMember rightRelative rightEq =>
          have anchorEq : leftAnchor = rightAnchor :=
            first.prefix_anchor_unique leftMember rightMember
              ⟨leftRelative, leftEq⟩ ⟨rightRelative, rightEq⟩
          subst rightAnchor
          have relativeEq : leftRelative = rightRelative := by
            apply List.append_cancel_left
            exact leftEq.trans rightEq.symm
          subst rightRelative
          rfl

instance instSubsingleton {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {first : ValidAddressCut tree} {source : InternalAddress} :
    Subsingleton (CutAddressDestination first source) :=
  ⟨unique⟩

/-- The choice used by `locate` is propositionally the unique destination. -/
theorem locate_eq {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first : ValidAddressCut tree) (source : InternalAddress)
    (destination : CutAddressDestination first source) :
    locate first source = destination :=
  Subsingleton.elim _ _

end CutAddressDestination

/-! ## Exact transport into recursive cut carriers -/

mutual

/-- Outside every selected prefix, cutting preserves the complete address
status, not merely old interfaces. -/
theorem CKCutPlan.statusOutside_remainder_preserved :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (address : InternalAddress) ->
    (∀ site : cut.Site,
      ¬ AddressPrefix (cut.address site) address) ->
    cut.remainder.statusAt address = tree.statusAt address
  | _, _, .interface _, address, _ => by
      simp [CKCutPlan.remainder]
  | _, _, .ordinary _ _ cuts, address, outside => by
      cases address with
      | nil => rfl
      | cons slot rest =>
          simpa [CKTree.statusAt, CKCutPlan.remainder,
            CKCutPlan.Site, CKCutPlan.address] using
            cuts.statusOutside_remainder_preserved slot rest
              (by intro site; exact outside site)

/-- Ordered-child form of full status preservation. -/
theorem CKChildCuts.statusOutside_remainder_preserved :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (slot : Nat) ->
    (address : InternalAddress) ->
    (∀ site : cuts.Site,
      ¬ AddressPrefix (cuts.address site) (slot :: address)) ->
    cuts.remainder.statusAt slot address = children.statusAt slot address
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons _ _ headCut tailCuts, slot, address, outside => by
      cases slot with
      | zero =>
          apply headCut.statusOutside_remainder_preserved address
          intro site isPrefix
          apply outside (Sum.inl site)
          simpa [CKChildCuts.address, AddressPrefix] using isPrefix
      | succ slot =>
          apply tailCuts.statusOutside_remainder_preserved slot address
          intro site isPrefix
          apply outside (Sum.inr site)
          have shiftedPrefix :=
            (InternalAddress.shiftHead_prefix_iff
              (tailCuts.address_nonroot site) (by simp)).mpr isPrefix
          simpa [CKChildCuts.address] using shiftedPrefix

/-- Detaching a root leaves no outside address; descent uses the plan law. -/
theorem CKBranchCut.statusOutside_remainder_preserved :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (address : InternalAddress) ->
    (∀ site : cut.Site,
      ¬ AddressPrefix (cut.relativeAddress site) address) ->
    cut.remainder.statusAt address = tree.statusAt address
  | _, _, .detach _, _, outside => by
      exact False.elim <| outside PUnit.unit (by
        simp [CKBranchCut.relativeAddress, AddressPrefix])
  | _, _, .descend cut, address, outside =>
      cut.statusOutside_remainder_preserved address outside

end

mutual

/-- Looking below a detached occurrence is exactly looking below its selected
source prefix. -/
theorem CKCutPlan.detached_statusAt_source :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (site : cut.Site) ->
    (relative : InternalAddress) ->
    (cut.detached site).statusAt relative =
      tree.statusAt (cut.address site ++ relative)
  | _, _, .interface _, site, _ => nomatch site
  | _, _, .ordinary o children cuts, site, relative => by
      have nonempty := cuts.address_nonroot site
      cases addressEq : cuts.address site with
      | nil => exact (nonempty addressEq).elim
      | cons slot rest =>
          change (cuts.detached site).statusAt relative =
            (CKTree.ordinary o children).statusAt
              (cuts.address site ++ relative)
          rw [addressEq]
          simpa [addressEq, List.head!] using
            cuts.detached_statusAt_source site relative

/-- Child-tuple form of the exact detached/source lookup equation. -/
theorem CKChildCuts.detached_statusAt_source :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (site : cuts.Site) ->
    (relative : InternalAddress) ->
    (cuts.detached site).statusAt relative =
      children.statusAt (cuts.address site).head!
        ((cuts.address site).tail ++ relative)
  | _, _, .nil, site, _ => nomatch site
  | _, _, .cons head tail headCut tailCuts, site, relative => by
      change Sum headCut.Site tailCuts.Site at site
      cases site with
      | inl site =>
          change (headCut.detached site).statusAt relative =
            (CKChildren.cons head tail).statusAt 0
              (headCut.relativeAddress site ++ relative)
          exact headCut.detached_statusAt_source site relative
      | inr site =>
          have nonempty := tailCuts.address_nonroot site
          cases addressEq : tailCuts.address site with
          | nil => exact (nonempty addressEq).elim
          | cons slot rest =>
              simpa [CKChildCuts.detached, CKChildCuts.address,
                addressEq, InternalAddress.shiftHead, List.head!] using
                tailCuts.detached_statusAt_source site relative

/-- Root detachment has the empty relative prefix; descent is recursive. -/
theorem CKBranchCut.detached_statusAt_source :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (site : cut.Site) ->
    (relative : InternalAddress) ->
    (cut.detached site).statusAt relative =
      tree.statusAt (cut.relativeAddress site ++ relative)
  | _, _, .detach _, site, relative => by
      change PUnit at site
      cases site
      rfl
  | _, _, .descend cut, site, relative =>
      cut.detached_statusAt_source site relative

end

namespace CKCut

/-- An ordinary source vertex outside all selected subtrees survives at the
same address in the retained remainder. -/
theorem remainder_vertexAt_outside
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCut tree) {address : InternalAddress}
    (vertex : tree.VertexAt address)
    (outside : ∀ site : cut.Site,
      ¬ AddressPrefix (cut.plan.address site) address) :
    cut.remainder.VertexAt address := by
  apply cut.remainder.vertexAt_of_statusAt_eq_ordinary address
  change cut.plan.remainder.statusAt address = .ordinary
  exact (cut.plan.statusOutside_remainder_preserved address outside).trans
    vertex.statusAt_eq_ordinary

/-- The selected detached tree carries exactly the source vertices below its
address, with the selected prefix removed. -/
theorem detached_vertexAt_iff_source
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCut tree) (site : cut.Site) (relative : InternalAddress) :
    (cut.plan.detached site).VertexAt relative ↔
      tree.VertexAt (cut.plan.address site ++ relative) := by
  rw [CKTree.vertexAt_iff_statusAt_eq_ordinary,
    CKTree.vertexAt_iff_statusAt_eq_ordinary,
    cut.plan.detached_statusAt_source site relative]

end CKCut

/-- Source-addressed transport of every occurrence of `second` after
`first`.  The source address is the key, so equal displayed detached trees
remain distinct occurrences. -/
structure CutTransport {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) where
  destination : (source : InternalAddress) → source ∈ second.addresses →
    CutAddressDestination first source

namespace CutTransport

/-- Canonical address transport.  It is defined for every pair of cuts;
`Noncrossing` is the additional condition under which the transported pieces
form two globally coherent stages. -/
noncomputable def canonical {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) : CutTransport first second where
  destination := fun source _ => CutAddressDestination.locate first source

end CutTransport

namespace ValidAddressCut

/-- Addresses selected by either of two source cuts. -/
def combinedAddresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) : Finset InternalAddress :=
  first.addresses ∪ second.addresses

/-- Second-cut addresses which remain in the first cut's root remainder. -/
def retainedAddresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) : Finset InternalAddress :=
  second.addresses.filter fun source =>
    ∀ anchor ∈ first.addresses, ¬ AddressPrefix anchor source

/-- Transport the part of `second` not lying inside a first-cut detached
subtree into the retained remainder.  Ancestors of first-cut sites and
incomparable branches both remain at their literal source addresses. -/
def retainedAfter {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) :
    ValidAddressCut first.toCut.remainder where
  addresses := retainedAddresses first second
  address_vertex := by
    intro address member
    have data := Finset.mem_filter.mp member
    apply first.toCut.remainder_vertexAt_outside
      (second.address_vertex data.1)
    intro site isPrefix
    apply data.2 (first.toCut.plan.address site)
    · rw [← first.toCut_addressFinset]
      exact (first.toCut.plan.mem_addressFinset_iff _).mpr
        ⟨site, rfl⟩
    · exact isPrefix
  prefixFree := by
    intro p q pMember qMember different
    exact second.prefixFree
      (Finset.mem_filter.mp pMember).1
      (Finset.mem_filter.mp qMember).1 different
  address_nonroot := by
    intro address member
    exact second.address_nonroot (Finset.mem_filter.mp member).1
  sourceOrdinary := first.toCut.remainder_isOrdinary

/-- Relative addresses of second-cut occurrences lying in one exact detached
first-cut factor. -/
def insideRelativeAddresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) (site : first.toCut.Site) :
    Finset InternalAddress :=
  (second.addresses.filter fun source =>
      AddressPrefix (first.toCut.plan.address site) source).image
    (fun source => source.drop (first.toCut.plan.address site).length)

/-- Relative membership retains an exact source address and its literal
prefix equation; the image operation does not erase occurrence provenance. -/
theorem mem_insideRelativeAddresses_iff {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) (site : first.toCut.Site)
    (relative : InternalAddress) :
    relative ∈ insideRelativeAddresses first second site ↔
      ∃ source ∈ second.addresses,
        first.toCut.plan.address site ++ relative = source := by
  constructor
  · intro member
    rcases Finset.mem_image.mp member with
      ⟨source, sourceData, relativeEq⟩
    have sourceMember := (Finset.mem_filter.mp sourceData).1
    have sourcePrefix := (Finset.mem_filter.mp sourceData).2
    refine ⟨source, sourceMember, ?_⟩
    rw [← relativeEq]
    exact (List.prefix_append_drop sourcePrefix).symm
  · rintro ⟨source, sourceMember, sourceEq⟩
    have sourcePrefix :
        AddressPrefix (first.toCut.plan.address site) source :=
      ⟨relative, sourceEq⟩
    have dropEq : source.drop (first.toCut.plan.address site).length =
        relative := by
      rw [← sourceEq]
      simp
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_filter.mpr ⟨sourceMember, sourcePrefix⟩,
        dropEq⟩

/-- A source occurrence lying below the first cut belongs to one unique
detached first-cut site. -/
theorem inside_site_unique {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first : ValidAddressCut tree) {source : InternalAddress}
    (left right : first.toCut.Site)
    (leftPrefix : AddressPrefix (first.toCut.plan.address left) source)
    (rightPrefix : AddressPrefix (first.toCut.plan.address right) source) :
    left = right := by
  apply first.toCut.address_injective
  apply first.prefix_anchor_unique
  · rw [← first.toCut_addressFinset]
    exact (first.toCut.plan.mem_addressFinset_iff _).mpr ⟨left, rfl⟩
  · rw [← first.toCut_addressFinset]
    exact (first.toCut.plan.mem_addressFinset_iff _).mpr ⟨right, rfl⟩
  · exact leftPrefix
  · exact rightPrefix

/-- Transport the part of `second` lying below one selected first-cut
occurrence into that exact detached component.  Relative addresses are
obtained by deleting the retained source prefix. -/
def insideAfter {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree)
    (cutsDisjoint : Disjoint first.addresses second.addresses)
    (site : first.toCut.Site) :
    ValidAddressCut (first.toCut.plan.detached site) where
  addresses := insideRelativeAddresses first second site
  address_vertex := by
    intro relative member
    rcases Finset.mem_image.mp member with
      ⟨source, sourceData, relativeEq⟩
    have sourceMember := (Finset.mem_filter.mp sourceData).1
    have sourcePrefix := (Finset.mem_filter.mp sourceData).2
    have prefixEq := List.prefix_append_drop sourcePrefix
    apply (first.toCut.detached_vertexAt_iff_source site relative).mpr
    have addressEq :
        first.toCut.plan.address site ++ relative = source := by
      calc
        first.toCut.plan.address site ++ relative =
            first.toCut.plan.address site ++
              source.drop (first.toCut.plan.address site).length := by
                rw [relativeEq]
        _ = source := prefixEq.symm
    rw [addressEq]
    exact second.address_vertex sourceMember
  prefixFree := by
    intro p q pMember qMember different
    rcases Finset.mem_image.mp pMember with ⟨pSource, pData, pEq⟩
    rcases Finset.mem_image.mp qMember with ⟨qSource, qData, qEq⟩
    have pMemberSecond := (Finset.mem_filter.mp pData).1
    have qMemberSecond := (Finset.mem_filter.mp qData).1
    have pPrefix := (Finset.mem_filter.mp pData).2
    have qPrefix := (Finset.mem_filter.mp qData).2
    have pSourceEq := List.prefix_append_drop pPrefix
    have qSourceEq := List.prefix_append_drop qPrefix
    have sourceDifferent : pSource ≠ qSource := by
      intro sourceEq
      subst qSource
      exact different (pEq.symm.trans qEq)
    have sourceIncomparable := second.prefixFree pMemberSecond
      qMemberSecond sourceDifferent
    constructor
    · intro relativePrefix
      apply sourceIncomparable.1
      rw [pSourceEq, qSourceEq]
      rw [pEq, qEq]
      exact (List.prefix_append_right_inj _).mpr relativePrefix
    · intro relativePrefix
      apply sourceIncomparable.2
      rw [pSourceEq, qSourceEq]
      rw [pEq, qEq]
      exact (List.prefix_append_right_inj _).mpr relativePrefix
  address_nonroot := by
    intro relative member relativeRoot
    rcases Finset.mem_image.mp member with
      ⟨source, sourceData, relativeEq⟩
    have sourceMember := (Finset.mem_filter.mp sourceData).1
    have sourcePrefix := (Finset.mem_filter.mp sourceData).2
    have sourceEq := List.prefix_append_drop sourcePrefix
    have droppedRoot : source.drop
        (first.toCut.plan.address site).length = [] :=
      relativeEq.trans relativeRoot
    have sourceIsAnchor : source = first.toCut.plan.address site := by
      simpa [droppedRoot] using sourceEq
    have anchorMember : first.toCut.plan.address site ∈ first.addresses := by
      rw [← first.toCut_addressFinset]
      exact (first.toCut.plan.mem_addressFinset_iff _).mpr ⟨site, rfl⟩
    exact (Finset.disjoint_left.mp cutsDisjoint anchorMember
      (sourceIsAnchor ▸ sourceMember))
  sourceOrdinary := first.toCut.plan.detachedOrdinary site

/-- Every second-cut occurrence is transported either to the retained root
component or to at least one (necessarily unique by first-cut prefix
freeness) detached first-cut component. -/
theorem mem_retainedAddresses_or_insideRelativeAddresses
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) {source : InternalAddress}
    (sourceMember : source ∈ second.addresses) :
    source ∈ retainedAddresses first second ∨
      ∃ site : first.toCut.Site,
        source.drop (first.toCut.plan.address site).length ∈
          insideRelativeAddresses first second site := by
  classical
  by_cases outside : ∀ anchor ∈ first.addresses,
      ¬ AddressPrefix anchor source
  · exact Or.inl (Finset.mem_filter.mpr ⟨sourceMember, outside⟩)
  · push_neg at outside
    rcases outside with ⟨anchor, anchorMember, isPrefix⟩
    have planMember : anchor ∈ first.toCut.plan.addressFinset := by
      simpa [first.toCut_addressFinset] using anchorMember
    rcases (first.toCut.plan.mem_addressFinset_iff anchor).mp planMember with
      ⟨site, siteAddress⟩
    refine Or.inr ⟨site, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨source, Finset.mem_filter.mpr ⟨sourceMember, ?_⟩, rfl⟩
    simpa [siteAddress] using isPrefix

end ValidAddressCut

namespace CutAddressDestination

/-- Every destination case is witnessed by the corresponding transported
valid-address cut, with the original source address retained explicitly. -/
theorem transported_membership {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) {source : InternalAddress}
    (sourceMember : source ∈ second.addresses)
    (destination : CutAddressDestination first source) :
    match destination with
    | .retained _ =>
        source ∈ ValidAddressCut.retainedAddresses first second
    | .detached anchor _ relative _ =>
        ∃ site : first.toCut.Site,
          first.toCut.plan.address site = anchor ∧
            relative ∈
              ValidAddressCut.insideRelativeAddresses first second site := by
  cases destination with
  | retained outside =>
      exact Finset.mem_filter.mpr ⟨sourceMember, outside⟩
  | detached anchor anchorMember relative sourceEq =>
      have planMember : anchor ∈ first.toCut.plan.addressFinset := by
        simpa [first.toCut_addressFinset] using anchorMember
      rcases (first.toCut.plan.mem_addressFinset_iff anchor).mp planMember with
        ⟨site, siteEq⟩
      refine ⟨site, siteEq, ?_⟩
      apply (ValidAddressCut.mem_insideRelativeAddresses_iff
        first second site relative).mpr
      refine ⟨source, sourceMember, ?_⟩
      simpa [siteEq] using sourceEq

end CutAddressDestination

namespace ValidAddressCut

/-- The source-nearest selected addresses.  These are the holes visible in
the final punctured root component after both levels have been exposed. -/
def frontierAddresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) : Finset InternalAddress :=
  (combinedAddresses first second).filter fun address =>
    ¬ ∃ outer ∈ combinedAddresses first second,
      StrictlyInside address outer

/-- The final root frontier is itself a valid CK cut.  This construction is
source-addressed and therefore independent of procedural cut order. -/
def combinedFrontier {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) : ValidAddressCut tree where
  addresses := frontierAddresses first second
  address_vertex := by
    intro address member
    have combined := (Finset.mem_filter.mp member).1
    rcases Finset.mem_union.mp combined with inFirst | inSecond
    · exact first.address_vertex inFirst
    · exact second.address_vertex inSecond
  prefixFree := by
    intro p q pMember qMember different
    have pData := Finset.mem_filter.mp pMember
    have qData := Finset.mem_filter.mp qMember
    constructor
    · intro pPrefixQ
      apply qData.2
      exact ⟨p, pData.1, pPrefixQ, different.symm⟩
    · intro qPrefixP
      apply pData.2
      exact ⟨q, qData.1, qPrefixP, different⟩
  address_nonroot := by
    intro address member
    have combined := (Finset.mem_filter.mp member).1
    rcases Finset.mem_union.mp combined with inFirst | inSecond
    · exact first.address_nonroot inFirst
    · exact second.address_nonroot inSecond
  sourceOrdinary := first.sourceOrdinary

/-- A frontier occurrence belonging to the second cut survives in the first
remainder and is therefore selected by the retained transported cut. -/
theorem frontier_right_mem_retainedAddresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree)
    (cutsDisjoint : Disjoint first.addresses second.addresses)
    {address : InternalAddress}
    (frontierMember : address ∈ frontierAddresses first second)
    (secondMember : address ∈ second.addresses) :
    address ∈ retainedAddresses first second := by
  apply Finset.mem_filter.mpr
  refine ⟨secondMember, ?_⟩
  intro anchor anchorMember isPrefix
  have different : address ≠ anchor := by
    intro equal
    subst anchor
    exact Finset.disjoint_left.mp cutsDisjoint anchorMember secondMember
  exact (Finset.mem_filter.mp frontierMember).2
    ⟨anchor, Finset.mem_union_left _ anchorMember,
      ⟨isPrefix, different⟩⟩

/-- Every source-nearest occurrence of two disjoint cuts is a literal
interface of the actual first-then-second retained root. -/
theorem sequential_remainder_interfaceAt_frontier {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree)
    (cutsDisjoint : Disjoint first.addresses second.addresses)
    {address : InternalAddress}
    (frontierMember : address ∈ frontierAddresses first second) :
    (first.retainedAfter second).toCut.remainder.InterfaceAt address := by
  have combinedMember := (Finset.mem_filter.mp frontierMember).1
  rcases Finset.mem_union.mp combinedMember with firstMember | secondMember
  · have firstPlanMember : address ∈ first.toCut.plan.addressFinset := by
      simpa [first.toCut_addressFinset] using firstMember
    rcases (first.toCut.plan.mem_addressFinset_iff address).mp
        firstPlanMember with ⟨firstSite, firstAddress⟩
    have oldInterface : first.toCut.remainder.InterfaceAt address := by
      simpa [firstAddress] using
        first.toCut.plan.remainder_interfaceAt_site firstSite
    apply (first.retainedAfter second).toCut
      |>.oldInterfaceAt_outside_selectedPrefixes_preserved oldInterface
    intro retainedSite retainedPrefix
    have retainedPlanMember :
        (first.retainedAfter second).toCut.plan.address retainedSite ∈
          (first.retainedAfter second).toCut.plan.addressFinset :=
      ((first.retainedAfter second).toCut.plan.mem_addressFinset_iff _).mpr
        ⟨retainedSite, rfl⟩
    have retainedMember :
        (first.retainedAfter second).toCut.plan.address retainedSite ∈
          retainedAddresses first second := by
      simpa [(first.retainedAfter second).toCut_addressFinset] using
        retainedPlanMember
    have secondSelected := (Finset.mem_filter.mp retainedMember).1
    have different : address ≠
        (first.retainedAfter second).toCut.plan.address retainedSite := by
      intro equal
      apply Finset.disjoint_left.mp cutsDisjoint firstMember
      rw [equal]
      exact secondSelected
    exact (Finset.mem_filter.mp frontierMember).2
      ⟨(first.retainedAfter second).toCut.plan.address retainedSite,
        Finset.mem_union_right _ secondSelected,
        ⟨retainedPrefix, different⟩⟩
  · have retainedMember := frontier_right_mem_retainedAddresses
        first second cutsDisjoint frontierMember secondMember
    have retainedPlanMember :
        address ∈ (first.retainedAfter second).toCut.plan.addressFinset := by
      simpa [(first.retainedAfter second).toCut_addressFinset] using
        retainedMember
    rcases ((first.retainedAfter second).toCut.plan.mem_addressFinset_iff
        address).mp retainedPlanMember with
      ⟨site, addressEq⟩
    simpa [addressEq] using
      (first.retainedAfter second).toCut.plan.remainder_interfaceAt_site site

/-- An occurrence transported inside a first detached factor is identified by
that exact first site together with its relative address. -/
abbrev InsideTransportLocation {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first : ValidAddressCut tree) :=
  first.toCut.Site × InternalAddress

/-- A proposed inside location denotes one exact second-cut source address. -/
def IsInsideTransportLocation {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) (source : InternalAddress)
    (location : InsideTransportLocation first) : Prop :=
  location.2 ∈ insideRelativeAddresses first second location.1 ∧
    first.toCut.plan.address location.1 ++ location.2 = source

/-- Explicit occurrence-level transport bijection, stated fibrewise: every
second-cut source occurrence has exactly one destination.  It is either the
literal retained address and no inside location exists, or one unique
first-site/relative-address pair and it is not retained. -/
theorem transport_partition_unique {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) {source : InternalAddress}
    (sourceMember : source ∈ second.addresses) :
    (source ∈ retainedAddresses first second ∧
      ¬ ∃ location : InsideTransportLocation first,
        IsInsideTransportLocation first second source location) ∨
    (source ∉ retainedAddresses first second ∧
      ∃! location : InsideTransportLocation first,
        IsInsideTransportLocation first second source location) := by
  classical
  by_cases retainedMember : source ∈ retainedAddresses first second
  · apply Or.inl
    refine ⟨retainedMember, ?_⟩
    rintro ⟨⟨site, relative⟩, _, sourceEq⟩
    have outside := (Finset.mem_filter.mp retainedMember).2
    apply outside (first.toCut.plan.address site)
    · rw [← first.toCut_addressFinset]
      exact (first.toCut.plan.mem_addressFinset_iff _).mpr ⟨site, rfl⟩
    · exact ⟨relative, sourceEq⟩
  · apply Or.inr
    refine ⟨retainedMember, ?_⟩
    have notOutside : ¬ (∀ anchor ∈ first.addresses,
        ¬ AddressPrefix anchor source) := by
      intro outside
      exact retainedMember (Finset.mem_filter.mpr ⟨sourceMember, outside⟩)
    push_neg at notOutside
    rcases notOutside with ⟨anchor, anchorMember, anchorPrefix⟩
    have planMember : anchor ∈ first.toCut.plan.addressFinset := by
      simpa [first.toCut_addressFinset] using anchorMember
    rcases (first.toCut.plan.mem_addressFinset_iff anchor).mp planMember with
      ⟨site, siteEq⟩
    let relative := source.drop (first.toCut.plan.address site).length
    have sitePrefix : AddressPrefix (first.toCut.plan.address site) source := by
      simpa [siteEq] using anchorPrefix
    have sourceEq : first.toCut.plan.address site ++ relative = source := by
      exact (List.prefix_append_drop sitePrefix).symm
    have relativeMember :
        relative ∈ insideRelativeAddresses first second site :=
      (mem_insideRelativeAddresses_iff first second site relative).mpr
        ⟨source, sourceMember, sourceEq⟩
    refine ⟨⟨site, relative⟩, ⟨relativeMember, sourceEq⟩, ?_⟩
    rintro ⟨otherSite, otherRelative⟩ ⟨_, otherSourceEq⟩
    have siteEqual : site = otherSite := first.inside_site_unique
      site otherSite ⟨relative, sourceEq⟩
        ⟨otherRelative, otherSourceEq⟩
    subst otherSite
    have relativeEqual : relative = otherRelative := by
      apply List.append_cancel_left
      exact sourceEq.trans otherSourceEq.symm
    subst otherRelative
    rfl

end ValidAddressCut

/-- Whether a source address lies weakly below a selected address of one cut. -/
def BelowCut {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (cut : ValidAddressCut tree) (address : InternalAddress) : Prop :=
  ∃ selected ∈ cut.addresses, AddressPrefix selected address

/-- The three canonical source-addressed vertex regions.  `middle` combines
the two one-cut-only cases without exchanging their cut labels. -/
inductive TwoCutRegion where
  | root
  | middleFirst
  | middleSecond
  | lower
deriving DecidableEq, Repr

namespace TwoCutRegion

/-- Exchange only the labels of the two one-cut middle regions. -/
def swap : TwoCutRegion -> TwoCutRegion
  | .root => .root
  | .middleFirst => .middleSecond
  | .middleSecond => .middleFirst
  | .lower => .lower

@[simp]
theorem swap_swap (region : TwoCutRegion) : region.swap.swap = region := by
  cases region <;> rfl

end TwoCutRegion

/-- Classify a source vertex solely by which of the two cut frontiers lies
above it.  The four constructors encode three geometric layers: the two
middle constructors retain the originating cut label. -/
noncomputable def sourceRegion {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) (address : InternalAddress) :
    TwoCutRegion := by
  classical
  by_cases belowFirst : BelowCut first address
  · by_cases belowSecond : BelowCut second address
    · exact .lower
    · exact .middleFirst
  · by_cases belowSecond : BelowCut second address
    · exact .middleSecond
    · exact .root

/-- Reversing the schedule changes only the labels of the two middle
regions; root and lower regions are literally unchanged. -/
theorem sourceRegion_swap {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) (address : InternalAddress) :
    (sourceRegion second first address).swap =
      sourceRegion first second address := by
  classical
  by_cases belowFirst : BelowCut first address <;>
    by_cases belowSecond : BelowCut second address <;>
    simp [sourceRegion, belowFirst, belowSecond, TwoCutRegion.swap]

/-- One canonical two-stage witness.  It records the original source cuts;
all relative transports and regions are computed from these source identities,
never from a commutative forest. -/
structure CanonicalTwoStageWitness {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) where
  noncrossing : Noncrossing first second

namespace CanonicalTwoStageWitness

variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
variable {first second : ValidAddressCut tree}

/-- Occurrence identities exposed in first-then-second order. -/
abbrev FirstOrderOccurrence :=
  Sum {address // address ∈ first.addresses}
    {address // address ∈ second.addresses}

/-- The same identities exposed in second-then-first order. -/
abbrev SecondOrderOccurrence :=
  Sum {address // address ∈ second.addresses}
    {address // address ∈ first.addresses}

/-- Source address retained by a first-order occurrence. -/
def firstOrderSourceAddress :
    FirstOrderOccurrence (first := first) (second := second) →
      InternalAddress
  | .inl occurrence => occurrence.1
  | .inr occurrence => occurrence.1

/-- Source address retained by a second-order occurrence. -/
def secondOrderSourceAddress :
    SecondOrderOccurrence (first := first) (second := second) →
      InternalAddress
  | .inl occurrence => occurrence.1
  | .inr occurrence => occurrence.1

/-- Source-tagged occurrence bijection between the two schedules.  It swaps
only the stage tag and never identifies source addresses, so multiplicity of
equal displayed trees is retained.  This is not yet a proof that the actual
transported detached tree entries agree; that stronger statement depends on
`ExactTwoStageRemainderCoherence`. -/
def detachedOccurrenceEquiv :
    FirstOrderOccurrence (first := first) (second := second) ≃
      SecondOrderOccurrence (first := first) (second := second) where
  toFun
    | .inl occurrence => .inr occurrence
    | .inr occurrence => .inl occurrence
  invFun
    | .inl occurrence => .inr occurrence
    | .inr occurrence => .inl occurrence
  left_inv := by intro occurrence; cases occurrence <;> rfl
  right_inv := by intro occurrence; cases occurrence <;> rfl

/-- The schedule bijection preserves every literal source address. -/
@[simp]
theorem detachedOccurrenceEquiv_sourceAddress
    (occurrence : FirstOrderOccurrence (first := first) (second := second)) :
    secondOrderSourceAddress (detachedOccurrenceEquiv occurrence) =
      firstOrderSourceAddress occurrence := by
  cases occurrence <;> rfl

/-- Every second-stage occurrence in the first schedule has the unique actual
retained-or-inside transport location proved above. -/
theorem secondOccurrence_uniqueDestination
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : {address // address ∈ second.addresses}) :
    (occurrence.1 ∈ first.retainedAddresses second ∧
      ¬ ∃ location : ValidAddressCut.InsideTransportLocation first,
        ValidAddressCut.IsInsideTransportLocation
          first second occurrence.1 location) ∨
    (occurrence.1 ∉ first.retainedAddresses second ∧
      ∃! location : ValidAddressCut.InsideTransportLocation first,
        ValidAddressCut.IsInsideTransportLocation
          first second occurrence.1 location) :=
  first.transport_partition_unique second occurrence.2

/-- Symmetric unique location for first-stage occurrences in the reverse
schedule. -/
theorem firstOccurrence_uniqueDestination
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : {address // address ∈ first.addresses}) :
    (occurrence.1 ∈ second.retainedAddresses first ∧
      ¬ ∃ location : ValidAddressCut.InsideTransportLocation second,
        ValidAddressCut.IsInsideTransportLocation
          second first occurrence.1 location) ∨
    (occurrence.1 ∉ second.retainedAddresses first ∧
      ∃! location : ValidAddressCut.InsideTransportLocation second,
        ValidAddressCut.IsInsideTransportLocation
          second first occurrence.1 location) :=
  second.transport_partition_unique first occurrence.2

/-- Transport of the second source cut after the first. -/
noncomputable def secondAfterFirst
    (witness : CanonicalTwoStageWitness first second) :
    CutTransport first second :=
  CutTransport.canonical first second

/-- The part of the second cut transported to the retained first remainder. -/
def secondRetainedAfterFirst
    (witness : CanonicalTwoStageWitness first second) :
    ValidAddressCut first.toCut.remainder :=
  first.retainedAfter second

/-- The part of the second cut transported into one exact detached first
factor, retaining its relative addresses. -/
def secondInsideFirst
    (witness : CanonicalTwoStageWitness first second)
    (site : first.toCut.Site) :
    ValidAddressCut (first.toCut.plan.detached site) :=
  first.insideAfter second witness.noncrossing.disjoint site

/-- Transport of the first source cut after the second. -/
noncomputable def firstAfterSecond
    (witness : CanonicalTwoStageWitness first second) :
    CutTransport second first :=
  CutTransport.canonical second first

/-- Reverse-order transport to the retained second remainder. -/
def firstRetainedAfterSecond
    (witness : CanonicalTwoStageWitness first second) :
    ValidAddressCut second.toCut.remainder :=
  second.retainedAfter first

/-- Reverse-order transport into one detached second factor. -/
def firstInsideSecond
    (witness : CanonicalTwoStageWitness first second)
    (site : second.toCut.Site) :
    ValidAddressCut (second.toCut.plan.detached site) :=
  second.insideAfter first witness.noncrossing.disjoint.symm site

/-- Transported cutting in the retained first remainder reconstructs that
exact remainder. -/
theorem secondRetainedAfterFirst_reconstructs
    (witness : CanonicalTwoStageWitness first second) :
    witness.secondRetainedAfterFirst.toCut.fill
        witness.secondRetainedAfterFirst.toCut.plan.detached =
      first.toCut.remainder :=
  witness.secondRetainedAfterFirst.toCut.fill_detached_reconstructs

/-- Transported cutting inside one detached first factor reconstructs that
exact addressed factor. -/
theorem secondInsideFirst_reconstructs
    (witness : CanonicalTwoStageWitness first second)
    (site : first.toCut.Site) :
    (witness.secondInsideFirst site).toCut.fill
        (witness.secondInsideFirst site).toCut.plan.detached =
      first.toCut.plan.detached site :=
  (witness.secondInsideFirst site).toCut.fill_detached_reconstructs

/-- Reconstruct every second-stage part transported inside a first detached
factor, then perform the original distinguished first-stage fill.  This does
not start from the further-cut retained root. -/
theorem first_then_second_inside_filling_reconstructs
    (witness : CanonicalTwoStageWitness first second) :
    first.toCut.fill (fun site =>
      (witness.secondInsideFirst site).toCut.fill
        (witness.secondInsideFirst site).toCut.plan.detached) = tree := by
  have fillers : (fun site =>
      (witness.secondInsideFirst site).toCut.fill
        (witness.secondInsideFirst site).toCut.plan.detached) =
      first.toCut.plan.detached := by
    funext site
    exact witness.secondInsideFirst_reconstructs site
  rw [fillers]
  exact first.toCut.fill_detached_reconstructs

/-- Reverse-order retained reconstruction. -/
theorem firstRetainedAfterSecond_reconstructs
    (witness : CanonicalTwoStageWitness first second) :
    witness.firstRetainedAfterSecond.toCut.fill
        witness.firstRetainedAfterSecond.toCut.plan.detached =
      second.toCut.remainder :=
  witness.firstRetainedAfterSecond.toCut.fill_detached_reconstructs

/-- Reverse-order detached-factor reconstruction. -/
theorem firstInsideSecond_reconstructs
    (witness : CanonicalTwoStageWitness first second)
    (site : second.toCut.Site) :
    (witness.firstInsideSecond site).toCut.fill
        (witness.firstInsideSecond site).toCut.plan.detached =
      second.toCut.plan.detached site :=
  (witness.firstInsideSecond site).toCut.fill_detached_reconstructs

/-- The symmetric inside-factor reconstruction followed by the original
second-stage fill; it likewise does not start from the further-cut root. -/
theorem second_then_first_inside_filling_reconstructs
    (witness : CanonicalTwoStageWitness first second) :
    second.toCut.fill (fun site =>
      (witness.firstInsideSecond site).toCut.fill
        (witness.firstInsideSecond site).toCut.plan.detached) = tree := by
  have fillers : (fun site =>
      (witness.firstInsideSecond site).toCut.fill
        (witness.firstInsideSecond site).toCut.plan.detached) =
      second.toCut.plan.detached := by
    funext site
    exact witness.firstInsideSecond_reconstructs site
  rw [fillers]
  exact second.toCut.fill_detached_reconstructs

/-- Separate first-then-second local reconstruction data: the transported root
cut reconstructs the first remainder, every transported inside cut
reconstructs its exact addressed factor, and restarting from the original
first cut reconstructs the source.  These clauses do not compose a filling
from the further-cut final root. -/
theorem firstThenSecond_reconstruction_laws
    (witness : CanonicalTwoStageWitness first second) :
    (witness.secondRetainedAfterFirst.toCut.fill
        witness.secondRetainedAfterFirst.toCut.plan.detached =
      first.toCut.remainder) ∧
    (∀ site : first.toCut.Site,
      (witness.secondInsideFirst site).toCut.fill
          (witness.secondInsideFirst site).toCut.plan.detached =
        first.toCut.plan.detached site) ∧
    (first.toCut.fill (fun site =>
        (witness.secondInsideFirst site).toCut.fill
          (witness.secondInsideFirst site).toCut.plan.detached) = tree) :=
  ⟨witness.secondRetainedAfterFirst_reconstructs,
    witness.secondInsideFirst_reconstructs,
    witness.first_then_second_inside_filling_reconstructs⟩

/-- Symmetric separate local reconstruction data; again, this is not a
composed filling from the further-cut final root. -/
theorem secondThenFirst_reconstruction_laws
    (witness : CanonicalTwoStageWitness first second) :
    (witness.firstRetainedAfterSecond.toCut.fill
        witness.firstRetainedAfterSecond.toCut.plan.detached =
      second.toCut.remainder) ∧
    (∀ site : second.toCut.Site,
      (witness.firstInsideSecond site).toCut.fill
          (witness.firstInsideSecond site).toCut.plan.detached =
        second.toCut.plan.detached site) ∧
    (second.toCut.fill (fun site =>
        (witness.firstInsideSecond site).toCut.fill
          (witness.firstInsideSecond site).toCut.plan.detached) = tree) :=
  ⟨witness.firstRetainedAfterSecond_reconstructs,
    witness.firstInsideSecond_reconstructs,
    witness.second_then_first_inside_filling_reconstructs⟩

/-- The canonical final root cut, obtained from the source-nearest selected
addresses of both stages. -/
def finalCut (witness : CanonicalTwoStageWitness first second) :
    ValidAddressCut tree :=
  ValidAddressCut.combinedFrontier first second

/-- Final punctured root component. -/
def finalRoot (witness : CanonicalTwoStageWitness first second) :
    CKTree sigma InstanceData G :=
  witness.finalCut.toCut.remainder

/-- The literal root remaining after first cutting `first`, then cutting the
transported part of `second` which remains in that root component. -/
def firstThenSecondRoot (witness : CanonicalTwoStageWitness first second) :
    CKTree sigma InstanceData G :=
  witness.secondRetainedAfterFirst.toCut.remainder

/-- The literal root remaining under the reverse permitted schedule. -/
def secondThenFirstRoot (witness : CanonicalTwoStageWitness first second) :
    CKTree sigma InstanceData G :=
  witness.firstRetainedAfterSecond.toCut.remainder

/-- The exact remaining Phase-D root-coherence target.  Establishing this
proposition requires a constructor-recursive theorem that sequential retained
remainders compile to the union frontier; address-status equality alone is
insufficient because it forgets occurrence decorations. -/
def ExactTwoStageRemainderCoherence
    (witness : CanonicalTwoStageWitness first second) : Prop :=
  witness.firstThenSecondRoot = witness.finalRoot ∧
    witness.secondThenFirstRoot = witness.finalRoot

/-- Swapping the cut labels swaps only the two middle values of the
source-address classifier.  This is not equality of transported region
components or maps, and it does not use the noncrossing certificate. -/
theorem sourceRegion_classifier_swap
    (_witness : CanonicalTwoStageWitness first second)
    (address : InternalAddress) :
    (sourceRegion second first address).swap =
      sourceRegion first second address :=
  sourceRegion_swap first second address

/-- Every canonical frontier occurrence is a literal interface of the actual
first-then-second root. -/
theorem firstThenSecondRoot_interfaceAt_frontier
    (witness : CanonicalTwoStageWitness first second)
    {address : InternalAddress}
    (member : address ∈ ValidAddressCut.frontierAddresses first second) :
    witness.firstThenSecondRoot.InterfaceAt address :=
  ValidAddressCut.sequential_remainder_interfaceAt_frontier
    first second witness.noncrossing.disjoint member

/-- The same canonical frontier occurs in the actual reverse-order root. -/
theorem secondThenFirstRoot_interfaceAt_frontier
    (witness : CanonicalTwoStageWitness first second)
    {address : InternalAddress}
    (member : address ∈ ValidAddressCut.frontierAddresses first second) :
    witness.secondThenFirstRoot.InterfaceAt address := by
  have swappedMember : address ∈
      ValidAddressCut.frontierAddresses second first := by
    simpa [ValidAddressCut.frontierAddresses,
      ValidAddressCut.combinedAddresses, Finset.union_comm] using member
  exact ValidAddressCut.sequential_remainder_interfaceAt_frontier
    second first witness.noncrossing.disjoint.symm swappedMember

/-- The canonical one-stage frontier root exposes the same source-addressed
frontier occurrences. -/
theorem finalRoot_interfaceAt_frontier
    (witness : CanonicalTwoStageWitness first second)
    {address : InternalAddress}
    (member : address ∈ ValidAddressCut.frontierAddresses first second) :
    witness.finalRoot.InterfaceAt address := by
  have finalMember : address ∈ witness.finalCut.addresses := by
    simpa [finalCut, ValidAddressCut.combinedFrontier] using member
  have planMember : address ∈ witness.finalCut.toCut.plan.addressFinset := by
    rw [witness.finalCut.toCut_addressFinset]
    exact finalMember
  rcases (witness.finalCut.toCut.plan.mem_addressFinset_iff address).mp
      planMember with ⟨site, addressEq⟩
  simpa [addressEq] using
    witness.finalCut.toCut.plan.remainder_interfaceAt_site site

/-- Every canonical frontier address is an untyped interface in each of the
two actual staged roots and the canonical root.  This is common interface
presence, not equality of roots, interface sets, or typed path witnesses. -/
theorem actualRoots_have_frontierInterfaces
    (witness : CanonicalTwoStageWitness first second)
    {address : InternalAddress}
    (member : address ∈ ValidAddressCut.frontierAddresses first second) :
    witness.firstThenSecondRoot.InterfaceAt address ∧
      witness.secondThenFirstRoot.InterfaceAt address ∧
        witness.finalRoot.InterfaceAt address :=
  ⟨witness.firstThenSecondRoot_interfaceAt_frontier member,
    witness.secondThenFirstRoot_interfaceAt_frontier member,
    witness.finalRoot_interfaceAt_frontier member⟩

/-- All three actual/canonical roots retain the exact whole source boundary. -/
theorem actualRoots_rootBoundary
    (witness : CanonicalTwoStageWitness first second) :
    witness.firstThenSecondRoot.rootBoundary = tree.rootBoundary ∧
      witness.secondThenFirstRoot.rootBoundary = tree.rootBoundary ∧
        witness.finalRoot.rootBoundary = tree.rootBoundary := by
  exact ⟨rfl, rfl, rfl⟩

/-- Distinguished filling of the canonical visible-frontier cut reconstructs
the exact source tree.  Agreement of this remainder with the two sequential
remainders is stated separately at the proven source-address frontier. -/
theorem frontier_filling_reconstructs
    (witness : CanonicalTwoStageWitness first second) :
    witness.finalCut.toCut.fill witness.finalCut.toCut.plan.detached = tree :=
  witness.finalCut.toCut.fill_detached_reconstructs

end CanonicalTwoStageWitness

/-- The strict independent-refinement clause is the constructor-recursive
insertion theorem: it fixes every old occurrence and ordered premise while
transporting each replacement across the other incomparable puncture. -/
alias strict_interchange_of_independent_refinements :=
  CKTree.PunctureAt.insertIncomparable_commutes

/-- Appending three arbitrary address segments is independent of binary
parenthesisation. -/
theorem relativeAddress_parenthesization
    (outer middle inner : InternalAddress) :
    (outer ++ middle) ++ inner = outer ++ (middle ++ inner) := by
  simp

/-- A binary parenthesisation of a nonempty finite sequence of relative
address segments. -/
inductive AddressBracketing where
  | atom (segment : InternalAddress)
  | join (left right : AddressBracketing)
deriving Repr

namespace AddressBracketing

/-- Ordered leaves; premise positions are never exchanged. -/
def leaves : AddressBracketing → List InternalAddress
  | .atom segment => [segment]
  | .join left right => left.leaves ++ right.leaves

/-- Address obtained by composing the represented relative prefixes. -/
def compose : AddressBracketing → InternalAddress
  | .atom segment => segment
  | .join left right => left.compose ++ right.compose

theorem compose_eq_flatten_leaves (bracketing : AddressBracketing) :
    bracketing.compose = bracketing.leaves.flatten := by
  induction bracketing with
  | atom segment => simp [compose, leaves]
  | join left right leftIH rightIH =>
      simp [compose, leaves, leftIH, rightIH]

theorem compose_independent_of_parenthesization
    {left right : AddressBracketing}
    (sameLeaves : left.leaves = right.leaves) :
    left.compose = right.compose := by
  rw [left.compose_eq_flatten_leaves, right.compose_eq_flatten_leaves,
    sameLeaves]

end AddressBracketing

/-- A finite hierarchy is globally ranked, rather than merely pairwise
noncrossing.  Lower ranks are strictly deeper whenever two selected addresses
are comparable.  This is the missing global hypothesis needed to rule out an
orientation cycle among three or more cuts. -/
structure RankedCutHierarchy {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) where
  levelCount : Nat
  levelCountPositive : 0 < levelCount
  cut : Fin levelCount → ValidAddressCut tree
  disjoint : ∀ {i j}, i ≠ j → Disjoint (cut i).addresses (cut j).addresses
  rank_respects_inside : ∀ {i j} {p q},
    p ∈ (cut i).addresses → q ∈ (cut j).addresses →
    StrictlyInside p q → i.1 < j.1

namespace RankedCutHierarchy

/-- All selected source addresses in a finite globally ranked hierarchy. -/
def allAddresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (hierarchy : RankedCutHierarchy tree) : Finset InternalAddress :=
  Finset.univ.biUnion fun level => (hierarchy.cut level).addresses

/-- Source-nearest occurrences of the entire finite hierarchy. -/
def frontierAddresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (hierarchy : RankedCutHierarchy tree) : Finset InternalAddress :=
  hierarchy.allAddresses.filter fun address =>
    ¬ ∃ outer ∈ hierarchy.allAddresses,
      StrictlyInside address outer

/-- Canonical visible root cut of a finite ranked hierarchy. -/
def finalCut {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (hierarchy : RankedCutHierarchy tree) : ValidAddressCut tree where
  addresses := hierarchy.frontierAddresses
  address_vertex := by
    intro address member
    have allMember := (Finset.mem_filter.mp member).1
    rcases Finset.mem_biUnion.mp allMember with
      ⟨level, _, levelMember⟩
    exact (hierarchy.cut level).address_vertex levelMember
  prefixFree := by
    intro p q pMember qMember different
    have pData := Finset.mem_filter.mp pMember
    have qData := Finset.mem_filter.mp qMember
    constructor
    · intro pPrefixQ
      exact qData.2 ⟨p, pData.1, pPrefixQ, different.symm⟩
    · intro qPrefixP
      exact pData.2 ⟨q, qData.1, qPrefixP, different⟩
  address_nonroot := by
    intro address member
    have allMember := (Finset.mem_filter.mp member).1
    rcases Finset.mem_biUnion.mp allMember with
      ⟨level, _, levelMember⟩
    exact (hierarchy.cut level).address_nonroot levelMember
  sourceOrdinary :=
    (hierarchy.cut ⟨0, hierarchy.levelCountPositive⟩).sourceOrdinary

/-- Final punctured root tree of the hierarchy. -/
def finalRoot {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (hierarchy : RankedCutHierarchy tree) : CKTree sigma InstanceData G :=
  hierarchy.finalCut.toCut.remainder

/-- Every pair of distinct levels in a globally ranked hierarchy satisfies
the two-cut noncrossing condition. -/
theorem pair_noncrossing {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (hierarchy : RankedCutHierarchy tree) {i j : Fin hierarchy.levelCount}
    (different : i ≠ j) :
    Noncrossing (hierarchy.cut i) (hierarchy.cut j) := by
  refine ⟨hierarchy.disjoint different, ?_⟩
  rintro ⟨⟨p, pMember, q, qMember, pInside⟩,
    ⟨q', q'Member, p', p'Member, qInside⟩⟩
  have ij := hierarchy.rank_respects_inside pMember qMember pInside
  have ji := hierarchy.rank_respects_inside q'Member p'Member qInside
  omega

/-- The address-level parenthesisation certificate retains the canonical
frontier root together with a composed relative address map.  It does not by
itself encode an iterated cut schedule. -/
def evaluateParenthesization {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (hierarchy : RankedCutHierarchy tree)
    (bracketing : AddressBracketing) :
    CKTree sigma InstanceData G × InternalAddress :=
  (hierarchy.finalRoot, bracketing.compose)

/-- For one fixed ranked hierarchy, the address-level certificate is
independent of parenthesisation: the root is source-canonical and the relative
address part follows finite associativity of prefix composition. -/
theorem evaluate_independent_of_parenthesization
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (hierarchy : RankedCutHierarchy tree)
    {left right : AddressBracketing}
    (sameLeaves : left.leaves = right.leaves) :
    hierarchy.evaluateParenthesization left =
      hierarchy.evaluateParenthesization right := by
  apply Prod.ext
  · rfl
  · exact AddressBracketing.compose_independent_of_parenthesization
      sameLeaves

end RankedCutHierarchy

/-! ## Tiny address-level falsification fixtures -/

namespace HierarchyGapFixture

/-- Outer/inner addresses of the manuscript running tree `i(m(bS,bT))`. -/
def runningOuter : Finset InternalAddress := { [0] }
def runningInner : Finset InternalAddress := { [0, 0], [0, 1] }

theorem running_nested_noncrossing :
    AddressFamiliesNoncrossing runningOuter runningInner := by
  decide

/-- Two genuinely independent branches impose no nesting direction. -/
def independentLeft : Finset InternalAddress := { [0, 0] }
def independentRight : Finset InternalAddress := { [1, 0] }

theorem independent_branches_noncrossing :
    AddressFamiliesNoncrossing independentLeft independentRight := by
  decide

/-- Opposite nesting directions on two branches. -/
def mixedFirst : Finset InternalAddress := { [0], [1, 0] }
def mixedSecond : Finset InternalAddress := { [0, 0], [1] }

theorem mixed_orientation_rejected :
    ¬ AddressFamiliesNoncrossing mixedFirst mixedSecond := by
  decide

/-- Three pairwise-compatible cut levels whose forced orientations cycle.
These are zero-based forms of
`A={(1,1),(3)}`, `B={(1),(2,1)}`, `C={(2),(3,1)}`. -/
def cycleA : Finset InternalAddress := { [0, 0], [2] }
def cycleB : Finset InternalAddress := { [0], [1, 0] }
def cycleC : Finset InternalAddress := { [1], [2, 0] }

theorem cycle_pair_AB : AddressFamiliesNoncrossing cycleA cycleB := by
  decide

theorem cycle_pair_BC : AddressFamiliesNoncrossing cycleB cycleC := by
  decide

theorem cycle_pair_CA : AddressFamiliesNoncrossing cycleC cycleA := by
  decide

theorem cycle_A_inside_B : HasInsideAddresses cycleA cycleB := by decide
theorem cycle_B_inside_C : HasInsideAddresses cycleB cycleC := by decide
theorem cycle_C_inside_A : HasInsideAddresses cycleC cycleA := by decide

/-- No global natural-number ranking can realize the cyclic pairwise
orientations. -/
theorem no_global_rank (rankA rankB rankC : Nat)
    (AB : rankA < rankB) (BC : rankB < rankC) (CA : rankC < rankA) :
    False := by
  omega

end HierarchyGapFixture

end Potkin

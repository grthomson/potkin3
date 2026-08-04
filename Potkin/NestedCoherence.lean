import Potkin.SourceAddressPruning
import Potkin.RealizedCut
import Potkin.GeneralFilling
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

/-!
# Exact source-addressed two-stage CK-cut coherence

This file keeps the comparison of successive cuts at occurrence level.  In
particular, all relations below are relations on addresses in one fixed source
tree; relative addresses used after transport are accompanied by the equation
which recovers their source address.

The two-stage results identify actual transported components, compare both
schedule occurrence families through explicit bijections, prove equality of
the decorated final remainders, retain multiplicity under forest projection,
and reconstruct by a composed fill from the final root.  Arbitrary finite
ranked schedule coherence is deliberately not claimed here: only its data,
canonical frontier, and the ordinary address-append lemma are present.
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

/-- Strong independent-branch hypothesis: every cross-cut pair is prefix
incomparable.  Unlike `Noncrossing`, this excludes consistently nested pairs
as well as equality and makes the literal union a valid antichain cut. -/
def CrossIncomparableCuts {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) : Prop :=
  ∀ p ∈ first.addresses, ∀ q ∈ second.addresses,
    PrefixIncomparable p q

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

/-- Under the stronger independent-branch hypothesis, the literal finite
union is itself one public valid address cut.  For merely noncrossing nested
cuts, use `combinedFrontier` instead. -/
def unionOfCrossIncomparable {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree)
    (incomparable : CrossIncomparableCuts first second) :
    ValidAddressCut tree where
  addresses := first.addresses ∪ second.addresses
  address_vertex := by
    intro address member
    rcases Finset.mem_union.mp member with firstMember | secondMember
    · exact first.address_vertex firstMember
    · exact second.address_vertex secondMember
  prefixFree := by
    intro p q pMember qMember different
    rcases Finset.mem_union.mp pMember with pFirst | pSecond <;>
      rcases Finset.mem_union.mp qMember with qFirst | qSecond
    · exact first.prefixFree pFirst qFirst different
    · exact incomparable p pFirst q qSecond
    · exact prefixIncomparable_symm (incomparable q qFirst p pSecond)
    · exact second.prefixFree pSecond qSecond different
  address_nonroot := by
    intro address member
    rcases Finset.mem_union.mp member with firstMember | secondMember
    · exact first.address_nonroot firstMember
    · exact second.address_nonroot secondMember
  sourceOrdinary := first.sourceOrdinary

@[simp]
theorem unionOfCrossIncomparable_addresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree)
    (incomparable : CrossIncomparableCuts first second) :
    (unionOfCrossIncomparable first second incomparable).addresses =
      first.addresses ∪ second.addresses := rfl

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

/-- The cut-specific visible frontier is the generic finite source-nearest
frontier of the combined source addresses. -/
theorem frontierAddresses_eq_addressSelectionFrontier
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (first second : ValidAddressCut tree) :
    frontierAddresses first second =
      AddressSelection.frontier (combinedAddresses first second) := by
  ext address
  simp [frontierAddresses, AddressSelection.frontier, StrictlyInside]

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
equal displayed trees is retained.  This definition itself is address-only;
the later middle/lower component equivalences prove equality of the actual
transported decorated entries. -/
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

/-- Relative addresses of every combined selected occurrence strictly below
one canonical source-frontier occurrence. -/
def frontierInnerRelativeAddresses
    (witness : CanonicalTwoStageWitness first second)
    (outer : witness.finalCut.toCut.Site) : Finset InternalAddress :=
  ((ValidAddressCut.combinedAddresses first second).filter fun source =>
      StrictlyInside source (witness.finalCut.toCut.plan.address outer)).image
    (fun source => source.drop
      (witness.finalCut.toCut.plan.address outer).length)

/-- Relative membership carries its original source address and literal
prefix equation. -/
theorem mem_frontierInnerRelativeAddresses_iff
    (witness : CanonicalTwoStageWitness first second)
    (outer : witness.finalCut.toCut.Site) (relative : InternalAddress) :
    relative ∈ witness.frontierInnerRelativeAddresses outer ↔
      ∃ source ∈ ValidAddressCut.combinedAddresses first second,
        StrictlyInside source
          (witness.finalCut.toCut.plan.address outer) ∧
        witness.finalCut.toCut.plan.address outer ++ relative = source := by
  constructor
  · intro member
    rcases Finset.mem_image.mp member with
      ⟨source, sourceData, relativeEq⟩
    have combinedMember := (Finset.mem_filter.mp sourceData).1
    have sourceInside := (Finset.mem_filter.mp sourceData).2
    refine ⟨source, combinedMember, sourceInside, ?_⟩
    rw [← relativeEq]
    exact (List.prefix_append_drop sourceInside.1).symm
  · rintro ⟨source, combinedMember, sourceInside, sourceEq⟩
    have dropEq : source.drop
        (witness.finalCut.toCut.plan.address outer).length = relative := by
      rw [← sourceEq]
      simp
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_filter.mpr
        ⟨combinedMember, sourceInside⟩, dropEq⟩

/-- Below a source-frontier occurrence, all remaining selected addresses lie
in the opposite source antichain and are therefore prefix-free. -/
theorem frontier_descendants_prefixFree
    (witness : CanonicalTwoStageWitness first second)
    {anchor p q : InternalAddress}
    (anchorMember : anchor ∈
      ValidAddressCut.frontierAddresses first second)
    (pMember : p ∈ ValidAddressCut.combinedAddresses first second)
    (qMember : q ∈ ValidAddressCut.combinedAddresses first second)
    (pInside : StrictlyInside p anchor)
    (qInside : StrictlyInside q anchor) (different : p ≠ q) :
    PrefixIncomparable p q := by
  have anchorCombined := (Finset.mem_filter.mp anchorMember).1
  rcases Finset.mem_union.mp anchorCombined with anchorFirst | anchorSecond
  · have pSecond : p ∈ second.addresses := by
      rcases Finset.mem_union.mp pMember with pFirst | pSecond
      · exact False.elim <|
          (first.prefixFree anchorFirst pFirst
            (fun equal => pInside.2 equal.symm)).1 pInside.1
      · exact pSecond
    have qSecond : q ∈ second.addresses := by
      rcases Finset.mem_union.mp qMember with qFirst | qSecond
      · exact False.elim <|
          (first.prefixFree anchorFirst qFirst
            (fun equal => qInside.2 equal.symm)).1 qInside.1
      · exact qSecond
    exact second.prefixFree pSecond qSecond different
  · have pFirst : p ∈ first.addresses := by
      rcases Finset.mem_union.mp pMember with pFirst | pSecond
      · exact pFirst
      · exact False.elim <|
          (second.prefixFree anchorSecond pSecond
            (fun equal => pInside.2 equal.symm)).1 pInside.1
    have qFirst : q ∈ first.addresses := by
      rcases Finset.mem_union.mp qMember with qFirst | qSecond
      · exact qFirst
      · exact False.elim <|
          (second.prefixFree anchorSecond qSecond
            (fun equal => qInside.2 equal.symm)).1 qInside.1
    exact first.prefixFree pFirst qFirst different

/-- The exact inner cut inside one canonical frontier-detached component.
It is constructed directly from source addresses and retains the relative
prefix equation for every site. -/
def frontierInnerCut
    (witness : CanonicalTwoStageWitness first second)
    (outer : witness.finalCut.toCut.Site) :
    ValidAddressCut (witness.finalCut.toCut.plan.detached outer) where
  addresses := witness.frontierInnerRelativeAddresses outer
  address_vertex := by
    intro relative member
    rcases (witness.mem_frontierInnerRelativeAddresses_iff outer relative).mp
        member with ⟨source, combinedMember, _, sourceEq⟩
    apply (witness.finalCut.toCut.detached_vertexAt_iff_source
      outer relative).mpr
    rw [sourceEq]
    rcases Finset.mem_union.mp combinedMember with firstMember | secondMember
    · exact first.address_vertex firstMember
    · exact second.address_vertex secondMember
  prefixFree := by
    intro p q pMember qMember different
    rcases (witness.mem_frontierInnerRelativeAddresses_iff outer p).mp
      pMember with ⟨pSource, pCombined, pInside, pEq⟩
    rcases (witness.mem_frontierInnerRelativeAddresses_iff outer q).mp
      qMember with ⟨qSource, qCombined, qInside, qEq⟩
    have sourceDifferent : pSource ≠ qSource := by
      intro equal
      exact different (List.append_cancel_left
        (pEq.trans (equal.trans qEq.symm)))
    have outerPlanMember :
        witness.finalCut.toCut.plan.address outer ∈
          witness.finalCut.toCut.plan.addressFinset :=
      (witness.finalCut.toCut.plan.mem_addressFinset_iff _).mpr
        ⟨outer, rfl⟩
    have outerFrontier : witness.finalCut.toCut.plan.address outer ∈
        ValidAddressCut.frontierAddresses first second := by
      simpa [finalCut, ValidAddressCut.combinedFrontier] using outerPlanMember
    have sourceIncomparable := witness.frontier_descendants_prefixFree
      outerFrontier pCombined qCombined pInside qInside sourceDifferent
    constructor
    · intro relativePrefix
      apply sourceIncomparable.1
      rw [← pEq, ← qEq]
      exact (List.prefix_append_right_inj _).mpr relativePrefix
    · intro relativePrefix
      apply sourceIncomparable.2
      rw [← pEq, ← qEq]
      exact (List.prefix_append_right_inj _).mpr relativePrefix
  address_nonroot := by
    intro relative member relativeRoot
    rcases (witness.mem_frontierInnerRelativeAddresses_iff outer relative).mp
      member with ⟨source, _, sourceInside, sourceEq⟩
    apply sourceInside.2
    simpa [relativeRoot] using sourceEq.symm
  sourceOrdinary := witness.finalCut.toCut.plan.detachedOrdinary outer

/-- The canonical occurrence-decorated three-region object.  Its middle
occurrences are exact source-frontier sites; its lower occurrences are exact
sites of the relative inner cut in that frontier factor. -/
structure CanonicalThreeRegionDecomposition
    (witness : CanonicalTwoStageWitness first second) where
  innerCut : (outer : witness.finalCut.toCut.Site) →
    ValidAddressCut (witness.finalCut.toCut.plan.detached outer)

/-- Canonical decomposition built directly from the admitted source tree. -/
def canonicalDecomposition
    (witness : CanonicalTwoStageWitness first second) :
    CanonicalThreeRegionDecomposition witness where
  innerCut := witness.frontierInnerCut

namespace CanonicalThreeRegionDecomposition

variable {witness : CanonicalTwoStageWitness first second}

/-- Source-addressed middle occurrence identities. -/
abbrev MiddleOccurrence
    (decomposition : CanonicalThreeRegionDecomposition witness) :=
  witness.finalCut.toCut.Site

/-- Source-addressed lower occurrence identities, retaining the exact outer
site and relative inner site before any forest projection. -/
abbrev LowerOccurrence
    (decomposition : CanonicalThreeRegionDecomposition witness) :=
  (outer : witness.finalCut.toCut.Site) ×
    (decomposition.innerCut outer).toCut.Site

/-- Actual punctured middle component at one exact source occurrence. -/
def middleEntry (decomposition : CanonicalThreeRegionDecomposition witness)
    (outer : decomposition.MiddleOccurrence) : CKCutEntry sigma InstanceData :=
  { address := witness.finalCut.toCut.plan.address outer
    boundary := witness.finalCut.toCut.plan.siteBoundary outer
    tree := (decomposition.innerCut outer).toCut.remainder
    ordinary := (decomposition.innerCut outer).toCut.remainder_isOrdinary }

/-- Actual lower detached occurrence with both relative and original source
addresses retained by its identity. -/
def lowerEntry (decomposition : CanonicalThreeRegionDecomposition witness)
    (occurrence : decomposition.LowerOccurrence) :
    CKCutEntry sigma InstanceData :=
  { address := witness.finalCut.toCut.plan.address occurrence.1 ++
      (decomposition.innerCut occurrence.1).toCut.plan.address occurrence.2
    boundary := (decomposition.innerCut occurrence.1).toCut.plan.siteBoundary
      occurrence.2
    tree := (decomposition.innerCut occurrence.1).toCut.plan.detached
      occurrence.2
    ordinary := (decomposition.innerCut occurrence.1).toCut.plan.detachedOrdinary
      occurrence.2 }

/-- Relative-to-source prefix equation, retained literally. -/
theorem lowerEntry_sourceEquation
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (occurrence : decomposition.LowerOccurrence) :
    witness.finalCut.toCut.plan.address occurrence.1 ++
        (decomposition.innerCut occurrence.1).toCut.plan.address occurrence.2 =
      (decomposition.lowerEntry occurrence).address := rfl

/-- Deterministic occurrence-level middle tuple. -/
def middleTuple (decomposition : CanonicalThreeRegionDecomposition witness) :
    List (CKCutEntry sigma InstanceData) :=
  witness.finalCut.toCut.orderedSites.map decomposition.middleEntry

/-- Deterministic lower tuple, preserving outer-block order, relative order,
and equal displayed occurrences at distinct source addresses. -/
def lowerTuple (decomposition : CanonicalThreeRegionDecomposition witness) :
    List (CKCutEntry sigma InstanceData) :=
  witness.finalCut.toCut.orderedSites.flatMap fun outer =>
    (decomposition.innerCut outer).toCut.orderedSites.map fun inner =>
      decomposition.lowerEntry ⟨outer, inner⟩

/-- Commutative middle forest projection, after occurrence data is retained. -/
def middleForest (decomposition : CanonicalThreeRegionDecomposition witness) :
    CKForest sigma InstanceData :=
  Multiset.ofList <| decomposition.middleTuple.map fun entry =>
    { boundary := entry.boundary
      tree := entry.tree
      ordinary := entry.ordinary }

/-- Commutative lower forest projection, preserving occurrence multiplicity. -/
def lowerForest (decomposition : CanonicalThreeRegionDecomposition witness) :
    CKForest sigma InstanceData :=
  Multiset.ofList <| decomposition.lowerTuple.map fun entry =>
    { boundary := entry.boundary
      tree := entry.tree
      ordinary := entry.ordinary }

/-- Genuine composed two-stage filling from the final source-frontier root:
each punctured middle factor is first reconstructed from its lower factors,
then those reconstructed factors fill the final root. -/
def composedFilling (decomposition : CanonicalThreeRegionDecomposition witness) :
    CKTree sigma InstanceData G :=
  witness.finalCut.toCut.fill fun outer =>
    (decomposition.innerCut outer).toCut.fill
      (decomposition.innerCut outer).toCut.plan.detached

/-- The composed canonical filling reconstructs the exact admitted source
tree without restarting from either original schedule cut. -/
theorem composedFilling_reconstructs
    (decomposition : CanonicalThreeRegionDecomposition witness) :
    decomposition.composedFilling = tree := by
  have fillers : (fun outer =>
      (decomposition.innerCut outer).toCut.fill
        (decomposition.innerCut outer).toCut.plan.detached) =
      witness.finalCut.toCut.plan.detached := by
    funext outer
    exact (decomposition.innerCut outer).toCut.fill_detached_reconstructs
  rw [composedFilling, fillers]
  exact witness.finalCut.toCut.fill_detached_reconstructs

/-- The genuinely staged filling and the direct distinguished filling of the
canonical combined frontier agree as actual decorated trees.  The staged
side first uses the relative inner sites carried by `LowerOccurrence`; the
direct side uses the source-frontier sites carried by `MiddleOccurrence`. -/
theorem composedFilling_eq_frontierFilling
    (decomposition : CanonicalThreeRegionDecomposition witness) :
    decomposition.composedFilling =
      witness.finalCut.toCut.fill witness.finalCut.toCut.plan.detached := by
  rw [decomposition.composedFilling_reconstructs,
    witness.finalCut.toCut.fill_detached_reconstructs]

end CanonicalThreeRegionDecomposition

/-! ## Native schedule occurrence families and source-address equivalences -/

/-- Canonical source-address identity of a middle occurrence. -/
abbrev CanonicalMiddleAddress
    (witness : CanonicalTwoStageWitness first second) :=
  {address // address ∈ ValidAddressCut.frontierAddresses first second}

/-- Middle occurrences actually exposed by the first-then-second schedule:
frontier sites of the first cut, plus the retained second-stage sites. -/
abbrev FirstScheduleMiddleOccurrence
    (witness : CanonicalTwoStageWitness first second) :=
  Sum
    {site : first.toCut.Site // first.toCut.plan.address site ∈
      ValidAddressCut.frontierAddresses first second}
    witness.secondRetainedAfterFirst.toCut.Site

/-- Symmetric middle occurrences of the reverse schedule. -/
abbrev SecondScheduleMiddleOccurrence
    (witness : CanonicalTwoStageWitness first second) :=
  Sum
    {site : second.toCut.Site // second.toCut.plan.address site ∈
      ValidAddressCut.frontierAddresses first second}
    witness.firstRetainedAfterSecond.toCut.Site

/-- Literal source address of a first-schedule middle occurrence. -/
def firstScheduleMiddleSourceAddress
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleMiddleOccurrence witness → InternalAddress
  | .inl site => first.toCut.plan.address site.1
  | .inr site =>
      witness.secondRetainedAfterFirst.toCut.plan.address site

/-- Literal source address of a reverse-schedule middle occurrence. -/
def secondScheduleMiddleSourceAddress
    (witness : CanonicalTwoStageWitness first second) :
    SecondScheduleMiddleOccurrence witness → InternalAddress
  | .inl site => second.toCut.plan.address site.1
  | .inr site =>
      witness.firstRetainedAfterSecond.toCut.plan.address site

/-- Every retained second-stage site is source-nearest in the combined
family. -/
theorem secondRetainedAfterFirst_site_frontier
    (witness : CanonicalTwoStageWitness first second)
    (site : witness.secondRetainedAfterFirst.toCut.Site) :
    witness.secondRetainedAfterFirst.toCut.plan.address site ∈
      ValidAddressCut.frontierAddresses first second := by
  let source := witness.secondRetainedAfterFirst.toCut.plan.address site
  have planMember : source ∈
      witness.secondRetainedAfterFirst.toCut.plan.addressFinset :=
    (witness.secondRetainedAfterFirst.toCut.plan.mem_addressFinset_iff _).mpr
      ⟨site, rfl⟩
  have retainedMember : source ∈
      ValidAddressCut.retainedAddresses first second := by
    simpa [secondRetainedAfterFirst,
      ValidAddressCut.toCut_addressFinset] using planMember
  have retainedData := Finset.mem_filter.mp retainedMember
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_union_right _ retainedData.1, ?_⟩
  rintro ⟨outer, outerCombined, sourceInside⟩
  rcases Finset.mem_union.mp outerCombined with outerFirst | outerSecond
  · exact retainedData.2 outer outerFirst sourceInside.1
  · exact (second.prefixFree outerSecond retainedData.1
      (fun equal => sourceInside.2 equal.symm)).1 sourceInside.1

/-- Symmetric retained-site frontier fact. -/
theorem firstRetainedAfterSecond_site_frontier
    (witness : CanonicalTwoStageWitness first second)
    (site : witness.firstRetainedAfterSecond.toCut.Site) :
    witness.firstRetainedAfterSecond.toCut.plan.address site ∈
      ValidAddressCut.frontierAddresses first second := by
  have swapped := (CanonicalTwoStageWitness.mk
    witness.noncrossing.symm).secondRetainedAfterFirst_site_frontier site
  simpa [ValidAddressCut.frontierAddresses,
    ValidAddressCut.combinedAddresses, Finset.union_comm,
    firstRetainedAfterSecond, secondRetainedAfterFirst] using swapped

/-- The first native middle family maps into the canonical source-address
family. -/
def firstScheduleMiddleToCanonical
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : FirstScheduleMiddleOccurrence witness) :
    CanonicalMiddleAddress witness :=
  match occurrence with
  | .inl site => ⟨first.toCut.plan.address site.1, site.2⟩
  | .inr site =>
      ⟨witness.secondRetainedAfterFirst.toCut.plan.address site,
        witness.secondRetainedAfterFirst_site_frontier site⟩

/-- The reverse native middle family maps into the same canonical addresses. -/
def secondScheduleMiddleToCanonical
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : SecondScheduleMiddleOccurrence witness) :
    CanonicalMiddleAddress witness :=
  match occurrence with
  | .inl site => ⟨second.toCut.plan.address site.1, site.2⟩
  | .inr site =>
      ⟨witness.firstRetainedAfterSecond.toCut.plan.address site,
        witness.firstRetainedAfterSecond_site_frontier site⟩

/-- First-schedule middle source addresses are injective, including across
the two sum branches. -/
theorem firstScheduleMiddleToCanonical_injective
    (witness : CanonicalTwoStageWitness first second) :
    Function.Injective witness.firstScheduleMiddleToCanonical := by
  intro left right equal
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          apply congrArg Sum.inl
          apply Subtype.ext
          apply first.toCut.address_injective
          exact congrArg Subtype.val equal
      | inr right =>
          have firstMember : first.toCut.plan.address left.1 ∈
              first.addresses := by
            rw [← first.toCut_addressFinset]
            exact (first.toCut.plan.mem_addressFinset_iff _).mpr
              ⟨left.1, rfl⟩
          have rightPlanMember :=
            (witness.secondRetainedAfterFirst.toCut.plan
              |>.mem_addressFinset_iff _).mpr ⟨right, rfl⟩
          have secondMember :
              witness.secondRetainedAfterFirst.toCut.plan.address right ∈
                second.addresses := by
            have retained :
                witness.secondRetainedAfterFirst.toCut.plan.address right ∈
                  ValidAddressCut.retainedAddresses first second := by
              simpa [secondRetainedAfterFirst] using rightPlanMember
            exact (Finset.mem_filter.mp retained).1
          have addressEq : first.toCut.plan.address left.1 =
              witness.secondRetainedAfterFirst.toCut.plan.address right := by
            exact congrArg Subtype.val equal
          rw [← addressEq] at secondMember
          exact False.elim <| Finset.disjoint_left.mp
            witness.noncrossing.disjoint firstMember
              secondMember
  | inr left =>
      cases right with
      | inl right =>
          have leftPlanMember :=
            (witness.secondRetainedAfterFirst.toCut.plan
              |>.mem_addressFinset_iff _).mpr ⟨left, rfl⟩
          have secondMember :
              witness.secondRetainedAfterFirst.toCut.plan.address left ∈
                second.addresses := by
            have retained :
                witness.secondRetainedAfterFirst.toCut.plan.address left ∈
                  ValidAddressCut.retainedAddresses first second := by
              simpa [secondRetainedAfterFirst] using leftPlanMember
            exact (Finset.mem_filter.mp retained).1
          have firstMember : first.toCut.plan.address right.1 ∈
              first.addresses := by
            rw [← first.toCut_addressFinset]
            exact (first.toCut.plan.mem_addressFinset_iff _).mpr
              ⟨right.1, rfl⟩
          have addressEq :
              witness.secondRetainedAfterFirst.toCut.plan.address left =
                first.toCut.plan.address right.1 := by
            exact congrArg Subtype.val equal
          rw [addressEq] at secondMember
          exact False.elim <| Finset.disjoint_left.mp
            witness.noncrossing.disjoint firstMember secondMember
      | inr right =>
          apply congrArg Sum.inr
          apply witness.secondRetainedAfterFirst.toCut.address_injective
          exact congrArg Subtype.val equal

/-- Every canonical middle address occurs in the native first schedule. -/
theorem firstScheduleMiddleToCanonical_surjective
    (witness : CanonicalTwoStageWitness first second) :
    Function.Surjective witness.firstScheduleMiddleToCanonical := by
  intro canonical
  have combined := (Finset.mem_filter.mp canonical.2).1
  rcases Finset.mem_union.mp combined with firstMember | secondMember
  · have planMember : canonical.1 ∈ first.toCut.plan.addressFinset := by
      simpa [first.toCut_addressFinset] using firstMember
    rcases (first.toCut.plan.mem_addressFinset_iff canonical.1).mp
      planMember with ⟨site, siteEq⟩
    refine ⟨Sum.inl ⟨site, ?_⟩, ?_⟩
    · simpa [siteEq] using canonical.2
    · apply Subtype.ext
      exact siteEq
  · have retained := ValidAddressCut.frontier_right_mem_retainedAddresses
      first second witness.noncrossing.disjoint canonical.2 secondMember
    have planMember : canonical.1 ∈
        witness.secondRetainedAfterFirst.toCut.plan.addressFinset := by
      simpa [secondRetainedAfterFirst,
        ValidAddressCut.toCut_addressFinset] using retained
    rcases (witness.secondRetainedAfterFirst.toCut.plan
      |>.mem_addressFinset_iff canonical.1).mp planMember with
      ⟨site, siteEq⟩
    refine ⟨Sum.inr site, ?_⟩
    apply Subtype.ext
    exact siteEq

/-- Explicit source-address bijection for first-then-second middle
occurrences. -/
noncomputable def firstScheduleMiddleEquiv
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleMiddleOccurrence witness ≃ CanonicalMiddleAddress witness :=
  Equiv.ofBijective witness.firstScheduleMiddleToCanonical
    ⟨witness.firstScheduleMiddleToCanonical_injective,
      witness.firstScheduleMiddleToCanonical_surjective⟩

/-- Reverse-schedule middle bijection, obtained by the same source-address
construction with cut labels exchanged. -/
noncomputable def secondScheduleMiddleEquiv
    (witness : CanonicalTwoStageWitness first second) :
    SecondScheduleMiddleOccurrence witness ≃ CanonicalMiddleAddress witness := by
  let swapped : CanonicalTwoStageWitness second first :=
    ⟨witness.noncrossing.symm⟩
  let canonicalSwap : CanonicalMiddleAddress swapped ≃
      CanonicalMiddleAddress witness := Equiv.ofBijective
    (fun occurrence => ⟨occurrence.1, by
      simpa [ValidAddressCut.frontierAddresses,
        ValidAddressCut.combinedAddresses, Finset.union_comm] using occurrence.2⟩)
    (by
      constructor
      · intro left right equal
        apply Subtype.ext
        exact congrArg
          (fun occurrence : CanonicalMiddleAddress witness => occurrence.1)
          equal
      · intro occurrence
        exact ⟨⟨occurrence.1, by
          simpa [ValidAddressCut.frontierAddresses,
            ValidAddressCut.combinedAddresses, Finset.union_comm] using
              occurrence.2⟩, Subtype.ext rfl⟩)
  let nativeSwap : SecondScheduleMiddleOccurrence witness ≃
      FirstScheduleMiddleOccurrence swapped :=
  { toFun := fun
      | .inl site => .inl ⟨site.1, by
          simpa [ValidAddressCut.frontierAddresses,
            ValidAddressCut.combinedAddresses, Finset.union_comm] using site.2⟩
      | .inr site => .inr site
    invFun := fun
      | .inl site => .inl ⟨site.1, by
          simpa [ValidAddressCut.frontierAddresses,
            ValidAddressCut.combinedAddresses, Finset.union_comm] using site.2⟩
      | .inr site => .inr site
    left_inv := by
      intro occurrence
      cases occurrence with
      | inl site =>
          apply congrArg Sum.inl
          apply Subtype.ext
          rfl
      | inr site => rfl
    right_inv := by
      intro occurrence
      cases occurrence with
      | inl site =>
          apply congrArg Sum.inl
          apply Subtype.ext
          rfl
      | inr site => rfl
  }
  exact nativeSwap.trans (swapped.firstScheduleMiddleEquiv.trans canonicalSwap)

/-- Canonical frontier site selected by one canonical middle source address. -/
noncomputable def canonicalMiddleSite
    (witness : CanonicalTwoStageWitness first second)
    (address : CanonicalMiddleAddress witness) :
    witness.finalCut.toCut.Site :=
  witness.finalCut.toCut.siteAddressEquiv.symm
    ⟨address.1, by
      simpa [finalCut, ValidAddressCut.combinedFrontier] using address.2⟩

@[simp]
theorem canonicalMiddleSite_address
    (witness : CanonicalTwoStageWitness first second)
    (address : CanonicalMiddleAddress witness) :
    witness.finalCut.toCut.plan.address
        (witness.canonicalMiddleSite address) = address.1 := by
  have inverse := witness.finalCut.toCut.siteAddressEquiv.apply_symm_apply
    ⟨address.1, by
      simpa [finalCut, ValidAddressCut.combinedFrontier] using address.2⟩
  exact congrArg Subtype.val inverse

/-- Actual canonical punctured middle component at a source address. -/
noncomputable def canonicalMiddleComponent
    (witness : CanonicalTwoStageWitness first second)
    (address : CanonicalMiddleAddress witness) :
    CKComponent sigma InstanceData :=
  let outer := witness.canonicalMiddleSite address
  (witness.canonicalDecomposition.innerCut outer).toCut.remainderComponent

/-- Actual middle component exposed by the first native schedule. -/
def firstScheduleMiddleComponent
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleMiddleOccurrence witness → CKComponent sigma InstanceData
  | .inl site =>
      (witness.secondInsideFirst site.1).toCut.remainderComponent
  | .inr site =>
      witness.secondRetainedAfterFirst.toCut.detachedComponent site

/-- Actual middle component exposed by the reverse native schedule. -/
def secondScheduleMiddleComponent
    (witness : CanonicalTwoStageWitness first second) :
    SecondScheduleMiddleOccurrence witness → CKComponent sigma InstanceData
  | .inl site =>
      (witness.firstInsideSecond site.1).toCut.remainderComponent
  | .inr site =>
      witness.firstRetainedAfterSecond.toCut.detachedComponent site

/-- At a first-cut frontier site, the canonical relative inner family is
exactly the transported second family. -/
theorem frontierInnerRelativeAddresses_eq_secondInsideFirst
    (witness : CanonicalTwoStageWitness first second)
    (site : first.toCut.Site)
    (frontier : first.toCut.plan.address site ∈
      ValidAddressCut.frontierAddresses first second) :
    witness.frontierInnerRelativeAddresses
        (witness.canonicalMiddleSite
          ⟨first.toCut.plan.address site, frontier⟩) =
      ValidAddressCut.insideRelativeAddresses first second site := by
  ext relative
  rw [witness.mem_frontierInnerRelativeAddresses_iff]
  rw [ValidAddressCut.mem_insideRelativeAddresses_iff]
  constructor
  · rintro ⟨source, combinedMember, sourceInside, sourceEq⟩
    have outerEq : witness.finalCut.toCut.plan.address
        (witness.canonicalMiddleSite
          ⟨first.toCut.plan.address site, frontier⟩) =
        first.toCut.plan.address site :=
      witness.canonicalMiddleSite_address _
    have sourceInsideFirst : StrictlyInside source
        (first.toCut.plan.address site) := by
      simpa [outerEq] using sourceInside
    have sourceSecond : source ∈ second.addresses := by
      rcases Finset.mem_union.mp combinedMember with sourceFirst | sourceSecond
      · exact False.elim <|
          (first.prefixFree
            (by
              rw [← first.toCut_addressFinset]
              exact (first.toCut.plan.mem_addressFinset_iff _).mpr
                ⟨site, rfl⟩)
            sourceFirst (fun equal => sourceInsideFirst.2 equal.symm)).1
              sourceInsideFirst.1
      · exact sourceSecond
    exact ⟨source, sourceSecond, by simpa [outerEq] using sourceEq⟩
  · rintro ⟨source, sourceSecond, sourceEq⟩
    have outerEq : witness.finalCut.toCut.plan.address
        (witness.canonicalMiddleSite
          ⟨first.toCut.plan.address site, frontier⟩) =
        first.toCut.plan.address site :=
      witness.canonicalMiddleSite_address _
    have sourceDifferent : source ≠ first.toCut.plan.address site := by
      intro equal
      have firstMember : first.toCut.plan.address site ∈ first.addresses := by
        rw [← first.toCut_addressFinset]
        exact (first.toCut.plan.mem_addressFinset_iff _).mpr ⟨site, rfl⟩
      exact Finset.disjoint_left.mp witness.noncrossing.disjoint
        firstMember (equal ▸ sourceSecond)
    refine ⟨source, Finset.mem_union_right _ sourceSecond, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      exact ⟨relative, by simpa [outerEq] using sourceEq⟩
      intro equal
      exact sourceDifferent (by simpa [outerEq] using equal)
    · simpa [outerEq] using sourceEq

/-- At a first-cut frontier occurrence, the native transported remainder and
the canonical punctured middle component are the same actual decorated
component, not merely the same source address. -/
theorem firstScheduleMiddleComponent_inl_eq_canonical
    (witness : CanonicalTwoStageWitness first second)
    (site : first.toCut.Site)
    (frontier : first.toCut.plan.address site ∈
      ValidAddressCut.frontierAddresses first second) :
    witness.firstScheduleMiddleComponent (Sum.inl ⟨site, frontier⟩) =
      witness.canonicalMiddleComponent
        ⟨first.toCut.plan.address site, frontier⟩ := by
  let canonicalAddress : CanonicalMiddleAddress witness :=
    ⟨first.toCut.plan.address site, frontier⟩
  let outer := witness.canonicalMiddleSite canonicalAddress
  change (witness.secondInsideFirst site).toCut.remainderComponent =
    (witness.frontierInnerCut outer).toCut.remainderComponent
  have outerAddress : witness.finalCut.toCut.plan.address outer =
      first.toCut.plan.address site := by
    exact witness.canonicalMiddleSite_address canonicalAddress
  have sourceComponentEq : first.toCut.detachedComponent site =
      witness.finalCut.toCut.detachedComponent outer :=
    first.toCut.detachedComponent_eq_of_address_eq
      witness.finalCut.toCut site outer outerAddress.symm
  have selectedEq : (witness.secondInsideFirst site).addresses =
      (witness.frontierInnerCut outer).addresses := by
    change ValidAddressCut.insideRelativeAddresses first second site =
      witness.frontierInnerRelativeAddresses outer
    exact (witness.frontierInnerRelativeAddresses_eq_secondInsideFirst
      site frontier).symm
  apply CKComponent.ext
  · change (first.toCut.detachedComponent site).boundary =
      (witness.finalCut.toCut.detachedComponent outer).boundary
    exact congrArg CKComponent.boundary sourceComponentEq
  · have leftTreeEq := ValidAddressCut.remainder_eq_pruneAddresses
        (witness.secondInsideFirst site)
    have rightTreeEq := ValidAddressCut.remainder_eq_pruneAddresses
        (witness.frontierInnerCut outer)
    have leftHEq : HEq
        (witness.secondInsideFirst site).toCut.remainder
        ((first.toCut.detachedComponent site).tree.pruneAddresses
          (witness.secondInsideFirst site).addresses) := by
      exact heqOfEq leftTreeEq
    have middleHEq := CKComponent.pruneAddresses_tree_heq_of_eq
      sourceComponentEq selectedEq
    have rightHEq : HEq
        (witness.frontierInnerCut outer).toCut.remainder
        ((witness.finalCut.toCut.detachedComponent outer).tree.pruneAddresses
          (witness.frontierInnerCut outer).addresses) := by
      exact heqOfEq rightTreeEq
    exact leftHEq.trans (middleHEq.trans rightHEq.symm)

/-- At a second-cut frontier site, the canonical relative inner family is
exactly the first-family suffixes below that source address. -/
theorem frontierInnerRelativeAddresses_eq_belowFirst
    (witness : CanonicalTwoStageWitness first second)
    (source : InternalAddress) (sourceSecond : source ∈ second.addresses)
    (frontier : source ∈
      ValidAddressCut.frontierAddresses first second) :
    witness.frontierInnerRelativeAddresses
        (witness.canonicalMiddleSite ⟨source, frontier⟩) =
      AddressSelection.belowRelative first.addresses source := by
  ext relative
  rw [witness.mem_frontierInnerRelativeAddresses_iff]
  rw [AddressSelection.mem_belowRelative_iff]
  have outerEq : witness.finalCut.toCut.plan.address
      (witness.canonicalMiddleSite ⟨source, frontier⟩) = source :=
    witness.canonicalMiddleSite_address _
  constructor
  · rintro ⟨selected, combinedMember, selectedInside, selectedEq⟩
    have selectedInsideSource : StrictlyInside selected source := by
      simpa [outerEq] using selectedInside
    rcases Finset.mem_union.mp combinedMember with selectedFirst | selectedSecond
    · have relativeMember := selectedFirst
      rw [← selectedEq, outerEq] at relativeMember
      exact relativeMember
    · exact False.elim <|
        (second.prefixFree sourceSecond selectedSecond
          (fun equal => selectedInsideSource.2 equal.symm)).1
            selectedInsideSource.1
  · intro selectedMember
    let selected := source ++ relative
    have selectedFirst : selected ∈ first.addresses := selectedMember
    have different : selected ≠ source := by
      intro equal
      exact Finset.disjoint_left.mp witness.noncrossing.disjoint
        selectedFirst (equal ▸ sourceSecond)
    refine ⟨selected, Finset.mem_union_left _ selectedFirst, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      exact ⟨relative, by simp [selected, outerEq]⟩
      intro equal
      exact different (by simpa [outerEq] using equal)
    · simp [selected, outerEq]

/-- A retained second-stage detached factor is the source factor pruned by
exactly the first-family descendants. -/
theorem secondRetainedAfterFirst_component_eq_prunedSource
    (witness : CanonicalTwoStageWitness first second)
    (site : witness.secondRetainedAfterFirst.toCut.Site) :
    witness.secondRetainedAfterFirst.toCut.detachedComponent site =
      (witness.finalCut.toCut.detachedComponent
        (witness.canonicalMiddleSite
          (witness.firstScheduleMiddleToCanonical (Sum.inr site)))).pruneNonroot
          (AddressSelection.belowRelative first.addresses
            (witness.secondRetainedAfterFirst.toCut.plan.address site))
          (by
            apply AddressSelection.belowRelative_root_absent
            intro dominated
            rcases dominated with ⟨anchor, anchorMember, anchorPrefix⟩
            have planMember :=
              (witness.secondRetainedAfterFirst.toCut.plan
                |>.mem_addressFinset_iff _).mpr ⟨site, rfl⟩
            have retained :
                witness.secondRetainedAfterFirst.toCut.plan.address site ∈
                  ValidAddressCut.retainedAddresses first second := by
              simpa [secondRetainedAfterFirst] using planMember
            exact (Finset.mem_filter.mp retained).2
              anchor anchorMember anchorPrefix) := by
  let source := witness.secondRetainedAfterFirst.toCut.plan.address site
  let canonical := witness.firstScheduleMiddleToCanonical (Sum.inr site)
  let outer := witness.canonicalMiddleSite canonical
  have outerAddress : witness.finalCut.toCut.plan.address outer = source := by
    exact witness.canonicalMiddleSite_address canonical
  have planMember : source ∈
      witness.secondRetainedAfterFirst.toCut.plan.addressFinset :=
    (witness.secondRetainedAfterFirst.toCut.plan.mem_addressFinset_iff _).mpr
      ⟨site, rfl⟩
  have retained : source ∈
      ValidAddressCut.retainedAddresses first second := by
    simpa [source, secondRetainedAfterFirst] using planMember
  have outside : ¬ AddressSelection.Dominates first.addresses source := by
    rintro ⟨anchor, anchorMember, anchorPrefix⟩
    exact (Finset.mem_filter.mp retained).2 anchor anchorMember anchorPrefix
  have actualLookup :=
    witness.secondRetainedAfterFirst.toCut.plan
      |>.componentAt?_address_eq_detachedComponent site
  have sourceLookup := witness.finalCut.toCut.plan
    |>.componentAt?_address_eq_detachedComponent outer
  have remainderTreeEq := ValidAddressCut.remainder_eq_pruneAddresses first
  have remainderLookupEq := congrArg
    (fun retainedTree => retainedTree.componentAt? source) remainderTreeEq
  have pruneLookup := CKTree.componentAt?_pruneAddresses
    tree first.addresses source outside
  have sourceLookupAt : tree.componentAt? source =
      some (witness.finalCut.toCut.detachedComponent outer) := by
    simpa [outerAddress] using sourceLookup
  have someEqual :
      some (witness.secondRetainedAfterFirst.toCut.detachedComponent site) =
        some ((witness.finalCut.toCut.detachedComponent outer).pruneNonroot
          (AddressSelection.belowRelative first.addresses source)
          (AddressSelection.belowRelative_root_absent outside)) := by
    calc
      some (witness.secondRetainedAfterFirst.toCut.detachedComponent site) =
          first.toCut.remainder.componentAt? source := actualLookup.symm
      _ = (tree.pruneAddresses first.addresses).componentAt? source :=
        remainderLookupEq
      _ = (tree.componentAt? source).map (fun component =>
          component.pruneNonroot
            (AddressSelection.belowRelative first.addresses source)
            (AddressSelection.belowRelative_root_absent outside)) := pruneLookup
      _ = some ((witness.finalCut.toCut.detachedComponent outer).pruneNonroot
          (AddressSelection.belowRelative first.addresses source)
          (AddressSelection.belowRelative_root_absent outside)) := by
        rw [sourceLookupAt]
        change some _ = some _
        apply congrArg some
        apply CKComponent.ext <;> rfl
  exact Option.some.inj someEqual

/-- The retained branch of the first native schedule preserves the actual
transported middle component under the canonical address equivalence. -/
theorem firstScheduleMiddleComponent_inr_eq_canonical
    (witness : CanonicalTwoStageWitness first second)
    (site : witness.secondRetainedAfterFirst.toCut.Site) :
    witness.firstScheduleMiddleComponent (Sum.inr site) =
      witness.canonicalMiddleComponent
        (witness.firstScheduleMiddleEquiv (Sum.inr site)) := by
  let source := witness.secondRetainedAfterFirst.toCut.plan.address site
  let canonical := witness.firstScheduleMiddleToCanonical (Sum.inr site)
  let outer := witness.canonicalMiddleSite canonical
  have sourceSecond : source ∈ second.addresses := by
    have planMember :=
      (witness.secondRetainedAfterFirst.toCut.plan
        |>.mem_addressFinset_iff _).mpr ⟨site, rfl⟩
    have retained : source ∈
        ValidAddressCut.retainedAddresses first second := by
      simpa [source, secondRetainedAfterFirst] using planMember
    exact (Finset.mem_filter.mp retained).1
  have frontier : source ∈
      ValidAddressCut.frontierAddresses first second :=
    witness.secondRetainedAfterFirst_site_frontier site
  have selectedEq : (witness.frontierInnerCut outer).addresses =
      AddressSelection.belowRelative first.addresses source := by
    exact witness.frontierInnerRelativeAddresses_eq_belowFirst
      source sourceSecond frontier
  have actualEq := witness.secondRetainedAfterFirst_component_eq_prunedSource site
  have canonicalNormal := ValidAddressCut.remainderComponent_eq_pruneNonroot
    (witness.frontierInnerCut outer)
  change witness.secondRetainedAfterFirst.toCut.detachedComponent site =
    (witness.frontierInnerCut outer).toCut.remainderComponent
  rw [actualEq, canonicalNormal]
  apply CKComponent.ext
  · rfl
  · exact CKComponent.pruneAddresses_tree_heq_of_eq rfl selectedEq.symm

/-- The explicit first-schedule source-address bijection preserves the actual
transported decorated middle component pointwise. -/
theorem firstScheduleMiddleEquiv_component
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : FirstScheduleMiddleOccurrence witness) :
    witness.firstScheduleMiddleComponent occurrence =
      witness.canonicalMiddleComponent
        (witness.firstScheduleMiddleEquiv occurrence) := by
  cases occurrence with
  | inl site =>
      change witness.firstScheduleMiddleComponent (Sum.inl site) =
        witness.canonicalMiddleComponent
          ⟨first.toCut.plan.address site.1, site.2⟩
      exact witness.firstScheduleMiddleComponent_inl_eq_canonical
        site.1 site.2
  | inr site =>
      exact witness.firstScheduleMiddleComponent_inr_eq_canonical site

/-- Canonical source-address identity of a lower occurrence. -/
abbrev CanonicalLowerAddress
    (witness : CanonicalTwoStageWitness first second) :=
  {address // address ∈ ValidAddressCut.combinedAddresses first second ∧
    address ∉ ValidAddressCut.frontierAddresses first second}

/-- The canonical lower-address type is finite because its predicate is the
difference of two explicit finite source-address sets. -/
noncomputable instance canonicalLowerAddressFintype
    (witness : CanonicalTwoStageWitness first second) :
    Fintype (CanonicalLowerAddress witness) :=
  Fintype.ofFinset
    (ValidAddressCut.combinedAddresses first second \
      ValidAddressCut.frontierAddresses first second) (by
        intro address
        rw [Finset.mem_sdiff]
        change
          (address ∈ ValidAddressCut.combinedAddresses first second ∧
              address ∉ ValidAddressCut.frontierAddresses first second) ↔
            (address ∈ ValidAddressCut.combinedAddresses first second ∧
              address ∉ ValidAddressCut.frontierAddresses first second)
        simp)

/-- Lower occurrences actually exposed by the first schedule: transported
second sites inside a first factor, plus first sites lying below a retained
second frontier. -/
abbrev FirstScheduleLowerOccurrence
    (witness : CanonicalTwoStageWitness first second) :=
  Sum
    (Σ outer : first.toCut.Site,
      (witness.secondInsideFirst outer).toCut.Site)
    {site : first.toCut.Site // first.toCut.plan.address site ∉
      ValidAddressCut.frontierAddresses first second}

/-- Literal global source address of a first-schedule lower occurrence. -/
def firstScheduleLowerSourceAddress
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleLowerOccurrence witness → InternalAddress
  | .inl occurrence =>
      first.toCut.plan.address occurrence.1 ++
        (witness.secondInsideFirst occurrence.1).toCut.plan.address
          occurrence.2
  | .inr occurrence => first.toCut.plan.address occurrence.1

/-- Actual lower detached component of the first schedule. -/
def firstScheduleLowerComponent
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleLowerOccurrence witness → CKComponent sigma InstanceData
  | .inl occurrence =>
      (witness.secondInsideFirst occurrence.1).toCut.detachedComponent
        occurrence.2
  | .inr occurrence => first.toCut.detachedComponent occurrence.1

/-- One transported inside occurrence recovers a selected second source
address. -/
theorem secondInsideFirst_source_mem
    (witness : CanonicalTwoStageWitness first second)
    (outer : first.toCut.Site)
    (inner : (witness.secondInsideFirst outer).toCut.Site) :
    witness.firstScheduleLowerSourceAddress (Sum.inl ⟨outer, inner⟩) ∈
      second.addresses := by
  have planMember :
      (witness.secondInsideFirst outer).toCut.plan.address inner ∈
        (witness.secondInsideFirst outer).toCut.plan.addressFinset :=
    ((witness.secondInsideFirst outer).toCut.plan.mem_addressFinset_iff _).mpr
      ⟨inner, rfl⟩
  have relativeMember :
      (witness.secondInsideFirst outer).toCut.plan.address inner ∈
        ValidAddressCut.insideRelativeAddresses first second outer := by
    simpa [secondInsideFirst] using planMember
  rcases (ValidAddressCut.mem_insideRelativeAddresses_iff
    first second outer _).mp relativeMember with
    ⟨source, sourceMember, sourceEq⟩
  simpa [firstScheduleLowerSourceAddress, sourceEq]

/-- The first native lower family maps into the canonical lower addresses. -/
def firstScheduleLowerToCanonical
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : FirstScheduleLowerOccurrence witness) :
    CanonicalLowerAddress witness := by
  refine ⟨witness.firstScheduleLowerSourceAddress occurrence, ?_, ?_⟩
  · cases occurrence with
    | inl occurrence =>
        exact Finset.mem_union_right _
          (witness.secondInsideFirst_source_mem occurrence.1 occurrence.2)
    | inr occurrence =>
        apply Finset.mem_union_left
        rw [← first.toCut_addressFinset]
        exact (first.toCut.plan.mem_addressFinset_iff _).mpr
          ⟨occurrence.1, rfl⟩
  · cases occurrence with
    | inl occurrence =>
        intro frontier
        have outerMember : first.toCut.plan.address occurrence.1 ∈
            ValidAddressCut.combinedAddresses first second := by
          apply Finset.mem_union_left
          rw [← first.toCut_addressFinset]
          exact (first.toCut.plan.mem_addressFinset_iff _).mpr
            ⟨occurrence.1, rfl⟩
        have sourcePrefix :
            AddressPrefix (first.toCut.plan.address occurrence.1)
              (witness.firstScheduleLowerSourceAddress
                (Sum.inl occurrence)) := by
          refine ⟨(witness.secondInsideFirst occurrence.1).toCut.plan.address
            occurrence.2, ?_⟩
          rfl
        have sourceNe :
            witness.firstScheduleLowerSourceAddress (Sum.inl occurrence) ≠
              first.toCut.plan.address occurrence.1 := by
          intro equal
          have nonroot :=
            (witness.secondInsideFirst occurrence.1).toCut.address_nonroot
              occurrence.2
          have relativeEmpty :
              (witness.secondInsideFirst occurrence.1).toCut.plan.address
                  occurrence.2 = [] :=
            List.append_cancel_left
              (as := first.toCut.plan.address occurrence.1) (by
              simpa [firstScheduleLowerSourceAddress] using equal)
          exact nonroot relativeEmpty
        exact (Finset.mem_filter.mp frontier).2
          ⟨first.toCut.plan.address occurrence.1, outerMember,
            ⟨sourcePrefix, sourceNe⟩⟩
    | inr occurrence => exact occurrence.2

/-- The native first lower-address map is injective. -/
theorem firstScheduleLowerToCanonical_injective
    (witness : CanonicalTwoStageWitness first second) :
    Function.Injective witness.firstScheduleLowerToCanonical := by
  intro left right equal
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          have addressEq :
              first.toCut.plan.address left.1 ++
                  (witness.secondInsideFirst left.1).toCut.plan.address left.2 =
                first.toCut.plan.address right.1 ++
                  (witness.secondInsideFirst right.1).toCut.plan.address
                    right.2 :=
            by
              simpa [firstScheduleLowerToCanonical,
                firstScheduleLowerSourceAddress] using
                congrArg Subtype.val equal
          have outerEq : left.1 = right.1 := first.inside_site_unique
            left.1 right.1
              ⟨(witness.secondInsideFirst left.1).toCut.plan.address left.2,
                rfl⟩
              ⟨(witness.secondInsideFirst right.1).toCut.plan.address right.2,
                addressEq.symm⟩
          rcases left with ⟨leftOuter, leftInner⟩
          rcases right with ⟨rightOuter, rightInner⟩
          change leftOuter = rightOuter at outerEq
          subst rightOuter
          have innerEq : leftInner = rightInner :=
            (witness.secondInsideFirst leftOuter).toCut.address_injective
              (List.append_cancel_left addressEq)
          subst rightInner
          rfl
      | inr right =>
          have secondMember := witness.secondInsideFirst_source_mem left.1 left.2
          have firstMember : first.toCut.plan.address right.1 ∈
              first.addresses := by
            rw [← first.toCut_addressFinset]
            exact (first.toCut.plan.mem_addressFinset_iff _).mpr
              ⟨right.1, rfl⟩
          have sourceEq :
              witness.firstScheduleLowerSourceAddress (Sum.inl left) =
                first.toCut.plan.address right.1 :=
            by
              simpa [firstScheduleLowerToCanonical,
                firstScheduleLowerSourceAddress] using
                congrArg Subtype.val equal
          rw [sourceEq] at secondMember
          exact False.elim <| Finset.disjoint_left.mp
            witness.noncrossing.disjoint firstMember secondMember
  | inr left =>
      cases right with
      | inl right =>
          have secondMember := witness.secondInsideFirst_source_mem right.1 right.2
          have firstMember : first.toCut.plan.address left.1 ∈
              first.addresses := by
            rw [← first.toCut_addressFinset]
            exact (first.toCut.plan.mem_addressFinset_iff _).mpr
              ⟨left.1, rfl⟩
          have sourceEq :
              first.toCut.plan.address left.1 =
                witness.firstScheduleLowerSourceAddress (Sum.inl right) :=
            by
              simpa [firstScheduleLowerToCanonical,
                firstScheduleLowerSourceAddress] using
                congrArg Subtype.val equal
          rw [← sourceEq] at secondMember
          exact False.elim <| Finset.disjoint_left.mp
            witness.noncrossing.disjoint firstMember secondMember
      | inr right =>
          apply congrArg Sum.inr
          apply Subtype.ext
          apply first.toCut.address_injective
          simpa [firstScheduleLowerToCanonical,
            firstScheduleLowerSourceAddress] using
            congrArg Subtype.val equal

/-- Every canonical lower address occurs once in the native first schedule. -/
theorem firstScheduleLowerToCanonical_surjective
    (witness : CanonicalTwoStageWitness first second) :
    Function.Surjective witness.firstScheduleLowerToCanonical := by
  intro canonical
  rcases canonical.2.1 with combinedMember
  rcases Finset.mem_union.mp combinedMember with firstMember | secondMember
  · have planMember : canonical.1 ∈ first.toCut.plan.addressFinset := by
      simpa [first.toCut_addressFinset] using firstMember
    rcases (first.toCut.plan.mem_addressFinset_iff canonical.1).mp
      planMember with ⟨site, siteEq⟩
    refine ⟨Sum.inr ⟨site, ?_⟩, ?_⟩
    · simpa [siteEq] using canonical.2.2
    · apply Subtype.ext
      simpa [firstScheduleLowerToCanonical,
        firstScheduleLowerSourceAddress] using siteEq
  · have hasOuter : ∃ outer ∈
        ValidAddressCut.combinedAddresses first second,
        StrictlyInside canonical.1 outer := by
      by_contra noOuter
      exact canonical.2.2 (Finset.mem_filter.mpr
        ⟨combinedMember, noOuter⟩)
    rcases hasOuter with ⟨outerAddress, outerCombined, sourceInside⟩
    have outerFirst : outerAddress ∈ first.addresses := by
      rcases Finset.mem_union.mp outerCombined with outerFirst | outerSecond
      · exact outerFirst
      · exact False.elim <| (second.prefixFree outerSecond secondMember
          (fun equal => sourceInside.2 equal.symm)).1 sourceInside.1
    have outerPlanMember : outerAddress ∈ first.toCut.plan.addressFinset := by
      simpa [first.toCut_addressFinset] using outerFirst
    rcases (first.toCut.plan.mem_addressFinset_iff outerAddress).mp
      outerPlanMember with ⟨outer, outerEq⟩
    let relative := canonical.1.drop outerAddress.length
    have sourceEq : outerAddress ++ relative = canonical.1 :=
      (List.prefix_append_drop sourceInside.1).symm
    have relativeMember : relative ∈
        ValidAddressCut.insideRelativeAddresses first second outer := by
      apply (ValidAddressCut.mem_insideRelativeAddresses_iff
        first second outer relative).mpr
      exact ⟨canonical.1, secondMember, by simpa [outerEq] using sourceEq⟩
    have innerPlanMember : relative ∈
        (witness.secondInsideFirst outer).toCut.plan.addressFinset := by
      simpa [secondInsideFirst] using relativeMember
    rcases ((witness.secondInsideFirst outer).toCut.plan
      |>.mem_addressFinset_iff relative).mp innerPlanMember with
      ⟨inner, innerEq⟩
    refine ⟨Sum.inl ⟨outer, inner⟩, ?_⟩
    apply Subtype.ext
    simp only [firstScheduleLowerToCanonical,
      firstScheduleLowerSourceAddress]
    rw [outerEq, innerEq]
    exact sourceEq

/-- Explicit multiplicity-preserving lower-occurrence bijection. -/
noncomputable def firstScheduleLowerEquiv
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleLowerOccurrence witness ≃ CanonicalLowerAddress witness :=
  Equiv.ofBijective witness.firstScheduleLowerToCanonical
    ⟨witness.firstScheduleLowerToCanonical_injective,
      witness.firstScheduleLowerToCanonical_surjective⟩

/-- Corresponding lower occurrences are the same actual global decorated
source subtree under the explicit address bijection. -/
theorem firstScheduleLowerEquiv_componentLookup
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : FirstScheduleLowerOccurrence witness) :
    tree.componentAt?
        (witness.firstScheduleLowerEquiv occurrence).1 =
      some (witness.firstScheduleLowerComponent occurrence) := by
  cases occurrence with
  | inl occurrence =>
      simpa [firstScheduleLowerEquiv, firstScheduleLowerToCanonical,
        firstScheduleLowerSourceAddress, firstScheduleLowerComponent] using
        first.toCut.nestedDetachedComponent_globalLookup occurrence.1
          (witness.secondInsideFirst occurrence.1).toCut occurrence.2
  | inr occurrence =>
      simpa [firstScheduleLowerEquiv, firstScheduleLowerToCanonical,
        firstScheduleLowerSourceAddress, firstScheduleLowerComponent] using
        first.toCut.plan.componentAt?_address_eq_detachedComponent occurrence.1

/-! ### Canonical and reverse-schedule lower occurrences -/

/-- The source address carried by one canonical lower occurrence. -/
def CanonicalThreeRegionDecomposition.lowerSourceAddress
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (occurrence : decomposition.LowerOccurrence) : InternalAddress :=
  witness.finalCut.toCut.plan.address occurrence.1 ++
    (decomposition.innerCut occurrence.1).toCut.plan.address occurrence.2

/-- Canonical lower occurrences map to the non-frontier selected source
addresses without forgetting their outer/relative decomposition. -/
def canonicalLowerOccurrenceToAddress
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : witness.canonicalDecomposition.LowerOccurrence) :
    CanonicalLowerAddress witness := by
  let relative :=
    (witness.canonicalDecomposition.innerCut occurrence.1).toCut.plan.address
      occurrence.2
  have relativePlanMember : relative ∈
      (witness.canonicalDecomposition.innerCut occurrence.1).toCut.plan.addressFinset :=
    ((witness.canonicalDecomposition.innerCut occurrence.1).toCut.plan
      |>.mem_addressFinset_iff relative).mpr ⟨occurrence.2, rfl⟩
  have relativeMember : relative ∈
      witness.frontierInnerRelativeAddresses occurrence.1 := by
    simpa [canonicalDecomposition, frontierInnerCut] using relativePlanMember
  refine ⟨witness.canonicalDecomposition.lowerSourceAddress occurrence,
    ?_, ?_⟩
  · rcases (witness.mem_frontierInnerRelativeAddresses_iff
        occurrence.1 relative).mp relativeMember with
      ⟨source, sourceMember, _, sourceEq⟩
    simpa [CanonicalThreeRegionDecomposition.lowerSourceAddress,
      relative, sourceEq] using sourceMember
  · intro sourceFrontier
    rcases (witness.mem_frontierInnerRelativeAddresses_iff
        occurrence.1 relative).mp relativeMember with
      ⟨source, _, sourceInside, sourceEq⟩
    have outerPlanMember : witness.finalCut.toCut.plan.address occurrence.1 ∈
        witness.finalCut.toCut.plan.addressFinset :=
      (witness.finalCut.toCut.plan.mem_addressFinset_iff _).mpr
        ⟨occurrence.1, rfl⟩
    have outerFrontier : witness.finalCut.toCut.plan.address occurrence.1 ∈
        ValidAddressCut.frontierAddresses first second := by
      simpa [finalCut, ValidAddressCut.combinedFrontier] using outerPlanMember
    exact (Finset.mem_filter.mp sourceFrontier).2
      ⟨witness.finalCut.toCut.plan.address occurrence.1,
        (Finset.mem_filter.mp outerFrontier).1,
        by
          simpa [CanonicalThreeRegionDecomposition.lowerSourceAddress,
            relative, sourceEq] using sourceInside⟩

/-- The canonical lower occurrence map is injective, including equal
displayed factors at distinct source sites. -/
theorem canonicalLowerOccurrenceToAddress_injective
    (witness : CanonicalTwoStageWitness first second) :
    Function.Injective witness.canonicalLowerOccurrenceToAddress := by
  intro left right equal
  have addressEq :
      witness.finalCut.toCut.plan.address left.1 ++
          (witness.canonicalDecomposition.innerCut left.1).toCut.plan.address
            left.2 =
        witness.finalCut.toCut.plan.address right.1 ++
          (witness.canonicalDecomposition.innerCut right.1).toCut.plan.address
            right.2 := by
    simpa [canonicalLowerOccurrenceToAddress,
      CanonicalThreeRegionDecomposition.lowerSourceAddress] using
      congrArg Subtype.val equal
  have outerEq : left.1 = right.1 := witness.finalCut.inside_site_unique
    left.1 right.1
      ⟨(witness.canonicalDecomposition.innerCut left.1).toCut.plan.address
        left.2, rfl⟩
      ⟨(witness.canonicalDecomposition.innerCut right.1).toCut.plan.address
        right.2, addressEq.symm⟩
  rcases left with ⟨leftOuter, leftInner⟩
  rcases right with ⟨rightOuter, rightInner⟩
  change leftOuter = rightOuter at outerEq
  subst rightOuter
  have innerEq : leftInner = rightInner :=
    (witness.canonicalDecomposition.innerCut leftOuter).toCut.address_injective
      (List.append_cancel_left addressEq)
  subst rightInner
  rfl

/-- Every non-frontier selected source occurrence has one unique canonical
outer/relative lower occurrence. -/
theorem canonicalLowerOccurrenceToAddress_surjective
    (witness : CanonicalTwoStageWitness first second) :
    Function.Surjective witness.canonicalLowerOccurrenceToAddress := by
  intro canonical
  have selectedDominates : AddressSelection.Dominates
      (ValidAddressCut.combinedAddresses first second) canonical.1 :=
    ⟨canonical.1, canonical.2.1, by simp [AddressPrefix]⟩
  have frontierDominates : AddressSelection.Dominates
      (AddressSelection.frontier
        (ValidAddressCut.combinedAddresses first second)) canonical.1 :=
    (AddressSelection.dominates_frontier_iff _ _).mpr selectedDominates
  rcases frontierDominates with
    ⟨outerAddress, outerFrontierSelection, outerPrefix⟩
  have outerFrontier : outerAddress ∈
      ValidAddressCut.frontierAddresses first second := by
    rw [ValidAddressCut.frontierAddresses_eq_addressSelectionFrontier]
    exact outerFrontierSelection
  let outer := witness.canonicalMiddleSite ⟨outerAddress, outerFrontier⟩
  have outerEq : witness.finalCut.toCut.plan.address outer = outerAddress :=
    witness.canonicalMiddleSite_address ⟨outerAddress, outerFrontier⟩
  let relative := canonical.1.drop outerAddress.length
  have sourceEq : outerAddress ++ relative = canonical.1 :=
    (List.prefix_append_drop outerPrefix).symm
  have strictInside : StrictlyInside canonical.1 outerAddress := by
    refine ⟨outerPrefix, ?_⟩
    intro equal
    apply canonical.2.2
    simpa [equal] using outerFrontier
  have relativeMember : relative ∈
      witness.frontierInnerRelativeAddresses outer := by
    apply (witness.mem_frontierInnerRelativeAddresses_iff outer relative).mpr
    exact ⟨canonical.1, canonical.2.1,
      by simpa [outerEq] using strictInside,
      by simpa [outerEq] using sourceEq⟩
  have innerPlanMember : relative ∈
      (witness.canonicalDecomposition.innerCut outer).toCut.plan.addressFinset := by
    simpa [canonicalDecomposition, frontierInnerCut] using relativeMember
  rcases ((witness.canonicalDecomposition.innerCut outer).toCut.plan
      |>.mem_addressFinset_iff relative).mp innerPlanMember with
    ⟨inner, innerEq⟩
  refine ⟨⟨outer, inner⟩, ?_⟩
  apply Subtype.ext
  simp only [canonicalLowerOccurrenceToAddress,
    CanonicalThreeRegionDecomposition.lowerSourceAddress]
  rw [outerEq, innerEq]
  exact sourceEq

/-- Exact bijection between canonical relative lower occurrences and their
global non-frontier source addresses. -/
noncomputable def canonicalLowerOccurrenceEquiv
    (witness : CanonicalTwoStageWitness first second) :
    witness.canonicalDecomposition.LowerOccurrence ≃
      CanonicalLowerAddress witness :=
  Equiv.ofBijective witness.canonicalLowerOccurrenceToAddress
    ⟨witness.canonicalLowerOccurrenceToAddress_injective,
      witness.canonicalLowerOccurrenceToAddress_surjective⟩

namespace CanonicalThreeRegionDecomposition

variable {witness : CanonicalTwoStageWitness first second}

/-- Actual lower component selected by one canonical relative occurrence. -/
def lowerComponent
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (occurrence : decomposition.LowerOccurrence) :
    CKComponent sigma InstanceData :=
  (decomposition.innerCut occurrence.1).toCut.detachedComponent occurrence.2

end CanonicalThreeRegionDecomposition

/-- Canonical lower occurrences look up the actual decorated source subtree
at their retained global address. -/
theorem canonicalLowerOccurrenceEquiv_componentLookup
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : witness.canonicalDecomposition.LowerOccurrence) :
    tree.componentAt?
        (witness.canonicalLowerOccurrenceEquiv occurrence).1 =
      some (witness.canonicalDecomposition.lowerComponent occurrence) := by
  simpa [canonicalLowerOccurrenceEquiv,
    canonicalLowerOccurrenceToAddress,
    CanonicalThreeRegionDecomposition.lowerSourceAddress,
    CanonicalThreeRegionDecomposition.lowerComponent,
    canonicalDecomposition] using
    witness.finalCut.toCut.nestedDetachedComponent_globalLookup occurrence.1
      (witness.canonicalDecomposition.innerCut occurrence.1).toCut occurrence.2

/-- First-native lower occurrences correspond to canonical relative
occurrences, not merely to unstructured source addresses. -/
noncomputable def firstScheduleLowerOccurrenceEquiv
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleLowerOccurrence witness ≃
      witness.canonicalDecomposition.LowerOccurrence :=
  witness.firstScheduleLowerEquiv.trans
    witness.canonicalLowerOccurrenceEquiv.symm

/-- The first schedule preserves the actual occurrence-decorated lower
component under the canonical relative-occurrence bijection. -/
theorem firstScheduleLowerOccurrenceEquiv_component
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : FirstScheduleLowerOccurrence witness) :
    witness.firstScheduleLowerComponent occurrence =
      witness.canonicalDecomposition.lowerComponent
        (witness.firstScheduleLowerOccurrenceEquiv occurrence) := by
  have native := witness.firstScheduleLowerEquiv_componentLookup occurrence
  have canonical := witness.canonicalLowerOccurrenceEquiv_componentLookup
    (witness.firstScheduleLowerOccurrenceEquiv occurrence)
  have sameAddress :
      (witness.firstScheduleLowerEquiv occurrence).1 =
        (witness.canonicalLowerOccurrenceEquiv
          (witness.firstScheduleLowerOccurrenceEquiv occurrence)).1 := by
    simp [firstScheduleLowerOccurrenceEquiv]
  rw [sameAddress] at native
  exact Option.some.inj (native.symm.trans canonical)

/-- Exchange the two source-cut labels while retaining the same ambient
decorated source tree. -/
def swapped (witness : CanonicalTwoStageWitness first second) :
    CanonicalTwoStageWitness second first :=
  ⟨witness.noncrossing.symm⟩

/-- Reverse-schedule lower occurrences are literally the first-schedule
occurrences of the label-swapped witness.  Thus they retain both the outer
second-cut site and every relative first-cut site. -/
abbrev SecondScheduleLowerOccurrence
    (witness : CanonicalTwoStageWitness first second) :=
  FirstScheduleLowerOccurrence witness.swapped

/-- Global source address of a reverse-schedule lower occurrence. -/
def secondScheduleLowerSourceAddress
    (witness : CanonicalTwoStageWitness first second) :
    SecondScheduleLowerOccurrence witness → InternalAddress :=
  witness.swapped.firstScheduleLowerSourceAddress

/-- Actual occurrence-decorated lower component in the reverse schedule. -/
def secondScheduleLowerComponent
    (witness : CanonicalTwoStageWitness first second) :
    SecondScheduleLowerOccurrence witness → CKComponent sigma InstanceData :=
  witness.swapped.firstScheduleLowerComponent

/-- Swapping labels induces an address-preserving equivalence between the
two presentations of canonical non-frontier source addresses. -/
noncomputable def swappedCanonicalLowerAddressEquiv
    (witness : CanonicalTwoStageWitness first second) :
    CanonicalLowerAddress witness.swapped ≃ CanonicalLowerAddress witness :=
  Equiv.ofBijective
    (fun occurrence => ⟨occurrence.1, by
      constructor
      · simpa [ValidAddressCut.combinedAddresses, Finset.union_comm] using
          occurrence.2.1
      · simpa [ValidAddressCut.frontierAddresses,
          ValidAddressCut.combinedAddresses, Finset.union_comm] using
          occurrence.2.2⟩)
    (by
      constructor
      · intro left right equal
        apply Subtype.ext
        exact congrArg
          (fun occurrence : CanonicalLowerAddress witness => occurrence.1)
          equal
      · intro occurrence
        refine ⟨⟨occurrence.1, ?_⟩, Subtype.ext rfl⟩
        constructor
        · simpa [ValidAddressCut.combinedAddresses, Finset.union_comm] using
            occurrence.2.1
        · simpa [ValidAddressCut.frontierAddresses,
            ValidAddressCut.combinedAddresses, Finset.union_comm] using
            occurrence.2.2)

/-- Explicit reverse-schedule lower-address bijection. -/
noncomputable def secondScheduleLowerEquiv
    (witness : CanonicalTwoStageWitness first second) :
    SecondScheduleLowerOccurrence witness ≃ CanonicalLowerAddress witness :=
  witness.swapped.firstScheduleLowerEquiv.trans
    witness.swappedCanonicalLowerAddressEquiv

@[simp]
theorem secondScheduleLowerEquiv_sourceAddress
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : SecondScheduleLowerOccurrence witness) :
    (witness.secondScheduleLowerEquiv occurrence).1 =
      witness.secondScheduleLowerSourceAddress occurrence := by
  rfl

/-- Reverse lower occurrences retrieve the same actual global decorated
source subtree under the explicit source-address bijection. -/
theorem secondScheduleLowerEquiv_componentLookup
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : SecondScheduleLowerOccurrence witness) :
    tree.componentAt? (witness.secondScheduleLowerEquiv occurrence).1 =
      some (witness.secondScheduleLowerComponent occurrence) := by
  simpa [secondScheduleLowerEquiv, secondScheduleLowerComponent,
    swappedCanonicalLowerAddressEquiv] using
    witness.swapped.firstScheduleLowerEquiv_componentLookup occurrence

/-- Reverse-native lower occurrences correspond to canonical relative
occurrences while retaining multiplicity. -/
noncomputable def secondScheduleLowerOccurrenceEquiv
    (witness : CanonicalTwoStageWitness first second) :
    SecondScheduleLowerOccurrence witness ≃
      witness.canonicalDecomposition.LowerOccurrence :=
  witness.secondScheduleLowerEquiv.trans
    witness.canonicalLowerOccurrenceEquiv.symm

/-- The reverse schedule preserves each actual lower decorated component. -/
theorem secondScheduleLowerOccurrenceEquiv_component
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : SecondScheduleLowerOccurrence witness) :
    witness.secondScheduleLowerComponent occurrence =
      witness.canonicalDecomposition.lowerComponent
        (witness.secondScheduleLowerOccurrenceEquiv occurrence) := by
  have native := witness.secondScheduleLowerEquiv_componentLookup occurrence
  have canonical := witness.canonicalLowerOccurrenceEquiv_componentLookup
    (witness.secondScheduleLowerOccurrenceEquiv occurrence)
  have sameAddress :
      (witness.secondScheduleLowerEquiv occurrence).1 =
        (witness.canonicalLowerOccurrenceEquiv
          (witness.secondScheduleLowerOccurrenceEquiv occurrence)).1 := by
    simp [secondScheduleLowerOccurrenceEquiv]
  rw [sameAddress] at native
  exact Option.some.inj (native.symm.trans canonical)

/-! ### Reverse middle-component coherence -/

/-- The reverse native middle family is the first native family after
exchanging the two source-cut labels. -/
noncomputable def secondScheduleMiddleSwapEquiv
    (witness : CanonicalTwoStageWitness first second) :
    SecondScheduleMiddleOccurrence witness ≃
      FirstScheduleMiddleOccurrence witness.swapped where
  toFun
    | .inl site => .inl ⟨site.1, by
        simpa [ValidAddressCut.frontierAddresses,
          ValidAddressCut.combinedAddresses, Finset.union_comm] using site.2⟩
    | .inr site => .inr site
  invFun
    | .inl site => .inl ⟨site.1, by
        simpa [ValidAddressCut.frontierAddresses,
          ValidAddressCut.combinedAddresses, Finset.union_comm] using site.2⟩
    | .inr site => .inr site
  left_inv := by
    intro occurrence
    cases occurrence with
    | inl site =>
        apply congrArg Sum.inl
        apply Subtype.ext
        rfl
    | inr site => rfl
  right_inv := by
    intro occurrence
    cases occurrence with
    | inl site =>
        apply congrArg Sum.inl
        apply Subtype.ext
        rfl
    | inr site => rfl

/-- Canonical middle source identities are unchanged by exchanging the cut
labels. -/
noncomputable def swappedCanonicalMiddleAddressEquiv
    (witness : CanonicalTwoStageWitness first second) :
    CanonicalMiddleAddress witness.swapped ≃ CanonicalMiddleAddress witness :=
  Equiv.ofBijective
    (fun occurrence => ⟨occurrence.1, by
      simpa [ValidAddressCut.frontierAddresses,
        ValidAddressCut.combinedAddresses, Finset.union_comm] using occurrence.2⟩)
    (by
      constructor
      · intro left right equal
        apply Subtype.ext
        exact congrArg
          (fun occurrence : CanonicalMiddleAddress witness => occurrence.1)
          equal
      · intro occurrence
        exact ⟨⟨occurrence.1, by
          simpa [ValidAddressCut.frontierAddresses,
            ValidAddressCut.combinedAddresses, Finset.union_comm] using
              occurrence.2⟩, Subtype.ext rfl⟩)

/-- The previously exposed reverse middle equivalence is exactly the
label-swapped construction, at occurrence level. -/
theorem secondScheduleMiddleEquiv_eq_swapped
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : SecondScheduleMiddleOccurrence witness) :
    witness.secondScheduleMiddleEquiv occurrence =
      witness.swappedCanonicalMiddleAddressEquiv
        (witness.swapped.firstScheduleMiddleEquiv
          (witness.secondScheduleMiddleSwapEquiv occurrence)) := by
  rfl

/-- The actual native reverse middle component is definitionally the actual
first-schedule component of the label-swapped witness. -/
theorem secondScheduleMiddleComponent_eq_swapped
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : SecondScheduleMiddleOccurrence witness) :
    witness.secondScheduleMiddleComponent occurrence =
      witness.swapped.firstScheduleMiddleComponent
        (witness.secondScheduleMiddleSwapEquiv occurrence) := by
  cases occurrence <;> rfl

/-- The canonical punctured middle component is invariant under exchanging
the two source-cut labels.  The proof compares the actual source component
and exact relative pruning family, not only its boundary. -/
theorem canonicalMiddleComponent_swapped
    (witness : CanonicalTwoStageWitness first second)
    (address : CanonicalMiddleAddress witness.swapped) :
    witness.swapped.canonicalMiddleComponent address =
      witness.canonicalMiddleComponent
        (witness.swappedCanonicalMiddleAddressEquiv address) := by
  let swappedOuter := witness.swapped.canonicalMiddleSite address
  let originalAddress := witness.swappedCanonicalMiddleAddressEquiv address
  let originalOuter := witness.canonicalMiddleSite originalAddress
  change (witness.swapped.frontierInnerCut swappedOuter).toCut.remainderComponent =
    (witness.frontierInnerCut originalOuter).toCut.remainderComponent
  have swappedOuterAddress :
      witness.swapped.finalCut.toCut.plan.address swappedOuter = address.1 :=
    witness.swapped.canonicalMiddleSite_address address
  have originalOuterAddress :
      witness.finalCut.toCut.plan.address originalOuter = address.1 := by
    rw [witness.canonicalMiddleSite_address originalAddress]
    rfl
  have sourceComponentEq :
      witness.swapped.finalCut.toCut.detachedComponent swappedOuter =
        witness.finalCut.toCut.detachedComponent originalOuter :=
    witness.swapped.finalCut.toCut.detachedComponent_eq_of_address_eq
      witness.finalCut.toCut swappedOuter originalOuter
        (swappedOuterAddress.trans originalOuterAddress.symm)
  have selectedEq :
      (witness.swapped.frontierInnerCut swappedOuter).addresses =
        (witness.frontierInnerCut originalOuter).addresses := by
    change witness.swapped.frontierInnerRelativeAddresses swappedOuter =
      witness.frontierInnerRelativeAddresses originalOuter
    ext relative
    rw [witness.swapped.mem_frontierInnerRelativeAddresses_iff,
      witness.mem_frontierInnerRelativeAddresses_iff]
    constructor
    · rintro ⟨source, member, inside, sourceEq⟩
      refine ⟨source, ?_, ?_, ?_⟩
      · simpa [ValidAddressCut.combinedAddresses, Finset.union_comm] using
          member
      · simpa [swappedOuterAddress, originalOuterAddress] using inside
      · simpa [swappedOuterAddress, originalOuterAddress] using sourceEq
    · rintro ⟨source, member, inside, sourceEq⟩
      refine ⟨source, ?_, ?_, ?_⟩
      · simpa [ValidAddressCut.combinedAddresses, Finset.union_comm] using
          member
      · simpa [swappedOuterAddress, originalOuterAddress] using inside
      · simpa [swappedOuterAddress, originalOuterAddress] using sourceEq
  apply CKComponent.ext
  · change
      (witness.swapped.finalCut.toCut.detachedComponent swappedOuter).boundary =
        (witness.finalCut.toCut.detachedComponent originalOuter).boundary
    exact congrArg CKComponent.boundary sourceComponentEq
  · have leftTreeEq := ValidAddressCut.remainder_eq_pruneAddresses
        (witness.swapped.frontierInnerCut swappedOuter)
    have rightTreeEq := ValidAddressCut.remainder_eq_pruneAddresses
        (witness.frontierInnerCut originalOuter)
    have leftHEq : HEq
        (witness.swapped.frontierInnerCut swappedOuter).toCut.remainder
        ((witness.swapped.finalCut.toCut.detachedComponent swappedOuter).tree
          |>.pruneAddresses
            (witness.swapped.frontierInnerCut swappedOuter).addresses) :=
      heqOfEq leftTreeEq
    have middleHEq := CKComponent.pruneAddresses_tree_heq_of_eq
      sourceComponentEq selectedEq
    have rightHEq : HEq
        (witness.frontierInnerCut originalOuter).toCut.remainder
        ((witness.finalCut.toCut.detachedComponent originalOuter).tree
          |>.pruneAddresses
            (witness.frontierInnerCut originalOuter).addresses) :=
      heqOfEq rightTreeEq
    exact leftHEq.trans (middleHEq.trans rightHEq.symm)

/-- The reverse middle occurrence bijection preserves the actual punctured
decorated component pointwise. -/
theorem secondScheduleMiddleEquiv_component
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : SecondScheduleMiddleOccurrence witness) :
    witness.secondScheduleMiddleComponent occurrence =
      witness.canonicalMiddleComponent
        (witness.secondScheduleMiddleEquiv occurrence) := by
  rw [witness.secondScheduleMiddleComponent_eq_swapped occurrence,
    witness.secondScheduleMiddleEquiv_eq_swapped occurrence]
  exact (witness.swapped.firstScheduleMiddleEquiv_component
      (witness.secondScheduleMiddleSwapEquiv occurrence)).trans
    (witness.canonicalMiddleComponent_swapped
      (witness.swapped.firstScheduleMiddleEquiv
        (witness.secondScheduleMiddleSwapEquiv occurrence)))

/-! ### Coassociativity-ready occurrence and forest comparison -/

/-- Explicit occurrence bijection between the two middle schedules through
their common canonical source-address family. -/
noncomputable def firstToSecondMiddleEquiv
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleMiddleOccurrence witness ≃
      SecondScheduleMiddleOccurrence witness :=
  witness.firstScheduleMiddleEquiv.trans witness.secondScheduleMiddleEquiv.symm

/-- Corresponding middle occurrences in the two schedules are the same
actual punctured decorated component. -/
theorem firstToSecondMiddleEquiv_component
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : FirstScheduleMiddleOccurrence witness) :
    witness.firstScheduleMiddleComponent occurrence =
      witness.secondScheduleMiddleComponent
        (witness.firstToSecondMiddleEquiv occurrence) := by
  calc
    witness.firstScheduleMiddleComponent occurrence =
        witness.canonicalMiddleComponent
          (witness.firstScheduleMiddleEquiv occurrence) :=
      witness.firstScheduleMiddleEquiv_component occurrence
    _ = witness.canonicalMiddleComponent
          (witness.secondScheduleMiddleEquiv
            (witness.firstToSecondMiddleEquiv occurrence)) := by
      rw [firstToSecondMiddleEquiv]
      simp
    _ = witness.secondScheduleMiddleComponent
          (witness.firstToSecondMiddleEquiv occurrence) :=
      (witness.secondScheduleMiddleEquiv_component _).symm

/-- Explicit occurrence bijection between the two lower schedules through
the canonical outer/relative occurrence family. -/
noncomputable def firstToSecondLowerEquiv
    (witness : CanonicalTwoStageWitness first second) :
    FirstScheduleLowerOccurrence witness ≃
      SecondScheduleLowerOccurrence witness :=
  witness.firstScheduleLowerOccurrenceEquiv.trans
    witness.secondScheduleLowerOccurrenceEquiv.symm

/-- Corresponding lower occurrences are the same actual detached decorated
component, even when equal displayed factors occur with multiplicity. -/
theorem firstToSecondLowerEquiv_component
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : FirstScheduleLowerOccurrence witness) :
    witness.firstScheduleLowerComponent occurrence =
      witness.secondScheduleLowerComponent
        (witness.firstToSecondLowerEquiv occurrence) := by
  calc
    witness.firstScheduleLowerComponent occurrence =
        witness.canonicalDecomposition.lowerComponent
          (witness.firstScheduleLowerOccurrenceEquiv occurrence) :=
      witness.firstScheduleLowerOccurrenceEquiv_component occurrence
    _ = witness.canonicalDecomposition.lowerComponent
          (witness.secondScheduleLowerOccurrenceEquiv
            (witness.firstToSecondLowerEquiv occurrence)) := by
      rw [firstToSecondLowerEquiv]
      simp
    _ = witness.secondScheduleLowerComponent
          (witness.firstToSecondLowerEquiv occurrence) :=
      (witness.secondScheduleLowerOccurrenceEquiv_component _).symm

/-- Canonical middle forest indexed once by exact source-address identity.
Mapping distinct addresses to equal components retains their multiplicity. -/
noncomputable def canonicalMiddleOccurrenceForest
    (witness : CanonicalTwoStageWitness first second) :
    CKForest sigma InstanceData := by
  classical
  exact (Finset.univ : Finset (CanonicalMiddleAddress witness)).1.map
    witness.canonicalMiddleComponent

/-- First-schedule middle forest, explicitly reindexed by the canonical
occurrence bijection before commutative projection. -/
noncomputable def firstScheduleMiddleForest
    (witness : CanonicalTwoStageWitness first second) :
    CKForest sigma InstanceData := by
  classical
  exact (Finset.univ : Finset (CanonicalMiddleAddress witness)).1.map
    (fun canonical => witness.firstScheduleMiddleComponent
      (witness.firstScheduleMiddleEquiv.symm canonical))

/-- Reverse-schedule middle forest under the same canonical indexing. -/
noncomputable def secondScheduleMiddleForest
    (witness : CanonicalTwoStageWitness first second) :
    CKForest sigma InstanceData := by
  classical
  exact (Finset.univ : Finset (CanonicalMiddleAddress witness)).1.map
    (fun canonical => witness.secondScheduleMiddleComponent
      (witness.secondScheduleMiddleEquiv.symm canonical))

theorem firstScheduleMiddleForest_eq_canonical
    (witness : CanonicalTwoStageWitness first second) :
    witness.firstScheduleMiddleForest = witness.canonicalMiddleOccurrenceForest := by
  classical
  apply congrArg (fun f : CanonicalMiddleAddress witness →
      CKComponent sigma InstanceData =>
    (Finset.univ : Finset (CanonicalMiddleAddress witness)).1.map f)
  funext canonical
  simpa using witness.firstScheduleMiddleEquiv_component
    (witness.firstScheduleMiddleEquiv.symm canonical)

theorem secondScheduleMiddleForest_eq_canonical
    (witness : CanonicalTwoStageWitness first second) :
    witness.secondScheduleMiddleForest = witness.canonicalMiddleOccurrenceForest := by
  classical
  apply congrArg (fun f : CanonicalMiddleAddress witness →
      CKComponent sigma InstanceData =>
    (Finset.univ : Finset (CanonicalMiddleAddress witness)).1.map f)
  funext canonical
  simpa using witness.secondScheduleMiddleEquiv_component
    (witness.secondScheduleMiddleEquiv.symm canonical)

/-- Canonical lower forest indexed by the exact outer/relative occurrences,
before forgetting those identities. -/
noncomputable def canonicalLowerOccurrenceForest
    (witness : CanonicalTwoStageWitness first second) :
    CKForest sigma InstanceData := by
  classical
  exact (Finset.univ : Finset (CanonicalLowerAddress witness)).1.map
    (fun canonical => witness.canonicalDecomposition.lowerComponent
      (witness.canonicalLowerOccurrenceEquiv.symm canonical))

/-- First lower forest with actual native components and canonical
occurrence reindexing. -/
noncomputable def firstScheduleLowerForest
    (witness : CanonicalTwoStageWitness first second) :
    CKForest sigma InstanceData := by
  classical
  exact (Finset.univ : Finset (CanonicalLowerAddress witness)).1.map
    (fun canonical => witness.firstScheduleLowerComponent
      (witness.firstScheduleLowerEquiv.symm canonical))

/-- Reverse lower forest with actual native components and canonical
occurrence reindexing. -/
noncomputable def secondScheduleLowerForest
    (witness : CanonicalTwoStageWitness first second) :
    CKForest sigma InstanceData := by
  classical
  exact (Finset.univ : Finset (CanonicalLowerAddress witness)).1.map
    (fun canonical => witness.secondScheduleLowerComponent
      (witness.secondScheduleLowerEquiv.symm canonical))

theorem firstScheduleLowerForest_eq_canonical
    (witness : CanonicalTwoStageWitness first second) :
    witness.firstScheduleLowerForest = witness.canonicalLowerOccurrenceForest := by
  classical
  apply congrArg (fun f : CanonicalLowerAddress witness →
      CKComponent sigma InstanceData =>
    (Finset.univ : Finset (CanonicalLowerAddress witness)).1.map f)
  funext canonical
  simpa [firstScheduleLowerOccurrenceEquiv] using
    witness.firstScheduleLowerOccurrenceEquiv_component
      (witness.firstScheduleLowerEquiv.symm canonical)

theorem secondScheduleLowerForest_eq_canonical
    (witness : CanonicalTwoStageWitness first second) :
    witness.secondScheduleLowerForest = witness.canonicalLowerOccurrenceForest := by
  classical
  apply congrArg (fun f : CanonicalLowerAddress witness →
      CKComponent sigma InstanceData =>
    (Finset.univ : Finset (CanonicalLowerAddress witness)).1.map f)
  funext canonical
  simpa [secondScheduleLowerOccurrenceEquiv] using
    witness.secondScheduleLowerOccurrenceEquiv_component
      (witness.secondScheduleLowerEquiv.symm canonical)

/-- Multiplicity-preserving equality of both commutative forest projections.
This is a corollary of occurrence equivalences and pointwise actual-component
equality, not a finite agreement oracle. -/
theorem scheduleForests_cohere
    (witness : CanonicalTwoStageWitness first second) :
    witness.firstScheduleLowerForest = witness.secondScheduleLowerForest ∧
      witness.firstScheduleMiddleForest = witness.secondScheduleMiddleForest := by
  exact ⟨witness.firstScheduleLowerForest_eq_canonical.trans
      witness.secondScheduleLowerForest_eq_canonical.symm,
    witness.firstScheduleMiddleForest_eq_canonical.trans
      witness.secondScheduleMiddleForest_eq_canonical.symm⟩

/-- The literal root remaining after first cutting `first`, then cutting the
transported part of `second` which remains in that root component. -/
def firstThenSecondRoot (witness : CanonicalTwoStageWitness first second) :
    CKTree sigma InstanceData G :=
  witness.secondRetainedAfterFirst.toCut.remainder

/-- The literal root remaining under the reverse permitted schedule. -/
def secondThenFirstRoot (witness : CanonicalTwoStageWitness first second) :
    CKTree sigma InstanceData G :=
  witness.firstRetainedAfterSecond.toCut.remainder

/-- Exact root-coherence proposition: both sequential retained remainders are
literally the canonical combined-frontier decorated tree.  The theorem below
inhabits it via constructor-recursive source pruning; address-status equality
alone would be insufficient because it forgets occurrence decorations. -/
def ExactTwoStageRemainderCoherence
    (witness : CanonicalTwoStageWitness first second) : Prop :=
  witness.firstThenSecondRoot = witness.finalRoot ∧
    witness.secondThenFirstRoot = witness.finalRoot

/-- The first staged ambient remainder is the direct occurrence-preserving
source pruning by both exact cut families. -/
theorem firstThenSecondRoot_eq_pruneCombined
    (witness : CanonicalTwoStageWitness first second) :
    witness.firstThenSecondRoot =
      tree.pruneAddresses (ValidAddressCut.combinedAddresses first second) := by
  calc
    witness.firstThenSecondRoot =
        first.toCut.remainder.pruneAddresses
          witness.secondRetainedAfterFirst.addresses :=
      ValidAddressCut.remainder_eq_pruneAddresses
        witness.secondRetainedAfterFirst
    _ = (tree.pruneAddresses first.addresses).pruneAddresses
          witness.secondRetainedAfterFirst.addresses := by
      exact congrArg
        (fun retained => retained.pruneAddresses
          witness.secondRetainedAfterFirst.addresses)
        (ValidAddressCut.remainder_eq_pruneAddresses first)
    _ = tree.pruneAddresses
          (ValidAddressCut.combinedAddresses first second) := by
      change (tree.pruneAddresses first.addresses).pruneAddresses
          (AddressSelection.retainedAfter first.addresses second.addresses) =
        tree.pruneAddresses (first.addresses ∪ second.addresses)
      exact CKTree.pruneAddresses_retainedAfter tree
        first.addresses second.addresses

/-- The reverse staged ambient remainder computes the same direct decorated
source pruning, with no equality of recursive cut certificates. -/
theorem secondThenFirstRoot_eq_pruneCombined
    (witness : CanonicalTwoStageWitness first second) :
    witness.secondThenFirstRoot =
      tree.pruneAddresses (ValidAddressCut.combinedAddresses first second) := by
  calc
    witness.secondThenFirstRoot =
        second.toCut.remainder.pruneAddresses
          witness.firstRetainedAfterSecond.addresses :=
      ValidAddressCut.remainder_eq_pruneAddresses
        witness.firstRetainedAfterSecond
    _ = (tree.pruneAddresses second.addresses).pruneAddresses
          witness.firstRetainedAfterSecond.addresses := by
      exact congrArg
        (fun retained => retained.pruneAddresses
          witness.firstRetainedAfterSecond.addresses)
        (ValidAddressCut.remainder_eq_pruneAddresses second)
    _ = tree.pruneAddresses
          (ValidAddressCut.combinedAddresses first second) := by
      change (tree.pruneAddresses second.addresses).pruneAddresses
          (AddressSelection.retainedAfter second.addresses first.addresses) =
        tree.pruneAddresses (first.addresses ∪ second.addresses)
      rw [Finset.union_comm]
      exact CKTree.pruneAddresses_retainedAfter tree
        second.addresses first.addresses

/-- The canonical source-frontier cut computes the same direct pruning by
the whole combined family; dominated selections are redundant. -/
theorem finalRoot_eq_pruneCombined
    (witness : CanonicalTwoStageWitness first second) :
    witness.finalRoot =
      tree.pruneAddresses (ValidAddressCut.combinedAddresses first second) := by
  calc
    witness.finalRoot = tree.pruneAddresses witness.finalCut.addresses :=
      ValidAddressCut.remainder_eq_pruneAddresses witness.finalCut
    _ = tree.pruneAddresses
        (AddressSelection.frontier
          (ValidAddressCut.combinedAddresses first second)) := by
      apply congrArg (tree.pruneAddresses)
      change ValidAddressCut.frontierAddresses first second =
        AddressSelection.frontier
          (ValidAddressCut.combinedAddresses first second)
      exact ValidAddressCut.frontierAddresses_eq_addressSelectionFrontier
        first second
    _ = tree.pruneAddresses
        (ValidAddressCut.combinedAddresses first second) :=
      CKTree.pruneAddresses_frontier tree _

/-- Exact two-stage ambient decorated-tree coherence.  Both schedules and
the canonical source frontier retain literally the same occurrences and
ordered children. -/
theorem exactTwoStageRemainderCoherence
    (witness : CanonicalTwoStageWitness first second) :
    ExactTwoStageRemainderCoherence witness := by
  constructor
  · exact witness.firstThenSecondRoot_eq_pruneCombined.trans
      witness.finalRoot_eq_pruneCombined.symm
  · exact witness.secondThenFirstRoot_eq_pruneCombined.trans
      witness.finalRoot_eq_pruneCombined.symm

/-- The non-linear three-region basis datum exposed to the next
coefficientwise milestone.  Tensor order is represented by named fields;
each forest is commutative only within its own coordinate. -/
structure ThreeRegionBasisData (sigma : Signature.{u, v})
    (InstanceData : Type w) where
  lower : CKForest sigma InstanceData
  middle : CKForest sigma InstanceData
  root : CKComponent sigma InstanceData

namespace ThreeRegionBasisData

@[ext]
theorem ext {left right : ThreeRegionBasisData sigma InstanceData}
    (lower : left.lower = right.lower)
    (middle : left.middle = right.middle)
    (root : left.root = right.root) : left = right := by
  cases left
  cases right
  simp_all

end ThreeRegionBasisData

/-- Canonical lower/middle/root triple of actual decorated components. -/
noncomputable def canonicalRegionData
    (witness : CanonicalTwoStageWitness first second) :
    ThreeRegionBasisData sigma InstanceData :=
  { lower := witness.canonicalLowerOccurrenceForest
    middle := witness.canonicalMiddleOccurrenceForest
    root :=
      { boundary := G
        tree := witness.finalRoot
        ordinary := witness.finalCut.toCut.remainder_isOrdinary } }

/-- Actual first-then-second schedule triple. -/
noncomputable def firstScheduleRegionData
    (witness : CanonicalTwoStageWitness first second) :
    ThreeRegionBasisData sigma InstanceData :=
  { lower := witness.firstScheduleLowerForest
    middle := witness.firstScheduleMiddleForest
    root :=
      { boundary := G
        tree := witness.firstThenSecondRoot
        ordinary := witness.secondRetainedAfterFirst.toCut.remainder_isOrdinary } }

/-- Actual reverse schedule triple. -/
noncomputable def secondScheduleRegionData
    (witness : CanonicalTwoStageWitness first second) :
    ThreeRegionBasisData sigma InstanceData :=
  { lower := witness.secondScheduleLowerForest
    middle := witness.secondScheduleMiddleForest
    root :=
      { boundary := G
        tree := witness.secondThenFirstRoot
        ordinary := witness.firstRetainedAfterSecond.toCut.remainder_isOrdinary } }

/-- The first schedule yields the canonical ordered triple of basis objects. -/
theorem firstScheduleRegionData_eq_canonical
    (witness : CanonicalTwoStageWitness first second) :
    witness.firstScheduleRegionData = witness.canonicalRegionData := by
  unfold firstScheduleRegionData canonicalRegionData
  apply ThreeRegionBasisData.ext
  · exact witness.firstScheduleLowerForest_eq_canonical
  · exact witness.firstScheduleMiddleForest_eq_canonical
  · apply CKComponent.ext
    · rfl
    · exact heqOfEq witness.exactTwoStageRemainderCoherence.1

/-- The reverse schedule yields the same canonical ordered triple. -/
theorem secondScheduleRegionData_eq_canonical
    (witness : CanonicalTwoStageWitness first second) :
    witness.secondScheduleRegionData = witness.canonicalRegionData := by
  unfold secondScheduleRegionData canonicalRegionData
  apply ThreeRegionBasisData.ext
  · exact witness.secondScheduleLowerForest_eq_canonical
  · exact witness.secondScheduleMiddleForest_eq_canonical
  · apply CKComponent.ext
    · rfl
    · exact heqOfEq witness.exactTwoStageRemainderCoherence.2

/-- Coassociativity-ready equality of the two actual ordered three-region
basis data, obtained from explicit occurrence bijections and exact root
equality before any sums, coefficients, or tensors are introduced. -/
theorem scheduleRegionData_cohere
    (witness : CanonicalTwoStageWitness first second) :
    witness.firstScheduleRegionData = witness.secondScheduleRegionData :=
  witness.firstScheduleRegionData_eq_canonical.trans
    witness.secondScheduleRegionData_eq_canonical.symm

/-- Paper-facing package of the exact two-stage witness-level result. -/
structure ExactTwoStageRegionCoherence
    (witness : CanonicalTwoStageWitness first second) : Prop where
  middleComponents : ∀ occurrence,
    witness.firstScheduleMiddleComponent occurrence =
      witness.secondScheduleMiddleComponent
        (witness.firstToSecondMiddleEquiv occurrence)
  lowerComponents : ∀ occurrence,
    witness.firstScheduleLowerComponent occurrence =
      witness.secondScheduleLowerComponent
        (witness.firstToSecondLowerEquiv occurrence)
  finalRoots : ExactTwoStageRemainderCoherence witness
  basisTriple : witness.firstScheduleRegionData =
    witness.secondScheduleRegionData
  reconstructs : witness.canonicalDecomposition.composedFilling = tree

/-- The exact two-stage region-coherence package is inhabited universally
for every disjoint noncrossing pair of public address cuts. -/
theorem exactTwoStageRegionCoherence
    (witness : CanonicalTwoStageWitness first second) :
    ExactTwoStageRegionCoherence witness :=
  { middleComponents := witness.firstToSecondMiddleEquiv_component
    lowerComponents := witness.firstToSecondLowerEquiv_component
    finalRoots := witness.exactTwoStageRemainderCoherence
    basisTriple := witness.scheduleRegionData_cohere
    reconstructs := witness.canonicalDecomposition.composedFilling_reconstructs }

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
noncrossing.  Ranks increase from an outer selected address to a strictly
deeper selected address.  This is the global hypothesis needed to rule out an
orientation cycle among three or more cuts. -/
structure RankedCutHierarchy {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) where
  levelCount : Nat
  levelCountPositive : 0 < levelCount
  cut : Fin levelCount → ValidAddressCut tree
  disjoint : ∀ {i j}, i ≠ j → Disjoint (cut i).addresses (cut j).addresses
  rank_respects_prefix : ∀ {i j} {p q},
    p ∈ (cut i).addresses → q ∈ (cut j).addresses →
    StrictlyInside q p → i.1 < j.1

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
  have ji := hierarchy.rank_respects_prefix qMember pMember pInside
  have ij := hierarchy.rank_respects_prefix p'Member q'Member qInside
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
    (BA : rankB < rankA) (CB : rankC < rankB) (AC : rankA < rankC) :
    False := by
  omega

end HierarchyGapFixture

end Potkin

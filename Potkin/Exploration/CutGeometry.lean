import Mathlib.Order.Antichain
import Potkin.Examples.InverseCut

/-!
# A faithful mathlib antichain view of native CK cuts

The ancestry orientation is root-to-leaf: `AddressPrefix p q` means that
`p` is an ancestor of `q`.  `Mathlib.IsAntichain` alone is insufficient:
the finite set must contain existing positive nonroot vertices, and the
source itself must be positive.  This adapter is only a subtype of address
finsets; it introduces no proof, tree, context, or recursive cut syntax.

All equivalences fix the exact decorated source.  Thus their canonical
compiled witness, ordered tuple, typed remainder and registry-admission
facts are unchanged.  There is no quotient by equal factor values here.
-/

namespace Potkin.Exploration
universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- A library antichain plus precisely the native endpoint/eligibility guards. -/
abbrev EligibleAntichains (tree : CKTree sigma InstanceData G) :=
  {addresses : Finset InternalAddress //
    tree.IsOrdinary ∧
    (∀ address ∈ addresses, tree.VertexAt address ∧ address ≠ []) ∧
    IsAntichain AddressPrefix (↑addresses : Set InternalAddress)}

theorem native_prefixFree_iff_mathlib (addresses : Finset InternalAddress) :
    (∀ p ∈ addresses, ∀ q ∈ addresses, p ≠ q → PrefixIncomparable p q) ↔
      IsAntichain AddressPrefix (↑addresses : Set InternalAddress) := by
  constructor
  · intro native p hp q hq different
    exact (native p hp q hq different).1
  · intro library p hp q hq different
    exact ⟨library hp hq different, library hq hp different.symm⟩

/-- Both directions use native address validation, not proof-plan equality by fiat. -/
def validCutAntichainEquiv : ValidAddressCut tree ≃ EligibleAntichains tree where
  toFun cut := ⟨cut.addresses, cut.sourceOrdinary,
    (fun address member => ⟨cut.address_vertex member, cut.address_nonroot member⟩),
    (native_prefixFree_iff_mathlib cut.addresses).mp
      (fun _ hp _ hq different => cut.prefixFree hp hq different)⟩
  invFun family := {
    addresses := family.val
    sourceOrdinary := family.property.1
    address_vertex := fun {address} member => (family.property.2.1 address member).1
    address_nonroot := fun {address} member => (family.property.2.1 address member).2
    prefixFree := fun {p q} hp hq different =>
      (native_prefixFree_iff_mathlib family.val).mpr family.property.2.2
        p hp q hq different }
  left_inv cut := ValidAddressCut.ext rfl
  right_inv family := Subtype.ext rfl

/-- The public extensional cut is faithfully identified with eligible antichains. -/
def cutAntichainEquiv : ExtensionalCKCut tree ≃ EligibleAntichains tree :=
  ExtensionalCKCut.validAddressEquiv.trans validCutAntichainEquiv

@[simp] theorem cutAntichainEquiv_addresses (cut : ExtensionalCKCut tree) :
    (cutAntichainEquiv cut).val = cut.addresses := rfl

/-- Round-trip equality retains the whole native witness, not merely its forest. -/
theorem antichain_roundtrip_compiled (cut : ExtensionalCKCut tree) :
    (cutAntichainEquiv.symm (cutAntichainEquiv cut)).compiled = cut.compiled :=
  congrArg ExtensionalCKCut.compiled (cutAntichainEquiv.left_inv cut)

/-- Library subset closure gives a native cut for any subset of its selected sites.
The subset may be empty; root/typed-interface eligibility is inherited. -/
def restrictNativeCut (cut : ExtensionalCKCut tree)
    (addresses : Finset InternalAddress) (subset : addresses ⊆ cut.addresses) :
    ExtensionalCKCut tree :=
  cutAntichainEquiv.symm ⟨addresses,
    cut.sourceOrdinary,
    (fun address member =>
      ⟨cut.validAddressCut.address_vertex (subset member),
        cut.validAddressCut.address_nonroot (subset member)⟩),
    (cutAntichainEquiv cut).property.2.2.subset (fun _ member => subset member)⟩

@[simp] theorem restrictNativeCut_addresses (cut : ExtensionalCKCut tree)
    (addresses : Finset InternalAddress) (subset : addresses ⊆ cut.addresses) :
    (restrictNativeCut cut addresses subset).addresses = addresses := rfl

/-- No address has two distinct selected ancestors: the geometric reason an
installed subtree can belong to at most one selected detached region. -/
theorem selected_ancestor_unique (cut : ExtensionalCKCut tree)
    {p q address : InternalAddress} (hp : p ∈ cut.addresses) (hq : q ∈ cut.addresses)
    (pAbove : AddressPrefix p address) (qAbove : AddressPrefix q address) : p = q := by
  have antichain := (cutAntichainEquiv cut).property.2.2
  rcases List.prefix_or_prefix_of_prefix pAbove qAbove with comparable | comparable
  · exact antichain.eq hp hq comparable
  · exact antichain.eq' hp hq comparable

/-- Distinct selected CK factors occupy disjoint descendant cones in this source. -/
theorem selected_descendant_cones_disjoint (cut : ExtensionalCKCut tree)
    {p q : InternalAddress} (hp : p ∈ cut.addresses) (hq : q ∈ cut.addresses)
    (different : p ≠ q) :
    Disjoint {address | AddressPrefix p address} {address | AddressPrefix q address} := by
  exact Set.disjoint_left.mpr (fun _ pAbove qAbove =>
    different (selected_ancestor_unique cut hp hq pAbove qAbove))

/-- Antichainhood does not permit the witness-free whole-root endpoint as a cut. -/
theorem root_singleton_antichain_but_not_cut :
    IsAntichain AddressPrefix ({[]} : Set InternalAddress) ∧
      ¬ ∃ cut : ExtensionalCKCut tree, cut.addresses = {[]} := by
  refine ⟨IsAntichain.singleton, ?_⟩
  rintro ⟨cut, addresses⟩
  have rootMember : [] ∈ cut.addresses := by simp [addresses]
  exact cut.validAddressCut.address_nonroot rootMember rfl

/-- Even an empty antichain does not create an ordinary cut of a bare interface. -/
theorem interface_has_no_ordinary_cut (H : Hypersequent sigma) :
    ¬ Nonempty (ExtensionalCKCut (CKTree.interface H : CKTree sigma InstanceData H)) := by
  rintro ⟨cut⟩
  exact cut.sourceOrdinary

/-! Tactic lab: compare real inverse/membership bookkeeping with the explicit
proofs above. Suggestions are inspected but central proofs remain explicit. -/
example (cut : ExtensionalCKCut tree) :
    (cutAntichainEquiv.symm (cutAntichainEquiv cut)).addresses = cut.addresses := by
  simp?

example (cut : ExtensionalCKCut tree) {p : InternalAddress} (member : p ∈ cut.addresses) :
    p ≠ [] := by
  exact?

/-! Meaning audit: this is an inhabited, exact-registry admitted source, and
the two equal providers remain two physical selected addresses. No enumeration
or finite-family agreement is used to prove the universal bridge. -/
open Examples.InverseCut in
example :
    LocallyAdmittedTree Examples.RecursiveCut.duplicatePresentation
      (twoHoles.fillAssignment both) ∧
    (cutAntichainEquiv (ExtensionalCKCut.ofCKCut bothCut)).val =
      ({[0], [1]} : Finset InternalAddress) := by
  refine ⟨?_, ?_⟩
  · exact twoHoles.fillAssignment_locallyAdmitted both two_holes_admitted
      both_providers_admitted
  · rfl

/-! Probe D triage. The existing substitution API is intrinsically indexed:
`R.LeafAssignment := (h : R.LeafOccurrence) → CKTree _ _ (R.leafBoundary h)`.
Filling preserves exact output boundary and ordered occurrence decoration.
Ordinary `Monad Type` accepts an unindexed replacement `α → m β`, which cannot
express this per-hole boundary constraint or fixed registry admission. A lawful
indexed interface is plausible; no monad law is assumed or constructed here.
-/
#check CKTree.LeafAssignment
#check CKTree.fillAssignment
#check CKTree.fillAssignment_locallyAdmitted
#check CKTree.leafAssignmentCutEquiv
#check CKTree.PunctureAt.insertIncomparable_replacementPunctures_prefixed

#check IsAntichain.subset
#check IsAntichain.eq
#check List.prefix_or_prefix_of_prefix
#print IsAntichain
#synth DecidableEq InternalAddress
#print axioms validCutAntichainEquiv
#print axioms cutAntichainEquiv
#print axioms selected_ancestor_unique
#print axioms selected_descendant_cones_disjoint
#print axioms restrictNativeCut

end Potkin.Exploration

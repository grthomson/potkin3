import Mathlib.Data.Finset.Attach
import Potkin.Checked

namespace Potkin

universe u v w

/-- Zero-based internal child-slot addresses; `[]` is the root. -/
abbrev InternalAddress := List Nat

/-- Positive one-based addresses used by the Racket and user-facing APIs. -/
structure RacketAddress where
  slots : List Nat
  positive : ∀ n ∈ slots, 0 < n

namespace InternalAddress

/-- Convert every zero-based selector to its positive one-based successor. -/
def toRacket (address : InternalAddress) : RacketAddress where
  slots := address.map Nat.succ
  positive := by
    intro n hn
    rcases List.mem_map.mp hn with ⟨k, _, rfl⟩
    exact Nat.succ_pos k

end InternalAddress

namespace RacketAddress

/-- Positive-address equality is determined by the selector list. -/
@[ext]
theorem ext {a b : RacketAddress} (h : a.slots = b.slots) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Convert every valid positive selector back to its zero-based predecessor. -/
def toInternal (address : RacketAddress) : InternalAddress :=
  address.slots.map Nat.pred

@[simp]
theorem toInternal_toRacket (address : InternalAddress) :
    address.toRacket.toInternal = address := by
  simp [toInternal, InternalAddress.toRacket, Function.comp_def]

@[simp]
theorem toRacket_toInternal (address : RacketAddress) :
    address.toInternal.toRacket = address := by
  cases address with
  | mk slots positive =>
      have hslots : (slots.map Nat.pred).map Nat.succ = slots := by
        simp only [List.map_map]
        induction slots with
        | nil => rfl
        | cons n ns ih =>
            have hn : 0 < n := positive n (by simp)
            have hns : ∀ k ∈ ns, 0 < k := by
              intro k hk
              exact positive k (by simp [hk])
            have hhead : Nat.succ (Nat.pred n) = n :=
              Nat.succ_pred (Nat.ne_of_gt hn)
            simp only [List.map_cons, Function.comp_apply]
            rw [hhead, ih hns]
      exact RacketAddress.ext hslots

end RacketAddress

namespace CKTree

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-- A vertex witness.  Interfaces deliberately have no constructor here. -/
inductive VertexAt : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> InternalAddress -> Prop where
  | root (o : LocalOccurrence sigma InstanceData) (children : CKChildren sigma InstanceData o.shape.premises) :
      VertexAt (.ordinary o children) []
  | child (o : LocalOccurrence sigma InstanceData)
      (children : CKChildren sigma InstanceData o.shape.premises)
      (i : Fin o.shape.premises.length) {address : InternalAddress}
      (below : VertexAt (children.get i) address) :
      VertexAt (.ordinary o children) (i.1 :: address)

theorem vertexAt_root_of_isOrdinary {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (h : tree.IsOrdinary) :
    tree.VertexAt [] := by
  cases tree with
  | interface => exact False.elim h
  | ordinary o children => exact .root o children

end CKTree

/-- Prefix order on addresses. -/
def AddressPrefix (a b : InternalAddress) : Prop := a <+: b

/-- Neither address is a prefix of the other. -/
def PrefixIncomparable (a b : InternalAddress) : Prop :=
  ¬ AddressPrefix a b ∧ ¬ AddressPrefix b a

/-- One positive root together with its ordered typed children. -/
structure RootConstruction
    (sigma : Signature.{u, v}) (InstanceData : Type w) where
  occurrence : LocalOccurrence sigma InstanceData
  children : CKChildren sigma InstanceData occurrence.shape.premises

namespace RootConstruction

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-- Retrieve one ordered source child. -/
def child (C : RootConstruction sigma InstanceData)
    (i : Fin C.occurrence.shape.premises.length) :
    CKTree sigma InstanceData (C.occurrence.shape.premises.get i) :=
  C.children.get i

/-- Adjoin the retained occurrence root. -/
def tree (C : RootConstruction sigma InstanceData) :
    CKTree sigma InstanceData C.occurrence.shape.conclusion :=
  .ordinary C.occurrence C.children

end RootConstruction

/-- A nonempty proper cut selecting ordinary immediate child roots. -/
structure RootCut {sigma : Signature.{u, v}} {InstanceData : Type w}
    (C : RootConstruction sigma InstanceData) where
  sites : Finset (Fin C.occurrence.shape.premises.length)
  nonempty : sites.Nonempty
  selectedOrdinary : (i : Fin C.occurrence.shape.premises.length) ->
    i ∈ sites -> (C.child i).IsOrdinary

namespace RootCut

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {C : RootConstruction sigma InstanceData}

/-- One selected occurrence, retaining its exact premise slot. -/
abbrev Site (cut : RootCut C) :=
  {i : Fin C.occurrence.shape.premises.length // i ∈ cut.sites}

/-- Exact zero-based address of a selected immediate child. -/
def address (cut : RootCut C) (site : cut.Site) : InternalAddress :=
  [site.1.1]

/-- The dependent address-aligned detached tuple, before commutativization. -/
def detached (cut : RootCut C) (site : cut.Site) :
    CKTree sigma InstanceData
      (C.occurrence.shape.premises.get site.1) :=
  C.child site.1

/-- The exact boundary required by the puncture at a selected site. -/
def requirement (cut : RootCut C) (site : cut.Site) : Hypersequent sigma :=
  C.occurrence.shape.premises.get site.1

/-- Replace selected children by typed interfaces and retain all others. -/
def retainedChild (cut : RootCut C)
    (i : Fin C.occurrence.shape.premises.length) :
    CKTree sigma InstanceData (C.occurrence.shape.premises.get i) :=
  if _h : i ∈ cut.sites then
    .interface (C.occurrence.shape.premises.get i)
  else
    C.child i

/-- The punctured retained component has the original positive root. -/
def retained (cut : RootCut C) :
    CKTree sigma InstanceData C.occurrence.shape.conclusion :=
  CKTree.ordinaryFn C.occurrence (cut.retainedChild)

/-- Commutative forest image of the detached tuple, retaining multiplicity. -/
def detachedForest (cut : RootCut C) : CKForest sigma InstanceData :=
  cut.sites.attach.1.map (fun site =>
    { boundary := C.occurrence.shape.premises.get site.1
      tree := C.child site.1
      ordinary := cut.selectedOrdinary site.1 site.2 })

/-- Fill only the selected typed punctures from an address-indexed tuple. -/
def fill (cut : RootCut C)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (C.occurrence.shape.premises.get site.1)) :
    CKTree sigma InstanceData C.occurrence.shape.conclusion :=
  CKTree.ordinaryFn C.occurrence (fun i =>
    if h : i ∈ cut.sites then fillers ⟨i, h⟩ else cut.retainedChild i)

@[simp]
theorem retainedChild_at_site (cut : RootCut C) (site : cut.Site) :
    cut.retainedChild site.1 = .interface (cut.requirement site) := by
  simp [retainedChild, requirement, site.2]

/-- Each puncture requirement is exactly the corresponding detached root type. -/
theorem puncture_requires_detached_root (cut : RootCut C) (site : cut.Site) :
    cut.detached site = C.child site.1 := rfl

/-- The retained vacancy and aligned detached factor share exactly one boundary. -/
theorem puncture_matches_detached (cut : RootCut C) (site : cut.Site) :
    cut.retainedChild site.1 = .interface (cut.requirement site) ∧
      cut.detached site = C.child site.1 :=
  ⟨cut.retainedChild_at_site site, cut.puncture_requires_detached_root site⟩

/-- Every selected address denotes an existing ordinary vertex of the source. -/
theorem address_exists (cut : RootCut C) (site : cut.Site) :
    (C.tree).VertexAt (cut.address site) := by
  unfold RootConstruction.tree address
  apply CKTree.VertexAt.child C.occurrence C.children site.1
  exact CKTree.vertexAt_root_of_isOrdinary (cut.selectedOrdinary site.1 site.2)

/-- A proper cut never contains the root address. -/
theorem address_nonroot (cut : RootCut C) (site : cut.Site) :
    cut.address site ≠ [] := by simp [address]

/-- The selected address family is nonempty. -/
theorem addresses_nonempty (cut : RootCut C) : Nonempty cut.Site := by
  rcases cut.nonempty with ⟨i, hi⟩
  exact ⟨⟨i, hi⟩⟩

/-- Distinct selected immediate slots have prefix-incomparable addresses. -/
theorem addresses_prefixFree (cut : RootCut C) {p q : cut.Site}
    (hne : p ≠ q) : PrefixIncomparable (cut.address p) (cut.address q) := by
  have hval : p.1.1 ≠ q.1.1 := by
    intro h
    apply hne
    apply Subtype.ext
    exact Fin.ext h
  simp [PrefixIncomparable, AddressPrefix, address, hval, Ne.symm hval]

/-- Filling from the retained aligned tuple reconstructs the exact source tree. -/
theorem fill_detached_reconstructs (cut : RootCut C) :
    cut.fill cut.detached = C.tree := by
  unfold fill RootConstruction.tree CKTree.ordinaryFn
  congr 1
  apply CKChildren.ext
  intro i
  simp only [CKChildren.get_ofFn]
  by_cases h : i ∈ cut.sites
  · simp [detached, RootConstruction.child, h]
  · simp [retainedChild, RootConstruction.child, h]

end RootCut

end Potkin

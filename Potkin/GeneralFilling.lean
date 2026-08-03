import Potkin.CKCutPuncture
import Potkin.RealizedCut

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-! ## Complete open trees -/

mutual

/-- An open CK tree is complete exactly when it contains no typed interface. -/
def CKTree.IsComplete : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> Prop
  | _, .interface _ => False
  | _, .ordinary _ children => children.IsComplete

/-- Completeness of an ordered child tuple is componentwise. -/
def CKChildren.IsComplete : {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries -> Prop
  | _, .nil => True
  | _, .cons head tail => head.IsComplete /\ tail.IsComplete

end

/-! ## Boundary-indexed puncture witnesses -/

mutual

/--
A typed puncture witness retains both its source address and the exact whole
hypersequent required at that vacancy.  The boundary parameter is essential:
the older `InterfaceAt` relation records only that a vacancy exists.
-/
inductive CKTree.PunctureAt (H : Hypersequent sigma) :
    {G : Hypersequent sigma} ->
      CKTree sigma InstanceData G -> InternalAddress ->
        Type (max (max u v) w) where
  | root : CKTree.PunctureAt H (.interface H) []
  | child (o : LocalOccurrence sigma InstanceData)
      (children : CKChildren sigma InstanceData o.shape.premises)
      (slot : Nat) (address : InternalAddress)
      (below : CKChildren.PunctureAt H children slot address) :
      CKTree.PunctureAt H (.ordinary o children) (slot :: address)

/-- A puncture witness located in one exact position of an ordered tuple. -/
inductive CKChildren.PunctureAt (H : Hypersequent sigma) :
    {boundaries : List (Hypersequent sigma)} ->
      CKChildren sigma InstanceData boundaries -> Nat ->
        InternalAddress -> Type (max (max u v) w) where
  | head {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
      (head : CKTree sigma InstanceData G)
      (tail : CKChildren sigma InstanceData Gs)
      (address : InternalAddress)
      (below : CKTree.PunctureAt H head address) :
      CKChildren.PunctureAt H (.cons head tail) 0 address
  | tail {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
      (head : CKTree sigma InstanceData G)
      (tail : CKChildren sigma InstanceData Gs)
      (slot : Nat) (address : InternalAddress)
      (below : CKChildren.PunctureAt H tail slot address) :
      CKChildren.PunctureAt H (.cons head tail) (slot + 1) address

end

/-- Propositional existence of a boundary-indexed puncture path. -/
abbrev CKTree.HasPunctureAt (H : Hypersequent sigma)
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (address : InternalAddress) : Prop :=
  Nonempty (CKTree.PunctureAt H tree address)

/-- Propositional existence of a tuple puncture path. -/
abbrev CKChildren.HasPunctureAt (H : Hypersequent sigma)
    {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries)
    (slot : Nat) (address : InternalAddress) : Prop :=
  Nonempty (CKChildren.PunctureAt H children slot address)

mutual

/-- Forgetting a puncture's required boundary gives the legacy vacancy fact. -/
theorem CKTree.PunctureAt.toInterfaceAt :
    {G H : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {address : InternalAddress} ->
    CKTree.PunctureAt H tree address -> tree.InterfaceAt address
  | _, _, _, _, .root => .root _
  | _, _, _, _, .child o children _ _ below => by
      rcases below.toInterfaceAt with ⟨i, slotEq, childInterface⟩
      simpa [slotEq] using CKTree.InterfaceAt.child o children i childInterface

/-- A tuple puncture determines its in-range dependent premise slot. -/
theorem CKChildren.PunctureAt.toInterfaceAt :
    {boundaries : List (Hypersequent sigma)} ->
    {H : Hypersequent sigma} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    {slot : Nat} -> {address : InternalAddress} ->
    CKChildren.PunctureAt H children slot address ->
      ∃ i : Fin boundaries.length,
        i.1 = slot ∧ (children.get i).InterfaceAt address
  | _, _, _, _, _, .head _ _ _ below =>
      ⟨⟨0, by simp⟩, rfl, below.toInterfaceAt⟩
  | _, _, _, _, _, .tail _ _ _ _ below => by
      rcases below.toInterfaceAt with ⟨i, slotEq, childInterface⟩
      exact ⟨i.succ, by simp [slotEq], childInterface⟩

end


namespace CKChildren.PunctureAt

/-- Lift a typed puncture of a dependent child into the containing tuple. -/
def ofGet :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    (i : Fin boundaries.length) ->
    {H : Hypersequent sigma} -> {address : InternalAddress} ->
    CKTree.PunctureAt H (children.get i) address ->
      CKChildren.PunctureAt H children i.1 address
  | _ :: _, .cons childHead childTail, ⟨0, _⟩, _, address, below =>
      .head childHead childTail address below
  | _ :: _, .cons childHead childTail, ⟨slot + 1, bound⟩, _, address, below =>
      .tail childHead childTail slot address
        (ofGet childTail ⟨slot, Nat.lt_of_succ_lt_succ bound⟩ below)

end CKChildren.PunctureAt

namespace CKChildren

/-- A proof-relevant tuple puncture together with its full nonroot address. -/
structure AddressPuncture (H : Hypersequent sigma)
    {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries)
    (address : InternalAddress) where
  slot : Nat
  rest : InternalAddress
  address_eq : address = slot :: rest
  witness : CKChildren.PunctureAt H children slot rest

end CKChildren

mutual

/-- Constructor view of a typed tree puncture, stated generically so that
dependent occurrence indices never have to be compared during inversion. -/
def CKTree.PunctureAt.childPart :
    {G H : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {address : InternalAddress} ->
    (puncture : CKTree.PunctureAt H tree address) ->
      match tree, address with
      | .ordinary _ children, slot :: rest =>
          CKChildren.PunctureAt H children slot rest
      | _, _ => PUnit
  | _, _, _, _, .root => PUnit.unit
  | _, _, _, _, .child _ _ _ _ below => below

/-- Constructor view of a typed tuple puncture. -/
def CKChildren.PunctureAt.tuplePart :
    {boundaries : List (Hypersequent sigma)} ->
    {H : Hypersequent sigma} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    {slot : Nat} -> {address : InternalAddress} ->
    (puncture : CKChildren.PunctureAt H children slot address) ->
      match children, slot with
      | .cons childHead _, 0 => CKTree.PunctureAt H childHead address
      | .cons _ tail, Nat.succ tailSlot =>
          CKChildren.PunctureAt H tail tailSlot address
      | _, _ => PUnit
  | _, _, _, _, _, .head _ _ _ below => below
  | _, _, _, _, _, .tail _ _ _ _ below => below

end

namespace InternalAddress

/-- First-selector shifting commutes with suffix prefixing on nonroot paths. -/
theorem shiftHead_append_of_ne_nil (p q : InternalAddress) (hne : p ≠ []) :
    shiftHead (p ++ q) = shiftHead p ++ q := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons slot rest => rfl

end InternalAddress

/-- Prefix incomparability is symmetric. -/
theorem prefixIncomparable_symm {p q : InternalAddress}
    (h : PrefixIncomparable p q) : PrefixIncomparable q p :=
  ⟨h.2, h.1⟩

namespace CKTree.InterfaceAt

/-- Every untyped vacancy has one exact boundary-indexed puncture witness. -/
theorem exists_typed :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {address : InternalAddress} ->
    tree.InterfaceAt address ->
      ∃ H : Hypersequent sigma, tree.HasPunctureAt H address
  | _, _, _, .root H => ⟨H, ⟨.root⟩⟩
  | _, _, _, .child o children i below => by
      rcases below.exists_typed with ⟨H, ⟨typed⟩⟩
      exact ⟨H, ⟨.child o children i.1 _
        (CKChildren.PunctureAt.ofGet children i typed)⟩⟩

end CKTree.InterfaceAt

mutual

/-- Replace one exact typed puncture without changing any retained occurrence. -/
def CKTree.PunctureAt.insert :
    {G H : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {address : InternalAddress} ->
    CKTree.PunctureAt H tree address ->
      CKTree sigma InstanceData H -> CKTree sigma InstanceData G
  | _, _, _, _, .root, replacement => replacement
  | _, _, _, _, .child o _ _ _ below, replacement =>
      .ordinary o (below.insert replacement)

/-- Replace a typed puncture inside an ordered child tuple. -/
def CKChildren.PunctureAt.insert :
    {boundaries : List (Hypersequent sigma)} ->
    {H : Hypersequent sigma} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    {slot : Nat} -> {address : InternalAddress} ->
    CKChildren.PunctureAt H children slot address ->
      CKTree sigma InstanceData H ->
        CKChildren sigma InstanceData boundaries
  | _, _, _, _, _, .head _ tail _ below, replacement =>
      .cons (below.insert replacement) tail
  | _, _, _, _, _, .tail head _ _ _ below, replacement =>
      .cons head (below.insert replacement)

end

mutual

/-- Typed insertion preserves local admission of both the retained context
and the replacement. -/
def CKTree.PunctureAt.insertLocallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G H : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {address : InternalAddress} ->
    (puncture : CKTree.PunctureAt H tree address) ->
    {replacement : CKTree sigma InstanceData H} ->
    LocallyAdmittedTree P tree ->
    LocallyAdmittedTree P replacement ->
      LocallyAdmittedTree P (puncture.insert replacement)
  | _, _, _, _, .root, _, _, replacementAdmitted => replacementAdmitted
  | _, _, _, _, .child _ _ _ _ below, _, contextAdmitted,
      replacementAdmitted =>
        ⟨contextAdmitted.1,
          below.insertLocallyAdmitted contextAdmitted.2 replacementAdmitted⟩

/-- Ordered-tuple form of local-admission preservation under insertion. -/
def CKChildren.PunctureAt.insertLocallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {boundaries : List (Hypersequent sigma)} ->
    {H : Hypersequent sigma} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    {slot : Nat} -> {address : InternalAddress} ->
    (puncture : CKChildren.PunctureAt H children slot address) ->
    {replacement : CKTree sigma InstanceData H} ->
    LocallyAdmittedChildren P children ->
    LocallyAdmittedTree P replacement ->
      LocallyAdmittedChildren P (puncture.insert replacement)
  | _, _, _, _, _, .head _ _ _ below, _, contextAdmitted,
      replacementAdmitted =>
        ⟨below.insertLocallyAdmitted contextAdmitted.1 replacementAdmitted,
          contextAdmitted.2⟩
  | _, _, _, _, _, .tail _ _ _ _ below, _, contextAdmitted,
      replacementAdmitted =>
        ⟨contextAdmitted.1,
          below.insertLocallyAdmitted contextAdmitted.2 replacementAdmitted⟩

end

mutual

/-- Inserting the same typed vacancy is the identity context action. -/
@[simp]
theorem CKTree.PunctureAt.insert_interface :
    {G H : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {address : InternalAddress} ->
    (puncture : CKTree.PunctureAt H tree address) ->
      puncture.insert (.interface H) = tree
  | _, _, _, _, .root => rfl
  | _, H, _, _, .child o children _ _ below => by
      change CKTree.ordinary o (below.insert (.interface H)) =
        CKTree.ordinary o children
      exact congrArg (CKTree.ordinary o) below.insert_interface

@[simp]
theorem CKChildren.PunctureAt.insert_interface :
    {boundaries : List (Hypersequent sigma)} ->
    {H : Hypersequent sigma} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    {slot : Nat} -> {address : InternalAddress} ->
    (puncture : CKChildren.PunctureAt H children slot address) ->
      puncture.insert (.interface H) = children
  | _, H, _, _, _, .head childHead tail _ below => by
      change CKChildren.cons (below.insert (.interface H)) tail =
        CKChildren.cons childHead tail
      exact congrArg (fun replacementHead =>
        CKChildren.cons replacementHead tail) below.insert_interface
  | _, H, _, _, _, .tail childHead tail _ _ below => by
      change CKChildren.cons childHead (below.insert (.interface H)) =
        CKChildren.cons childHead tail
      exact congrArg (CKChildren.cons childHead) below.insert_interface

end

mutual

/-- Every puncture internal to a replacement acquires the outer prefix. -/
def CKTree.PunctureAt.insert_replacement :
    {G H K : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {outerAddress innerAddress : InternalAddress} ->
    (outer : CKTree.PunctureAt H tree outerAddress) ->
    {replacement : CKTree sigma InstanceData H} ->
    CKTree.PunctureAt K replacement innerAddress ->
      CKTree.PunctureAt K (outer.insert replacement)
        (outerAddress ++ innerAddress)
  | _, _, _, _, _, _, .root, replacement, inner => by
      simpa using inner
  | _, _, _, _, _, _, .child o children slot address below,
      replacement, inner => by
      simpa only [insert, List.cons_append] using
        CKTree.PunctureAt.child o (below.insert replacement)
          slot (address ++ _) (below.insert_replacement inner)

/-- Tuple form of prefixing punctures internal to an inserted replacement. -/
def CKChildren.PunctureAt.insert_replacement :
    {boundaries : List (Hypersequent sigma)} ->
    {H K : Hypersequent sigma} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    {slot : Nat} -> {outerAddress innerAddress : InternalAddress} ->
    (outer : CKChildren.PunctureAt H children slot outerAddress) ->
    {replacement : CKTree sigma InstanceData H} ->
    CKTree.PunctureAt K replacement innerAddress ->
      CKChildren.PunctureAt K (outer.insert replacement) slot
        (outerAddress ++ innerAddress)
  | _, _, _, _, _, _, _, .head head tail address below,
      replacement, inner => by
      exact .head (below.insert replacement) tail (address ++ _)
        (below.insert_replacement inner)
  | _, _, _, _, _, _, _, .tail head tail slot address below,
      replacement, inner => by
      exact .tail head (below.insert replacement) slot (address ++ _)
        (below.insert_replacement inner)

end

mutual

/-- Transport a second, prefix-incomparable puncture through one insertion.
Its literal old source address is unchanged. -/
def CKTree.PunctureAt.transportIncomparable :
    {G H K : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {selectedAddress otherAddress : InternalAddress} ->
    (selected : CKTree.PunctureAt H tree selectedAddress) ->
    (other : CKTree.PunctureAt K tree otherAddress) ->
    PrefixIncomparable selectedAddress otherAddress ->
    (replacement : CKTree sigma InstanceData H) ->
      CKTree.PunctureAt K (selected.insert replacement) otherAddress
  | _, _, _, _, _, otherAddress, .root, _, incomparable, _ =>
      False.elim (incomparable.1 (by simp [AddressPrefix]))
  | _, _, _, _, _, otherFullAddress,
      .child o children selectedSlot selectedAddress selected,
      other, incomparable, replacement => by
        cases otherFullAddress with
        | nil =>
            exact False.elim (incomparable.2 (by simp [AddressPrefix]))
        | cons otherSlot otherAddress =>
            exact .child o (selected.insert replacement)
              otherSlot otherAddress
              (selected.transportIncomparable other.childPart
                incomparable replacement)

/-- Ordered-tuple transport of a prefix-incomparable puncture. -/
def CKChildren.PunctureAt.transportIncomparable :
    {boundaries : List (Hypersequent sigma)} ->
    {H K : Hypersequent sigma} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    {selectedSlot otherSlot : Nat} ->
    {selectedAddress otherAddress : InternalAddress} ->
    (selected : CKChildren.PunctureAt H children
      selectedSlot selectedAddress) ->
    (other : CKChildren.PunctureAt K children otherSlot otherAddress) ->
    PrefixIncomparable
      (selectedSlot :: selectedAddress) (otherSlot :: otherAddress) ->
    (replacement : CKTree sigma InstanceData H) ->
      CKChildren.PunctureAt K (selected.insert replacement)
        otherSlot otherAddress
  | _, _, _, _, _, otherSlot, _, otherAddress,
      .head childHead tail selectedAddress selected,
      other, incomparable, replacement => by
        cases otherSlot with
        | zero =>
            exact .head (selected.insert replacement) tail otherAddress
              (selected.transportIncomparable other.tuplePart
                (by simpa [PrefixIncomparable, AddressPrefix] using incomparable)
                replacement)
        | succ tailSlot =>
            exact .tail (selected.insert replacement) tail tailSlot
              otherAddress other.tuplePart
  | _, _, _, _, _, otherSlot, _, otherAddress,
      .tail childHead tail selectedSlot selectedAddress selected,
      other, incomparable, replacement => by
        cases otherSlot with
        | zero =>
            exact .head childHead (selected.insert replacement) otherAddress
              other.tuplePart
        | succ tailSlot =>
            exact .tail childHead (selected.insert replacement) tailSlot
              otherAddress
              (selected.transportIncomparable other.tuplePart
                (by simpa [PrefixIncomparable, AddressPrefix] using incomparable)
                replacement)

end

/-- Constructor-view equation for a staged pair of incomparable insertions.
It lets later proofs expose the common ordinary parent without eliminating a
second witness through dependent occurrence indices. -/
theorem CKTree.PunctureAt.transport_insert_eq_childPart :
    {G H K : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {selectedAddress otherAddress : InternalAddress} ->
    (selected : CKTree.PunctureAt H tree selectedAddress) ->
    (other : CKTree.PunctureAt K tree otherAddress) ->
    (incomparable : PrefixIncomparable selectedAddress otherAddress) ->
    (selectedReplacement : CKTree sigma InstanceData H) ->
    (otherReplacement : CKTree sigma InstanceData K) ->
      match tree, selectedAddress, otherAddress with
      | CKTree.ordinary o children, selectedSlot :: selectedRest,
          otherSlot :: otherRest =>
          (selected.transportIncomparable other incomparable
              selectedReplacement).insert otherReplacement =
            CKTree.ordinary o
              ((selected.childPart.transportIncomparable other.childPart
                  incomparable selectedReplacement).insert otherReplacement)
      | _, _, _ => True
  | _, _, _, _, _, _, .root, _, _, _, _ => trivial
  | _, _, _, _, _, otherAddress,
      .child _ _ _ _ _, _, incomparable, _, _ => by
        cases otherAddress with
        | nil =>
            exact False.elim (incomparable.2 (by simp [AddressPrefix]))
        | cons _ _ => rfl


mutual

/-- Strict interchange of insertions at prefix-incomparable punctures.  This
is literal structural equality: all old occurrences and premise positions are
fixed, while replacement-internal addresses are prefixed by the two witnesses. -/
theorem CKTree.PunctureAt.insertIncomparable_commutes :
    {G H K : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {selectedAddress otherAddress : InternalAddress} ->
    (selected : CKTree.PunctureAt H tree selectedAddress) ->
    (other : CKTree.PunctureAt K tree otherAddress) ->
    (incomparable : PrefixIncomparable selectedAddress otherAddress) ->
    (selectedReplacement : CKTree sigma InstanceData H) ->
    (otherReplacement : CKTree sigma InstanceData K) ->
      (selected.transportIncomparable other incomparable
          selectedReplacement).insert otherReplacement =
        (other.transportIncomparable selected
          (prefixIncomparable_symm incomparable)
          otherReplacement).insert selectedReplacement
  | _, _, _, _, _, _, .root, _, incomparable, _, _ =>
      False.elim (incomparable.1 (by simp [AddressPrefix]))
  | _, _, _, _, _, otherAddress,
      .child _ _ _ _ selected, other,
      incomparable, selectedReplacement, otherReplacement => by
        cases otherAddress with
        | nil =>
            exact False.elim (incomparable.2 (by simp [AddressPrefix]))
        | cons otherSlot otherRest =>
            rw [CKTree.PunctureAt.transport_insert_eq_childPart
              (.child _ _ _ _ selected) other incomparable
              selectedReplacement otherReplacement]
            rw [CKTree.PunctureAt.transport_insert_eq_childPart
              other (.child _ _ _ _ selected)
              (prefixIncomparable_symm incomparable)
              otherReplacement selectedReplacement]
            exact congrArg (CKTree.ordinary _)
              (selected.insertIncomparable_commutes other.childPart incomparable
                selectedReplacement otherReplacement)

/-- Tuple form of strict independent-insertion interchange. -/
theorem CKChildren.PunctureAt.insertIncomparable_commutes :
    {boundaries : List (Hypersequent sigma)} ->
    {H K : Hypersequent sigma} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    {selectedSlot otherSlot : Nat} ->
    {selectedAddress otherAddress : InternalAddress} ->
    (selected : CKChildren.PunctureAt H children
      selectedSlot selectedAddress) ->
    (other : CKChildren.PunctureAt K children otherSlot otherAddress) ->
    (incomparable : PrefixIncomparable
      (selectedSlot :: selectedAddress) (otherSlot :: otherAddress)) ->
    (selectedReplacement : CKTree sigma InstanceData H) ->
    (otherReplacement : CKTree sigma InstanceData K) ->
      (selected.transportIncomparable other incomparable
          selectedReplacement).insert otherReplacement =
        (other.transportIncomparable selected
          (prefixIncomparable_symm incomparable)
          otherReplacement).insert selectedReplacement
  | _, _, _, _, _, _, _, _,
      .head _ tail _ selected, other,
      incomparable, selectedReplacement, otherReplacement => by
        cases other with
        | head _ _ _ otherBelow =>
            change CKChildren.cons
              ((selected.transportIncomparable otherBelow _
                selectedReplacement).insert otherReplacement) tail =
              CKChildren.cons
                ((otherBelow.transportIncomparable selected _
                  otherReplacement).insert selectedReplacement) tail
            exact congrArg (fun childHead => CKChildren.cons childHead tail)
              (selected.insertIncomparable_commutes otherBelow
                (by simpa [PrefixIncomparable, AddressPrefix] using incomparable)
                selectedReplacement otherReplacement)
        | tail _ _ _ _ _ => rfl
  | _, _, _, _, _, _, _, _,
      .tail childHead _ _ _ selected, other,
      incomparable, selectedReplacement, otherReplacement => by
        cases other with
        | head _ _ _ _ => rfl
        | tail _ _ _ _ otherBelow =>
            change CKChildren.cons childHead
              ((selected.transportIncomparable otherBelow _
                selectedReplacement).insert otherReplacement) =
              CKChildren.cons childHead
                ((otherBelow.transportIncomparable selected _
                  otherReplacement).insert selectedReplacement)
            exact congrArg (CKChildren.cons childHead)
              (selected.insertIncomparable_commutes otherBelow
                (by simpa [PrefixIncomparable, AddressPrefix] using incomparable)
                selectedReplacement otherReplacement)

end

/-- Both replacement-internal puncture families have their literal outer
source prefixes in the common result of independent insertion.  The first
component is transported across interchange; the second is produced directly
in the selected-then-other schedule. -/
theorem CKTree.PunctureAt.insertIncomparable_replacementPunctures_prefixed
    {G H K L M : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    {selectedAddress otherAddress selectedRelative otherRelative :
      InternalAddress}
    (selected : CKTree.PunctureAt H tree selectedAddress)
    (other : CKTree.PunctureAt K tree otherAddress)
    (incomparable : PrefixIncomparable selectedAddress otherAddress)
    (selectedReplacement : CKTree sigma InstanceData H)
    (otherReplacement : CKTree sigma InstanceData K)
    (selectedInner : CKTree.PunctureAt L selectedReplacement selectedRelative)
    (otherInner : CKTree.PunctureAt M otherReplacement otherRelative) :
    CKTree.HasPunctureAt L
        ((selected.transportIncomparable other incomparable
          selectedReplacement).insert otherReplacement)
        (selectedAddress ++ selectedRelative) ∧
      CKTree.HasPunctureAt M
        ((selected.transportIncomparable other incomparable
          selectedReplacement).insert otherReplacement)
        (otherAddress ++ otherRelative) := by
  constructor
  · rw [selected.insertIncomparable_commutes other incomparable
      selectedReplacement otherReplacement]
    exact ⟨(other.transportIncomparable selected
      (prefixIncomparable_symm incomparable) otherReplacement)
        |>.insert_replacement selectedInner⟩
  · exact ⟨(selected.transportIncomparable other incomparable
      selectedReplacement).insert_replacement otherInner⟩

/-! ## Address behavior of general filling -/

mutual

/-- A filler puncture is present at the selected source address plus its
relative address inside that filler. -/
def CKCutPlan.fill_punctureAt_filler :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    (site : cut.Site) -> {H : Hypersequent sigma} ->
    {address : InternalAddress} ->
    CKTree.PunctureAt H (fillers site) address ->
      CKTree.PunctureAt H (cut.fill fillers)
        (cut.address site ++ address)
  | _, _, .interface _, _, site, _, _, _ => nomatch site
  | _, _, .ordinary o _ cuts, fillers, site, H, address, puncture => by
      let packed := cuts.fill_punctureAt_filler fillers site puncture
      change CKTree.PunctureAt H (.ordinary o (cuts.fill fillers))
        (cuts.address site ++ address)
      rw [packed.address_eq]
      exact .child o (cuts.fill fillers) packed.slot packed.rest packed.witness

/-- Child-tuple form of filler puncture prefixing. -/
def CKChildCuts.fill_punctureAt_filler :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    (site : cuts.Site) -> {H : Hypersequent sigma} ->
    {address : InternalAddress} ->
    CKTree.PunctureAt H (fillers site) address ->
      CKChildren.AddressPuncture H (cuts.fill fillers)
        (cuts.address site ++ address)
  | _, _, .nil, _, site, _, _, _ => nomatch site
  | _, _, .cons head tail headCut tailCuts, fillers,
      site, H, address, puncture => by
      cases site with
      | inl headSite =>
          exact
            { slot := 0
              rest := headCut.relativeAddress headSite ++ address
              address_eq := rfl
              witness := .head
                (headCut.fill (fun s => fillers (Sum.inl s)))
                (tailCuts.fill (fun s => fillers (Sum.inr s))) _
                (headCut.fill_punctureAt_filler
                  (fun s => fillers (Sum.inl s)) headSite puncture) }
      | inr tailSite =>
          let packed := tailCuts.fill_punctureAt_filler
            (fun s => fillers (Sum.inr s)) tailSite puncture
          exact
            { slot := packed.slot + 1
              rest := packed.rest
              address_eq := by
                simp only [CKChildCuts.address]
                rw [← InternalAddress.shiftHead_append_of_ne_nil
                  (tailCuts.address tailSite) address
                  (tailCuts.address_nonroot tailSite)]
                simpa [InternalAddress.shiftHead] using
                  congrArg InternalAddress.shiftHead packed.address_eq
              witness := .tail
                (headCut.fill (fun s => fillers (Sum.inl s)))
                (tailCuts.fill (fun s => fillers (Sum.inr s)))
                packed.slot packed.rest packed.witness }

/-- Detachment contributes the empty relative prefix; descent composes
relative addresses recursively. -/
def CKBranchCut.fill_punctureAt_filler :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    (site : cut.Site) -> {H : Hypersequent sigma} ->
    {address : InternalAddress} ->
    CKTree.PunctureAt H (fillers site) address ->
      CKTree.PunctureAt H (cut.fill fillers)
        (cut.relativeAddress site ++ address)
  | _, _, .detach _, fillers, site, _, _, puncture => by
      cases site
      simpa using puncture
  | _, _, .descend cut, fillers, site, _, _, puncture =>
      cut.fill_punctureAt_filler fillers site puncture

end

mutual

/-- A source puncture outside every replaced subtree remains at its literal
source address after general filling. -/
def CKCutPlan.fill_oldPuncture_preserved :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    {H : Hypersequent sigma} -> {address : InternalAddress} ->
    CKTree.PunctureAt H tree address ->
    ((site : cut.Site) -> ¬ AddressPrefix (cut.address site) address) ->
      CKTree.PunctureAt H (cut.fill fillers) address
  | _, _, .interface _, _, _, _, puncture, _ => puncture
  | _, _, .ordinary o children cuts, fillers, H, address, puncture,
      outside => by
      cases address with
      | nil =>
          have impossible := puncture.toInterfaceAt.statusAt_eq_interface
          exact False.elim (by
            simpa [CKCutPlan.fill, CKTree.statusAt] using impossible)
      | cons slot rest =>
          exact .child o (cuts.fill fillers) slot rest
            (cuts.fill_oldPuncture_preserved fillers
              puncture.childPart outside)

/-- Tuple form of preservation for old punctures outside replaced subtrees. -/
def CKChildCuts.fill_oldPuncture_preserved :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    {H : Hypersequent sigma} -> {slot : Nat} ->
    {address : InternalAddress} ->
    CKChildren.PunctureAt H children slot address ->
    ((site : cuts.Site) ->
      ¬ AddressPrefix (cuts.address site) (slot :: address)) ->
      CKChildren.PunctureAt H (cuts.fill fillers) slot address
  | _, _, .nil, _, _, _, _, puncture, _ => nomatch puncture
  | _, _, .cons head tail headCut tailCuts, fillers,
      H, slot, address, puncture, outside => by
      cases slot with
      | zero =>
          refine .head
            (headCut.fill (fun site => fillers (Sum.inl site)))
            (tailCuts.fill (fun site => fillers (Sum.inr site))) address ?_
          apply headCut.fill_oldPuncture_preserved
            (fun site => fillers (Sum.inl site)) puncture.tuplePart
          intro site isPrefix
          exact outside (Sum.inl site) (by
            simpa [CKChildCuts.address, AddressPrefix] using isPrefix)
      | succ tailSlot =>
          refine .tail
            (headCut.fill (fun site => fillers (Sum.inl site)))
            (tailCuts.fill (fun site => fillers (Sum.inr site)))
            tailSlot address ?_
          apply tailCuts.fill_oldPuncture_preserved
            (fun site => fillers (Sum.inr site)) puncture.tuplePart
          intro site isPrefix
          apply outside (Sum.inr site)
          have shifted :=
            (InternalAddress.shiftHead_prefix_iff
              (tailCuts.address_nonroot site) (by simp)).mpr isPrefix
          simpa [CKChildCuts.address] using shifted

/-- A detached branch replaces its whole subtree, while descent preserves
unselected old punctures recursively. -/
def CKBranchCut.fill_oldPuncture_preserved :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    {H : Hypersequent sigma} -> {address : InternalAddress} ->
    CKTree.PunctureAt H tree address ->
    ((site : cut.Site) ->
      ¬ AddressPrefix (cut.relativeAddress site) address) ->
      CKTree.PunctureAt H (cut.fill fillers) address
  | _, _, .detach _, _, _, address, _, outside => by
      exact False.elim (outside PUnit.unit (by
        change AddressPrefix [] address
        simp [AddressPrefix]))
  | _, _, .descend cut, fillers, _, _, puncture, outside =>
      cut.fill_oldPuncture_preserved fillers puncture outside

end

mutual

/-- Every puncture after filling comes either from an unreplaced old source
puncture or from one uniquely addressed replacement region. -/
theorem CKCutPlan.fill_punctureAt_cases :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    {H : Hypersequent sigma} -> {address : InternalAddress} ->
    CKTree.PunctureAt H (cut.fill fillers) address ->
      (tree.HasPunctureAt H address ∧
        ((site : cut.Site) ->
          ¬ AddressPrefix (cut.address site) address)) ∨
      ∃ (site : cut.Site) (relative : InternalAddress),
        address = cut.address site ++ relative ∧
          (fillers site).HasPunctureAt H relative
  | _, _, .interface _, _, _, _, puncture =>
      Or.inl ⟨⟨puncture⟩, fun site => nomatch site⟩
  | _, _, .ordinary o children cuts, fillers, H, address, puncture => by
      cases address with
      | nil =>
          have impossible := puncture.toInterfaceAt.statusAt_eq_interface
          exact False.elim (by
            simpa [CKCutPlan.fill, CKTree.statusAt] using impossible)
      | cons slot rest =>
          rcases cuts.fill_punctureAt_cases fillers puncture.childPart with
            old | replacement
          · rcases old.1 with ⟨oldBelow⟩
            exact Or.inl ⟨⟨.child o children slot rest oldBelow⟩, old.2⟩
          · exact Or.inr replacement

/-- Ordered-tuple decomposition of every puncture after general filling. -/
theorem CKChildCuts.fill_punctureAt_cases :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    {H : Hypersequent sigma} -> {slot : Nat} ->
    {address : InternalAddress} ->
    CKChildren.PunctureAt H (cuts.fill fillers) slot address ->
      (children.HasPunctureAt H slot address ∧
        ((site : cuts.Site) ->
          ¬ AddressPrefix (cuts.address site) (slot :: address))) ∨
      ∃ (site : cuts.Site) (relative : InternalAddress),
        slot :: address = cuts.address site ++ relative ∧
          (fillers site).HasPunctureAt H relative
  | _, _, .nil, _, _, _, _, puncture => nomatch puncture
  | _, _, .cons head tail headCut tailCuts, fillers,
      H, slot, address, puncture => by
      cases slot with
      | zero =>
          rcases headCut.fill_punctureAt_cases
              (fun site => fillers (Sum.inl site)) puncture.tuplePart with
            old | replacement
          · rcases old.1 with ⟨oldBelow⟩
            refine Or.inl ⟨⟨.head head tail address oldBelow⟩, ?_⟩
            intro site
            cases site with
            | inl headSite =>
                intro isPrefix
                exact old.2 headSite (by
                  simpa [CKChildCuts.address, AddressPrefix] using isPrefix)
            | inr tailSite =>
                intro isPrefix
                cases addressEq : tailCuts.address tailSite with
                | nil =>
                    exact (tailCuts.address_nonroot tailSite) addressEq
                | cons tailSlot tailRest =>
                    change AddressPrefix
                      (InternalAddress.shiftHead (tailCuts.address tailSite))
                      (0 :: address) at isPrefix
                    rw [addressEq] at isPrefix
                    simpa [InternalAddress.shiftHead, AddressPrefix] using
                      isPrefix
          · rcases replacement with ⟨site, relative, addressEq, inner⟩
            exact Or.inr ⟨Sum.inl site, relative, by
              simpa [CKChildCuts.address] using
                congrArg (List.cons 0) addressEq, inner⟩
      | succ tailSlot =>
          rcases tailCuts.fill_punctureAt_cases
              (fun site => fillers (Sum.inr site)) puncture.tuplePart with
            old | replacement
          · rcases old.1 with ⟨oldBelow⟩
            refine Or.inl ⟨⟨.tail head tail tailSlot address oldBelow⟩, ?_⟩
            intro site
            cases site with
            | inl headSite =>
                simp [CKChildCuts.address, AddressPrefix]
            | inr tailSite =>
                intro isPrefix
                apply old.2 tailSite
                apply (InternalAddress.shiftHead_prefix_iff
                  (tailCuts.address_nonroot tailSite) (by simp)).mp
                simpa [CKChildCuts.address] using isPrefix
          · rcases replacement with ⟨site, relative, addressEq, inner⟩
            refine Or.inr ⟨Sum.inr site, relative, ?_, inner⟩
            have shifted := congrArg InternalAddress.shiftHead addressEq
            simpa [CKChildCuts.address,
              InternalAddress.shiftHead_append_of_ne_nil
                (tailCuts.address site) relative
                (tailCuts.address_nonroot site)] using shifted

/-- Branch decomposition of every puncture after general filling. -/
theorem CKBranchCut.fill_punctureAt_cases :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    {H : Hypersequent sigma} -> {address : InternalAddress} ->
    CKTree.PunctureAt H (cut.fill fillers) address ->
      (tree.HasPunctureAt H address ∧
        ((site : cut.Site) ->
          ¬ AddressPrefix (cut.relativeAddress site) address)) ∨
      ∃ (site : cut.Site) (relative : InternalAddress),
        address = cut.relativeAddress site ++ relative ∧
          (fillers site).HasPunctureAt H relative
  | _, _, .detach _, fillers, _, address, puncture =>
      Or.inr ⟨PUnit.unit, address, rfl, ⟨puncture⟩⟩
  | _, _, .descend cut, fillers, _, _, puncture =>
      cut.fill_punctureAt_cases fillers puncture

end

/-! ## General filling and local admission -/

mutual

/-- General filling preserves local admission by constructor recursion. -/
def CKCutPlan.fillLocallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    LocallyAdmittedTree P tree ->
    ((site : cut.Site) -> LocallyAdmittedTree P (fillers site)) ->
      LocallyAdmittedTree P (cut.fill fillers)
  | _, _, .interface _, _, admitted, _ => admitted
  | _, _, .ordinary _ _ cuts, fillers, admitted, fillerAdmitted =>
      ⟨admitted.1,
        cuts.fillLocallyAdmitted fillers admitted.2 fillerAdmitted⟩

/-- General filling is locally admitted in every ordered premise slot. -/
def CKChildCuts.fillLocallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    LocallyAdmittedChildren P children ->
    ((site : cuts.Site) -> LocallyAdmittedTree P (fillers site)) ->
      LocallyAdmittedChildren P (cuts.fill fillers)
  | _, _, .nil, _, _, _ => trivial
  | _, _, .cons _ _ headCut tailCuts, fillers, admitted, fillerAdmitted =>
      ⟨headCut.fillLocallyAdmitted
          (fun site => fillers (Sum.inl site)) admitted.1
          (fun site => fillerAdmitted (Sum.inl site)),
        tailCuts.fillLocallyAdmitted
          (fun site => fillers (Sum.inr site)) admitted.2
          (fun site => fillerAdmitted (Sum.inr site))⟩

/-- Detachment uses the supplied filler; descent preserves admission recursively. -/
def CKBranchCut.fillLocallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    LocallyAdmittedTree P tree ->
    ((site : cut.Site) -> LocallyAdmittedTree P (fillers site)) ->
      LocallyAdmittedTree P (cut.fill fillers)
  | _, _, .detach _, _, _, fillerAdmitted => fillerAdmitted PUnit.unit
  | _, _, .descend cut, fillers, admitted, fillerAdmitted =>
      cut.fillLocallyAdmitted fillers admitted fillerAdmitted

end

mutual

/-- Filling a complete source by complete replacements remains complete. -/
def CKCutPlan.fillIsComplete :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    tree.IsComplete ->
    ((site : cut.Site) -> (fillers site).IsComplete) ->
      (cut.fill fillers).IsComplete
  | _, _, .interface _, _, complete, _ => False.elim complete
  | _, _, .ordinary _ _ cuts, fillers, complete, fillerComplete =>
      cuts.fillIsComplete fillers complete fillerComplete

/-- Completeness of general filling is componentwise over ordered children. -/
def CKChildCuts.fillIsComplete :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    children.IsComplete ->
    ((site : cuts.Site) -> (fillers site).IsComplete) ->
      (cuts.fill fillers).IsComplete
  | _, _, .nil, _, _, _ => trivial
  | _, _, .cons _ _ headCut tailCuts, fillers, complete, fillerComplete =>
      ⟨headCut.fillIsComplete
          (fun site => fillers (Sum.inl site)) complete.1
          (fun site => fillerComplete (Sum.inl site)),
        tailCuts.fillIsComplete
          (fun site => fillers (Sum.inr site)) complete.2
          (fun site => fillerComplete (Sum.inr site))⟩

/-- Root detachment is complete exactly when its replacement is complete. -/
def CKBranchCut.fillIsComplete :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    tree.IsComplete ->
    ((site : cut.Site) -> (fillers site).IsComplete) ->
      (cut.fill fillers).IsComplete
  | _, _, .detach _, _, _, fillerComplete => fillerComplete PUnit.unit
  | _, _, .descend cut, fillers, complete, fillerComplete =>
      cut.fillIsComplete fillers complete fillerComplete

end

namespace CKCut

variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- General filling is indexed by, and therefore preserves, the source root boundary. -/
@[simp]
theorem fill_rootBoundary (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site)) :
    (cut.fill fillers).rootBoundary = tree.rootBoundary := rfl

/-- Every general filling of a public cut retains its positive root. -/
theorem fill_isOrdinary (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site)) :
    (cut.fill fillers).IsOrdinary := by
  rcases cut with ⟨sourceOrdinary, plan⟩
  cases plan with
  | interface _ => exact False.elim sourceOrdinary
  | ordinary _ _ _ => trivial

/-- Locally admitted sources and replacements give a locally admitted result. -/
theorem fill_locallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}
    (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (sourceAdmitted : LocallyAdmittedTree P tree)
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) :
    LocallyAdmittedTree P (cut.fill fillers) :=
  cut.plan.fillLocallyAdmitted fillers sourceAdmitted fillersAdmitted

/-- Complete sources and complete replacements give a complete result. -/
theorem fill_isComplete (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (sourceComplete : tree.IsComplete)
    (fillersComplete : (site : cut.Site) -> (fillers site).IsComplete) :
    (cut.fill fillers).IsComplete :=
  cut.plan.fillIsComplete fillers sourceComplete fillersComplete

/-- Punctures internal to a replacement occur at the selected source address
prefixed to their exact relative replacement address. -/
def fill_fillerPuncture_prefixed (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (site : cut.Site) {H : Hypersequent sigma}
    {relative : InternalAddress}
    (puncture : CKTree.PunctureAt H (fillers site) relative) :
    CKTree.PunctureAt H (cut.fill fillers)
      (cut.plan.address site ++ relative) :=
  cut.plan.fill_punctureAt_filler fillers site puncture

/-- An old source puncture survives literally when it is outside every
subtree replaced by this cut. -/
def fill_oldPuncture_preserved (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    {H : Hypersequent sigma} {address : InternalAddress}
    (puncture : CKTree.PunctureAt H tree address)
    (outside : (site : cut.Site) ->
      ¬ AddressPrefix (cut.plan.address site) address) :
    CKTree.PunctureAt H (cut.fill fillers) address :=
  cut.plan.fill_oldPuncture_preserved fillers puncture outside

/-- Exact address formula for all punctures after general cut filling. -/
theorem fill_punctureAt_iff (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    {H : Hypersequent sigma} {address : InternalAddress} :
    (cut.fill fillers).HasPunctureAt H address ↔
      (tree.HasPunctureAt H address ∧
        ((site : cut.Site) ->
          ¬ AddressPrefix (cut.plan.address site) address)) ∨
      ∃ (site : cut.Site) (relative : InternalAddress),
        address = cut.plan.address site ++ relative ∧
          (fillers site).HasPunctureAt H relative := by
  constructor
  · rintro ⟨puncture⟩
    exact cut.plan.fill_punctureAt_cases fillers puncture
  · intro source
    rcases source with old | replacement
    · rcases old.1 with ⟨puncture⟩
      exact ⟨cut.fill_oldPuncture_preserved fillers puncture old.2⟩
    · rcases replacement with ⟨site, relative, rfl, ⟨puncture⟩⟩
      exact ⟨cut.fill_fillerPuncture_prefixed fillers site puncture⟩

/-- Boundary-erased form of the exact old-or-prefixed-new puncture law. -/
theorem fill_interfaceAt_iff (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    {address : InternalAddress} :
    (cut.fill fillers).InterfaceAt address ↔
      (tree.InterfaceAt address ∧
        ((site : cut.Site) ->
          ¬ AddressPrefix (cut.plan.address site) address)) ∨
      ∃ (site : cut.Site) (relative : InternalAddress),
        address = cut.plan.address site ++ relative ∧
          (fillers site).InterfaceAt relative := by
  constructor
  · intro puncture
    rcases puncture.exists_typed with ⟨H, typed⟩
    rcases (cut.fill_punctureAt_iff fillers).mp typed with old | replacement
    · rcases old.1 with ⟨oldTyped⟩
      exact Or.inl ⟨oldTyped.toInterfaceAt, old.2⟩
    · rcases replacement with ⟨site, relative, addressEq, inner⟩
      rcases inner with ⟨innerTyped⟩
      exact Or.inr ⟨site, relative, addressEq, innerTyped.toInterfaceAt⟩
  · intro source
    rcases source with old | replacement
    · rcases old.1.exists_typed with ⟨H, typed⟩
      rcases typed with ⟨typedWitness⟩
      exact (cut.fill_oldPuncture_preserved fillers
        typedWitness old.2).toInterfaceAt
    · rcases replacement with ⟨site, relative, rfl, inner⟩
      rcases inner.exists_typed with ⟨H, typed⟩
      rcases typed with ⟨typedWitness⟩
      exact (cut.fill_fillerPuncture_prefixed fillers site
        typedWitness).toInterfaceAt

/-- Legacy `InterfaceAt` corollary for unrelated old vacancies. -/
theorem fill_oldInterfaceAt_preserved (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    {address : InternalAddress} (old : tree.InterfaceAt address)
    (outside : (site : cut.Site) ->
      ¬ AddressPrefix (cut.plan.address site) address) :
    (cut.fill fillers).InterfaceAt address := by
  rcases old.exists_typed with ⟨H, typed⟩
  rcases typed with ⟨typedWitness⟩
  exact (cut.fill_oldPuncture_preserved fillers
    typedWitness outside).toInterfaceAt

/-- General filling specializes to exact distinguished reconstruction. -/
theorem fill_originalDetached (cut : CKCut tree) :
    cut.fill cut.plan.detached = tree :=
  cut.fill_detached_reconstructs

end CKCut

/-! ## Completeness of checked realizations -/

/-- A checked derivation realizes to a complete, not merely locally admitted, tree. -/
def CheckedDerivation.realizeIsComplete
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}
    {G : Hypersequent sigma} (derivation : CheckedDerivation P G) :
    derivation.realize.IsComplete :=
  CheckedDerivation.rec
    (motive_1 := fun _ derivation => derivation.realize.IsComplete)
    (motive_2 := fun _ children =>
      (CheckedDerivation.CheckedChildren.realize children).IsComplete)
    (fun _ _ _ childrenComplete => by
      simpa only [CheckedDerivation.realize, CKTree.IsComplete] using
        childrenComplete)
    (by
      simp only [CheckedDerivation.CheckedChildren.realize,
        CKChildren.IsComplete])
    (fun _ _ headComplete tailComplete => by
      simpa only [CheckedDerivation.CheckedChildren.realize,
        CKChildren.IsComplete] using
        And.intro headComplete tailComplete)
    derivation

/-- Every child of a checked derivation realizes completely. -/
def CheckedChildren.realizeIsComplete
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}
    {boundaries : List (Hypersequent sigma)}
    (children : CheckedChildren P boundaries) :
    (CheckedDerivation.CheckedChildren.realize children).IsComplete :=
  CheckedChildren.rec
    (motive_1 := fun _ derivation => derivation.realize.IsComplete)
    (motive_2 := fun _ children =>
      (CheckedDerivation.CheckedChildren.realize children).IsComplete)
    (fun _ _ _ childrenComplete => by
      simpa only [CheckedDerivation.realize, CKTree.IsComplete] using
        childrenComplete)
    (by
      simp only [CheckedDerivation.CheckedChildren.realize,
        CKChildren.IsComplete])
    (fun _ _ headComplete tailComplete => by
      simpa only [CheckedDerivation.CheckedChildren.realize,
        CKChildren.IsComplete] using
        And.intro headComplete tailComplete)
    children

namespace CheckedDerivation

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

/-- Filling a cut of a checked proof by checked proofs is complete. -/
theorem fill_realize_isComplete {G : Hypersequent sigma}
    (source : CheckedDerivation P G) (cut : CKCut source.realize)
    (fillers : (site : cut.Site) ->
      CheckedDerivation P (cut.plan.siteBoundary site)) :
    (cut.fill (fun site => (fillers site).realize)).IsComplete :=
  cut.fill_isComplete (fun site => (fillers site).realize)
    source.realizeIsComplete (fun site => (fillers site).realizeIsComplete)

/-- The same checked filling remains in the exact locally admitted sector. -/
theorem fill_realize_locallyAdmitted {G : Hypersequent sigma}
    (source : CheckedDerivation P G) (cut : CKCut source.realize)
    (fillers : (site : cut.Site) ->
      CheckedDerivation P (cut.plan.siteBoundary site)) :
    LocallyAdmittedTree P
      (cut.fill (fun site => (fillers site).realize)) :=
  cut.fill_locallyAdmitted (fun site => (fillers site).realize)
    source.realizeLocallyAdmitted
    (fun site => (fillers site).realizeLocallyAdmitted)

end CheckedDerivation

/-! ## Realized general filling and base transport -/

namespace RealizedOpenComponent

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

private theorem ext_component
    {left right : RealizedOpenComponent P}
    (same : left.component = right.component) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- Package a general admitted filling in the same exact realized sector. -/
def fillOfCut (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) : RealizedOpenComponent P :=
  ofTree (cut.fill fillers) (cut.fill_isOrdinary fillers)
    (cut.fill_locallyAdmitted fillers source.locallyAdmitted fillersAdmitted)

@[simp]
theorem fillOfCut_component_tree (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) :
    (source.fillOfCut cut fillers fillersAdmitted).component.tree =
      cut.fill fillers := rfl

/-- The realized wrapper records completeness when both source and fillers
are complete; local admission alone does not imply this statement. -/
theorem fillOfCut_isComplete (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site))
    (sourceComplete : source.component.tree.IsComplete)
    (fillersComplete : (site : cut.Site) -> (fillers site).IsComplete) :
    (source.fillOfCut cut fillers fillersAdmitted).component.tree.IsComplete :=
  cut.fill_isComplete fillers sourceComplete fillersComplete

/-- Proof-preserving base transport commutes with arbitrary admitted filling. -/
@[simp]
theorem fillOfCut_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) :
    (source.fillOfCut cut fillers fillersAdmitted).mapBase f =
      (source.mapBase f).fillOfCut cut fillers
        (fun site => (fillersAdmitted site).mapBase f) := by
  apply ext_component
  rfl

end RealizedOpenComponent

end Potkin

import Potkin.CompositeCutExpansion

/-!
# Full native branch-cut packets through a typed puncture

The paper's `Cut(t)` includes detachment of the whole positive root and is
therefore `CKBranchCut t`, NOT the native nonroot `CKCut t`.  An interface has
only its empty branch cut.  No new proof, context, forest or cut carrier is
introduced: the auxiliary types below are only sums/products of existing
native cuts, indexed by an existing `PunctureAt` path.

`Choices` follows the pointed ordered premise spine. `NoSpine` forbids
selection of its vertices; `Ancestor` selects exactly one, masking every
deeper region.  The equivalence retains the actual native cut witness, hence
its complete ordered packet, dependent factor-to-hole matching and remainder
before any commutative collection.  This is unfiltered CK geometry; it does
not assume the paper's material-eligibility adapter.
-/

namespace Potkin.Research.ContextCutPackets

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual
/-- Recursive independent full-branch choices, with one swallowing option at
each positive spine vertex. This is an index, not a second cut carrier. -/
def Choices : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    CKTree sigma InstanceData H → Type (max (max u v) w)
  | _, _, _, _, .root, payload => CKBranchCut payload
  | _, _, _, _, .child _ _ _ _ below, payload =>
      PUnit.{max (max u v) w + 1} ⊕ ChildChoices below payload

def ChildChoices : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    CKTree sigma InstanceData H → Type (max (max u v) w)
  | _, _, _, _, _, .head _ tail _ below, payload =>
      Choices below payload × CKChildCuts tail
  | _, _, _, _, _, .tail head _ _ _ below, payload =>
      CKBranchCut head × ChildChoices below payload
end

mutual
/-- No selected context-spine vertex: every payload and sibling choice is
independent. Ordered tuple positions remain in the product index. -/
def NoSpine : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    CKTree sigma InstanceData H → Type (max (max u v) w)
  | _, _, _, _, .root, payload => CKBranchCut payload
  | _, _, _, _, .child _ _ _ _ below, payload => ChildNoSpine below payload

def ChildNoSpine : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    CKTree sigma InstanceData H → Type (max (max u v) w)
  | _, _, _, _, _, .head _ tail _ below, payload =>
      NoSpine below payload × CKChildCuts tail
  | _, _, _, _, _, .tail head _ _ _ below, payload =>
      CKBranchCut head × ChildNoSpine below payload

/-- Exactly one selected spine vertex. Its option has NO payload/deeper
sibling choices: that entire filled subtree is swallowed intact. -/
def Ancestor : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    Type (max (max u v) w)
  | _, _, _, _, .root => PEmpty.{max (max u v) w + 1}
  | _, _, _, _, .child _ _ _ _ below =>
      PUnit.{max (max u v) w + 1} ⊕ ChildAncestor below

def ChildAncestor : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    Type (max (max u v) w)
  | _, _, _, _, _, .head _ tail _ below =>
      Ancestor below × CKChildCuts tail
  | _, _, _, _, _, .tail head _ _ _ below =>
      CKBranchCut head × ChildAncestor below
end

mutual
def assemble : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) →
    Choices hole payload → CKBranchCut (hole.insert payload)
  | _, _, _, _, .root, _, choice => choice
  | _, _, _, _, .child o _ _ _ below, payload, choice =>
      match choice with
      | .inl _ => .detach trivial
      | .inr choice =>
          .descend (.ordinary o _ (assembleChildren below payload choice))

def assembleChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    ChildChoices hole payload → CKChildCuts (hole.insert payload)
  | _, _, _, _, _, .head _ tail _ below, payload, choice =>
      .cons _ tail (assemble below payload choice.1) choice.2
  | _, _, _, _, _, .tail head _ _ _ below, payload, choice =>
      .cons head _ choice.1 (assembleChildren below payload choice.2)
end

mutual
def decompose : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) →
    CKBranchCut (hole.insert payload) → Choices hole payload
  | _, _, _, _, .root, _, cut => cut
  | _, _, _, _, .child _ _ _ _ below, payload, cut =>
      match cut.rootChoice with
      | .inl _ => .inl PUnit.unit
      | .inr plan => .inr (decomposeChildren below payload plan.contents)

def decomposeChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    CKChildCuts (hole.insert payload) → ChildChoices hole payload
  | _, _, _, _, _, .head _ _ _ below, payload, cut =>
      (decompose below payload cut.contents.1, cut.contents.2)
  | _, _, _, _, _, .tail _ _ _ _ below, payload, cut =>
      (cut.contents.1, decomposeChildren below payload cut.contents.2)
end

mutual
theorem assemble_decompose : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) →
    (cut : CKBranchCut (hole.insert payload)) →
    assemble hole payload (decompose hole payload cut) = cut
  | _, _, _, _, .root, _, _ => rfl
  | _, _, _, _, .child o _ _ _ below, payload, cut => by
      have reassemble := cut.rootChoice_reconstructs (by trivial)
      generalize equal : cut.rootChoice = choice at *
      cases choice with
      | inl value =>
          simpa [assemble, decompose, equal] using reassemble
      | inr plan =>
          simp only [assemble, decompose, equal]
          rw [assembleChildren_decomposeChildren below payload plan.contents]
          have planEq : CKCutPlan.ordinary o (below.insert payload)
              plan.contents = plan := plan.contents_reconstructs
          exact (congrArg CKBranchCut.descend planEq).trans reassemble

theorem assembleChildren_decomposeChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    (cut : CKChildCuts (hole.insert payload)) →
    assembleChildren hole payload (decomposeChildren hole payload cut) = cut
  | _, _, _, _, _, .head _ _ _ below, payload, cut => by
      simp only [assembleChildren, decomposeChildren]
      rw [assemble_decompose below payload cut.contents.1]
      exact cut.contents_reconstructs
  | _, _, _, _, _, .tail _ _ _ _ below, payload, cut => by
      simp only [assembleChildren, decomposeChildren]
      rw [assembleChildren_decomposeChildren below payload cut.contents.2]
      exact cut.contents_reconstructs
end

mutual
theorem decompose_assemble : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (choice : Choices hole payload) →
    decompose hole payload (assemble hole payload choice) = choice
  | _, _, _, _, .root, _, _ => rfl
  | _, _, _, _, .child _ _ _ _ below, payload, choice => by
      cases choice with
      | inl value => cases value; rfl
      | inr choice =>
          simp only [decompose, assemble, CKBranchCut.rootChoice,
            CKCutPlan.contents, decomposeChildren_assembleChildren below payload choice]

theorem decomposeChildren_assembleChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    (choice : ChildChoices hole payload) →
    decomposeChildren hole payload (assembleChildren hole payload choice) = choice
  | _, _, _, _, _, .head _ _ _ below, payload, choice => by
      cases choice
      simp only [decomposeChildren, assembleChildren, CKChildCuts.contents,
        decompose_assemble]
  | _, _, _, _, _, .tail _ _ _ _ below, payload, choice => by
      cases choice
      simp only [decomposeChildren, assembleChildren, CKChildCuts.contents,
        decomposeChildren_assembleChildren]
end

def pointedBranchEquiv {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H) :
    CKBranchCut (hole.insert payload) ≃ Choices hole payload where
  toFun := decompose hole payload
  invFun := assemble hole payload
  left_inv := assemble_decompose hole payload
  right_inv := decompose_assemble hole payload

mutual
def split : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → Choices hole payload →
    NoSpine hole payload ⊕ Ancestor hole
  | _, _, _, _, .root, _, choice => .inl choice
  | _, _, _, _, .child _ _ _ _ below, payload, choice =>
      match choice with
      | .inl value => .inr (.inl value)
      | .inr choice =>
          match splitChildren below payload choice with
          | .inl choice => .inl choice
          | .inr choice => .inr (.inr choice)

def splitChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → ChildChoices hole payload →
    ChildNoSpine hole payload ⊕ ChildAncestor hole
  | _, _, _, _, _, .head _ _ _ below, payload, choice =>
      match split below payload choice.1 with
      | .inl head => .inl (head, choice.2)
      | .inr head => .inr (head, choice.2)
  | _, _, _, _, _, .tail _ _ _ _ below, payload, choice =>
      match splitChildren below payload choice.2 with
      | .inl tail => .inl (choice.1, tail)
      | .inr tail => .inr (choice.1, tail)
end

mutual
def merge : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) →
    NoSpine hole payload ⊕ Ancestor hole → Choices hole payload
  | _, _, _, _, .root, _, .inl choice => choice
  | _, _, _, _, .root, _, .inr impossible => nomatch impossible
  | _, _, _, _, .child _ _ _ _ below, payload, choice =>
      match choice with
      | .inl choice => .inr (mergeChildren below payload (.inl choice))
      | .inr ancestor =>
          match ancestor with
          | Sum.inl value => .inl value
          | Sum.inr choice => .inr (mergeChildren below payload (.inr choice))

def mergeChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    ChildNoSpine hole payload ⊕ ChildAncestor hole → ChildChoices hole payload
  | _, _, _, _, _, .head _ _ _ below, payload, .inl choice =>
      (merge below payload (.inl choice.1), choice.2)
  | _, _, _, _, _, .head _ _ _ below, payload, .inr choice =>
      (merge below payload (.inr choice.1), choice.2)
  | _, _, _, _, _, .tail _ _ _ _ below, payload, .inl choice =>
      (choice.1, mergeChildren below payload (.inl choice.2))
  | _, _, _, _, _, .tail _ _ _ _ below, payload, .inr choice =>
      (choice.1, mergeChildren below payload (.inr choice.2))
end

mutual
theorem merge_split : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (choice : Choices hole payload) →
    merge hole payload (split hole payload choice) = choice
  | _, _, _, _, .root, _, _ => rfl
  | _, _, _, _, .child _ _ _ _ below, payload, choice => by
      cases choice with
      | inl value => rfl
      | inr choice =>
          have inverse := mergeChildren_splitChildren below payload choice
          generalize equal : splitChildren below payload choice = result at *
          cases result <;> simpa only [split, merge, equal] using
            congrArg (Sum.inr : ChildChoices below payload →
              PUnit.{max (max u v) w + 1} ⊕ ChildChoices below payload) inverse

theorem mergeChildren_splitChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → (choice : ChildChoices hole payload) →
    mergeChildren hole payload (splitChildren hole payload choice) = choice
  | _, _, _, _, _, .head _ _ _ below, payload, choice => by
      have inverse := merge_split below payload choice.1
      generalize equal : split below payload choice.1 = result at *
      cases result <;> simpa [splitChildren, mergeChildren, equal] using
        congrArg (fun head => (head, choice.2)) inverse
  | _, _, _, _, _, .tail _ _ _ _ below, payload, choice => by
      have inverse := mergeChildren_splitChildren below payload choice.2
      generalize equal : splitChildren below payload choice.2 = result at *
      cases result <;> simpa [splitChildren, mergeChildren, equal] using
        congrArg (fun tail => (choice.1, tail)) inverse
end

mutual
theorem split_merge : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) →
    (choice : NoSpine hole payload ⊕ Ancestor hole) →
    split hole payload (merge hole payload choice) = choice
  | _, _, _, _, .root, _, .inl _ => rfl
  | _, _, _, _, .root, _, .inr impossible => nomatch impossible
  | _, _, _, _, .child _ _ _ _ below, payload, choice => by
      cases choice with
      | inl choice =>
          simp only [split, merge, splitChildren_mergeChildren]
      | inr ancestor =>
          change PUnit.{max (max u v) w + 1} ⊕ ChildAncestor below at ancestor
          cases ancestor with
          | inl value => rfl
          | inr choice =>
              simp only [split, merge, splitChildren_mergeChildren]

theorem splitChildren_mergeChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    (choice : ChildNoSpine hole payload ⊕ ChildAncestor hole) →
    splitChildren hole payload (mergeChildren hole payload choice) = choice
  | _, _, _, _, _, .head _ _ _ below, payload, .inl choice => by
      cases choice
      simp only [splitChildren, mergeChildren, split_merge]
  | _, _, _, _, _, .head _ _ _ below, payload, .inr choice => by
      cases choice
      simp only [splitChildren, mergeChildren, split_merge]
  | _, _, _, _, _, .tail _ _ _ _ below, payload, .inl choice => by
      cases choice
      simp only [splitChildren, mergeChildren, splitChildren_mergeChildren]
  | _, _, _, _, _, .tail _ _ _ _ below, payload, .inr choice => by
      cases choice
      simp only [splitChildren, mergeChildren, splitChildren_mergeChildren]
end

/-- Universal native form of the no-spine / unique-selected-ancestor packet
bijection. Siblings may themselves be arbitrary open native trees. -/
def fullPacketEquiv {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H) :
    CKBranchCut (hole.insert payload) ≃ NoSpine hole payload ⊕ Ancestor hole :=
  (pointedBranchEquiv hole payload).trans
    { toFun := split hole payload
      invFun := merge hole payload
      left_inv := merge_split hole payload
      right_inv := split_merge hole payload }

/-- The full branch analogue of `CKCut.detachedTuple`, using the SAME native
entry type. Root detachment records `[]`, without fabricating a proper cut. -/
def orderedPacket {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree) :
    List (CKCutEntry sigma InstanceData) :=
  cut.siteOrder.map fun site =>
    { address := cut.relativeAddress site
      boundary := cut.siteBoundary site
      tree := cut.detached site
      ordinary := cut.detachedOrdinary site }

/-- Strict descent retains exactly the existing public ordered detached
tuple. The additive branch adapter does not change the native proper carrier. -/
theorem orderedPacket_descend {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCut tree) :
    orderedPacket (.descend cut.plan) = cut.detachedTuple := rfl

theorem packet_and_remainder_preserved {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H)
    (cut : CKBranchCut (hole.insert payload)) :
    let reconstructed := (fullPacketEquiv hole payload).symm
      ((fullPacketEquiv hole payload) cut)
    (orderedPacket reconstructed, reconstructed.remainder) =
      (orderedPacket cut, cut.remainder) := by
  exact congrArg (fun c => (orderedPacket c, c.remainder))
    ((fullPacketEquiv hole payload).symm_apply_apply cut)

/-- Refill consumes the existing dependent native site family, not a forest
projection. It preserves the exact puncture-to-factor matching. -/
theorem assembled_refill {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H)
    (choice : NoSpine hole payload ⊕ Ancestor hole) :
    let cut := (fullPacketEquiv hole payload).symm choice
    cut.fill cut.detached = hole.insert payload :=
  CKBranchCut.fill_detached_reconstructs _

/-- The geometric equivalence stays in one exact registry when the input
context and payload are admitted there. No provenance cast is supplied. -/
theorem assembled_admitted {T : ProofTheory sigma InstanceData}
    {P : EquippedPresentation T} {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H)
    (contextAdmitted : LocallyAdmittedTree P context)
    (payloadAdmitted : LocallyAdmittedTree P payload)
    (choice : NoSpine hole payload ⊕ Ancestor hole) :
    let cut := (fullPacketEquiv hole payload).symm choice
    LocallyAdmittedTree P (hole.insert payload) ∧
      LocallyAdmittedTree P cut.remainder ∧
      (∀ site, LocallyAdmittedTree P (cut.detached site)) := by
  have admitted := hole.insertLocallyAdmitted contextAdmitted payloadAdmitted
  exact ⟨admitted, CKBranchCut.remainderLocallyAdmitted _ admitted,
    CKBranchCut.detachedLocallyAdmitted _ admitted⟩

/-- A selected outer spine root swallows the actual filled subtree, not a
primitive label or a payload cut choice. Its residual is the typed Box. -/
theorem outer_ancestor_packet (o : LocalOccurrence sigma InstanceData)
    {H : Hypersequent sigma}
    {children : CKChildren sigma InstanceData o.shape.premises}
    {slot : Nat} {address : InternalAddress}
    (below : CKChildren.PunctureAt H children slot address)
    (payload : CKTree sigma InstanceData H) :
    let hole := CKTree.PunctureAt.child o children slot address below
    let cut := assemble hole payload (.inl PUnit.unit)
    orderedPacket cut =
      [{ address := []
         boundary := o.shape.conclusion
         tree := hole.insert payload
         ordinary := trivial }] ∧
      cut.remainder = .interface o.shape.conclusion := by
  exact ⟨rfl, rfl⟩

mutual
/-- Native one-hole context composition: the prefixed puncture supplied by
`insert_replacement` has the same literal result as two successive fillings. -/
theorem insert_compose : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (payload : CKTree sigma InstanceData K) →
    (outer.insert_replacement inner).insert payload =
      outer.insert (inner.insert payload)
  | _, _, _, _, _, _, .root, _, _, _ => rfl
  | _, _, _, _, _, _, .child o _ _ _ below, _, inner, payload => by
      change CKTree.ordinary o
        ((below.insert_replacement inner).insert payload) =
        CKTree.ordinary o (below.insert (inner.insert payload))
      rw [insertChildren_compose below inner payload]

theorem insertChildren_compose : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} →
    {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (payload : CKTree sigma InstanceData K) →
    (outer.insert_replacement inner).insert payload =
      outer.insert (inner.insert payload)
  | _, _, _, _, _, _, _, .head _ tail _ below, _, inner, payload => by
      change CKChildren.cons ((below.insert_replacement inner).insert payload) tail =
        CKChildren.cons (below.insert (inner.insert payload)) tail
      rw [insert_compose below inner payload]
  | _, _, _, _, _, _, _, .tail head _ _ _ below, _, inner, payload => by
      change CKChildren.cons head ((below.insert_replacement inner).insert payload) =
        CKChildren.cons head (below.insert (inner.insert payload))
      rw [insertChildren_compose below inner payload]
end

#print axioms fullPacketEquiv
#print axioms packet_and_remainder_preserved
#print axioms orderedPacket_descend
#print axioms assembled_refill
#print axioms assembled_admitted
#print axioms outer_ancestor_packet
#print axioms insert_compose

end Potkin.Research.ContextCutPackets

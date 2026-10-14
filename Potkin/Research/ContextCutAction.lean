import Potkin.Research.ContextCutPackets
import Potkin.CKCutEnumeration
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.OfMap
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Native sibling-choice splicing for the CK context action

The indices here consist only of existing branch cuts in the fixed siblings
of a native typed puncture. They are not proof, cut, forest or context carriers.
The two splicing maps follow the actual ordered premise path. In particular an
outer selected ancestor has no inner choices, whereas an inner selected
ancestor is accompanied by every outer sibling choice.
-/

namespace Potkin.Research.ContextCutAction

open ContextCutPackets

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

private theorem sum_pair {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (f : α × β → R) :
    (∑ pair, f pair) = ∑ a, ∑ b, f (a, b) :=
  Finset.sum_product _ _ _

private theorem sum_alternatives {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (f : α ⊕ β → R) :
    (∑ choice, f choice) = (∑ a, f (.inl a)) + ∑ b, f (.inr b) :=
  Finset.sum_disjSum _ _ _

mutual
def SiblingChoices : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    CKTree.PunctureAt H context address → Type (max (max u v) w)
  | _, _, _, _, .root => PUnit.{max (max u v) w + 1}
  | _, _, _, _, .child _ _ _ _ below => ChildSiblingChoices below

def ChildSiblingChoices : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    CKChildren.PunctureAt H children slot address → Type (max (max u v) w)
  | _, _, _, _, _, .head _ tail _ below =>
      SiblingChoices below × CKChildCuts tail
  | _, _, _, _, _, .tail head _ _ _ below =>
      CKBranchCut head × ChildSiblingChoices below
end

mutual
def noSpineSplit : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → NoSpine hole payload →
    CKBranchCut payload × SiblingChoices hole
  | _, _, _, _, .root, _, cut => (cut, PUnit.unit)
  | _, _, _, _, .child _ _ _ _ below, payload, choice =>
      noSpineSplitChildren below payload choice

def noSpineSplitChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → ChildNoSpine hole payload →
    CKBranchCut payload × ChildSiblingChoices hole
  | _, _, _, _, _, .head _ _ _ below, payload, choice =>
      let selected := noSpineSplit below payload choice.1
      (selected.1, (selected.2, choice.2))
  | _, _, _, _, _, .tail _ _ _ _ below, payload, choice =>
      let selected := noSpineSplitChildren below payload choice.2
      (selected.1, (choice.1, selected.2))
end

mutual
def noSpineJoin : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) →
    CKBranchCut payload × SiblingChoices hole → NoSpine hole payload
  | _, _, _, _, .root, _, choice => choice.1
  | _, _, _, _, .child _ _ _ _ below, payload, choice =>
      noSpineJoinChildren below payload choice

def noSpineJoinChildren : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    CKBranchCut payload × ChildSiblingChoices hole → ChildNoSpine hole payload
  | _, _, _, _, _, .head _ _ _ below, payload, choice =>
      (noSpineJoin below payload (choice.1, choice.2.1), choice.2.2)
  | _, _, _, _, _, .tail _ _ _ _ below, payload, choice =>
      (choice.2.1, noSpineJoinChildren below payload (choice.1, choice.2.2))
end

mutual
theorem noSpineJoin_split : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (choice : NoSpine hole payload) →
    noSpineJoin hole payload (noSpineSplit hole payload choice) = choice
  | _, _, _, _, .root, _, _ => rfl
  | _, _, _, _, .child _ _ _ _ below, payload, choice =>
      noSpineJoinChildren_split below payload choice

theorem noSpineJoinChildren_split : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → (choice : ChildNoSpine hole payload) →
    noSpineJoinChildren hole payload (noSpineSplitChildren hole payload choice) = choice
  | _, _, _, _, _, .head _ _ _ below, payload, choice => by
      cases choice
      simp only [noSpineJoinChildren, noSpineSplitChildren, noSpineJoin_split]
  | _, _, _, _, _, .tail _ _ _ _ below, payload, choice => by
      cases choice
      simp only [noSpineJoinChildren, noSpineSplitChildren, noSpineJoinChildren_split]
end

mutual
theorem noSpineSplit_join : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) →
    (choice : CKBranchCut payload × SiblingChoices hole) →
    noSpineSplit hole payload (noSpineJoin hole payload choice) = choice
  | _, _, _, _, .root, _, choice => by cases choice with | mk cut unit => cases unit; rfl
  | _, _, _, _, .child _ _ _ _ below, payload, choice =>
      noSpineSplitChildren_join below payload choice

theorem noSpineSplitChildren_join : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    (choice : CKBranchCut payload × ChildSiblingChoices hole) →
    noSpineSplitChildren hole payload (noSpineJoinChildren hole payload choice) = choice
  | _, _, _, _, _, .head _ _ _ below, payload, choice => by
      have inverse := noSpineSplit_join below payload (choice.1, choice.2.1)
      simpa only [noSpineJoinChildren, noSpineSplitChildren] using
        congrArg (fun x => (x.1, (x.2, choice.2.2))) inverse
  | _, _, _, _, _, .tail _ _ _ _ below, payload, choice => by
      have inverse := noSpineSplitChildren_join below payload (choice.1, choice.2.2)
      simpa only [noSpineJoinChildren, noSpineSplitChildren] using
        congrArg (fun x => (x.1, (choice.2.1, x.2))) inverse
end

def noSpineEquiv {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H) :
    NoSpine hole payload ≃ CKBranchCut payload × SiblingChoices hole where
  toFun := noSpineSplit hole payload
  invFun := noSpineJoin hole payload
  left_inv := noSpineJoin_split hole payload
  right_inv := noSpineSplit_join hole payload

mutual
/-- Physical sibling choices of a composite spine are spliced without
commutative collection; the outer and inner tuple positions stay distinct. -/
def spliceSiblings : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    SiblingChoices (outer.insert_replacement inner) →
    SiblingChoices outer × SiblingChoices inner
  | _, _, _, _, _, _, .root, _, _, choice => (PUnit.unit, choice)
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choice =>
      spliceChildSiblings below inner choice

def spliceChildSiblings : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    ChildSiblingChoices (outer.insert_replacement inner) →
    ChildSiblingChoices outer × SiblingChoices inner
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, choice =>
      let selected := spliceSiblings below inner choice.1
      ((selected.1, choice.2), selected.2)
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, choice =>
      let selected := spliceChildSiblings below inner choice.2
      ((choice.1, selected.1), selected.2)
end

mutual
def unspliceSiblings : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    SiblingChoices outer × SiblingChoices inner →
    SiblingChoices (outer.insert_replacement inner)
  | _, _, _, _, _, _, .root, _, _, choice => choice.2
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choice =>
      unspliceChildSiblings below inner choice

def unspliceChildSiblings : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    ChildSiblingChoices outer × SiblingChoices inner →
    ChildSiblingChoices (outer.insert_replacement inner)
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, choice =>
      (unspliceSiblings below inner (choice.1.1, choice.2), choice.1.2)
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, choice =>
      (choice.1.1, unspliceChildSiblings below inner (choice.1.2, choice.2))
end

mutual
theorem unsplice_splice : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choice : SiblingChoices (outer.insert_replacement inner)) →
    unspliceSiblings outer inner (spliceSiblings outer inner choice) = choice
  | _, _, _, _, _, _, .root, _, _, _ => rfl
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choice =>
      unspliceChild_splice below inner choice

theorem unspliceChild_splice : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choice : ChildSiblingChoices (outer.insert_replacement inner)) →
    unspliceChildSiblings outer inner (spliceChildSiblings outer inner choice) = choice
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, choice => by
      cases choice
      simp only [unspliceChildSiblings, spliceChildSiblings, unsplice_splice]
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, choice => by
      cases choice
      simp only [unspliceChildSiblings, spliceChildSiblings, unspliceChild_splice]
end

mutual
theorem splice_unsplice : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choice : SiblingChoices outer × SiblingChoices inner) →
    spliceSiblings outer inner (unspliceSiblings outer inner choice) = choice
  | _, _, _, _, _, _, .root, _, _, choice => by
      cases choice with | mk unit inner => cases unit; rfl
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choice =>
      spliceChild_unsplice below inner choice

theorem spliceChild_unsplice : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choice : ChildSiblingChoices outer × SiblingChoices inner) →
    spliceChildSiblings outer inner (unspliceChildSiblings outer inner choice) = choice
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, choice => by
      have inverse := splice_unsplice below inner (choice.1.1, choice.2)
      simpa only [unspliceChildSiblings, spliceChildSiblings] using
        congrArg (fun x => ((x.1, choice.1.2), x.2)) inverse
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, choice => by
      have inverse := spliceChild_unsplice below inner (choice.1.2, choice.2)
      simpa only [unspliceChildSiblings, spliceChildSiblings] using
        congrArg (fun x => ((choice.1.1, x.1), x.2)) inverse
end

def siblingSpliceEquiv {G H K : Hypersequent sigma}
    {context : CKTree sigma InstanceData G}
    {outerAddress innerAddress : InternalAddress}
    (outer : CKTree.PunctureAt H context outerAddress)
    {innerContext : CKTree sigma InstanceData H}
    (inner : CKTree.PunctureAt K innerContext innerAddress) :
    SiblingChoices (outer.insert_replacement inner) ≃
      SiblingChoices outer × SiblingChoices inner where
  toFun := spliceSiblings outer inner
  invFun := unspliceSiblings outer inner
  left_inv := unsplice_splice outer inner
  right_inv := splice_unsplice outer inner

mutual
/-- An ancestor selected in the inner context receives all outer sibling
choices. An ancestor selected in the outer context swallows the inner context
and therefore has no choices from its siblings or payload. -/
def spliceAncestor : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    Ancestor (outer.insert_replacement inner) →
    (SiblingChoices outer × Ancestor inner) ⊕ Ancestor outer
  | _, _, _, _, _, _, .root, _, _, choice => .inl (PUnit.unit, choice)
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choice =>
      match choice with
      | Sum.inl unit => .inr (.inl unit)
      | Sum.inr choice =>
          match spliceChildAncestor below inner choice with
          | .inl choice => .inl choice
          | .inr choice => .inr (.inr choice)

def spliceChildAncestor : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    ChildAncestor (outer.insert_replacement inner) →
    (ChildSiblingChoices outer × Ancestor inner) ⊕ ChildAncestor outer
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, choice =>
      match spliceAncestor below inner choice.1 with
      | .inl selected => .inl ((selected.1, choice.2), selected.2)
      | .inr selected => .inr (selected, choice.2)
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, choice =>
      match spliceChildAncestor below inner choice.2 with
      | .inl selected => .inl ((choice.1, selected.1), selected.2)
      | .inr selected => .inr (choice.1, selected)
end

mutual
def unspliceAncestor : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (SiblingChoices outer × Ancestor inner) ⊕ Ancestor outer →
    Ancestor (outer.insert_replacement inner)
  | _, _, _, _, _, _, .root, _, _, .inl choice => choice.2
  | _, _, _, _, _, _, .root, _, _, .inr impossible => nomatch impossible
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choice =>
      match choice with
      | .inl choice => .inr (unspliceChildAncestor below inner (.inl choice))
      | .inr ancestor =>
          match ancestor with
          | Sum.inl unit => .inl unit
          | Sum.inr ancestor => .inr (unspliceChildAncestor below inner (.inr ancestor))

def unspliceChildAncestor : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (ChildSiblingChoices outer × Ancestor inner) ⊕ ChildAncestor outer →
    ChildAncestor (outer.insert_replacement inner)
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, .inl choice =>
      (unspliceAncestor below inner (.inl (choice.1.1, choice.2)), choice.1.2)
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, .inr choice =>
      (unspliceAncestor below inner (.inr choice.1), choice.2)
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, .inl choice =>
      (choice.1.1, unspliceChildAncestor below inner (.inl (choice.1.2, choice.2)))
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, .inr choice =>
      (choice.1, unspliceChildAncestor below inner (.inr choice.2))
end

mutual
theorem unspliceAncestor_splice : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choice : Ancestor (outer.insert_replacement inner)) →
    unspliceAncestor outer inner (spliceAncestor outer inner choice) = choice
  | _, _, _, _, _, _, .root, _, _, _ => rfl
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choice => by
      change PUnit.{max (max u v) w + 1} ⊕
        ChildAncestor (below.insert_replacement inner) at choice
      cases choice with
      | inl unit => rfl
      | inr choice =>
          have inverse := unspliceChildAncestor_splice below inner choice
          generalize equal : spliceChildAncestor below inner choice = result at *
          cases result <;> simpa only [spliceAncestor, unspliceAncestor, equal] using
            congrArg (Sum.inr : ChildAncestor (below.insert_replacement inner) →
              PUnit.{max (max u v) w + 1} ⊕
                ChildAncestor (below.insert_replacement inner)) inverse

theorem unspliceChildAncestor_splice : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choice : ChildAncestor (outer.insert_replacement inner)) →
    unspliceChildAncestor outer inner (spliceChildAncestor outer inner choice) = choice
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, choice => by
      have inverse := unspliceAncestor_splice below inner choice.1
      generalize equal : spliceAncestor below inner choice.1 = result at *
      cases result <;> simpa only [spliceChildAncestor, unspliceChildAncestor, equal] using
        congrArg (fun x => (x, choice.2)) inverse
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, choice => by
      have inverse := unspliceChildAncestor_splice below inner choice.2
      generalize equal : spliceChildAncestor below inner choice.2 = result at *
      cases result <;> simpa only [spliceChildAncestor, unspliceChildAncestor, equal] using
        congrArg (fun x => (choice.1, x)) inverse
end

mutual
theorem spliceAncestor_unsplice : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choice : (SiblingChoices outer × Ancestor inner) ⊕ Ancestor outer) →
    spliceAncestor outer inner (unspliceAncestor outer inner choice) = choice
  | _, _, _, _, _, _, .root, _, _, .inl choice => by
      cases choice with | mk unit ancestor => cases unit; rfl
  | _, _, _, _, _, _, .root, _, _, .inr impossible => nomatch impossible
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choice => by
      cases choice with
      | inl choice =>
          simp only [spliceAncestor, unspliceAncestor, spliceChildAncestor_unsplice]
      | inr ancestor =>
          change PUnit.{max (max u v) w + 1} ⊕ ChildAncestor below at ancestor
          cases ancestor with
          | inl unit => rfl
          | inr ancestor =>
              simp only [spliceAncestor, unspliceAncestor, spliceChildAncestor_unsplice]

theorem spliceChildAncestor_unsplice : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choice : (ChildSiblingChoices outer × Ancestor inner) ⊕ ChildAncestor outer) →
    spliceChildAncestor outer inner (unspliceChildAncestor outer inner choice) = choice
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, .inl choice => by
      simp only [spliceChildAncestor, unspliceChildAncestor, spliceAncestor_unsplice]
      simp only [Prod.eta]
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, .inr choice => by
      simp only [spliceChildAncestor, unspliceChildAncestor, spliceAncestor_unsplice]
      simp only [Prod.eta]
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, .inl choice => by
      simp only [spliceChildAncestor, unspliceChildAncestor, spliceChildAncestor_unsplice]
      simp only [Prod.eta]
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, .inr choice => by
      simp only [spliceChildAncestor, unspliceChildAncestor, spliceChildAncestor_unsplice]
      simp only [Prod.eta]
end

def ancestorSpliceEquiv {G H K : Hypersequent sigma}
    {context : CKTree sigma InstanceData G}
    {outerAddress innerAddress : InternalAddress}
    (outer : CKTree.PunctureAt H context outerAddress)
    {innerContext : CKTree sigma InstanceData H}
    (inner : CKTree.PunctureAt K innerContext innerAddress) :
    Ancestor (outer.insert_replacement inner) ≃
      (SiblingChoices outer × Ancestor inner) ⊕ Ancestor outer where
  toFun := spliceAncestor outer inner
  invFun := unspliceAncestor outer inner
  left_inv := unspliceAncestor_splice outer inner
  right_inv := spliceAncestor_unsplice outer inner

#print axioms noSpineEquiv
#print axioms siblingSpliceEquiv
#print axioms ancestorSpliceEquiv

mutual
/-- The no-spine operator's literal typed state. Only off-spine siblings are
pruned; the pointed payload is an arbitrary native state, not necessarily a
remainder in the image of a coaction. -/
def graftState : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) → SiblingChoices hole →
    CKTree sigma InstanceData H → CKTree sigma InstanceData G
  | _, _, _, _, .root, _, payload => payload
  | _, _, _, _, .child o _ _ _ below, siblings, payload =>
      .ordinary o (graftChildState below siblings payload)

def graftChildState : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    ChildSiblingChoices hole → CKTree sigma InstanceData H →
    CKChildren sigma InstanceData Gs
  | _, _, _, _, _, .head _ _ _ below, siblings, payload =>
      .cons (graftState below siblings.1 payload) siblings.2.remainder
  | _, _, _, _, _, .tail _ _ _ _ below, siblings, payload =>
      .cons siblings.1.remainder (graftChildState below siblings.2 payload)
end

mutual
/-- State equality under actual choice splicing, stronger than boundary
equality or equality of collected coefficients. -/
theorem graftState_compose : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choices : SiblingChoices outer × SiblingChoices inner) →
    (payload : CKTree sigma InstanceData K) →
    graftState (outer.insert_replacement inner)
      (unspliceSiblings outer inner choices) payload =
      graftState outer choices.1 (graftState inner choices.2 payload)
  | _, _, _, _, _, _, .root, _, _, _, _ => rfl
  | _, _, _, _, _, _, .child o _ _ _ below, _, inner, choices, payload => by
      change CKTree.ordinary o
          (graftChildState (below.insert_replacement inner)
            (unspliceChildSiblings below inner choices) payload) =
        CKTree.ordinary o
          (graftChildState below choices.1 (graftState inner choices.2 payload))
      rw [graftChildState_compose below inner choices payload]

theorem graftChildState_compose : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choices : ChildSiblingChoices outer × SiblingChoices inner) →
    (payload : CKTree sigma InstanceData K) →
    graftChildState (outer.insert_replacement inner)
      (unspliceChildSiblings outer inner choices) payload =
      graftChildState outer choices.1 (graftState inner choices.2 payload)
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, choices, payload => by
      exact congrArg (fun tree => CKChildren.cons tree choices.1.2.remainder)
        (graftState_compose below inner (choices.1.1, choices.2) payload)
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, choices, payload => by
      exact congrArg (fun children => CKChildren.cons choices.1.1.remainder children)
        (graftChildState_compose below inner (choices.1.2, choices.2) payload)
end

mutual
def noSpineCut : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → CKBranchCut payload →
    SiblingChoices hole → CKBranchCut (hole.insert payload)
  | _, _, _, _, .root, _, cut, _ => cut
  | _, _, _, _, .child o _ _ _ below, payload, cut, siblings =>
      .descend (.ordinary o _ (noSpineChildCut below payload cut siblings))

def noSpineChildCut : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → CKBranchCut payload →
    ChildSiblingChoices hole → CKChildCuts (hole.insert payload)
  | _, _, _, _, _, .head _ tail _ below, payload, cut, siblings =>
      .cons _ tail (noSpineCut below payload cut siblings.1) siblings.2
  | _, _, _, _, _, .tail head _ _ _ below, payload, cut, siblings =>
      .cons head _ siblings.1 (noSpineChildCut below payload cut siblings.2)
end

mutual
/-- The concrete no-spine cut has exactly the grafted native remainder. -/
theorem noSpineCut_remainder : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (cut : CKBranchCut payload) →
    (siblings : SiblingChoices hole) →
    (noSpineCut hole payload cut siblings).remainder =
      graftState hole siblings cut.remainder
  | _, _, _, _, .root, _, _, _ => rfl
  | _, _, _, _, .child o _ _ _ below, payload, cut, siblings => by
      change CKTree.ordinary o
          (noSpineChildCut below payload cut siblings).remainder =
        CKTree.ordinary o (graftChildState below siblings cut.remainder)
      rw [noSpineChildCut_remainder below payload cut siblings]

theorem noSpineChildCut_remainder : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → (cut : CKBranchCut payload) →
    (siblings : ChildSiblingChoices hole) →
    (noSpineChildCut hole payload cut siblings).remainder =
      graftChildState hole siblings cut.remainder
  | _, _, _, _, _, .head _ _ _ below, payload, cut, siblings => by
      simp only [noSpineChildCut, CKChildCuts.remainder, graftChildState]
      rw [noSpineCut_remainder below payload cut siblings.1]
  | _, _, _, _, _, .tail _ _ _ _ below, payload, cut, siblings => by
      simp only [noSpineChildCut, CKChildCuts.remainder, graftChildState]
      rw [noSpineChildCut_remainder below payload cut siblings.2]
end

mutual
theorem noSpineCut_eq_assembled : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (cut : CKBranchCut payload) →
    (siblings : SiblingChoices hole) →
    noSpineCut hole payload cut siblings =
      assemble hole payload (merge hole payload
        (.inl (noSpineJoin hole payload (cut, siblings))))
  | _, _, _, _, .root, _, _, _ => rfl
  | _, _, _, _, .child o _ _ _ below, payload, cut, siblings => by
      simp only [noSpineCut, assemble, merge, noSpineJoin]
      rw [noSpineChildCut_eq_assembled below payload cut siblings]
      rfl

theorem noSpineChildCut_eq_assembled : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → (cut : CKBranchCut payload) →
    (siblings : ChildSiblingChoices hole) →
    noSpineChildCut hole payload cut siblings =
      assembleChildren hole payload (mergeChildren hole payload
        (.inl (noSpineJoinChildren hole payload (cut, siblings))))
  | _, _, _, _, _, .head _ _ _ below, payload, cut, siblings => by
      simp only [noSpineChildCut, assembleChildren, mergeChildren, noSpineJoinChildren]
      rw [noSpineCut_eq_assembled below payload cut siblings.1]
  | _, _, _, _, _, .tail _ _ _ _ below, payload, cut, siblings => by
      simp only [noSpineChildCut, assembleChildren, mergeChildren, noSpineJoinChildren]
      rw [noSpineChildCut_eq_assembled below payload cut siblings.2]
end

/-- All occurrence matching and physical order are obtained before collection
from the verified native full-packet equivalence. -/
theorem noSpineCut_refill {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H) (cut : CKBranchCut payload)
    (siblings : SiblingChoices hole) :
    let assembled := noSpineCut hole payload cut siblings
    assembled.fill assembled.detached = hole.insert payload :=
  CKBranchCut.fill_detached_reconstructs _

#print axioms graftState_compose
#print axioms noSpineCut_remainder
#print axioms noSpineCut_eq_assembled
#print axioms noSpineCut_refill

/-- Explicit commutative projection of the already retained ordered native
packet. This forgets addresses and order only at the coefficient layer. -/
def branchForest {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree) :
    CKForest sigma InstanceData :=
  ↑((orderedPacket cut).map fun entry =>
    ({ boundary := entry.boundary, tree := entry.tree,
       ordinary := entry.ordinary } : CKComponent sigma InstanceData))

mutual
def planForest : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → CKCutPlan tree →
    CKForest sigma InstanceData
  | _, _, .interface _ => 0
  | _, _, .ordinary _ _ cuts => childForest cuts

def childForest : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → CKChildCuts children →
    CKForest sigma InstanceData
  | _, _, .nil => 0
  | _, _, .cons _ _ head tail => branchForest head + childForest tail
end

mutual
theorem planForest_packet : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    planForest cut = ↑(cut.siteOrder.map fun site =>
      ({ boundary := cut.siteBoundary site, tree := cut.detached site,
         ordinary := cut.detachedOrdinary site } : CKComponent sigma InstanceData))
  | _, _, .interface _ => rfl
  | _, _, .ordinary _ _ cuts => childForest_packet cuts

theorem childForest_packet : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    childForest cuts = ↑(cuts.siteOrder.map fun site =>
      ({ boundary := cuts.siteBoundary site, tree := cuts.detached site,
         ordinary := cuts.detachedOrdinary site } : CKComponent sigma InstanceData))
  | _, _, .nil => rfl
  | _, _, .cons headTree tailTree head tail => by
      rw [childForest, childForest_packet tail]
      simp only [branchForest, orderedPacket, CKChildCuts.siteOrder]
      simp only [List.map_append, List.map_map, Function.comp_def, CKChildCuts.siteBoundary,
        CKChildCuts.detached, CKChildCuts.detachedOrdinary]
      apply congrArg (fun entries : List (CKComponent sigma InstanceData) =>
        (↑entries : CKForest sigma InstanceData))
      let encode : (CKChildCuts.cons headTree tailTree head tail).Site →
          CKComponent sigma InstanceData := fun site =>
        ⟨(CKChildCuts.cons headTree tailTree head tail).siteBoundary site,
          (CKChildCuts.cons headTree tailTree head tail).detached site,
          (CKChildCuts.cons headTree tailTree head tail).detachedOrdinary site⟩
      have distribution := List.map_append (f := encode)
        (l₁ := head.siteOrder.map Sum.inl) (l₂ := tail.siteOrder.map Sum.inr)
      have composition := congrArg₂ List.append
        (List.map_map (g := encode) (f := Sum.inl) (l := head.siteOrder))
        (List.map_map (g := encode) (f := Sum.inr) (l := tail.siteOrder))
      exact (distribution.trans composition).symm
end

@[simp] theorem branchForest_descend {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCutPlan tree) :
    branchForest (.descend cut) = planForest cut := by
  rw [planForest_packet]
  simp only [branchForest, orderedPacket, CKBranchCut.siteOrder,
    CKBranchCut.siteBoundary, CKBranchCut.detached, CKBranchCut.detachedOrdinary,
    List.map_map, Function.comp_def]
  rfl

@[simp] theorem branchForest_detach {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (ordinary : tree.IsOrdinary) :
    branchForest (.detach ordinary) =
      {({ boundary := G, tree := tree, ordinary := ordinary } :
        CKComponent sigma InstanceData)} := rfl

mutual
def siblingForest : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) → SiblingChoices hole →
    CKForest sigma InstanceData
  | _, _, _, _, .root, _ => 0
  | _, _, _, _, .child _ _ _ _ below, choices => childSiblingForest below choices

def childSiblingForest : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    ChildSiblingChoices hole → CKForest sigma InstanceData
  | _, _, _, _, _, .head _ _ _ below, choices =>
      siblingForest below choices.1 + childForest choices.2
  | _, _, _, _, _, .tail _ _ _ _ below, choices =>
      branchForest choices.1 + childSiblingForest below choices.2
end

mutual
theorem siblingForest_compose : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choices : SiblingChoices outer × SiblingChoices inner) →
    siblingForest (outer.insert_replacement inner)
      (unspliceSiblings outer inner choices) =
      siblingForest outer choices.1 + siblingForest inner choices.2
  | _, _, _, _, _, _, .root, _, _, _ => (zero_add _).symm
  | _, _, _, _, _, _, .child _ _ _ _ below, _, inner, choices =>
      childSiblingForest_compose below inner choices

theorem childSiblingForest_compose : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (choices : ChildSiblingChoices outer × SiblingChoices inner) →
    childSiblingForest (outer.insert_replacement inner)
      (unspliceChildSiblings outer inner choices) =
      childSiblingForest outer choices.1 + siblingForest inner choices.2
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, choices => by
      exact (congrArg (fun forest => forest + childForest choices.1.2)
        (siblingForest_compose below inner (choices.1.1, choices.2))).trans
        (add_right_comm _ _ _)
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, choices => by
      exact (congrArg (fun forest => branchForest choices.1.1 + forest)
        (childSiblingForest_compose below inner (choices.1.2, choices.2))).trans
        (add_assoc _ _ _).symm
end

mutual
theorem noSpineCut_forest : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (cut : CKBranchCut payload) →
    (siblings : SiblingChoices hole) →
    branchForest (noSpineCut hole payload cut siblings) =
      branchForest cut + siblingForest hole siblings
  | _, _, _, _, .root, _, _, _ => (add_zero _).symm
  | _, _, _, _, .child _ _ _ _ below, payload, cut, siblings => by
      simp only [noSpineCut, branchForest_descend, planForest, siblingForest]
      exact noSpineChildCut_forest below payload cut siblings

theorem noSpineChildCut_forest : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → (cut : CKBranchCut payload) →
    (siblings : ChildSiblingChoices hole) →
    childForest (noSpineChildCut hole payload cut siblings) =
      branchForest cut + childSiblingForest hole siblings
  | _, _, _, _, _, .head _ _ _ below, payload, cut, siblings => by
      simp only [noSpineChildCut, childForest, childSiblingForest]
      rw [noSpineCut_forest below payload cut siblings.1]
      exact add_assoc _ _ _
  | _, _, _, _, _, .tail _ _ _ _ below, payload, cut, siblings => by
      simp only [noSpineChildCut, childForest, childSiblingForest]
      rw [noSpineChildCut_forest below payload cut siblings.2]
      exact add_left_comm _ _ _
end

noncomputable section

instance branchFintype {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    Fintype (CKBranchCut tree) := by
  classical
  exact Fintype.ofList tree.enumerateBranchCuts CKBranchCut.mem_enumerate

instance childFintype {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData Gs) : Fintype (CKChildCuts children) := by
  classical
  exact Fintype.ofList children.enumerateCuts CKChildCuts.mem_enumerate

mutual
def siblingsFintype : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) → Fintype (SiblingChoices hole)
  | _, _, _, _, .root => by
      change Fintype PUnit.{max (max u v) w + 1}
      infer_instance
  | _, _, _, _, .child _ _ _ _ below => childSiblingsFintype below

def childSiblingsFintype : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    Fintype (ChildSiblingChoices hole)
  | _, _, _, _, _, .head _ tail _ below => by
      letI := siblingsFintype below
      change Fintype (SiblingChoices below × CKChildCuts tail)
      exact inferInstance
  | _, _, _, _, _, .tail head _ _ _ below => by
      letI := childSiblingsFintype below
      change Fintype (CKBranchCut head × ChildSiblingChoices below)
      exact inferInstance
end

instance {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) : Fintype (SiblingChoices hole) :=
  siblingsFintype hole

/-- The existing native commutative forest and literal typed state, paired
only as coefficient basis metadata. -/
abbrev ExtractionBasis (G : Hypersequent sigma) :=
  CKForest sigma InstanceData × CKTree sigma InstanceData G

abbrev ExtractionRecords (G : Hypersequent sigma) :=
  FreeAbelianGroup (ExtractionBasis (InstanceData := InstanceData) G)

abbrev States (G : Hypersequent sigma) :=
  FreeAbelianGroup (CKTree sigma InstanceData G)

def G {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) :
    States (InstanceData := InstanceData) H →+ States (InstanceData := InstanceData) G :=
  FreeAbelianGroup.lift fun payload => FreeAbelianGroup.of (hole.insert payload)

def L {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) :
    ExtractionRecords (InstanceData := InstanceData) H →+
      ExtractionRecords (InstanceData := InstanceData) G :=
  FreeAbelianGroup.lift fun record => ∑ siblings : SiblingChoices hole,
    FreeAbelianGroup.of
      (record.1 + siblingForest hole siblings, graftState hole siblings record.2)

/-- Universal finite-sum no-spine composition, on arbitrary signed extraction
records. It is not restricted to coaction images. The proof uses the actual
sibling-choice bijection and both the coefficient and literal state laws. -/
theorem L_compose {G H K : Hypersequent sigma}
    {context : CKTree sigma InstanceData G}
    {outerAddress innerAddress : InternalAddress}
    (outer : CKTree.PunctureAt H context outerAddress)
    {innerContext : CKTree sigma InstanceData H}
    (inner : CKTree.PunctureAt K innerContext innerAddress) :
    L (outer.insert_replacement inner) = (L outer).comp (L inner) := by
  apply FreeAbelianGroup.lift_ext
  intro record
  simp only [L, AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of, map_sum]
  rw [Finset.sum_comm]
  rw [← sum_pair (fun choices : SiblingChoices outer × SiblingChoices inner =>
    FreeAbelianGroup.of
      (record.1 + siblingForest inner choices.2 + siblingForest outer choices.1,
        graftState outer choices.1 (graftState inner choices.2 record.2)))]
  symm
  apply Fintype.sum_equiv (siblingSpliceEquiv outer inner).symm
  intro choices
  change FreeAbelianGroup.of
      (record.1 + siblingForest inner choices.2 + siblingForest outer choices.1,
        graftState outer choices.1 (graftState inner choices.2 record.2)) =
    FreeAbelianGroup.of
      (record.1 + siblingForest (outer.insert_replacement inner)
        (unspliceSiblings outer inner choices),
        graftState (outer.insert_replacement inner)
          (unspliceSiblings outer inner choices) record.2)
  rw [siblingForest_compose, graftState_compose]
  simp only [add_assoc, add_comm, add_left_comm]

#print axioms siblingForest_compose
#print axioms noSpineCut_forest
#print axioms L_compose

mutual
/-- Concrete ancestor term, retaining its actual native filled subtree factor
and its literal typed residual state. -/
def ancestorEffect : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → Ancestor hole →
    ExtractionBasis (InstanceData := InstanceData) G
  | _, _, _, _, .root, _, impossible => nomatch impossible
  | _, _, _, _, .child o _ _ _ below, payload, ancestor =>
      match ancestor with
      | Sum.inl _ =>
          ({({ boundary := o.shape.conclusion, tree := .ordinary o (below.insert payload),
               ordinary := trivial } : CKComponent sigma InstanceData)},
            .interface o.shape.conclusion)
      | Sum.inr ancestor =>
          let result := childAncestorEffect below payload ancestor
          (result.1, .ordinary o result.2)

def childAncestorEffect : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → ChildAncestor hole →
    CKForest sigma InstanceData × CKChildren sigma InstanceData Gs
  | _, _, _, _, _, .head _ _ _ below, payload, ancestor =>
      let result := ancestorEffect below payload ancestor.1
      (result.1 + childForest ancestor.2, .cons result.2 ancestor.2.remainder)
  | _, _, _, _, _, .tail _ _ _ _ below, payload, ancestor =>
      let result := childAncestorEffect below payload ancestor.2
      (branchForest ancestor.1 + result.1, .cons ancestor.1.remainder result.2)
end

mutual
def ancestorCut : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → Ancestor hole →
    CKBranchCut (hole.insert payload)
  | _, _, _, _, .root, _, impossible => nomatch impossible
  | _, _, _, _, .child o _ _ _ below, payload, ancestor =>
      match ancestor with
      | Sum.inl _ => .detach trivial
      | Sum.inr ancestor => .descend (.ordinary o _ (childAncestorCut below payload ancestor))

def childAncestorCut : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → ChildAncestor hole →
    CKChildCuts (hole.insert payload)
  | _, _, _, _, _, .head _ tail _ below, payload, ancestor =>
      .cons _ tail (ancestorCut below payload ancestor.1) ancestor.2
  | _, _, _, _, _, .tail head _ _ _ below, payload, ancestor =>
      .cons head _ ancestor.1 (childAncestorCut below payload ancestor.2)
end

mutual
theorem ancestorCut_eq_assembled : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (ancestor : Ancestor hole) →
    ancestorCut hole payload ancestor =
      assemble hole payload (merge hole payload (.inr ancestor))
  | _, _, _, _, .root, _, impossible => nomatch impossible
  | _, _, _, _, .child _ _ _ _ below, payload, ancestor => by
      change PUnit.{max (max u v) w + 1} ⊕ ChildAncestor below at ancestor
      cases ancestor with
      | inl unit => rfl
      | inr ancestor =>
          simp only [ancestorCut, assemble, merge]
          rw [childAncestorCut_eq_assembled below payload ancestor]

theorem childAncestorCut_eq_assembled : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → (ancestor : ChildAncestor hole) →
    childAncestorCut hole payload ancestor =
      assembleChildren hole payload (mergeChildren hole payload (.inr ancestor))
  | _, _, _, _, _, .head _ _ _ below, payload, ancestor => by
      simp only [childAncestorCut, assembleChildren, mergeChildren]
      rw [ancestorCut_eq_assembled below payload ancestor.1]
  | _, _, _, _, _, .tail _ _ _ _ below, payload, ancestor => by
      simp only [childAncestorCut, assembleChildren, mergeChildren]
      rw [childAncestorCut_eq_assembled below payload ancestor.2]
end

mutual
theorem ancestorCut_effect : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (ancestor : Ancestor hole) →
    (branchForest (ancestorCut hole payload ancestor),
      (ancestorCut hole payload ancestor).remainder) = ancestorEffect hole payload ancestor
  | _, _, _, _, .root, _, impossible => nomatch impossible
  | _, _, _, _, .child _ _ _ _ below, payload, ancestor => by
      change PUnit.{max (max u v) w + 1} ⊕ ChildAncestor below at ancestor
      cases ancestor with
      | inl unit => rfl
      | inr ancestor =>
          have result := childAncestorCut_effect below payload ancestor
          simpa only [ancestorCut, ancestorEffect, branchForest_descend, planForest,
            CKBranchCut.remainder, CKCutPlan.remainder] using
              congrArg (fun result => (result.1, CKTree.ordinary _ result.2)) result

theorem childAncestorCut_effect : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → (ancestor : ChildAncestor hole) →
    (childForest (childAncestorCut hole payload ancestor),
      (childAncestorCut hole payload ancestor).remainder) =
        childAncestorEffect hole payload ancestor
  | _, _, _, _, _, .head _ _ _ below, payload, ancestor => by
      have result := ancestorCut_effect below payload ancestor.1
      simpa only [childAncestorCut, childAncestorEffect, childForest,
        CKChildCuts.remainder] using
        congrArg (fun result => (result.1 + childForest ancestor.2,
          CKChildren.cons result.2 ancestor.2.remainder)) result
  | _, _, _, _, _, .tail _ _ _ _ below, payload, ancestor => by
      have result := childAncestorCut_effect below payload ancestor.2
      simpa only [childAncestorCut, childAncestorEffect, childForest,
        CKChildCuts.remainder] using
        congrArg (fun result => (branchForest ancestor.1 + result.1,
          CKChildren.cons ancestor.1.remainder result.2)) result
end

mutual
theorem ancestorEffect_inner : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (payload : CKTree sigma InstanceData K) →
    (choices : SiblingChoices outer × Ancestor inner) →
    ancestorEffect (outer.insert_replacement inner) payload
      (unspliceAncestor outer inner (.inl choices)) =
      (siblingForest outer choices.1 + (ancestorEffect inner payload choices.2).1,
        graftState outer choices.1 (ancestorEffect inner payload choices.2).2)
  | _, _, _, _, _, _, .root, _, _, _, _ => by
      simp only [CKTree.PunctureAt.insert_replacement, siblingForest, graftState,
        unspliceAncestor, zero_add, Prod.eta, id_eq]
      rfl
  | _, _, _, _, _, _, .child o _ _ _ below, _, inner, payload, choices => by
      have result := childAncestorEffect_inner below inner payload choices
      simpa only [CKTree.PunctureAt.insert_replacement, ancestorEffect,
        unspliceAncestor, siblingForest, graftState] using
        congrArg (fun result => (result.1, CKTree.ordinary o result.2)) result

theorem childAncestorEffect_inner : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (payload : CKTree sigma InstanceData K) →
    (choices : ChildSiblingChoices outer × Ancestor inner) →
    childAncestorEffect (outer.insert_replacement inner) payload
      (unspliceChildAncestor outer inner (.inl choices)) =
      (childSiblingForest outer choices.1 + (ancestorEffect inner payload choices.2).1,
        graftChildState outer choices.1 (ancestorEffect inner payload choices.2).2)
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, payload, choices => by
      have result := ancestorEffect_inner below inner payload (choices.1.1, choices.2)
      exact (congrArg (fun term =>
        (term.1 + childForest choices.1.2,
          CKChildren.cons term.2 choices.1.2.remainder)) result).trans
        (congrArg (fun forest => (forest,
          CKChildren.cons
            (graftState below choices.1.1 (ancestorEffect inner payload choices.2).2)
            choices.1.2.remainder)) (add_right_comm _ _ _))
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, payload, choices => by
      have result := childAncestorEffect_inner below inner payload (choices.1.2, choices.2)
      exact (congrArg (fun term =>
        (branchForest choices.1.1 + term.1,
          CKChildren.cons choices.1.1.remainder term.2)) result).trans
        (congrArg (fun forest => (forest,
          CKChildren.cons choices.1.1.remainder
            (graftChildState below choices.1.2 (ancestorEffect inner payload choices.2).2)))
          (add_assoc _ _ _).symm)
end

mutual
theorem ancestorEffect_outer : {G H K : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} →
    {outerAddress innerAddress : InternalAddress} →
    (outer : CKTree.PunctureAt H context outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (payload : CKTree sigma InstanceData K) → (ancestor : Ancestor outer) →
    ancestorEffect (outer.insert_replacement inner) payload
      (unspliceAncestor outer inner (.inr ancestor)) =
        ancestorEffect outer (inner.insert payload) ancestor
  | _, _, _, _, _, _, .root, _, _, _, impossible => nomatch impossible
  | _, _, _, _, _, _, .child o _ _ _ below, _, inner, payload, ancestor => by
      change PUnit.{max (max u v) w + 1} ⊕ ChildAncestor below at ancestor
      cases ancestor with
      | inl unit =>
          exact congrArg (fun (tuple : CKChildren sigma InstanceData o.shape.premises) =>
            (Multiset.cons
              (⟨o.shape.conclusion, CKTree.ordinary o tuple, trivial⟩ :
                CKComponent sigma InstanceData) 0,
              CKTree.interface o.shape.conclusion))
            (insertChildren_compose below inner payload)
      | inr ancestor =>
          exact congrArg (fun term => (term.1, CKTree.ordinary o term.2))
            (childAncestorEffect_outer below inner payload ancestor)

theorem childAncestorEffect_outer : {Gs : List (Hypersequent sigma)} →
    {H K : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {outerAddress innerAddress : InternalAddress} →
    (outer : CKChildren.PunctureAt H children slot outerAddress) →
    {innerContext : CKTree sigma InstanceData H} →
    (inner : CKTree.PunctureAt K innerContext innerAddress) →
    (payload : CKTree sigma InstanceData K) → (ancestor : ChildAncestor outer) →
    childAncestorEffect (outer.insert_replacement inner) payload
      (unspliceChildAncestor outer inner (.inr ancestor)) =
        childAncestorEffect outer (inner.insert payload) ancestor
  | _, _, _, _, _, _, _, .head _ _ _ below, _, inner, payload, ancestor => by
      exact congrArg (fun term =>
        (term.1 + childForest ancestor.2, CKChildren.cons term.2 ancestor.2.remainder))
        (ancestorEffect_outer below inner payload ancestor.1)
  | _, _, _, _, _, _, _, .tail _ _ _ _ below, _, inner, payload, ancestor => by
      exact congrArg (fun term =>
        (branchForest ancestor.1 + term.1, CKChildren.cons ancestor.1.remainder term.2))
        (childAncestorEffect_outer below inner payload ancestor.2)
end

mutual
def ancestorsFintype : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) → Fintype (Ancestor hole)
  | _, _, _, _, .root => by
      change Fintype PEmpty.{max (max u v) w + 1}
      infer_instance
  | _, _, _, _, .child _ _ _ _ below => by
      letI := childAncestorsFintype below
      change Fintype (PUnit.{max (max u v) w + 1} ⊕ ChildAncestor below)
      exact inferInstance

def childAncestorsFintype : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    Fintype (ChildAncestor hole)
  | _, _, _, _, _, .head _ tail _ below => by
      letI := ancestorsFintype below
      change Fintype (Ancestor below × CKChildCuts tail)
      exact inferInstance
  | _, _, _, _, _, .tail head _ _ _ below => by
      letI := childAncestorsFintype below
      change Fintype (CKBranchCut head × ChildAncestor below)
      exact inferInstance
end

instance {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) : Fintype (Ancestor hole) :=
  ancestorsFintype hole

def A {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) :
    States (InstanceData := InstanceData) H →+
      ExtractionRecords (InstanceData := InstanceData) G :=
  FreeAbelianGroup.lift fun payload => ∑ ancestor : Ancestor hole,
    FreeAbelianGroup.of (ancestorEffect hole payload ancestor)

theorem A_compose {G H K : Hypersequent sigma}
    {context : CKTree sigma InstanceData G}
    {outerAddress innerAddress : InternalAddress}
    (outer : CKTree.PunctureAt H context outerAddress)
    {innerContext : CKTree sigma InstanceData H}
    (inner : CKTree.PunctureAt K innerContext innerAddress) :
    A (outer.insert_replacement inner) =
      (L outer).comp (A inner) + (A outer).comp (ContextCutAction.G inner) := by
  apply FreeAbelianGroup.lift_ext
  intro payload
  simp only [A, ContextCutAction.G, L, AddMonoidHom.comp_apply, AddMonoidHom.add_apply,
    FreeAbelianGroup.lift_apply_of, map_sum]
  rw [Finset.sum_comm]
  rw [← sum_pair (fun choices : SiblingChoices outer × Ancestor inner =>
    FreeAbelianGroup.of
      ((ancestorEffect inner payload choices.2).1 + siblingForest outer choices.1,
        graftState outer choices.1 (ancestorEffect inner payload choices.2).2))]
  let alternative : (SiblingChoices outer × Ancestor inner) ⊕ Ancestor outer →
      ExtractionRecords (InstanceData := InstanceData) G := fun choice =>
    match choice with
    | .inl choices => FreeAbelianGroup.of
        ((ancestorEffect inner payload choices.2).1 + siblingForest outer choices.1,
          graftState outer choices.1 (ancestorEffect inner payload choices.2).2)
    | .inr ancestor => FreeAbelianGroup.of
        (ancestorEffect outer (inner.insert payload) ancestor)
  have reindex :
      (∑ ancestor : Ancestor (outer.insert_replacement inner),
        FreeAbelianGroup.of (ancestorEffect (outer.insert_replacement inner) payload ancestor)) =
      ∑ choice, alternative choice := by
    symm
    apply Fintype.sum_equiv (ancestorSpliceEquiv outer inner).symm
    intro choice
    cases choice with
    | inl choices =>
        change FreeAbelianGroup.of
            ((ancestorEffect inner payload choices.2).1 + siblingForest outer choices.1,
              graftState outer choices.1 (ancestorEffect inner payload choices.2).2) =
          FreeAbelianGroup.of
            (ancestorEffect (outer.insert_replacement inner) payload
              (unspliceAncestor outer inner (.inl choices)))
        rw [ancestorEffect_inner, add_comm]
    | inr ancestor =>
        change FreeAbelianGroup.of (ancestorEffect outer (inner.insert payload) ancestor) =
          FreeAbelianGroup.of
            (ancestorEffect (outer.insert_replacement inner) payload
              (unspliceAncestor outer inner (.inr ancestor)))
        rw [ancestorEffect_outer]
  rw [reindex, sum_alternatives]

#print axioms ancestorCut_effect
#print axioms ancestorEffect_inner
#print axioms ancestorEffect_outer
#print axioms A_compose

instance {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address)
    (payload : CKTree sigma InstanceData H) : Fintype (NoSpine hole payload) :=
  Fintype.ofEquiv (CKBranchCut payload × SiblingChoices hole) (noSpineEquiv hole payload).symm

def delta {G : Hypersequent sigma} :
    States (InstanceData := InstanceData) G →+
      ExtractionRecords (InstanceData := InstanceData) G :=
  FreeAbelianGroup.lift fun tree => ∑ cut : CKBranchCut tree,
    FreeAbelianGroup.of (branchForest cut, cut.remainder)

/-- Universal full-branch context coaction identity, derived by finite-sum
reindexing of native cuts before coefficient collection. -/
theorem delta_context {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) :
    delta.comp (ContextCutAction.G hole) = (L hole).comp delta + A hole := by
  apply FreeAbelianGroup.lift_ext
  intro payload
  simp only [delta, ContextCutAction.G, L, A, AddMonoidHom.comp_apply,
    AddMonoidHom.add_apply, FreeAbelianGroup.lift_apply_of, map_sum]
  calc
    (∑ cut : CKBranchCut (hole.insert payload),
      FreeAbelianGroup.of (branchForest cut, cut.remainder)) =
      ∑ choice : NoSpine hole payload ⊕ Ancestor hole,
        FreeAbelianGroup.of
          (branchForest ((fullPacketEquiv hole payload).symm choice),
            ((fullPacketEquiv hole payload).symm choice).remainder) := by
          apply Fintype.sum_equiv (fullPacketEquiv hole payload)
          intro cut
          rw [Equiv.symm_apply_apply]
    _ = (∑ cut : CKBranchCut payload, ∑ siblings : SiblingChoices hole,
        FreeAbelianGroup.of
          (branchForest cut + siblingForest hole siblings,
            graftState hole siblings cut.remainder)) +
        ∑ ancestor : Ancestor hole,
          FreeAbelianGroup.of (ancestorEffect hole payload ancestor) := by
      rw [sum_alternatives]
      congr 1
      · rw [← sum_pair (fun pair : CKBranchCut payload × SiblingChoices hole =>
          FreeAbelianGroup.of
            (branchForest pair.1 + siblingForest hole pair.2,
              graftState hole pair.2 pair.1.remainder))]
        symm
        apply Fintype.sum_equiv (noSpineEquiv hole payload).symm
        intro pair
        change FreeAbelianGroup.of
            (branchForest pair.1 + siblingForest hole pair.2,
              graftState hole pair.2 pair.1.remainder) =
          FreeAbelianGroup.of
            (branchForest (assemble hole payload (merge hole payload
              (.inl (noSpineJoin hole payload pair)))),
              (assemble hole payload (merge hole payload
                (.inl (noSpineJoin hole payload pair)))).remainder)
        rw [← noSpineCut_eq_assembled, noSpineCut_forest, noSpineCut_remainder]
      · apply Finset.sum_congr rfl
        intro ancestor _
        change FreeAbelianGroup.of
            (branchForest (assemble hole payload (merge hole payload (.inr ancestor))),
              (assemble hole payload (merge hole payload (.inr ancestor))).remainder) = _
        rw [← ancestorCut_eq_assembled, ancestorCut_effect]

#print axioms delta_context

mutual
def emptyPlan : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → CKCutPlan tree
  | _, .interface G => .interface G
  | _, .ordinary o children => .ordinary o children (emptyChildren children)

def emptyChildren : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → CKChildCuts children
  | _, .nil => .nil
  | _, .cons head tail => .cons head tail (.descend (emptyPlan head)) (emptyChildren tail)
end

def emptyBranch {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    CKBranchCut tree := .descend (emptyPlan tree)

mutual
@[simp] theorem emptyPlan_remainder : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (emptyPlan tree).remainder = tree
  | _, .interface _ => rfl
  | _, .ordinary _ children => by
      simp only [emptyPlan, CKCutPlan.remainder, emptyChildren_remainder]

@[simp] theorem emptyChildren_remainder : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (emptyChildren children).remainder = children
  | _, .nil => rfl
  | _, .cons head tail => by
      simp only [emptyChildren, CKChildCuts.remainder, CKBranchCut.remainder,
        emptyPlan_remainder, emptyChildren_remainder]
end

@[simp] theorem emptyBranch_remainder {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) : (emptyBranch tree).remainder = tree :=
  emptyPlan_remainder tree

mutual
@[simp] theorem emptyPlan_forest : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → planForest (emptyPlan tree) = 0
  | _, .interface _ => rfl
  | _, .ordinary _ children => emptyChildren_forest children

@[simp] theorem emptyChildren_forest : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → childForest (emptyChildren children) = 0
  | _, .nil => rfl
  | _, .cons _ tail => by
      simp only [emptyChildren, childForest, branchForest_descend,
        emptyPlan_forest, emptyChildren_forest, zero_add]
end

@[simp] theorem emptyBranch_forest {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) : branchForest (emptyBranch tree) = 0 := by
  simp only [emptyBranch, branchForest_descend, emptyPlan_forest]

private theorem forest_add_zero (left right : CKForest sigma InstanceData) :
    left + right = 0 ↔ left = 0 ∧ right = 0 := by
  constructor
  · intro zero
    have cards := congrArg Multiset.card zero
    simp only [Multiset.card_add, Multiset.card_zero, Nat.add_eq_zero] at cards
    exact ⟨Multiset.card_eq_zero.mp cards.1, Multiset.card_eq_zero.mp cards.2⟩
  · rintro ⟨rfl, rfl⟩
    exact add_zero 0

mutual
theorem planForest_zero_iff : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    planForest cut = 0 ↔ cut = emptyPlan tree
  | _, _, .interface _ => by simp only [planForest, emptyPlan]
  | _, _, .ordinary o children cuts => by
      rw [planForest, childrenForest_zero_iff]
      exact ⟨fun h => by rw [h]; rfl, fun h => by injection h⟩

theorem childrenForest_zero_iff : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
    childForest cuts = 0 ↔ cuts = emptyChildren children
  | _, _, .nil => by simp only [childForest, emptyChildren]
  | _, _, .cons head tail headCut tailCuts => by
      rw [childForest]
      have zeroSum : branchForest headCut + childForest tailCuts = 0 ↔
          branchForest headCut = 0 ∧ childForest tailCuts = 0 := by
        exact forest_add_zero _ _
      rw [zeroSum, branchForest_zero_iff, childrenForest_zero_iff]
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro equal
        have components := congrArg CKChildCuts.contents equal
        exact ⟨congrArg Prod.fst components, congrArg Prod.snd components⟩

theorem branchForest_zero_iff : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    branchForest cut = 0 ↔ cut = emptyBranch tree
  | _, _, .detach ordinary => by
      constructor
      · intro zero
        exact False.elim (Multiset.singleton_ne_zero _ zero)
      · intro impossible
        cases impossible
  | _, _, .descend plan => by
      rw [branchForest_descend, planForest_zero_iff]
      exact ⟨fun h => congrArg CKBranchCut.descend h,
        fun h => by injection h⟩
end

mutual
def emptySiblings : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) → SiblingChoices hole
  | _, _, _, _, .root => PUnit.unit
  | _, _, _, _, .child _ _ _ _ below => emptyChildSiblings below

def emptyChildSiblings : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) → ChildSiblingChoices hole
  | _, _, _, _, _, .head _ tail _ below => (emptySiblings below, emptyChildren tail)
  | _, _, _, _, _, .tail head _ _ _ below => (emptyBranch head, emptyChildSiblings below)
end

mutual
theorem siblingForest_zero_iff : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) → (choices : SiblingChoices hole) →
    siblingForest hole choices = 0 ↔ choices = emptySiblings hole
  | _, _, _, _, .root, choices => by
      cases choices
      simp only [siblingForest, emptySiblings]
  | _, _, _, _, .child _ _ _ _ below, choices => childSiblingForest_zero_iff below choices

theorem childSiblingForest_zero_iff : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (choices : ChildSiblingChoices hole) →
    childSiblingForest hole choices = 0 ↔ choices = emptyChildSiblings hole
  | _, _, _, _, _, .head _ _ _ below, choices => by
      cases choices
      simp only [childSiblingForest, forest_add_zero, siblingForest_zero_iff,
        childrenForest_zero_iff, emptyChildSiblings]
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro equal
        exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩
  | _, _, _, _, _, .tail _ _ _ _ below, choices => by
      cases choices
      simp only [childSiblingForest, forest_add_zero, branchForest_zero_iff,
        childSiblingForest_zero_iff, emptyChildSiblings]
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro equal
        exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩
end

mutual
@[simp] theorem graftState_empty : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) → (payload : CKTree sigma InstanceData H) →
    graftState hole (emptySiblings hole) payload = hole.insert payload
  | _, _, _, _, .root, _ => rfl
  | _, _, _, _, .child _ _ _ _ below, payload => by
      simp only [graftState, emptySiblings, CKTree.PunctureAt.insert,
        graftChildState_empty]

@[simp] theorem graftChildState_empty : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) →
    graftChildState hole (emptyChildSiblings hole) payload = hole.insert payload
  | _, _, _, _, _, .head _ _ _ below, payload => by
      simp only [graftChildState, emptyChildSiblings, CKChildren.PunctureAt.insert,
        graftState_empty, emptyChildren_remainder]
  | _, _, _, _, _, .tail _ _ _ _ below, payload => by
      simp only [graftChildState, emptyChildSiblings, CKChildren.PunctureAt.insert,
        graftChildState_empty, emptyBranch_remainder]
end

/-- Coefficient counit: select precisely the empty forest coefficient. The
typed Box in the state coordinate remains a distinct native basis element. -/
def e {G : Hypersequent sigma} :
    ExtractionRecords (InstanceData := InstanceData) G →+
      States (InstanceData := InstanceData) G := by
  classical
  exact FreeAbelianGroup.lift fun record =>
    if record.1 = 0 then FreeAbelianGroup.of record.2 else 0

theorem e_delta {G : Hypersequent sigma} :
    (e : ExtractionRecords (InstanceData := InstanceData) G →+ _).comp delta =
      AddMonoidHom.id _ := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro tree
  simp only [delta, e, AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of,
    AddMonoidHom.id_apply, map_sum]
  rw [Finset.sum_eq_single (emptyBranch tree)]
  · simp only [emptyBranch_forest, if_pos, emptyBranch_remainder]
  · intro cut _ different
    rw [if_neg]
    exact fun zero => different ((branchForest_zero_iff cut).mp zero)
  · intro notMember
    exact False.elim (notMember (Finset.mem_univ _))

theorem e_L {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) :
    e.comp (L hole) = (ContextCutAction.G hole).comp e := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro record
  simp only [e, L, ContextCutAction.G, AddMonoidHom.comp_apply,
    FreeAbelianGroup.lift_apply_of, map_sum]
  by_cases empty : record.1 = 0
  · rw [if_pos empty, FreeAbelianGroup.lift_apply_of]
    rw [Finset.sum_eq_single (emptySiblings hole)]
    · have emptyS := (siblingForest_zero_iff hole (emptySiblings hole)).mpr rfl
      simp only [empty, emptyS, add_zero, if_pos, graftState_empty]
    · intro siblings _ different
      rw [if_neg]
      intro zero
      have siblingZero : siblingForest hole siblings = 0 := by simpa [empty] using zero
      exact different ((siblingForest_zero_iff hole siblings).mp siblingZero)
    · intro notMember
      exact False.elim (notMember (Finset.mem_univ _))
  · rw [if_neg empty, map_zero]
    apply Finset.sum_eq_zero
    intro siblings _
    rw [if_neg]
    intro zero
    exact empty ((forest_add_zero _ _).mp zero).1

#print axioms e_delta
#print axioms e_L

mutual
theorem ancestorEffect_positive : {G H : Hypersequent sigma} →
    {context : CKTree sigma InstanceData G} → {address : InternalAddress} →
    (hole : CKTree.PunctureAt H context address) →
    (payload : CKTree sigma InstanceData H) → (ancestor : Ancestor hole) →
    (ancestorEffect hole payload ancestor).1 ≠ 0
  | _, _, _, _, .root, _, impossible => nomatch impossible
  | _, _, _, _, .child _ _ _ _ below, payload, ancestor => by
      change PUnit.{max (max u v) w + 1} ⊕ ChildAncestor below at ancestor
      cases ancestor with
      | inl unit => exact Multiset.singleton_ne_zero _
      | inr ancestor => exact childAncestorEffect_positive below payload ancestor

theorem childAncestorEffect_positive : {Gs : List (Hypersequent sigma)} →
    {H : Hypersequent sigma} → {children : CKChildren sigma InstanceData Gs} →
    {slot : Nat} → {address : InternalAddress} →
    (hole : CKChildren.PunctureAt H children slot address) →
    (payload : CKTree sigma InstanceData H) → (ancestor : ChildAncestor hole) →
    (childAncestorEffect hole payload ancestor).1 ≠ 0
  | _, _, _, _, _, .head _ _ _ below, payload, ancestor => by
      intro zero
      exact ancestorEffect_positive below payload ancestor.1
        ((forest_add_zero _ _).mp zero).1
  | _, _, _, _, _, .tail _ _ _ _ below, payload, ancestor => by
      intro zero
      exact childAncestorEffect_positive below payload ancestor.2
        ((forest_add_zero _ _).mp zero).2
end

theorem e_A {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) : e.comp (A hole) = 0 := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro payload
  simp only [A, e, AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
    FreeAbelianGroup.lift_apply_of, map_sum]
  apply Finset.sum_eq_zero
  intro ancestor _
  exact if_neg (ancestorEffect_positive hole payload ancestor)

def K {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) :
    ExtractionRecords (InstanceData := InstanceData) H →+
      ExtractionRecords (InstanceData := InstanceData) G :=
  L hole + (A hole).comp e

private theorem corrected_compose
    {R₀ R₁ R₂ S₀ S₁ : Type*}
    [AddCommGroup R₀] [AddCommGroup R₁] [AddCommGroup R₂]
    [AddCommGroup S₀] [AddCommGroup S₁]
    (l₁ : R₁ →+ R₂) (l₀ : R₀ →+ R₁)
    (a₁ : S₁ →+ R₂) (a₀ : S₀ →+ R₁)
    (e₁ : R₁ →+ S₁) (e₀ : R₀ →+ S₀) (g₀ : S₀ →+ S₁)
    (counitL : e₁.comp l₀ = g₀.comp e₀)
    (counitA : e₁.comp a₀ = 0) :
    l₁.comp l₀ + (l₁.comp a₀ + a₁.comp g₀).comp e₀ =
      (l₁ + a₁.comp e₁).comp (l₀ + a₀.comp e₀) := by
  apply AddMonoidHom.ext
  intro record
  have lawL := DFunLike.congr_fun counitL record
  have lawA := DFunLike.congr_fun counitA (e₀ record)
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at lawL lawA
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add]
  rw [lawL, lawA]
  simp only [map_zero, add_zero, zero_add, add_assoc, add_comm, add_left_comm]

/-- Native context action on arbitrary signed records, including records
outside the image of `delta`. No coefficient-linearity or Hopf-morphism claim
is made: the ancestor correction extracts the empty coefficient first. -/
theorem K_compose {G H J : Hypersequent sigma}
    {context : CKTree sigma InstanceData G}
    {outerAddress innerAddress : InternalAddress}
    (outer : CKTree.PunctureAt H context outerAddress)
    {innerContext : CKTree sigma InstanceData H}
    (inner : CKTree.PunctureAt J innerContext innerAddress) :
    K (outer.insert_replacement inner) = (K outer).comp (K inner) := by
  change L (outer.insert_replacement inner) +
      (A (outer.insert_replacement inner)).comp e =
    (L outer + (A outer).comp e).comp (L inner + (A inner).comp e)
  rw [L_compose, A_compose]
  exact corrected_compose (L outer) (L inner) (A outer) (A inner)
    e e (ContextCutAction.G inner) (e_L inner) (e_A inner)

theorem delta_K {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) :
    delta.comp (ContextCutAction.G hole) = (K hole).comp delta := by
  have contextLaw := DFunLike.congr_fun (delta_context hole)
  apply AddMonoidHom.ext
  intro state
  have counit := DFunLike.congr_fun (e_delta (G := H) (InstanceData := InstanceData)) state
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at counit
  simpa only [K, AddMonoidHom.comp_apply, AddMonoidHom.add_apply, counit] using contextLaw state

theorem e_K {G H : Hypersequent sigma}
    {context : CKTree sigma InstanceData G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) :
    e.comp (K hole) = (ContextCutAction.G hole).comp e := by
  apply AddMonoidHom.ext
  intro record
  have counitL := DFunLike.congr_fun (e_L hole) record
  have counitA := DFunLike.congr_fun (e_A hole) (e record)
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at counitL counitA
  simpa only [K, AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add,
    AddMonoidHom.zero_apply, counitL, counitA, add_zero]

theorem G_compose {G H J : Hypersequent sigma}
    {context : CKTree sigma InstanceData G}
    {outerAddress innerAddress : InternalAddress}
    (outer : CKTree.PunctureAt H context outerAddress)
    {innerContext : CKTree sigma InstanceData H}
    (inner : CKTree.PunctureAt J innerContext innerAddress) :
    ContextCutAction.G (outer.insert_replacement inner) =
      (ContextCutAction.G outer).comp (ContextCutAction.G inner) := by
  apply FreeAbelianGroup.lift_ext
  intro payload
  simp only [ContextCutAction.G, AddMonoidHom.comp_apply,
    FreeAbelianGroup.lift_apply_of, insert_compose]

#print axioms e_A
#print axioms K_compose
#print axioms delta_K
#print axioms e_K
#print axioms G_compose

end
end Potkin.Research.ContextCutAction

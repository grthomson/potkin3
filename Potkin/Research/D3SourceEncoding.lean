import Potkin.Research.OpenDischarge
import Mathlib.Data.Fintype.Basic

/-!
# An independent propositional source fragment and its native interpretation

Source formulas and inference schemes are specified before their native
encoding.  Rule-instance keys are immutable lookup labels; `owner` and `uid`
are the separate stable system-reference/declaration tokens.  No admission or
global discharge correctness is built into this syntax.

The supplied native incidence describes displayed hypersequent components,
not formula-occurrence movement.  Singleton components have one local index
in each ordered premise, including the two equal bottom premises.
-/

namespace Potkin.Research.D3SourceEncoding

inductive Formula where
  | atom (name : Nat)
  | implication (antecedent consequent : Formula)
  deriving DecidableEq, Repr

abbrev Context := Multiset Formula

structure Sequent where
  lhs : Context
  rhs : Context
  deriving DecidableEq

structure Parameters where
  phi : Context
  psi : Context
  deriving DecidableEq

/-- Source schemes, independent of native tags, lookups, and legality. -/
inductive Rule where
  | identity (a : Formula)
  | weakening (a : Formula) (gamma pi : Context)
  | contraction (a : Formula) (gamma pi : Context)
  | top (role : Fin 2) (parameters : Parameters) (owner : Nat)
      (gamma pi : Context)
  | bottom (parameters : Parameters) (uid : Nat) (common : Sequent)
  | implicationRight (gamma : Context) (a b : Formula)

def topInput (role : Fin 2) (p : Parameters) (gamma pi : Context) : Sequent :=
  ⟨(if role.val = 0 then p.phi else p.psi) + gamma, pi⟩

def topOutput (role : Fin 2) (p : Parameters) (gamma pi : Context) : Sequent :=
  ⟨(if role.val = 0 then p.psi else p.phi) + gamma, pi⟩

def Rule.premises : Rule → List Sequent
  | .identity _ => []
  | .weakening _ gamma pi => [⟨gamma, pi⟩]
  | .contraction a gamma pi => [⟨{a} + {a} + gamma, pi⟩]
  | .top role p _ gamma pi => [topInput role p gamma pi]
  | .bottom _ _ S => [S, S]
  | .implicationRight gamma a b => [⟨{a} + gamma, {b}⟩]

def Rule.conclusion : Rule → Sequent
  | .identity a => ⟨{a}, {a}⟩
  | .weakening a gamma pi => ⟨{a} + gamma, pi⟩
  | .contraction a gamma pi => ⟨{a} + gamma, pi⟩
  | .top role p _ gamma pi => topOutput role p gamma pi
  | .bottom _ _ S => S
  | .implicationRight gamma a b => ⟨gamma, {.implication a b}⟩

/-- The actual source single-conclusion side conditions. -/
def Rule.Valid : Rule → Prop
  | .identity _ => True
  | .weakening _ _ pi => pi.card ≤ 1
  | .contraction _ _ pi => pi.card ≤ 1
  | .top _ _ _ _ pi => pi.card ≤ 1
  | .bottom _ _ S => S.rhs.card ≤ 1
  | .implicationRight _ _ _ => True

inductive Operation : Nat → Type where
  | implication : Operation 2

def signature : Potkin.Signature := ⟨Nat, Operation⟩

def encodeFormula : Formula → Potkin.Formula signature
  | .atom a => .atom a
  | .implication a b => .app2 .implication (encodeFormula a) (encodeFormula b)

private def leftArgument : Potkin.Formula signature → Potkin.Formula signature
  | .atom a => .atom a
  | .app .implication args => args 0

private def rightArgument : Potkin.Formula signature → Potkin.Formula signature
  | .atom a => .atom a
  | .app .implication args => args 1

theorem encodeFormula_injective : Function.Injective encodeFormula := by
  intro a
  induction a with
  | atom n =>
      intro b equal
      cases b with
      | atom m => cases equal; rfl
      | implication b c => cases equal
  | implication a b iha ihb =>
      intro c equal
      cases c with
      | atom n => cases equal
      | implication c d =>
          have ha := congrArg leftArgument equal
          have hb := congrArg rightArgument equal
          have ac := iha (by simpa [leftArgument, encodeFormula, Potkin.Formula.app2] using ha)
          have bd := ihb (by simpa [rightArgument, encodeFormula, Potkin.Formula.app2] using hb)
          cases ac
          cases bd
          rfl

def Imp (a b c : Potkin.Formula signature) : Prop :=
  c = .app2 .implication a b

theorem implication_image_iff (a b c : Formula) :
    Imp (encodeFormula a) (encodeFormula b) (encodeFormula c) ↔
      c = .implication a b := by
  change encodeFormula c = encodeFormula (.implication a b) ↔ _
  exact ⟨fun h => encodeFormula_injective h, congrArg encodeFormula⟩

def encodeContext (gamma : Context) : Potkin.Context signature :=
  gamma.map encodeFormula

@[simp] theorem encodeContext_add (gamma delta : Context) :
    encodeContext (gamma + delta) = encodeContext gamma + encodeContext delta :=
  Multiset.map_add _ _ _

@[simp] theorem encodeContext_singleton (a : Formula) :
    encodeContext {a} = {encodeFormula a} := Multiset.map_singleton _ _

@[simp] theorem encodeContext_card (gamma : Context) :
    (encodeContext gamma).card = gamma.card := Multiset.card_map _ _

theorem encodeContext_injective : Function.Injective encodeContext :=
  Multiset.map_injective encodeFormula_injective

def encodeSequent (S : Sequent) : Potkin.Sequent signature :=
  ⟨encodeContext S.lhs, encodeContext S.rhs⟩

theorem encodeSequent_injective : Function.Injective encodeSequent := by
  intro S T equal
  cases S with
  | mk lhs rhs =>
      cases T with
      | mk lhs' rhs' =>
          have hleft := encodeContext_injective (congrArg Potkin.Sequent.lhs equal)
          have hright := encodeContext_injective (congrArg Potkin.Sequent.rhs equal)
          cases hleft
          cases hright
          rfl

def boundary (S : Sequent) : Potkin.Hypersequent signature :=
  .singleton (encodeSequent S)

def encodeParameters (p : Parameters) : OpenDischarge.Parameters signature :=
  ⟨encodeContext p.phi, encodeContext p.psi⟩

theorem encodeParameters_injective : Function.Injective encodeParameters := by
  intro p q equal
  cases p with
  | mk phi psi =>
      cases q with
      | mk phi' psi' =>
          have hphi := encodeContext_injective
            (congrArg DependencyInterface.Parameters.phi equal)
          have hpsi := encodeContext_injective
            (congrArg DependencyInterface.Parameters.psi equal)
          cases hphi
          cases hpsi
          rfl

@[simp] theorem encode_topInput (role : Fin 2) (p : Parameters) (gamma pi : Context) :
    encodeSequent (topInput role p gamma pi) =
      OpenDischarge.topInput role (encodeParameters p) (encodeContext gamma) (encodeContext pi) := by
  by_cases h : role.val = 0 <;>
    simp [encodeSequent, topInput, OpenDischarge.topInput, DependencyInterface.topInput,
      encodeParameters, h]

@[simp] theorem encode_topOutput (role : Fin 2) (p : Parameters) (gamma pi : Context) :
    encodeSequent (topOutput role p gamma pi) =
      OpenDischarge.topOutput role (encodeParameters p) (encodeContext gamma) (encodeContext pi) := by
  by_cases h : role.val = 0 <;>
    simp [encodeSequent, topOutput, OpenDischarge.topOutput, DependencyInterface.topOutput,
      encodeParameters, h]

def ruleData : Rule → OpenDischarge.Data signature
  | .identity a => .identity (encodeFormula a)
  | .weakening a gamma pi => .weakening (encodeFormula a) (encodeContext gamma) (encodeContext pi)
  | .contraction a gamma pi => .contraction (encodeFormula a) (encodeContext gamma) (encodeContext pi)
  | .top role p owner gamma pi =>
      .top role (encodeParameters p) owner (encodeContext gamma) (encodeContext pi)
  | .bottom p uid S => .bottom (encodeParameters p) uid (encodeSequent S)
  | .implicationRight gamma a b =>
      .implicationRight (encodeContext gamma) (encodeFormula a) (encodeFormula b)
        (encodeFormula (.implication a b))

def ruleKind : Rule → Potkin.OccurrenceKind
  | .identity _ | .implicationRight _ _ _ => .logical
  | _ => .structural

def ruleShape (r : Rule) : Potkin.OccurrenceShape signature :=
  ⟨r.premises.map boundary, boundary r.conclusion⟩

private def profile (S : Sequent) : Potkin.ComponentProfile (boundary S) :=
  ⟨[encodeSequent S], rfl⟩

private def premiseProfiles : (Ss : List Sequent) →
    (i : Fin (Ss.map boundary).length) →
      Potkin.ComponentProfile ((Ss.map boundary).get i)
  | [], i => Fin.elim0 i
  | S :: Ss, i => Fin.cases (profile S) (fun j => premiseProfiles Ss j) i

private theorem premiseProfiles_length (Ss : List Sequent)
    (i : Fin (Ss.map boundary).length) :
    (premiseProfiles Ss i).displayed.length = 1 := by
  induction Ss with
  | nil => exact Fin.elim0 i
  | cons S Ss ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact ih i

def componentIncidence (r : Rule) : Potkin.ComponentIncidence (ruleShape r) where
  profiles := ⟨premiseProfiles r.premises, profile r.conclusion⟩
  edges := Finset.univ.image (fun i : Fin (r.premises.map boundary).length =>
    ⟨i, ⟨0, by rw [premiseProfiles_length]; decide⟩, ⟨0, by change 0 < 1; decide⟩⟩)

def occurrence (key : Nat) (r : Rule) :
    Potkin.LocalOccurrence signature (OpenDischarge.Data signature) :=
  ⟨key, ruleKind r, ruleShape r, ruleData r, some (componentIncidence r)⟩

/-- Soundness and reflection of every source inference on its encoding image.
This does not say that registry lookup is a logical-schema validator. -/
theorem exact_instance_iff (key : Nat) (r : Rule) :
    OpenDischarge.ExactInstance Imp (occurrence key r) ↔ r.Valid := by
  cases r <;>
    simp [occurrence, OpenDischarge.ExactInstance, Rule.Valid, ruleKind,
      ruleShape, ruleData, Rule.premises, Rule.conclusion, boundary]
  all_goals
    simp [encodeSequent, encodeParameters, encodeContext, Imp, encodeFormula,
      Multiset.map_add]

mutual
inductive Diagram : Sequent → Type where
  | hole (S : Sequent) : Diagram S
  | rule (key : Nat) (r : Rule) (children : Children r.premises) : Diagram r.conclusion
inductive Children : List Sequent → Type where
  | nil : Children []
  | cons {S : Sequent} {Ss : List Sequent} (head : Diagram S)
      (tail : Children Ss) : Children (S :: Ss)
end

mutual
def encode : {S : Sequent} → Diagram S →
    Potkin.CKTree signature (OpenDischarge.Data signature) (boundary S)
  | _, .hole S => .interface (boundary S)
  | _, .rule key r children => .ordinary (occurrence key r) (encodeChildren children)
def encodeChildren : {Ss : List Sequent} → Children Ss →
    Potkin.CKChildren signature (OpenDischarge.Data signature) (Ss.map boundary)
  | _, .nil => .nil
  | _, .cons head tail => .cons (encode head) (encodeChildren tail)
end

mutual
def LocallyCorrect : {S : Sequent} → Diagram S → Prop
  | _, .hole _ => True
  | _, .rule _ r children => r.Valid ∧ ChildrenCorrect children
def ChildrenCorrect : {Ss : List Sequent} → Children Ss → Prop
  | _, .nil => True
  | _, .cons head tail => LocallyCorrect head ∧ ChildrenCorrect tail
end

mutual
theorem exact_tree_iff : {S : Sequent} → (D : Diagram S) →
    (OpenDischarge.ExactTree Imp (encode D) ↔ LocallyCorrect D)
  | _, .hole _ => Iff.rfl
  | _, .rule key r children => by
      change (OpenDischarge.ExactInstance Imp (occurrence key r) ∧
        OpenDischarge.ExactChildren Imp (encodeChildren children)) ↔ _
      rw [exact_instance_iff, exact_children_iff]
      rfl
theorem exact_children_iff : {Ss : List Sequent} → (Ds : Children Ss) →
    (OpenDischarge.ExactChildren Imp (encodeChildren Ds) ↔ ChildrenCorrect Ds)
  | _, .nil => Iff.rfl
  | _, .cons head tail => by
      change (OpenDischarge.ExactTree Imp (encode head) ∧
        OpenDischarge.ExactChildren Imp (encodeChildren tail)) ↔ _
      rw [exact_tree_iff, exact_children_iff]
      rfl
end

mutual
def Diagram.Complete : {S : Sequent} → Diagram S → Prop
  | _, .hole _ => False
  | _, .rule _ _ children => children.Complete
def Children.Complete : {Ss : List Sequent} → Children Ss → Prop
  | _, .nil => True
  | _, .cons head tail => head.Complete ∧ tail.Complete
end

mutual
theorem complete_iff : {S : Sequent} → (D : Diagram S) →
    ((encode D).IsComplete ↔ D.Complete)
  | _, .hole _ => Iff.rfl
  | _, .rule _ _ children => children_complete_iff children
theorem children_complete_iff : {Ss : List Sequent} → (Ds : Children Ss) →
    ((encodeChildren Ds).IsComplete ↔ Ds.Complete)
  | _, .nil => Iff.rfl
  | _, .cons head tail => by
      change ((encode head).IsComplete ∧ (encodeChildren tail).IsComplete) ↔ _
      rw [complete_iff, children_complete_iff]
      rfl
end

mutual
@[reducible] def Diagram.Hole : {S : Sequent} → Diagram S → Type
  | _, .hole _ => PUnit
  | _, .rule _ _ children => children.Hole
@[reducible] def Children.Hole : {Ss : List Sequent} → Children Ss → Type
  | _, .nil => PEmpty
  | _, .cons head tail => head.Hole ⊕ tail.Hole
end

mutual
@[reducible] def Diagram.holeBoundary : {S : Sequent} → (D : Diagram S) → D.Hole → Sequent
  | S, .hole _, _ => S
  | _, .rule _ _ children, h => children.holeBoundary h
@[reducible] def Children.holeBoundary : {Ss : List Sequent} → (Ds : Children Ss) → Ds.Hole → Sequent
  | _, .nil, h => nomatch h
  | _, .cons head tail, hole => match hole with
      | Sum.inl h => head.holeBoundary h
      | Sum.inr h => tail.holeBoundary h
end

abbrev Diagram.Assignment {S : Sequent} (D : Diagram S) :=
  (h : D.Hole) → Diagram (D.holeBoundary h)
abbrev Children.Assignment {Ss : List Sequent} (Ds : Children Ss) :=
  (h : Ds.Hole) → Diagram (Ds.holeBoundary h)

mutual
def Diagram.fill : {S : Sequent} → (D : Diagram S) → D.Assignment → Diagram S
  | _, .hole _, F => F PUnit.unit
  | _, .rule key r children, F => .rule key r (children.fill F)
def Children.fill : {Ss : List Sequent} → (Ds : Children Ss) → Ds.Assignment → Children Ss
  | _, .nil, _ => .nil
  | _, .cons head tail, F =>
      .cons (head.fill (fun h => F (Sum.inl h))) (tail.fill (fun h => F (Sum.inr h)))
end

mutual
def holeEquiv : {S : Sequent} → (D : Diagram S) → D.Hole ≃ (encode D).LeafOccurrence
  | _, .hole _ => Equiv.refl _
  | _, .rule _ _ children => childrenHoleEquiv children
def childrenHoleEquiv : {Ss : List Sequent} → (Ds : Children Ss) →
    Ds.Hole ≃ (encodeChildren Ds).LeafOccurrence
  | _, .nil => Equiv.refl _
  | _, .cons head tail => Equiv.sumCongr (holeEquiv head) (childrenHoleEquiv tail)
end

mutual
theorem hole_boundary : {S : Sequent} → (D : Diagram S) → (h : D.Hole) →
    (encode D).leafBoundary (holeEquiv D h) = boundary (D.holeBoundary h)
  | _, .hole _, _ => rfl
  | _, .rule _ _ children, h => children_hole_boundary children h
theorem children_hole_boundary : {Ss : List Sequent} → (Ds : Children Ss) → (h : Ds.Hole) →
    (encodeChildren Ds).leafBoundary (childrenHoleEquiv Ds h) = boundary (Ds.holeBoundary h)
  | _, .nil, h => nomatch h
  | _, .cons head tail, hole => match hole with
      | Sum.inl h => hole_boundary head h
      | Sum.inr h => children_hole_boundary tail h
end

mutual
/-- The dependent transport follows the same physical sum constructors.
No name allocation, lookup change, or legality test occurs during filling. -/
def encodeAssignment : {S : Sequent} → (D : Diagram S) → D.Assignment →
    (encode D).LeafAssignment
  | _, .hole _, F => fun h => PUnit.casesOn h (encode (F PUnit.unit))
  | _, .rule _ _ children, F => encodeChildrenAssignment children F
def encodeChildrenAssignment : {Ss : List Sequent} → (Ds : Children Ss) →
    Ds.Assignment → (encodeChildren Ds).LeafAssignment
  | _, .nil, _ => fun h => nomatch h
  | _, .cons head tail, F => fun h => match h with
      | Sum.inl h => encodeAssignment head (fun x => F (Sum.inl x)) h
      | Sum.inr h => encodeChildrenAssignment tail (fun x => F (Sum.inr x)) h
end

mutual
theorem encodeAssignment_at : {S : Sequent} → (D : Diagram S) → (F : D.Assignment) →
    (h : D.Hole) → HEq (encodeAssignment D F (holeEquiv D h)) (encode (F h))
  | _, .hole _, _, h => by cases h; rfl
  | _, .rule _ _ children, F, h => encodeChildrenAssignment_at children F h
theorem encodeChildrenAssignment_at : {Ss : List Sequent} → (Ds : Children Ss) →
    (F : Ds.Assignment) → (h : Ds.Hole) →
      HEq (encodeChildrenAssignment Ds F (childrenHoleEquiv Ds h)) (encode (F h))
  | _, .nil, _, h => nomatch h
  | _, .cons head tail, F, hole => match hole with
      | Sum.inl h => encodeAssignment_at head (fun x => F (Sum.inl x)) h
      | Sum.inr h => encodeChildrenAssignment_at tail (fun x => F (Sum.inr x)) h
end

mutual
/-- Literal encoding/filling naturality for every diagram, including invalid
declaration collisions and unresolved or wrong-branch top references. -/
theorem encode_fill : {S : Sequent} → (D : Diagram S) → (F : D.Assignment) →
    encode (D.fill F) = (encode D).fillAssignment (encodeAssignment D F)
  | _, .hole _, _ => rfl
  | _, .rule key r children, F => by
      change CKTree.ordinary (occurrence key r) (encodeChildren (children.fill F)) =
        CKTree.ordinary (occurrence key r)
          ((encodeChildren children).fillAssignment (encodeChildrenAssignment children F))
      rw [encode_children_fill]
theorem encode_children_fill : {Ss : List Sequent} → (Ds : Children Ss) →
    (F : Ds.Assignment) → encodeChildren (Ds.fill F) =
      (encodeChildren Ds).fillAssignment (encodeChildrenAssignment Ds F)
  | _, .nil, _ => rfl
  | _, .cons head tail, F => by
      change CKChildren.cons (encode (head.fill (fun h => F (Sum.inl h))))
        (encodeChildren (tail.fill (fun h => F (Sum.inr h)))) =
        CKChildren.cons ((encode head).fillAssignment
          (encodeAssignment head (fun h => F (Sum.inl h))))
          ((encodeChildren tail).fillAssignment
            (encodeChildrenAssignment tail (fun h => F (Sum.inr h))))
      rw [encode_fill, encode_children_fill]
end

mutual
def Diagram.holeAddress : {S : Sequent} → (D : Diagram S) → D.Hole → InternalAddress
  | _, .hole _, _ => []
  | _, .rule _ _ children, h => children.holeAddress h
def Children.holeAddress : {Ss : List Sequent} → (Ds : Children Ss) → Ds.Hole → InternalAddress
  | _, .nil, h => nomatch h
  | _, .cons head tail, hole => match hole with
      | Sum.inl h => 0 :: head.holeAddress h
      | Sum.inr h => InternalAddress.shiftHead (tail.holeAddress h)
end

mutual
theorem hole_address : {S : Sequent} → (D : Diagram S) → (h : D.Hole) →
    (encode D).leafAddress (holeEquiv D h) = D.holeAddress h
  | _, .hole _, _ => rfl
  | _, .rule _ _ children, h => children_hole_address children h
theorem children_hole_address : {Ss : List Sequent} → (Ds : Children Ss) → (h : Ds.Hole) →
    (encodeChildren Ds).leafAddress (childrenHoleEquiv Ds h) = Ds.holeAddress h
  | _, .nil, h => nomatch h
  | _, .cons head tail, hole => match hole with
      | Sum.inl h => congrArg (List.cons 0) (hole_address head h)
      | Sum.inr h => congrArg InternalAddress.shiftHead (children_hole_address tail h)
end

mutual
def Diagram.holeOrder : {S : Sequent} → (D : Diagram S) → List D.Hole
  | _, .hole _ => [PUnit.unit]
  | _, .rule _ _ children => children.holeOrder
def Children.holeOrder : {Ss : List Sequent} → (Ds : Children Ss) → List Ds.Hole
  | _, .nil => []
  | _, .cons head tail => head.holeOrder.map Sum.inl ++ tail.holeOrder.map Sum.inr
end

mutual
theorem hole_order : {S : Sequent} → (D : Diagram S) →
    (encode D).leafOrder = D.holeOrder.map (holeEquiv D)
  | _, .hole _ => rfl
  | _, .rule _ _ children => children_hole_order children
theorem children_hole_order : {Ss : List Sequent} → (Ds : Children Ss) →
    (encodeChildren Ds).leafOrder = Ds.holeOrder.map (childrenHoleEquiv Ds)
  | _, .nil => rfl
  | _, .cons head tail => by
      simp only [encodeChildren, CKChildren.leafOrder, Children.holeOrder,
        childrenHoleEquiv, hole_order head, children_hole_order tail,
        List.map_append, List.map_map]
      rfl
end

mutual
/-- A typed source slot witness, only for interpreting source insertion.
Its image is the existing native `CKTree.PunctureAt`; it is not a second
native context/cut carrier used by extraction. -/
inductive Diagram.PunctureAt (H : Sequent) :
    {S : Sequent} → Diagram S → InternalAddress → Type where
  | root : Diagram.PunctureAt H (.hole H) []
  | child (key : Nat) (r : Rule) (children : Children r.premises)
      (slot : Nat) (address : InternalAddress)
      (below : Children.PunctureAt H children slot address) :
      Diagram.PunctureAt H (.rule key r children) (slot :: address)
inductive Children.PunctureAt (H : Sequent) :
    {Ss : List Sequent} → Children Ss → Nat → InternalAddress → Type where
  | head {S : Sequent} {Ss : List Sequent} (head : Diagram S) (tail : Children Ss)
      (address : InternalAddress) (below : Diagram.PunctureAt H head address) :
      Children.PunctureAt H (.cons head tail) 0 address
  | tail {S : Sequent} {Ss : List Sequent} (head : Diagram S) (tail : Children Ss)
      (slot : Nat) (address : InternalAddress)
      (below : Children.PunctureAt H tail slot address) :
      Children.PunctureAt H (.cons head tail) (slot + 1) address
end

mutual
def Diagram.PunctureAt.insert {H : Sequent} :
    {S : Sequent} → {D : Diagram S} → {address : InternalAddress} →
      Diagram.PunctureAt H D address → Diagram H → Diagram S
  | _, _, _, .root, Q => Q
  | _, _, _, .child key r children _ _ below, Q => .rule key r (below.insert Q)
def Children.PunctureAt.insert {H : Sequent} :
    {Ss : List Sequent} → {Ds : Children Ss} → {slot : Nat} → {address : InternalAddress} →
      Children.PunctureAt H Ds slot address → Diagram H → Children Ss
  | _, _, _, _, .head head tail _ below, Q => .cons (below.insert Q) tail
  | _, _, _, _, .tail head tail _ _ below, Q => .cons head (below.insert Q)
end

mutual
def encodePuncture {H : Sequent} :
    {S : Sequent} → {D : Diagram S} → {address : InternalAddress} →
      Diagram.PunctureAt H D address →
        CKTree.PunctureAt (boundary H) (encode D) address
  | _, _, _, .root => .root
  | _, _, _, .child key r children slot address below =>
      .child (occurrence key r) (encodeChildren children) slot address
        (encodeChildrenPuncture below)
def encodeChildrenPuncture {H : Sequent} :
    {Ss : List Sequent} → {Ds : Children Ss} → {slot : Nat} → {address : InternalAddress} →
      Children.PunctureAt H Ds slot address →
        CKChildren.PunctureAt (boundary H) (encodeChildren Ds) slot address
  | _, _, _, _, .head head tail address below =>
      .head (encode head) (encodeChildren tail) address (encodePuncture below)
  | _, _, _, _, .tail head tail slot address below =>
      .tail (encode head) (encodeChildren tail) slot address (encodeChildrenPuncture below)
end

mutual
theorem encode_insert {H : Sequent} :
    {S : Sequent} → {D : Diagram S} → {address : InternalAddress} →
      (slot : Diagram.PunctureAt H D address) → (Q : Diagram H) →
        encode (slot.insert Q) = (encodePuncture slot).insert (encode Q)
  | _, _, _, .root, _ => rfl
  | _, _, _, .child key r children _ _ below, Q => by
      change CKTree.ordinary (occurrence key r) (encodeChildren (below.insert Q)) =
        CKTree.ordinary (occurrence key r)
          ((encodeChildrenPuncture below).insert (encode Q))
      rw [encode_children_insert]
theorem encode_children_insert {H : Sequent} :
    {Ss : List Sequent} → {Ds : Children Ss} → {slot : Nat} → {address : InternalAddress} →
      (selected : Children.PunctureAt H Ds slot address) → (Q : Diagram H) →
        encodeChildren (selected.insert Q) = (encodeChildrenPuncture selected).insert (encode Q)
  | _, _, _, _, .head head tail _ below, Q => by
      change CKChildren.cons (encode (below.insert Q)) (encodeChildren tail) =
        CKChildren.cons ((encodePuncture below).insert (encode Q)) (encodeChildren tail)
      rw [encode_insert]
  | _, _, _, _, .tail head tail _ _ below, Q => by
      change CKChildren.cons (encode head) (encodeChildren (below.insert Q)) =
        CKChildren.cons (encode head) ((encodeChildrenPuncture below).insert (encode Q))
      rw [encode_children_insert]
end

end Potkin.Research.D3SourceEncoding

#print axioms Potkin.Research.D3SourceEncoding.encodeFormula_injective
#print axioms Potkin.Research.D3SourceEncoding.implication_image_iff
#print axioms Potkin.Research.D3SourceEncoding.exact_instance_iff
#print axioms Potkin.Research.D3SourceEncoding.exact_tree_iff
#print axioms Potkin.Research.D3SourceEncoding.encode_fill
#print axioms Potkin.Research.D3SourceEncoding.encode_insert

#check Potkin.Research.D3SourceEncoding.implication_image_iff
#check Potkin.Research.D3SourceEncoding.exact_instance_iff
#check Potkin.Research.D3SourceEncoding.exact_tree_iff
#check Potkin.Research.D3SourceEncoding.encode_fill
#check Potkin.Research.D3SourceEncoding.encode_insert

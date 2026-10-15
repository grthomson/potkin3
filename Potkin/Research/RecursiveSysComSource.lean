import Potkin.Research.PreparedSysComSource

/-!
# Recursive prepared Sys(com) source construction

`Source` is construction metadata, not a proof carrier. Its interpretation is
the existing native source `Diagram`. Physical source origins are indexed by
constructor-generated sums, independently of successful target translation.
A phase introduces its top applications at every physical child interface;
its shared parameters and all boundary equalities concern source rules only.
-/
namespace Potkin.Research.RecursiveSysComSource
open D3SourceEncoding D3SourceAdequacy
abbrev Formula := D3SourceEncoding.Formula
abbrev Context := D3SourceEncoding.Context
abbrev Sequent := D3SourceEncoding.Sequent
abbrev Parameters := D3SourceEncoding.Parameters

structure TopSpec (role : Fin 2) (parameters : Parameters) (out : Sequent) where
  gamma : Context
  pi : Context
  single : pi.card ≤ 1
  output : topOutput role parameters gamma pi = out

def TopSpec.input {role : Fin 2} {p : Parameters} {out : Sequent}
    (spec : TopSpec role p out) : Sequent := topInput role p spec.gamma spec.pi

def TopSpec.rebase {role : Fin 2} {p : Parameters} {out other : Sequent}
    (spec : TopSpec role p out) (equal : out = other) : TopSpec role p other :=
  ⟨spec.gamma, spec.pi, spec.single, spec.output.trans equal⟩

inductive Source : (S : Sequent) → (O : Type) → (bounds : O → Sequent) → Type 1 where
  | leaf (S : Sequent) : Source S PUnit (fun _ => S)
  | iw {O : Type} {bounds : O → Sequent} (key : Nat) (a : Formula)
      (gamma pi : Context) (single : pi.card ≤ 1)
      (body : Source ⟨gamma, pi⟩ O bounds) : Source ⟨{a} + gamma, pi⟩ O bounds
  | phase {OL OR : Type} {BL : OL → Sequent} {BR : OR → Sequent}
      (bottomKey uid : Nat) (p : Parameters) (S : Sequent) (single : S.rhs.card ≤ 1)
      (left : Source S OL BL) (right : Source S OR BR) (topKey : OL ⊕ OR → Nat)
      (specL : (o : OL) → TopSpec 0 p (BL o))
      (specR : (o : OR) → TopSpec 1 p (BR o)) :
      Source S (OL ⊕ OR)
        (Sum.elim (fun o => (specL o).input) (fun o => (specR o).input))

abbrev Source.Origin {S O bounds} (_ : Source S O bounds) := O
def Source.leafBoundary {S O bounds} (_ : Source S O bounds) : O → Sequent := bounds

def Source.origins : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → List O
  | _, _, _, .leaf _ => [PUnit.unit]
  | _, _, _, .iw _ _ _ _ _ body => body.origins
  | _, _, _, .phase _ _ _ _ _ left right _ _ _ =>
      left.origins.map Sum.inl ++ right.origins.map Sum.inr

theorem Source.origin_mem : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (source : Source S O bounds) → (o : O) → o ∈ source.origins
  | _, _, _, .leaf _, o => by cases o; exact List.mem_cons_self
  | _, _, _, .iw _ _ _ _ _ body, o => body.origin_mem o
  | _, _, _, .phase _ _ _ _ _ left right _ _ _, .inl o =>
      List.mem_append_left _ (List.mem_map.mpr ⟨o, left.origin_mem o, rfl⟩)
  | _, _, _, .phase _ _ _ _ _ left right _ _ _, .inr o =>
      List.mem_append_right _ (List.mem_map.mpr ⟨o, right.origin_mem o, rfl⟩)

theorem Source.origins_nodup : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (source : Source S O bounds) → source.origins.Nodup
  | _, _, _, .leaf _ => by simp [Source.origins]
  | _, _, _, .iw _ _ _ _ _ body => body.origins_nodup
  | _, _, _, .phase _ _ _ _ _ left right _ _ _ => by
      apply (left.origins_nodup.map Sum.inl_injective).append
        (right.origins_nodup.map Sum.inr_injective)
      intro a ha hb
      rcases List.mem_map.mp ha with ⟨x, _, rfl⟩
      rcases List.mem_map.mp hb with ⟨y, _, impossible⟩
      cases impossible

def Source.originWitness : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → O
  | _, _, _, .leaf _ => PUnit.unit
  | _, _, _, .iw _ _ _ _ _ body => body.originWitness
  | _, _, _, .phase _ _ _ _ _ left _ _ _ _ => .inl left.originWitness

theorem Source.origins_nonempty {S O bounds} (source : Source S O bounds) :
    source.origins ≠ [] := by
  intro empty
  have present := source.origin_mem source.originWitness
  rw [empty] at present
  exact List.not_mem_nil present

def Source.owners : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → List Nat
  | _, _, _, .leaf _ => []
  | _, _, _, .iw _ _ _ _ _ body => body.owners
  | _, _, _, .phase _ uid _ _ _ left right _ _ _ => uid :: (left.owners ++ right.owners)

/-- Source-only freshness and disjoint ownership, not target admission. -/
def WellScoped : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → Prop
  | _, _, _, .leaf _ => True
  | _, _, _, .iw _ _ _ _ _ body => WellScoped body
  | _, _, _, .phase _ uid _ _ _ left right _ _ _ =>
      WellScoped left ∧ WellScoped right ∧ uid ∉ left.owners ++ right.owners ∧
        List.Disjoint left.owners right.owners

def rightEmptyEquiv (A : Type) : A ≃ A ⊕ PEmpty where
  toFun := Sum.inl
  invFun := fun x => match x with | .inl a => a | .inr e => nomatch e
  left_inv := fun _ => rfl
  right_inv := fun x => by cases x with | inl a => rfl | inr e => exact PEmpty.elim e

def topDiagram (key uid : Nat) (role : Fin 2) (p : Parameters) {out : Sequent}
    (spec : TopSpec role p out) : Diagram out :=
  PreparedSysComSource.transport spec.output
    (.rule key (.top role p uid spec.gamma spec.pi) (.cons (.hole spec.input) .nil))

def topHoleEquiv (key uid : Nat) (role : Fin 2) (p : Parameters) {out : Sequent}
    (spec : TopSpec role p out) : PUnit ≃ (topDiagram key uid role p spec).Hole := by
  rcases spec with ⟨gamma, pi, single, equal⟩
  cases equal
  exact rightEmptyEquiv _

theorem topHole_boundary (key uid : Nat) (role : Fin 2) (p : Parameters) {out : Sequent}
    (spec : TopSpec role p out) (o : PUnit) :
    (topDiagram key uid role p spec).holeBoundary (topHoleEquiv key uid role p spec o) =
      spec.input := by
  rcases spec with ⟨gamma, pi, single, equal⟩
  cases equal
  cases o
  rfl

section Decoration
variable (uid : Nat) (role : Fin 2) (p : Parameters)

mutual
def decorate : {S : Sequent} → (D : Diagram S) → (key : D.Hole → Nat) →
    ((h : D.Hole) → TopSpec role p (D.holeBoundary h)) → Diagram S
  | _, .hole _, key, specs => topDiagram (key PUnit.unit) uid role p (specs PUnit.unit)
  | _, .rule key r children, keys, specs => .rule key r (decorateChildren children keys specs)
def decorateChildren : {Ss : List Sequent} → (Ds : Children Ss) → (key : Ds.Hole → Nat) →
    ((h : Ds.Hole) → TopSpec role p (Ds.holeBoundary h)) → Children Ss
  | _, .nil, _, _ => .nil
  | _, .cons head tail, keys, specs => .cons
      (decorate head (fun h => keys (.inl h)) (fun h => specs (.inl h)))
      (decorateChildren tail (fun h => keys (.inr h)) (fun h => specs (.inr h)))
end

mutual
def decorateHoleEquiv : {S : Sequent} → (D : Diagram S) → (key : D.Hole → Nat) →
    (specs : (h : D.Hole) → TopSpec role p (D.holeBoundary h)) →
    D.Hole ≃ (decorate uid role p D key specs).Hole
  | _, .hole _, key, specs => topHoleEquiv (key PUnit.unit) uid role p (specs PUnit.unit)
  | _, .rule _ _ children, key, specs => decorateChildrenHoleEquiv children key specs
def decorateChildrenHoleEquiv : {Ss : List Sequent} → (Ds : Children Ss) →
    (key : Ds.Hole → Nat) →
    (specs : (h : Ds.Hole) → TopSpec role p (Ds.holeBoundary h)) →
    Ds.Hole ≃ (decorateChildren uid role p Ds key specs).Hole
  | _, .nil, _, _ => Equiv.refl _
  | _, .cons head tail, key, specs => Equiv.sumCongr
      (decorateHoleEquiv head (fun h => key (.inl h)) (fun h => specs (.inl h)))
      (decorateChildrenHoleEquiv tail (fun h => key (.inr h)) (fun h => specs (.inr h)))
end

mutual
theorem decorateHole_boundary : {S : Sequent} → (D : Diagram S) → (key : D.Hole → Nat) →
    (specs : (h : D.Hole) → TopSpec role p (D.holeBoundary h)) → (h : D.Hole) →
    (decorate uid role p D key specs).holeBoundary (decorateHoleEquiv uid role p D key specs h) =
      (specs h).input
  | _, .hole _, key, specs, h => by cases h; exact topHole_boundary _ _ _ _ _ _
  | _, .rule _ _ children, key, specs, h => decorateChildrenHole_boundary children key specs h
theorem decorateChildrenHole_boundary : {Ss : List Sequent} → (Ds : Children Ss) →
    (key : Ds.Hole → Nat) →
    (specs : (h : Ds.Hole) → TopSpec role p (Ds.holeBoundary h)) → (h : Ds.Hole) →
    (decorateChildren uid role p Ds key specs).holeBoundary
        (decorateChildrenHoleEquiv uid role p Ds key specs h) = (specs h).input
  | _, .nil, _, _, h => nomatch h
  | _, .cons head tail, key, specs, h => by
      cases h with
      | inl h =>
          exact decorateHole_boundary head (fun x => key (.inl x))
            (fun x => specs (.inl x)) h
      | inr h =>
          exact decorateChildrenHole_boundary tail (fun x => key (.inr x))
            (fun x => specs (.inr x)) h
end

mutual
theorem decorate_eq_fill : {S : Sequent} → (D : Diagram S) → (key : D.Hole → Nat) →
    (specs : (h : D.Hole) → TopSpec role p (D.holeBoundary h)) →
    decorate uid role p D key specs =
      D.fill (fun h => topDiagram (key h) uid role p (specs h))
  | _, .hole _, _, _ => rfl
  | _, .rule key r children, keys, specs =>
      congrArg (Diagram.rule key r) (decorateChildren_eq_fill children keys specs)
theorem decorateChildren_eq_fill : {Ss : List Sequent} → (Ds : Children Ss) →
    (key : Ds.Hole → Nat) →
    (specs : (h : Ds.Hole) → TopSpec role p (Ds.holeBoundary h)) →
    decorateChildren uid role p Ds key specs =
      Ds.fill (fun h => topDiagram (key h) uid role p (specs h))
  | _, .nil, _, _ => rfl
  | _, .cons head tail, keys, specs => by
      change Children.cons _ _ = Children.cons _ _
      rw [decorate_eq_fill, decorateChildren_eq_fill]
end
end Decoration

/-- An adapter on an existing native diagram: no alternative proof syntax. -/
structure Native (S : Sequent) (O : Type) (bounds : O → Sequent) where
  diagram : Diagram S
  holes : O ≃ diagram.Hole
  boundary : ∀ o, diagram.holeBoundary (holes o) = bounds o

def Native.specAtHole {S O bounds} (n : Native S O bounds) (role : Fin 2) (p : Parameters)
    (specs : (o : O) → TopSpec role p (bounds o)) (h : n.diagram.Hole) :
    TopSpec role p (n.diagram.holeBoundary h) :=
  (specs (n.holes.symm h)).rebase
    ((n.boundary (n.holes.symm h)).symm.trans
      (congrArg n.diagram.holeBoundary (n.holes.apply_symm_apply h)))

def Native.decorate {S O bounds} (n : Native S O bounds) (uid : Nat) (role : Fin 2)
    (p : Parameters) (keys : O → Nat) (specs : (o : O) → TopSpec role p (bounds o)) :
    Native S O (fun o => (specs o).input) where
  diagram := RecursiveSysComSource.decorate uid role p n.diagram
    (fun h => keys (n.holes.symm h)) (n.specAtHole role p specs)
  holes := n.holes.trans (decorateHoleEquiv uid role p n.diagram
    (fun h => keys (n.holes.symm h)) (n.specAtHole role p specs))
  boundary := by
    intro o
    exact (decorateHole_boundary uid role p n.diagram
      (fun h => keys (n.holes.symm h)) (n.specAtHole role p specs) (n.holes o)).trans (by
        change (specs (n.holes.symm (n.holes o))).input = (specs o).input
        rw [n.holes.symm_apply_apply])

def Native.iw {S O bounds} (n : Native S O bounds) (key : Nat) (a : Formula)
    (gamma pi : Context) (equal : S = ⟨gamma, pi⟩) :
    Native ⟨{a} + gamma, pi⟩ O bounds := by
  cases equal
  exact ⟨.rule key (.weakening a gamma pi) (.cons n.diagram .nil),
    n.holes.trans (rightEmptyEquiv _), n.boundary⟩

def Native.bottom {S OL OR BL BR} (left : Native S OL BL) (right : Native S OR BR)
    (key uid : Nat) (p : Parameters) : Native S (OL ⊕ OR) (Sum.elim BL BR) where
  diagram := .rule key (.bottom p uid S) (.cons left.diagram (.cons right.diagram .nil))
  holes := Equiv.sumCongr left.holes (right.holes.trans (rightEmptyEquiv _))
  boundary := fun o => match o with
    | .inl x => left.boundary x
    | .inr x => right.boundary x

def Source.native : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → Native S O bounds
  | _, _, _, .leaf S => ⟨.hole S, Equiv.refl _, fun _ => rfl⟩
  | _, _, _, .iw key a gamma pi _ body => body.native.iw key a gamma pi rfl
  | _, _, _, .phase key uid p _ _ left right keys specL specR =>
      Native.bottom
        (left.native.decorate uid 0 p (fun o => keys (.inl o)) specL)
        (right.native.decorate uid 1 p (fun o => keys (.inr o)) specR) key uid p

def Source.erase {S O bounds} (source : Source S O bounds) : Diagram S := source.native.diagram
def Source.holeEquiv {S O bounds} (source : Source S O bounds) : O ≃ source.erase.Hole :=
  source.native.holes
theorem Source.holeBoundary {S O bounds} (source : Source S O bounds) (o : O) :
    source.erase.holeBoundary (source.holeEquiv o) = bounds o := source.native.boundary o

#check Source.phase
#check Source.native
#check Source.holeEquiv
#check Source.holeBoundary
#print axioms Source.holeBoundary
#print axioms Source.origins_nodup
#print axioms decorate_eq_fill
end Potkin.Research.RecursiveSysComSource

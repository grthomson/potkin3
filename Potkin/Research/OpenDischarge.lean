import Potkin.Research.DependencyInterface
import Potkin.AllHoleFilling

/-!
# Stable designated owners on native open derivations

The added data are rule annotations, not a replacement tree or context.
`LocalOccurrence.id` is an exact registered rule instance; a bottom's `uid`
is instead the identity of its declaration in this derivation.  The two
identities must not be conflated.  Local rule correctness and actual
ordered-branch discharge are independent predicates.

`Imp` must be instantiated by the actual implication constructor of the
chosen propositional signature.  It is not an assumed admission theorem.
The local fragment here comprises identity, IW, IC, implication right and
the two tops/common bottom of the explicitly annotated Sys(com).
-/

namespace Potkin.Research.OpenDischarge

universe u v
variable {sigma : Signature.{u, v}}

abbrev Parameters := DependencyInterface.Parameters

inductive Data (sigma : Signature.{u, v}) where
  | identity (formula : Formula sigma)
  | weakening (formula : Formula sigma) (gamma pi : Context sigma)
  | contraction (formula : Formula sigma) (gamma pi : Context sigma)
  | top (role : Fin 2) (parameters : Parameters sigma)
      (owner : Nat) (gamma pi : Context sigma)
  | bottom (parameters : Parameters sigma) (uid : Nat) (conclusion : Sequent sigma)
  | implicationRight (gamma : Context sigma)
      (antecedent consequent result : Formula sigma)

abbrev topInput := @DependencyInterface.topInput
abbrev topOutput := @DependencyInterface.topOutput

def ExactInstance (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (o : LocalOccurrence sigma (Data sigma)) : Prop :=
  o.incidence.isSome ∧ match o.instanceData with
  | .identity a => o.kind = .logical ∧
      o.shape = ⟨[], .singleton ⟨{a}, {a}⟩⟩
  | .weakening a gamma pi => pi.card ≤ 1 ∧ o.kind = .structural ∧
      o.shape = ⟨[.singleton ⟨gamma, pi⟩], .singleton ⟨{a} + gamma, pi⟩⟩
  | .contraction a gamma pi => pi.card ≤ 1 ∧ o.kind = .structural ∧
      o.shape = ⟨[.singleton ⟨{a} + {a} + gamma, pi⟩],
        .singleton ⟨{a} + gamma, pi⟩⟩
  | .top role p _ gamma pi => pi.card ≤ 1 ∧ o.kind = .structural ∧
      o.shape = ⟨[.singleton (topInput role p gamma pi)],
        .singleton (topOutput role p gamma pi)⟩
  | .bottom _ _ S => S.rhs.card ≤ 1 ∧ o.kind = .structural ∧
      o.shape = ⟨[.singleton S, .singleton S], .singleton S⟩
  | .implicationRight gamma a b c => Imp a b c ∧ o.kind = .logical ∧
      o.shape = ⟨[.singleton ⟨{a} + gamma, {b}⟩],
        .singleton ⟨gamma, {c}⟩⟩

mutual
def ExactTree (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → CKTree sigma (Data sigma) G → Prop
  | _, .interface _ => True
  | _, .ordinary o children => ExactInstance Imp o ∧ ExactChildren Imp children

def ExactChildren (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → CKChildren sigma (Data sigma) Gs → Prop
  | _, .nil => True
  | _, .cons head tail => ExactTree Imp head ∧ ExactChildren Imp tail
end

structure Requirement (sigma : Signature.{u, v}) where
  owner : Nat
  topAddress : InternalAddress
  topRule : Nat
  role : Fin 2
  parameters : Parameters sigma

structure Grant (sigma : Signature.{u, v}) where
  uid : Nat
  address : InternalAddress
  rule : Nat
  parameters : Parameters sigma

def Compatible (r : Requirement sigma) (g : Grant sigma) : Prop :=
  r.owner = g.uid ∧ r.parameters = g.parameters ∧
    ∃ suffix, r.topAddress = g.address ++ [r.role.val] ++ suffix

structure Events (sigma : Signature.{u, v}) where
  requirements : List (Requirement sigma)
  grants : List (Grant sigma)

def Events.append (a b : Events sigma) : Events sigma :=
  ⟨a.requirements ++ b.requirements, a.grants ++ b.grants⟩

def rootEvents (address : InternalAddress)
    (o : LocalOccurrence sigma (Data sigma)) : Events sigma :=
  match o.instanceData with
  | .top role p owner _ _ => ⟨[⟨owner, address, o.id, role, p⟩], []⟩
  | .bottom p uid _ => ⟨[], [⟨uid, address, o.id, p⟩]⟩
  | _ => ⟨[], []⟩

mutual
def events : {G : Hypersequent sigma} → CKTree sigma (Data sigma) G →
    InternalAddress → Events sigma
  | _, .interface _, _ => ⟨[], []⟩
  | _, .ordinary o children, address =>
      (rootEvents address o).append (childEvents children address 0)

def childEvents : {Gs : List (Hypersequent sigma)} →
    CKChildren sigma (Data sigma) Gs → InternalAddress → Nat → Events sigma
  | _, .nil, _, _ => ⟨[], []⟩
  | _, .cons head tail, address, slot =>
      (events head (address ++ [slot])).append (childEvents tail address (slot + 1))
end

def UniqueOwners (e : Events sigma) : Prop := (e.grants.map Grant.uid).Nodup

def LegalEvents (e : Events sigma) (external : List (Grant sigma)) : Prop :=
  ∀ r ∈ e.requirements, ∃ g ∈ e.grants ++ external, Compatible r g

def Legal (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) (external : List (Grant sigma)) : Prop :=
  ExactTree Imp tree ∧ UniqueOwners (events tree address) ∧
    LegalEvents (events tree address) external

def HasInternalOwner (e : Events sigma) (r : Requirement sigma) : Prop :=
  ∃ g ∈ e.grants, g.uid = r.owner

noncomputable def outstanding (e : Events sigma) : List (Requirement sigma) := by
  classical
  exact e.requirements.filter (fun r => ¬ HasInternalOwner e r)

def InteriorLegal (e : Events sigma) : Prop :=
  ∀ r ∈ e.requirements, HasInternalOwner e r → ∃ g ∈ e.grants, Compatible r g

def OutstandingLegal (e : Events sigma) (external : List (Grant sigma)) : Prop :=
  ∀ r ∈ outstanding e, ∃ g ∈ external, Compatible r g

def Fresh (e : Events sigma) (external : List (Grant sigma)) : Prop :=
  ∀ gi ∈ e.grants, ∀ ge ∈ external, gi.uid ≠ ge.uid

theorem mem_outstanding (e : Events sigma) (r : Requirement sigma) :
    r ∈ outstanding e ↔ r ∈ e.requirements ∧ ¬ HasInternalOwner e r := by
  classical
  simp [outstanding]

theorem legality_interface_iff (e : Events sigma) (external : List (Grant sigma))
    (fresh : Fresh e external) :
    LegalEvents e external ↔ InteriorLegal e ∧ OutstandingLegal e external := by
  constructor
  · intro legal
    constructor
    · intro r hr internal
      rcases legal r hr with ⟨g, hg, compatible⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact ⟨g, hg, compatible⟩
      · rcases internal with ⟨gi, hgi, uid⟩
        exact False.elim (fresh gi hgi g hg (uid.trans compatible.1))
    · intro r hr
      rcases (mem_outstanding e r).mp hr with ⟨present, free⟩
      rcases legal r present with ⟨g, hg, compatible⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact False.elim (free ⟨g, hg, compatible.1.symm⟩)
      · exact ⟨g, hg, compatible⟩
  · rintro ⟨interior, outside⟩ r hr
    by_cases internal : HasInternalOwner e r
    · rcases interior r hr internal with ⟨g, hg, compatible⟩
      exact ⟨g, List.mem_append_left _ hg, compatible⟩
    · rcases outside r ((mem_outstanding e r).mpr ⟨hr, internal⟩) with
        ⟨g, hg, compatible⟩
      exact ⟨g, List.mem_append_right _ hg, compatible⟩

mutual
theorem exact_fill (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma (Data sigma) G) →
    (assignment : tree.LeafAssignment) →
    (ExactTree Imp (tree.fillAssignment assignment) ↔
      ExactTree Imp tree ∧ ∀ hole, ExactTree Imp (assignment hole))
  | _, .interface _, assignment => by
      change ExactTree Imp (assignment PUnit.unit) ↔
        True ∧ ∀ hole : PUnit, ExactTree Imp (assignment hole)
      constructor
      · intro h; refine ⟨trivial, ?_⟩; intro hole; cases hole; exact h
      · intro h; exact h.2 PUnit.unit
  | _, .ordinary o children, assignment => by
      change ExactInstance Imp o ∧ ExactChildren Imp (children.fillAssignment assignment) ↔
        (ExactInstance Imp o ∧ ExactChildren Imp children) ∧
          ∀ hole, ExactTree Imp (assignment hole)
      rw [exact_fill_children Imp children assignment]
      constructor
      · rintro ⟨ho, hc, ha⟩; exact ⟨⟨ho, hc⟩, ha⟩
      · rintro ⟨⟨ho, hc⟩, ha⟩; exact ⟨ho, hc, ha⟩

theorem exact_fill_children (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma (Data sigma) Gs) →
    (assignment : children.LeafAssignment) →
    (ExactChildren Imp (children.fillAssignment assignment) ↔
      ExactChildren Imp children ∧ ∀ hole, ExactTree Imp (assignment hole))
  | _, .nil, _ => by
      constructor
      · intro _; refine ⟨trivial, ?_⟩; intro hole; exact nomatch hole
      · intro _; trivial
  | _, .cons head tail, assignment => by
      change ExactTree Imp (head.fillAssignment (fun h => assignment (.inl h))) ∧
        ExactChildren Imp (tail.fillAssignment (fun h => assignment (.inr h))) ↔
        (ExactTree Imp head ∧ ExactChildren Imp tail) ∧ ∀ hole, ExactTree Imp (assignment hole)
      rw [exact_fill Imp head, exact_fill_children Imp tail]
      constructor
      · rintro ⟨⟨hh, ah⟩, ⟨ht, tailAssignment⟩⟩
        refine ⟨⟨hh, ht⟩, ?_⟩
        intro hole; cases hole with
        | inl h => exact ah h
        | inr h => exact tailAssignment h
      · rintro ⟨⟨hh, ht⟩, ha⟩
        exact ⟨⟨hh, fun h => ha (.inl h)⟩, ⟨ht, fun h => ha (.inr h)⟩⟩
end

#print axioms legality_interface_iff
#print axioms exact_fill

end Potkin.Research.OpenDischarge

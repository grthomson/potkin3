import Potkin.CKCut

/-!
# A finite dependency interface for the actual `Sys(com)` fragment

Source: Ciabattoni--Genco, arXiv:1805.04852v1, Definition 2.1 and
Example 3.2.  A top in branch 0 changes `Phi,Gamma => Pi` into
`Psi,Gamma => Pi`; branch 1 does the reverse.  Their common bottom has
two ordered premises with the same sequent as its conclusion.  Repeated
tops are permitted.  We make the designated bottom instance explicit.

The records below are finite occurrence metadata, not another proof/cut
carrier.  Legality is defined independently by lookup of an actual bottom,
exact shared parameters and physical branch ancestry.  The interface is
then derived by deleting obligations whose owner occurs inside the piece.
It does not contain the piece, its decompositions, or a legality theorem.
There are no eigenvariables in this fragment.  Freshness here means that
external owner addresses cannot alias an internal bottom occurrence.
-/

namespace Potkin.Research.DependencyInterface

universe u v
variable {sigma : Signature.{u, v}}

/-- Only the shared active antecedent multisets are persistent. -/
structure Parameters (sigma : Signature.{u, v}) where
  phi : Context sigma
  psi : Context sigma

/-- Tags of the concrete source fragment; local contexts may vary at tops. -/
inductive Data (sigma : Signature.{u, v}) where
  | identity (formula : Formula sigma)
  | weakening (formula : Formula sigma) (gamma pi : Context sigma)
  | contraction (formula : Formula sigma) (gamma pi : Context sigma)
  | top (role : Fin 2) (parameters : Parameters sigma)
      (owner : InternalAddress) (ownerRule : Nat) (gamma pi : Context sigma)
  | bottom (parameters : Parameters sigma) (conclusion : Sequent sigma)

def topInput (role : Fin 2) (p : Parameters sigma)
    (gamma pi : Context sigma) : Sequent sigma :=
  ⟨(if role.val = 0 then p.phi else p.psi) + gamma, pi⟩

def topOutput (role : Fin 2) (p : Parameters sigma)
    (gamma pi : Context sigma) : Sequent sigma :=
  ⟨(if role.val = 0 then p.psi else p.phi) + gamma, pi⟩

/-- Literal rule-boundary checking, separate from dependency legality. -/
def ExactInstance (o : LocalOccurrence sigma (Data sigma)) : Prop :=
  o.incidence.isSome ∧ match o.instanceData with
  | .identity a => o.kind = .logical ∧
      o.shape = ⟨[], .singleton ⟨{a}, {a}⟩⟩
  | .weakening a gamma pi => pi.card ≤ 1 ∧ o.kind = .structural ∧
      o.shape = ⟨[.singleton ⟨gamma, pi⟩], .singleton ⟨{a} + gamma, pi⟩⟩
  | .contraction a gamma pi => pi.card ≤ 1 ∧ o.kind = .structural ∧
      o.shape = ⟨[.singleton ⟨{a} + {a} + gamma, pi⟩],
        .singleton ⟨{a} + gamma, pi⟩⟩
  | .top role p _ _ gamma pi => pi.card ≤ 1 ∧ o.kind = .structural ∧
      o.shape = ⟨[.singleton (topInput role p gamma pi)],
        .singleton (topOutput role p gamma pi)⟩
  | .bottom _ S => S.rhs.card ≤ 1 ∧ o.kind = .structural ∧
      o.shape = ⟨[.singleton S, .singleton S], .singleton S⟩

mutual
def ExactTree : {G : Hypersequent sigma} → CKTree sigma (Data sigma) G → Prop
  | _, .interface _ => True
  | _, .ordinary o children => ExactInstance o ∧ ExactChildren children
def ExactChildren : {Gs : List (Hypersequent sigma)} →
    CKChildren sigma (Data sigma) Gs → Prop
  | _, .nil => True
  | _, .cons head tail => ExactTree head ∧ ExactChildren tail
end

/-- One physical top occurrence, with its designated discharge owner. -/
structure Requirement (sigma : Signature.{u, v}) where
  owner : InternalAddress
  ownerRule : Nat
  topAddress : InternalAddress
  topRule : Nat
  role : Fin 2
  parameters : Parameters sigma

/-- One actual bottom occurrence.  The physical address is its identity. -/
structure Grant (sigma : Signature.{u, v}) where
  address : InternalAddress
  rule : Nat
  parameters : Parameters sigma

/-- Exact matching and ordered-branch ancestry, not just equal endsequents. -/
def Compatible (r : Requirement sigma) (g : Grant sigma) : Prop :=
  r.owner = g.address ∧ r.ownerRule = g.rule ∧ r.parameters = g.parameters ∧
    ∃ suffix, r.topAddress = g.address ++ [r.role.val] ++ suffix

/-- Finite traversal output.  Duplicate requests remain duplicate list rows. -/
structure Events (sigma : Signature.{u, v}) where
  requirements : List (Requirement sigma)
  grants : List (Grant sigma)

def Events.append (a b : Events sigma) : Events sigma :=
  ⟨a.requirements ++ b.requirements, a.grants ++ b.grants⟩

def rootEvents (address : InternalAddress)
    (o : LocalOccurrence sigma (Data sigma)) : Events sigma :=
  match o.instanceData with
  | .top role p owner ownerRule _ _ =>
      ⟨[⟨owner, ownerRule, address, o.id, role, p⟩], []⟩
  | .bottom p _ => ⟨[], [⟨address, o.id, p⟩]⟩
  | _ => ⟨[], []⟩

mutual
/-- Traverse existing ordered native trees, retaining absolute addresses. -/
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

/-- Independent legality: every top resolves against an actual internal or
external bottom with the exact parameters and the correct physical branch. -/
def LegalEvents (e : Events sigma) (external : List (Grant sigma)) : Prop :=
  ∀ r ∈ e.requirements, ∃ g ∈ e.grants ++ external, Compatible r g

def Legal {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (address : InternalAddress) (external : List (Grant sigma)) : Prop :=
  ExactTree tree ∧ LegalEvents (events tree address) external

/-- Whether the designated owner physically occurs in this piece. -/
def HasInternalOwner (e : Events sigma) (r : Requirement sigma) : Prop :=
  ∃ g ∈ e.grants, g.address = r.owner

/-- Only outstanding top obligations survive the interface projection. -/
noncomputable def interface (e : Events sigma) : List (Requirement sigma) := by
  classical
  exact e.requirements.filter (fun r => ¬ HasInternalOwner e r)

/-- Interior dependencies must be checked once; they are not exported. -/
def InteriorLegal (e : Events sigma) : Prop :=
  ∀ r ∈ e.requirements, HasInternalOwner e r →
    ∃ g ∈ e.grants, Compatible r g

def InterfaceLegal (e : Events sigma) (external : List (Grant sigma)) : Prop :=
  ∀ r ∈ interface e, ∃ g ∈ external, Compatible r g

/-- No external owner can impersonate a bottom inside the extracted piece. -/
def Fresh (e : Events sigma) (external : List (Grant sigma)) : Prop :=
  ∀ gi ∈ e.grants, ∀ ge ∈ external, gi.address ≠ ge.address

theorem mem_interface (e : Events sigma) (r : Requirement sigma) :
    r ∈ interface e ↔ r ∈ e.requirements ∧ ¬ HasInternalOwner e r := by
  classical
  simp [interface]

/-- Universal independently defined legality/interface agreement. -/
theorem legality_interface_iff (e : Events sigma) (external : List (Grant sigma))
    (fresh : Fresh e external) :
    LegalEvents e external ↔ InteriorLegal e ∧ InterfaceLegal e external := by
  classical
  constructor
  · intro legal
    constructor
    · intro r hr internal
      rcases legal r hr with ⟨g, hg, compatible⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact ⟨g, hg, compatible⟩
      · rcases internal with ⟨gi, hgi, address⟩
        exact False.elim (fresh gi hgi g hg (address.trans compatible.1))
    · intro r hr
      rcases (mem_interface e r).mp hr with ⟨present, free⟩
      rcases legal r present with ⟨g, hg, compatible⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact False.elim (free ⟨g, hg, compatible.1.symm⟩)
      · exact ⟨g, hg, compatible⟩
  · rintro ⟨interior, externalLegal⟩ r hr
    by_cases internal : HasInternalOwner e r
    · rcases interior r hr internal with ⟨g, hg, compatible⟩
      exact ⟨g, List.mem_append_left _ hg, compatible⟩
    · rcases externalLegal r ((mem_interface e r).mpr ⟨hr, internal⟩) with
        ⟨g, hg, compatible⟩
      exact ⟨g, List.mem_append_right _ hg, compatible⟩

theorem native_legality_interface_iff {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (address : InternalAddress)
    (external : List (Grant sigma)) (fresh : Fresh (events tree address) external) :
    Legal tree address external ↔ ExactTree tree ∧
      InteriorLegal (events tree address) ∧ InterfaceLegal (events tree address) external := by
  rw [Legal, legality_interface_iff _ _ fresh]

/-- The interface really forgets interior detail: only its list of pending
demands matters for transport against any fixed external environment. -/
theorem interface_replacement (old new : Events sigma)
    (same : interface old = interface new) (external : List (Grant sigma))
    (freshOld : Fresh old external) (freshNew : Fresh new external)
    (newInterior : InteriorLegal new) (oldLegal : LegalEvents old external) :
    LegalEvents new external := by
  apply (legality_interface_iff new external freshNew).mpr
  refine ⟨newInterior, ?_⟩
  have oldInterface := ((legality_interface_iff old external freshOld).mp oldLegal).2
  simpa only [InterfaceLegal, same] using oldInterface

/-- A replacement of an open native piece needs both exact local rules and
compatible outstanding dependencies; matching the boundary is insufficient. -/
theorem native_replacement {G : Hypersequent sigma}
    (old new : CKTree sigma (Data sigma) G) (address : InternalAddress)
    (external : List (Grant sigma))
    (same : interface (events old address) = interface (events new address))
    (freshOld : Fresh (events old address) external)
    (freshNew : Fresh (events new address) external)
    (newExact : ExactTree new) (newInterior : InteriorLegal (events new address))
    (oldLegal : Legal old address external) : Legal new address external :=
  ⟨newExact, interface_replacement _ _ same external freshOld freshNew
    newInterior oldLegal.2⟩

/-- Existing native refill is kept literal: no dependency metadata changes it. -/
theorem native_refill {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (cut : CKBranchCut tree) : cut.fill cut.detached = tree :=
  cut.fill_detached_reconstructs

#print axioms legality_interface_iff
#print axioms native_legality_interface_iff
#print axioms interface_replacement
#print axioms native_replacement
#print axioms native_refill

end Potkin.Research.DependencyInterface

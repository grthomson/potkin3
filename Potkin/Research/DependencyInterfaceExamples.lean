import Potkin.Research.DependencyInterface
import Potkin.Research.RevivalInterface
import Potkin.CompleteQuotation
import Potkin.Research.RemainderExtractionFlags

/-!
# A native cut crossing the discharge of a real `Sys(com)` instance

This is a finite exact stock of the published Example 3.2, with ordinary
LJ identity/IW/IC.  It is not a translation of all 2-systems or full LJ.
The public native checker checks local instances; the independent global
dependency theorem below additionally checks their designated discharge.
-/

namespace Potkin.Research.DependencyInterfaceExamples

open Potkin.Research.DependencyInterface
open Potkin.Research.ContextCutPackets Potkin.Research.ContextCutAction
open Potkin.Research.RemainderExtractionFlags
abbrev sigma := RevivalInterface.sigma
abbrev p := RevivalInterface.p
abbrev q := RevivalInterface.q

def parameters : Parameters sigma := ⟨{p}, {q}⟩
def incompatibleParameters : Parameters sigma := ⟨{p}+{p}, {q}+{p}⟩
def identityS : Sequent sigma := ⟨{p}, {p}⟩
def doubledS : Sequent sigma := ⟨{p}+{p}, {p}⟩
def commonS : Sequent sigma := ⟨{q}+{p}, {p}⟩
def GI := Hypersequent.singleton identityS
def GD := Hypersequent.singleton doubledS
def GS := Hypersequent.singleton commonS

inductive Label where
  | identity | weakenP | weakenQ | contractP | topLeft | topRight | topBad | bottom
  deriving DecidableEq, Repr

def labels : List Label :=
  [.identity, .weakenP, .weakenQ, .contractP, .topLeft, .topRight, .topBad, .bottom]
def id : Label → Nat
  | .identity => 500 | .weakenP => 501 | .weakenQ => 502 | .contractP => 503
  | .topLeft => 504 | .topRight => 505 | .topBad => 506 | .bottom => 507

private def profile (S : Sequent sigma) : ComponentProfile (.singleton S) := ⟨[S], rfl⟩
private def nullaryIncidence (S : Sequent sigma) :
    ComponentIncidence (⟨[], .singleton S⟩ : OccurrenceShape sigma) :=
  ⟨⟨fun i => Fin.elim0 i, profile S⟩, ∅⟩
private def unaryIncidence (I O : Sequent sigma) :
    ComponentIncidence (⟨[.singleton I], .singleton O⟩ : OccurrenceShape sigma) where
  profiles := ⟨fun i => Fin.cases (profile I) (fun j => Fin.elim0 j) i, profile O⟩
  edges := {⟨⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩,
    ⟨0, by change 0 < 1; decide⟩⟩}
private def binaryIncidence (S : Sequent sigma) :
    ComponentIncidence (⟨[.singleton S, .singleton S], .singleton S⟩ : OccurrenceShape sigma) where
  profiles := ⟨fun i => Fin.cases (profile S)
    (fun j => Fin.cases (profile S) (fun k => Fin.elim0 k) j) i, profile S⟩
  edges := {⟨⟨0, by change 0 < 2; decide⟩, ⟨0, by change 0 < 1; decide⟩,
      ⟨0, by change 0 < 1; decide⟩⟩,
    ⟨⟨1, by change 1 < 2; decide⟩, ⟨0, by change 0 < 1; decide⟩,
      ⟨0, by change 0 < 1; decide⟩⟩}

def unary (label : Label) (tag : Data sigma) (I O : Sequent sigma) :
    LocalOccurrence sigma (Data sigma) :=
  ⟨id label, .structural, ⟨[.singleton I], .singleton O⟩, tag,
    some (unaryIncidence I O)⟩

def occurrence : Label → LocalOccurrence sigma (Data sigma)
  | .identity => ⟨id .identity, .logical, ⟨[], GI⟩, .identity p,
      some (nullaryIncidence identityS)⟩
  | .weakenP => unary .weakenP (.weakening p {p} {p}) identityS doubledS
  | .weakenQ => unary .weakenQ (.weakening q {p} {p}) identityS commonS
  | .contractP => unary .contractP (.contraction p 0 {p}) doubledS identityS
  | .topLeft => unary .topLeft (.top ⟨0, by decide⟩ parameters [] (id .bottom) {p} {p})
      doubledS commonS
  | .topRight => unary .topRight (.top ⟨1, by decide⟩ parameters [] (id .bottom) {p} {p})
      commonS doubledS
  | .topBad => unary .topBad (.top ⟨0, by decide⟩ incompatibleParameters []
      (id .bottom) 0 {p}) doubledS commonS
  | .bottom => ⟨id .bottom, .structural, ⟨[GS, GS], GS⟩,
      .bottom parameters commonS, some (binaryIncidence commonS)⟩

theorem exact_occurrence (label : Label) : ExactInstance (occurrence label) := by
  cases label <;> simp [occurrence, unary, ExactInstance, identityS, doubledS,
    commonS, GI, GD, GS, topInput, topOutput, parameters, incompatibleParameters]

def registry := labels.map occurrence
def base : MaterialBase sigma (Data sigma) PrimitiveFragment.full where
  Member := fun _ => False
  member_material := fun h => False.elim h
  member_primitiveBoundary := fun h => False.elim h
def theory : ProofTheory sigma (Data sigma) where
  primitive := .full
  base := base
  rules := { logical := fun o => o ∈ registry ∧ o.kind = .logical
             structural := fun o => o ∈ registry ∧ o.kind = .structural }
  initial := fun _ => False
def presentation : EquippedPresentation theory where
  registry := registry
  uniqueIds := by decide
  admitted := by
    intro o h
    rcases List.mem_map.mp h with ⟨label, _, rfl⟩
    cases label <;>
      first | exact .logical rfl ⟨h, rfl⟩ | exact .structural rfl ⟨h, rfl⟩

theorem registered (label : Label) : occurrence label ∈ registry := by
  apply List.mem_map.mpr
  refine ⟨label, ?_, rfl⟩
  cases label <;> simp [labels]

def identity : CKTree sigma (Data sigma) GI := .ordinary (occurrence .identity) .nil
def doubled : CKTree sigma (Data sigma) GD :=
  .ordinary (occurrence .weakenP) (.cons identity .nil)
def factor : CKTree sigma (Data sigma) GS :=
  .ordinary (occurrence .topLeft) (.cons doubled .nil)
def badFactor : CKTree sigma (Data sigma) GS :=
  .ordinary (occurrence .topBad) (.cons doubled .nil)
def repeatedInterior : CKTree sigma (Data sigma) GD :=
  .ordinary (occurrence .weakenP)
    (.cons (.ordinary (occurrence .contractP) (.cons doubled .nil)) .nil)
def replacement : CKTree sigma (Data sigma) GS :=
  .ordinary (occurrence .topLeft) (.cons repeatedInterior .nil)
def second : CKTree sigma (Data sigma) GS :=
  .ordinary (occurrence .weakenQ)
    (.cons (.ordinary (occurrence .contractP)
      (.cons (.ordinary (occurrence .topRight)
        (.cons (.ordinary (occurrence .weakenQ) (.cons identity .nil)) .nil)) .nil)) .nil)
def source : CKTree sigma (Data sigma) GS :=
  .ordinary (occurrence .bottom) (.cons factor (.cons second .nil))
def replaced : CKTree sigma (Data sigma) GS :=
  .ordinary (occurrence .bottom) (.cons replacement (.cons second .nil))
def incompatible : CKTree sigma (Data sigma) GS :=
  .ordinary (occurrence .bottom) (.cons badFactor (.cons second .nil))

theorem source_complete : source.IsComplete := by trivial
theorem replaced_complete : replaced.IsComplete := by trivial
theorem incompatible_complete : incompatible.IsComplete := by trivial

theorem source_registered : LocallyAdmittedTree presentation source := by
  simp [source, factor, doubled, identity, second, LocallyAdmittedTree,
    LocallyAdmittedChildren, presentation, registered]

theorem replaced_registered : LocallyAdmittedTree presentation replaced := by
  simp [replaced, replacement, repeatedInterior, doubled, identity, second,
    LocallyAdmittedTree, LocallyAdmittedChildren, presentation, registered]

theorem incompatible_registered : LocallyAdmittedTree presentation incompatible := by
  simp [incompatible, badFactor, doubled, identity, second,
    LocallyAdmittedTree, LocallyAdmittedChildren, presentation, registered]

def checkedSource := CompleteQuotation.checkedOfComplete presentation source
  source_registered source_complete
def checkedReplacement := CompleteQuotation.checkedOfComplete presentation replaced
  replaced_registered replaced_complete
def checkedIncompatible := CompleteQuotation.checkedOfComplete presentation incompatible
  incompatible_registered incompatible_complete

theorem checked_source_realize : checkedSource.realize = source :=
  CompleteQuotation.quote_realize _ _ _ _
theorem checked_replacement_realize : checkedReplacement.realize = replaced :=
  CompleteQuotation.quote_realize _ _ _ _
theorem checked_incompatible_realize : checkedIncompatible.realize = incompatible :=
  CompleteQuotation.quote_realize _ _ _ _

mutual
private def pass : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → CKCutPlan tree
  | _, .interface G => .interface G
  | _, .ordinary o children => .ordinary o children (passChildren children)
private def passChildren : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → CKChildCuts children
  | _, .nil => .nil
  | _, .cons head tail => .cons head tail (.descend (pass head)) (passChildren tail)
end

mutual
private def pass_no_site : {G : Hypersequent sigma} →
    (tree : CKTree sigma (Data sigma) G) → (pass tree).Site → False
  | _, .interface _, site => nomatch site
  | _, .ordinary _ children, site => pass_children_no_site children site
private def pass_children_no_site : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) Gs) → (passChildren children).Site → False
  | _, .nil, site => nomatch site
  | _, .cons head tail, site => by
      change (pass head).Site ⊕ (passChildren tail).Site at site
      cases site with
      | inl site => exact pass_no_site head site
      | inr site => exact pass_children_no_site tail site
end

/-- A proper CK cut: the top in physical premise 0 is separated from its
bottom at the root.  It is not a fabricated root selection. -/
def crossingPlan : CKCutPlan source :=
  .ordinary _ _ (.cons factor (.cons second .nil) (.detach trivial)
    (.cons second .nil (.descend (pass second)) .nil))
def crossing : CKCut source := ⟨trivial, crossingPlan⟩

def replacementFillers : (site : crossing.Site) →
    CKTree sigma (Data sigma) (crossing.plan.siteBoundary site)
  | .inl _ => replacement
  | .inr (.inl site) => False.elim (pass_no_site second site)
  | .inr (.inr site) => nomatch site

theorem crossing_replace : crossing.fill replacementFillers = replaced := rfl

def external : List (Grant sigma) := [⟨[], id .bottom, parameters⟩]

theorem interface_forgets_interior :
    interface (events factor [0]) = interface (events replacement [0]) := by
  rfl

theorem factor_interior : InteriorLegal (events factor [0]) := by
  intro r hr internal
  simp [factor, doubled, identity, events, childEvents, rootEvents, Events.append,
    HasInternalOwner, occurrence, unary] at internal

theorem factor_fresh : Fresh (events factor [0]) external := by
  intro gi hgi
  simp [factor, doubled, identity, events, childEvents, rootEvents, Events.append,
    occurrence, unary] at hgi

theorem factor_legal : LegalEvents (events factor [0]) external := by
  intro r hr
  have equal : r = ⟨[], id .bottom, [0], id .topLeft, ⟨0, by decide⟩, parameters⟩ := by
    simpa [factor, doubled, identity, events, childEvents, rootEvents, Events.append,
      occurrence, unary] using hr
  subst r
  refine ⟨⟨[], id .bottom, parameters⟩, ?_, rfl, rfl, rfl, [], rfl⟩
  simp [external, factor, doubled, identity, events, childEvents, rootEvents,
    Events.append, occurrence, unary]

theorem replacement_interior : InteriorLegal (events replacement [0]) := by
  intro r hr internal
  simp [replacement, repeatedInterior, doubled, identity, events, childEvents,
    rootEvents, Events.append, HasInternalOwner, occurrence, unary] at internal

theorem replacement_fresh : Fresh (events replacement [0]) external := by
  intro gi hgi
  simp [replacement, repeatedInterior, doubled, identity, events, childEvents,
    rootEvents, Events.append, occurrence, unary] at hgi

/-- Certified by the universal interface theorem, not by recounting trees. -/
theorem compatible_replacement_legal : LegalEvents (events replacement [0]) external :=
  interface_replacement _ _ interface_forgets_interior external
    factor_fresh replacement_fresh replacement_interior factor_legal

/-- Identical ordinary whole boundary, incompatible persistent parameters. -/
theorem bad_factor_rejected : ¬ LegalEvents (events badFactor [0]) external := by
  intro legal
  have present : (⟨[], id .bottom, [0], id .topBad, ⟨0, by decide⟩,
      incompatibleParameters⟩ : Requirement sigma) ∈ (events badFactor [0]).requirements := by
    simp [badFactor, doubled, identity, events, childEvents, rootEvents,
      Events.append, occurrence, unary]
  rcases legal _ present with ⟨g, hg, compatible⟩
  have equal : g = ⟨[], id .bottom, parameters⟩ := by
    simpa [badFactor, doubled, identity, events, childEvents, rootEvents,
      Events.append, occurrence, unary, external] using hg
  subst g
  have pack := congrArg Parameters.phi compatible.2.2.1
  have count := congrArg Multiset.card pack
  simpa [incompatibleParameters, parameters] using count

def leftRequirement : Requirement sigma :=
  ⟨[], id .bottom, [0], id .topLeft, ⟨0, by decide⟩, parameters⟩
def rightRequirement : Requirement sigma :=
  ⟨[], id .bottom, [1,0,0], id .topRight, ⟨1, by decide⟩, parameters⟩
def owner : Grant sigma := ⟨[], id .bottom, parameters⟩

theorem source_events : events source [] = ⟨[leftRequirement, rightRequirement], [owner]⟩ := rfl
theorem replacement_events : events replaced [] = events source [] := rfl

theorem source_legal : Legal source [] [] := by
  constructor
  · simp [source, factor, doubled, identity, second, ExactTree, ExactChildren, exact_occurrence]
  · rw [source_events]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with equal | equal
    · subst r
      refine ⟨owner, by simp, rfl, rfl, rfl, [], rfl⟩
    · subst r
      refine ⟨owner, by simp, rfl, rfl, rfl, [0,0], rfl⟩

theorem replaced_legal : Legal replaced [] [] := by
  constructor
  · simp [replaced, replacement, repeatedInterior, doubled, identity, second,
      ExactTree, ExactChildren, exact_occurrence]
  · have present : leftRequirement ∈ (events replacement [0]).requirements := by
      simp [leftRequirement, replacement, repeatedInterior, doubled, identity,
        events, childEvents, rootEvents, Events.append, occurrence, unary]
    rcases compatible_replacement_legal _ present with ⟨g, hg, compatible⟩
    have equalOwner : g = owner := by
      simpa [replacement, repeatedInterior, doubled, identity, events, childEvents,
        rootEvents, Events.append, occurrence, unary, external, owner] using hg
    subst g
    rw [replacement_events, source_events]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with equal | equal
    · subst r
      exact ⟨owner, by simp, compatible⟩
    · subst r
      refine ⟨owner, by simp, rfl, rfl, rfl, [0,0], rfl⟩

theorem factor_not_independently_closed : ¬ LegalEvents (events factor [0]) [] := by
  intro legal
  have present : leftRequirement ∈ (events factor [0]).requirements := by
    simp [leftRequirement, factor, doubled, identity, events, childEvents,
      rootEvents, Events.append, occurrence, unary]
  rcases legal _ present with ⟨g, hg, _⟩
  simpa [factor, doubled, identity, events, childEvents, rootEvents,
    Events.append, occurrence, unary] using hg

theorem crossing_addresses : crossing.orderedAddresses = [[0]] := rfl
def crossingSite : crossing.Site := .inl PUnit.unit
theorem crossing_detached : crossing.plan.detached crossingSite = factor := rfl
theorem crossing_typed_remainder : crossing.remainder =
    .ordinary (occurrence .bottom) (.cons (.interface GS) (.cons second .nil)) := rfl
theorem crossing_refill : crossing.fill crossing.plan.detached = source :=
  crossing.fill_detached_reconstructs

/-- The same proper frontier after replacing its detached native factor. -/
def replacedPlan : CKCutPlan replaced :=
  .ordinary _ _ (.cons replacement (.cons second .nil) (.detach trivial)
    (.cons second .nil (.descend (pass second)) .nil))
def replacedCut : CKCut replaced := ⟨trivial, replacedPlan⟩

/-- First the separate full endpoint, then the proper changed-factor cut.
The other staging first cuts the factor, then takes the remaining whole branch. -/
def staged : BranchInside replaced :=
  ⟨.detach trivial, fun _ => .descend replacedPlan⟩
def restaged : BranchRemainder replaced := branchFlagEquiv replaced staged

theorem staged_lower : insideLowerPacket staged.1 staged.2 =
    [⟨[0], GS, replacement, by trivial⟩] := rfl
theorem staged_middle : insideMiddlePacket staged.1 staged.2 =
    [⟨[], GS, replacedCut.remainder, by trivial⟩] := rfl
theorem staged_box : insideRemainder staged.1 staged.2 = .interface GS := rfl

/-- Literal ordered packets, full typed remainder and all physical trees agree. -/
theorem staged_outputs :
    (orderedPacket restaged.1, orderedPacket restaged.2, restaged.2.remainder) =
    ([⟨[0], GS, replacement, by trivial⟩],
      [⟨[], GS, replacedCut.remainder, by trivial⟩], CKTree.interface GS) := by
  change (orderedPacket ((branchFlagEquiv replaced staged).1),
    orderedPacket ((branchFlagEquiv replaced staged).2),
    (branchFlagEquiv replaced staged).2.remainder) = _
  rw [branchFlag_outputs, staged_lower, staged_middle, staged_box]

theorem staged_refill :
    staged.1.fill (fun i => (staged.2 i).fill (staged.2 i).detached) = replaced :=
  inside_refill staged.1 staged.2

theorem restaged_refill : restaged.2.fill restaged.2.detached = restaged.1.remainder ∧
    restaged.1.fill restaged.1.detached = replaced :=
  remainder_refill replaced restaged

theorem staged_same_checked_result :
    staged.1.fill (fun i => (staged.2 i).fill (staged.2 i).detached) =
      checkedReplacement.realize ∧ restaged.1.fill restaged.1.detached =
      checkedReplacement.realize := by
  rw [checked_replacement_realize]
  exact ⟨staged_refill, restaged_refill.2⟩

/-- The remainder itself is cacheable in this complete-factor update. -/
theorem reused_remainder : replacedCut.remainder = crossing.remainder := rfl

/-- One integrated native reuse certificate: the original proper cut is
filled with the compatible new factor, the remainder is literally retained,
and both permitted extraction stagings yield that same checked result. -/
theorem replacement_workflow :
    Legal replaced [] [] ∧
    crossing.fill replacementFillers = checkedReplacement.realize ∧
    replacedCut.remainder = crossing.remainder ∧
    (staged.1.fill (fun i => (staged.2 i).fill (staged.2 i).detached) =
      checkedReplacement.realize ∧ restaged.1.fill restaged.1.detached =
      checkedReplacement.realize) :=
  ⟨replaced_legal, crossing_replace.trans checked_replacement_realize.symm,
    reused_remainder, staged_same_checked_result⟩

#print axioms exact_occurrence
#print axioms checked_source_realize
#print axioms checked_replacement_realize
#print axioms source_legal
#print axioms replaced_legal
#print axioms compatible_replacement_legal
#print axioms bad_factor_rejected
#print axioms crossing_replace
#print axioms crossing_refill
#print axioms staged_outputs
#print axioms staged_same_checked_result
#print axioms replacement_workflow

end Potkin.Research.DependencyInterfaceExamples

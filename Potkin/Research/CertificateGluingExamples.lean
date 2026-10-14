import Potkin.Research.CertificateCutGluing

/-!
# Cooperative right-ghost pieces, evaluated through the native gluing bridge

The example is secondary to universal gluing.  Its two factors are not closed
grounded; the single colour selected by their shared owner must be inherited
by both callbacks.  No new proof, cut, context or forest syntax is introduced.
-/

namespace Potkin.Research.CertificateGluingExamples

open RevivalInterface OpenCertificateKernel CertificateCutGluing

mutual
private def leavePlan : {G : Hypersequent sigma} →
    (tree : CKTree sigma Data G) → CKCutPlan tree
  | _, .interface G => .interface G
  | _, .ordinary o children => .ordinary o children (leaveChildren children)

private def leaveChildren : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → CKChildCuts children
  | _, .nil => .nil
  | _, .cons head tail => .cons head tail (.descend (leavePlan head)) (leaveChildren tail)
end

private theorem chooseModule_ordinary (a : Atom) : (chooseModule a).IsOrdinary := by
  cases a <;> trivial

private theorem exists_colour (predicate : Atom → Prop) :
    (∃ colour, predicate colour) ↔ predicate .p ∨ predicate .q := by
  constructor
  · rintro ⟨colour, holds⟩
    cases colour
    · exact Or.inl holds
    · exact Or.inr holds
  · rintro (holds | holds)
    · exact ⟨.p, holds⟩
    · exact ⟨.q, holds⟩

/-- Two physically different selected roots below the same right owner.
Their ordered addresses are [1,0] and [1,1], even when a=b. -/
def cooperativeCut (a b : Atom) : CKCut (fixture a b) :=
  ⟨by trivial,
    .ordinary (occurrence .owner) _
      (.cons _ _ (.descend (leavePlan (lower ordinaryS ordinaryS)))
        (.cons _ .nil
          (.descend (.ordinary (occurrence .disjLower) _
            (.cons _ _ (.detach (chooseModule_ordinary a))
              (.cons _ .nil (.detach (chooseModule_ordinary b)) .nil)))) .nil))⟩

theorem cooperative_addresses (a b : Atom) :
    ((cooperativeCut a b).detachedTuple.map fun entry => entry.address) = [[1,0],[1,1]] := by
  cases a <;> cases b <;> rfl

abbrev CooperativePieces (a b : Atom) :=
  PieceCertificates (.descend (cooperativeCut a b).plan) (fixture_complete a b) [] []

/-- The universal bridge, specialized without independently closing factors. -/
def cooperativeGluingEquiv (a b : Atom) :
    ClosedKernel (fixture a b) [] [] ≃ CooperativePieces a b :=
  cutGluingEquiv (.descend (cooperativeCut a b).plan) (fixture_complete a b) [] []

/-- Module scope compatibility for arbitrary physical starting addresses.
The shared right owner is initially uncheckpointed.  The module's genuine
empty-conclusion nodes introduce the checkpoint, not its vacant slot. -/
theorem module_inherited_scope (moduleColour ownerColour : Atom)
    (address : InternalAddress) :
    Nonempty (ClosedKernel (chooseModule moduleColour) address
      (enterOwner [] ownerColour true [])) ↔ moduleColour = ownerColour := by
  have admitted : LocallyAdmittedTree presentation (chooseModule moduleColour) := by
    cases moduleColour
    · exact modules_admitted.2.1
    · exact modules_admitted.2.2
  rw [closed_nonempty_iff _ admitted]
  cases moduleColour <;> cases ownerColour <;>
    simp [chooseModule, moduleP, moduleQ, HasScopedCertificate, ChildrenCertificate,
      emptyConclusion, advance, enterOwner, compatibleRight, occurrence,
      unaryOccurrence, leafOccurrence]

theorem independently_closed_factors_fail (a : Atom) :
    ¬ Nonempty (ClosedKernel (chooseModule a) [] []) := by
  have admitted : LocallyAdmittedTree presentation (chooseModule a) := by
    cases a
    · exact modules_admitted.2.1
    · exact modules_admitted.2.2
  rw [closed_nonempty_iff _ admitted]
  cases a <;>
    simp [chooseModule, moduleP, moduleQ, HasScopedCertificate, ChildrenCertificate,
      emptyConclusion, advance, compatibleRight, occurrence, unaryOccurrence, leafOccurrence]

/-- The cooperative pattern is an existence consequence of the Type-valued
gluing bridge and the common owner choice, not a new finite-count argument. -/
theorem cooperative_pattern (a b : Atom) :
    Nonempty (CooperativePieces a b) ↔ a = b := by
  rw [← (cooperativeGluingEquiv a b).nonempty_congr,
    closed_nonempty_iff _ (fixture_admitted a b)]
  cases a <;> cases b <;>
    simp [fixture, lower, ordinaryS, chooseModule, moduleP, moduleQ,
      HasScopedCertificate, ChildrenCertificate, OwnerCertificate,
      emptyConclusion, advance, enterOwner, compatibleRight,
      occurrence, unaryOccurrence, binaryOccurrence, leafOccurrence,
      unaryShape, binaryShape, nullaryShape, exists_colour]

theorem cooperative_refill (a b : Atom) :
    (cooperativeCut a b).fill (cooperativeCut a b).plan.detached = fixture a b :=
  (cooperativeCut a b).fill_detached_reconstructs

end Potkin.Research.CertificateGluingExamples

#check Potkin.Research.CertificateGluingExamples.cooperative_pattern
#print axioms Potkin.Research.CertificateGluingExamples.cooperative_addresses
#print axioms Potkin.Research.CertificateGluingExamples.cooperative_pattern
#print axioms Potkin.Research.CertificateGluingExamples.module_inherited_scope
#print axioms Potkin.Research.CertificateGluingExamples.independently_closed_factors_fail
#print axioms Potkin.Research.CertificateGluingExamples.cooperative_refill

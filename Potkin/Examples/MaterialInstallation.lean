import Potkin.MaterialInstallation
import Potkin.AtomicIdentityFragment

/-! A genuine checked two-slot completion and its subsequent native
extraction. This is a particular theorem application, not an exhaustive oracle. -/

namespace Potkin.Examples.MaterialInstallation
open AtomicIdentityFragment

def source : NamedTree Nat := namedIdentityCut 5 6 separated
def target : NamedTree Nat := namedIdentityCut 5 6 fused

theorem source_success : CheckResult.Succeeded
    (presentation.checkAt closedBoundary (rawIdentityCut rawSeparated)) := by decide
theorem target_success : CheckResult.Succeeded
    (presentation.checkAt closedBoundary (rawIdentityCut rawFused)) := by decide

def checkedSource : CheckedDerivation presentation closedBoundary :=
  CheckResult.get source_success
def checkedTarget : CheckedDerivation presentation closedBoundary :=
  CheckResult.get target_success

theorem source_checked : source.native = checkedSource.realize := rfl
theorem target_checked : target.native = checkedTarget.realize := rfl

/-- The first slot opens the actual impure Cut(g₀,Ax), not a fake material
probe. The two physical holes have distinct current addresses. -/
def installation : CKCut source.native where
  sourceOrdinary := by trivial
  plan := .ordinary cutOccurrence _
    (.cons separated.native _
      (.descend (.ordinary materialBinary _
        (.cons (identityCut tree₀) _ (.detach (by trivial))
          (.cons tree₁ .nil (.detach (by trivial)) .nil))))
      (.cons identityTree .nil (.descend (.ordinary identityOccurrence .nil .nil)) .nil))

theorem installation_addresses : installation.orderedAddresses = [[0, 0], [0, 1]] := rfl

def pureFillers : (site : installation.Site) →
    CKTree sigma Data (installation.plan.siteBoundary site)
  | .inl (.inl _) => tree₀
  | .inl (.inr (.inl _)) => tree₁
  | .inl (.inr (.inr impossible)) => nomatch impossible
  | .inr (.inl impossible) => nomatch impossible
  | .inr (.inr impossible) => nomatch impossible

def pureNames : (site : installation.Site) → (pureFillers site).OriginNames Nat
  | .inl (.inl _) => (1, PUnit.unit)
  | .inl (.inr (.inl _)) => (2, PUnit.unit)
  | .inl (.inr (.inr impossible)) => nomatch impossible
  | .inr (.inl impossible) => nomatch impossible
  | .inr (.inr impossible) => nomatch impossible

theorem installation_pure_filling : installation.fill pureFillers = target.native := rfl
theorem installation_pure_names :
    installation.plan.fillOriginNames pureFillers source.names pureNames = target.names := rfl
theorem installation_old_filling :
    installation.fill installation.plan.detached = source.native :=
  installation.fill_detached_reconstructs

theorem target_fresh : target.Fresh := by
  change ([5, 0, 1, 2, 6] : List Nat).Nodup
  decide
theorem source_fresh : source.Fresh := by
  change ([5, 0, 3, 1, 4, 2, 6] : List Nat).Nodup
  decide

/-- The old binary root is selected, and both payload-cut choices are
suppressed. The identity side branch remains in the complete typed residual. -/
def spanningChoices : installation.plan.ExpansionChoices pureFillers :=
  (.inl PUnit.unit, (.inr PUnit.unit, PUnit.unit))
def oldSpanningChoices : installation.plan.ExpansionChoices installation.plan.detached :=
  (.inl PUnit.unit, (.inr PUnit.unit, PUnit.unit))

def spanningCut : CKCut target.native := installation.expandedCut pureFillers spanningChoices
def oldSpanningCut : CKCut source.native :=
  installation.expandedCut installation.plan.detached oldSpanningChoices

theorem source_admitted : LocallyAdmittedTree presentation source.native :=
  (ClosedFragment.identityCut
    (ClosedFragment.binary (ClosedFragment.identityCut .ground₀) .ground₁)).locallyAdmitted
theorem target_admitted : LocallyAdmittedTree presentation target.native :=
  (ClosedFragment.identityCut (ClosedFragment.binary .ground₀ .ground₁)).locallyAdmitted

theorem new_spanning_eligible : spanningCut.plan.DetachedInBase base := by
  intro site
  cases site with
  | inl site =>
      cases site
      exact ⟨MaterialMember.binary, ⟨⟨MaterialMember.ground₀, trivial⟩,
        ⟨⟨MaterialMember.ground₁, trivial⟩, trivial⟩⟩⟩
  | inr impossible =>
      cases impossible with
      | inl impossible => nomatch impossible
      | inr impossible => nomatch impossible

theorem old_spanning_ineligible : ¬ oldSpanningCut.plan.DetachedInBase base := by
  intro eligible
  have whole := eligible (Sum.inl PUnit.unit)
  have logicalMember : base.Member cutOccurrence := whole.2.1.1
  have impossible := base.member_material logicalMember
  cases impossible

/-- A real SAME-REGISTRY gain, and its reverse is a loss. The source binary
factor was impure; the installed full factor spans BOTH supplied proofs. -/
theorem checked_spanning_gain_and_reverse_loss :
    LocallyAdmittedTree presentation source.native ∧
    LocallyAdmittedTree presentation target.native ∧
    ¬ oldSpanningCut.plan.DetachedInBase base ∧ spanningCut.plan.DetachedInBase base :=
  ⟨source_admitted, target_admitted, old_spanning_ineligible, new_spanning_eligible⟩

theorem spanning_address_and_full_tuple :
    spanningCut.orderedAddresses = [[0]] ∧
    spanningCut.detachedTuple =
      [⟨[0], closedBoundary, fused.native, by trivial⟩] := ⟨rfl, rfl⟩

theorem spanning_complete_residual :
    spanningCut.enrichedRemainder target.names = namedIdentityCut 5 6 (namedHole 0) := rfl

theorem spanning_full_coefficient :
    spanningCut.originForest target.names =
      ({⟨⟨closedBoundary, fused.native, by trivial⟩, fused.names⟩} :
        OriginForest sigma Data Nat) := rfl

/-- The newly available operation has the FULL binary coefficient and its
exact Cut/identity residual, with root origin 0 shared by coefficient/vacancy. -/
theorem gained_operation :
    spanningCut.plan.DetachedInBase base ∧
    spanningCut.originForest target.names =
      ({⟨⟨closedBoundary, fused.native, by trivial⟩, fused.names⟩} :
        OriginForest sigma Data Nat) ∧
    spanningCut.enrichedRemainder target.names = namedIdentityCut 5 6 (namedHole 0) :=
  ⟨new_spanning_eligible, spanning_full_coefficient, spanning_complete_residual⟩

/-- A subsequent genuine proper internal extraction of the available
composite: its first ground is detached and the second ground remains. -/
def innerCut : CKCut fused.native where
  sourceOrdinary := by trivial
  plan := .ordinary materialBinary _
    (.cons tree₀ _ (.detach (by trivial))
      (.cons tree₁ .nil (.descend (.ordinary ground₁ .nil .nil)) .nil))

theorem inner_address_factor_residual :
    innerCut.orderedAddresses = [[0]] ∧
    innerCut.detachedTuple = [⟨[0], closedBoundary, tree₀, by trivial⟩] ∧
    innerCut.enrichedRemainder fused.names =
      namedBinary 0 (namedHole 1) (named₁ 2) := ⟨rfl, rfl, rfl⟩

theorem inner_eligible : innerCut.plan.DetachedInBase base := by
  intro site
  cases site with
  | inl site => cases site; exact ⟨MaterialMember.ground₀, trivial⟩
  | inr impossible =>
      cases impossible with
      | inl impossible => nomatch impossible
      | inr impossible => nomatch impossible

theorem inner_middle_eligible : innerCut.remainder.AllVerticesInBase base :=
  innerCut.plan.remainderInBase_of_inBase base
    ⟨MaterialMember.binary, ⟨⟨MaterialMember.ground₀, trivial⟩,
      ⟨⟨MaterialMember.ground₁, trivial⟩, trivial⟩⟩⟩

def lowerCuts : (site : spanningCut.Site) → CKCut (spanningCut.plan.detached site)
  | .inl _ => innerCut
  | .inr (.inl impossible) => nomatch impossible
  | .inr (.inr impossible) => nomatch impossible

/-- The available full binary operation stays available after its internal
ground operation is opened; actual lower+middle data reassemble its packet
before returning to the same complete outer residual. -/
theorem checked_two_stage_availability :
    spanningCut.plan.DetachedInBase base ∧
    innerCut.plan.DetachedInBase base ∧
    innerCut.remainder.AllVerticesInBase base ∧
    spanningCut.stagedOriginForest target.names target_fresh lowerCuts =
      spanningCut.originForest target.names ∧
    OriginTree.decode (spanningCut.stagedOriginForest target.names target_fresh lowerCuts)
      (spanningCut.enrichedRemainder target.names).native
      (spanningCut.enrichedRemainder target.names).names = target :=
  ⟨new_spanning_eligible, inner_eligible, inner_middle_eligible,
    spanningCut.stagedOriginForest_eq target.names target_fresh lowerCuts,
    spanningCut.decode_twoStage target.names target_fresh lowerCuts⟩

end Potkin.Examples.MaterialInstallation

#print axioms Potkin.Examples.MaterialInstallation.checked_spanning_gain_and_reverse_loss
#print axioms Potkin.Examples.MaterialInstallation.gained_operation
#print axioms Potkin.Examples.MaterialInstallation.checked_two_stage_availability

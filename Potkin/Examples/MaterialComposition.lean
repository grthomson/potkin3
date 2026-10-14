import Potkin.Examples.MaterialInstallation
import Potkin.MaterialComposition
import Potkin.MaterialInheritedCuts

/-!
# A checked application of exact material coefficient composition

The full binary operation is newly eligible after two native typed slots are
filled. Its raw origin-enriched observation is deliberately not quotiented by
logical normalization: the old and new complete operations reconstruct proofs
of different degrees. The inherited physical cut nonetheless stays at [0].
This file specializes universal coefficient and availability theorems; it does
not calculate a finite cut enumeration or assert a coaction law.
-/

namespace Potkin.Examples.MaterialComposition
open AtomicIdentityFragment MaterialInstallation MaterialObservations

def spanningOperation : Operation sigma Data Nat closedBoundary :=
  cutTerm spanningCut target.names

def oldSpanningOperation : Operation sigma Data Nat closedBoundary :=
  cutTerm oldSpanningCut source.names

theorem spanning_operation_literal : spanningOperation =
    (({⟨⟨closedBoundary, fused.native, by trivial⟩, fused.names⟩} :
      OriginForest sigma Data Nat), namedIdentityCut 5 6 (namedHole 0)) := rfl

theorem spanning_available :
    Available base target.native target.names spanningOperation := by
  refine ⟨ExtensionalCKCut.ofCKCut spanningCut, ?_, ?_⟩
  · simpa only [ExtensionalCKCut.compiled_ofCKCut] using new_spanning_eligible
  · simp only [ExtensionalCKCut.compiled_ofCKCut, spanningOperation]

noncomputable def spanningCoefficient : Nat := by
  classical
  exact (cutSum base target.native (by trivial) target.names).count spanningOperation

theorem spanning_coefficient_positive : 0 < spanningCoefficient := by
  classical
  unfold spanningCoefficient
  rw [Multiset.count_pos]
  exact (mem_cutSum_iff base target.native (by trivial)
    target.names spanningOperation).mpr spanning_available

/-- Absence is proved for the complete raw operation, not inferred from a
failed membership test or merely from its original witness being impure. -/
theorem old_operation_unavailable_in_target :
    ¬ Available base target.native target.names oldSpanningOperation := by
  intro available
  have targetDecoded := available_decodes base target.native target.names
    oldSpanningOperation target_fresh available
  have sourceDecoded : OriginTree.decode oldSpanningOperation.1
      oldSpanningOperation.2.native oldSpanningOperation.2.names = source :=
    oldSpanningCut.decode_collected source.names source_fresh
  have equal : source = target := sourceDecoded.symm.trans targetDecoded
  have degrees := congrArg (fun tree : NamedTree Nat => tree.native.degree) equal
  change (7 : Nat) = 5 at degrees
  exact (by decide : (7 : Nat) ≠ 5) degrees

theorem new_operation_unavailable_in_source :
    ¬ Available base source.native source.names spanningOperation := by
  intro available
  have sourceDecoded := available_decodes base source.native source.names
    spanningOperation source_fresh available
  have targetDecoded : OriginTree.decode spanningOperation.1
      spanningOperation.2.native spanningOperation.2.names = target :=
    spanningCut.decode_collected target.names target_fresh
  have equal : source = target := sourceDecoded.symm.trans targetDecoded
  have degrees := congrArg (fun tree : NamedTree Nat => tree.native.degree) equal
  change (7 : Nat) = 5 at degrees
  exact (by decide : (7 : Nat) ≠ 5) degrees

/-- Exact multiset identity, with complete factors/residuals and multiplicity.
No fixture enumeration is evaluated in this theorem application. -/
theorem fixture_installed_sum :
    cutSum base target.native (by trivial) target.names =
      expansionSum base installation pureFillers source.names pureNames := by
  simpa only [installation_pure_filling, installation_pure_names] using
    material_cutSum_composition base installation pureFillers source.names pureNames

noncomputable def expansionCoefficient : Nat := by
  classical
  exact (expansionSum base installation pureFillers source.names pureNames).count
    spanningOperation

theorem fixture_installed_coefficient : spanningCoefficient = expansionCoefficient := by
  classical
  unfold spanningCoefficient expansionCoefficient
  rw [fixture_installed_sum]

def stageOperation : TwoStageOperation sigma Data Nat closedBoundary :=
  (({(named₀ 1).asComponent (by trivial)} :
      OriginForest sigma Data Nat),
    ({(namedBinary 0 (namedHole 1) (named₁ 2)).asComponent (by trivial)} :
      OriginForest sigma Data Nat),
    namedIdentityCut 5 6 (namedHole 0))

/-- The lower operation is g₀; the full positive OPEN middle operation is
binary(Box₁,g₁); the root remains Cut(Box₀,Ax). -/
theorem literal_stage :
    stagedTerm spanningCut target.names lowerCuts = stageOperation := rfl

theorem actual_staged_available :
    StagedAvailable base target.native target.names stageOperation := by
  refine ⟨ExtensionalCKCut.ofCKCut spanningCut, ?_, ?_⟩
  · simpa only [ExtensionalCKCut.compiled_ofCKCut] using new_spanning_eligible
  · have continuation : StagedContinuation base spanningCut target.names stageOperation := by
      refine ⟨lowerCuts, ?_, literal_stage⟩
      exact (pure_outer_all_stages base spanningCut new_spanning_eligible lowerCuts).1
    simpa only [ExtensionalCKCut.compiled_ofCKCut] using continuation

/-- Installation composition exposes the same actual subsequent operation
through the independently generated outer/inner expansion choices. -/
theorem staged_installed_application :
    ∃ choice : installation.plan.ExpansionChoices pureFillers,
      installation.plan.EligibleExpansion base pureFillers choice ∧
      ∃ inner : (site : (installation.expandedCut pureFillers choice).Site) →
          CKCut ((installation.expandedCut pureFillers choice).plan.detached site),
        stagedTerm (installation.expandedCut pureFillers choice)
          (installation.plan.fillOriginNames pureFillers source.names pureNames) inner =
            stageOperation := by
  apply (staged_available_composition_iff base installation pureFillers
    source.names pureNames stageOperation).mp
  simpa only [installation_pure_filling, installation_pure_names] using actual_staged_available

theorem old_spanning_safe :
    installation.plan.SafeExpansion installation.plan.detached oldSpanningChoices :=
  ⟨trivial, ⟨trivial, trivial⟩⟩

def pureFillersPositive : ∀ site, (pureFillers site).IsOrdinary
  | .inl (.inl _) => by trivial
  | .inl (.inr (.inl _)) => by trivial
  | .inl (.inr (.inr impossible)) => nomatch impossible
  | .inr (.inl impossible) => nomatch impossible
  | .inr (.inr impossible) => nomatch impossible

theorem transport_spanning_choice :
    installation.plan.transportSafeExpansion installation.plan.detached pureFillers
      pureFillersPositive oldSpanningChoices old_spanning_safe = spanningChoices := rfl

def oldPublic : ExtensionalCKCut (installation.fill installation.plan.detached) :=
  (installation.installedPublicCutEquiv installation.plan.detached).symm oldSpanningChoices

theorem oldPublic_safe : installation.InheritedDomain installation.plan.detached oldPublic := by
  unfold CKCut.InheritedDomain oldPublic
  rw [Equiv.apply_symm_apply]
  exact old_spanning_safe

def inheritedPublic : ExtensionalCKCut (installation.fill pureFillers) :=
  installation.transportInherited installation.plan.detached pureFillers
    pureFillersPositive oldPublic oldPublic_safe

/-- The partial inherited transport returns exactly the native public witness
of the gained operation, not an address fabricated from its coefficient. -/
theorem inherited_exact_witness :
    inheritedPublic = ExtensionalCKCut.ofCKCut spanningCut := by
  have oldChoice : (installation.installedPublicCutEquiv installation.plan.detached)
      oldPublic = oldSpanningChoices :=
    (installation.installedPublicCutEquiv installation.plan.detached).apply_symm_apply _
  change (installation.installedPublicCutEquiv pureFillers).symm
      (installation.plan.transportSafeExpansion installation.plan.detached pureFillers
        pureFillersPositive
        ((installation.installedPublicCutEquiv installation.plan.detached) oldPublic)
        oldPublic_safe) =
    (installation.installedPublicCutEquiv pureFillers).symm spanningChoices
  apply congrArg (installation.installedPublicCutEquiv pureFillers).symm
  simp only [oldChoice]
  exact transport_spanning_choice

theorem inherited_address_and_eligibility_gain :
    inheritedPublic.compiled = spanningCut ∧
    inheritedPublic.compiled.orderedAddresses = [[0]] ∧
    ¬ oldSpanningCut.plan.DetachedInBase base ∧
    inheritedPublic.compiled.plan.DetachedInBase base := by
  have equal : inheritedPublic.compiled = spanningCut := by
    rw [inherited_exact_witness]
    exact ExtensionalCKCut.compiled_ofCKCut spanningCut
  refine ⟨equal, ?_, old_spanning_ineligible, ?_⟩
  · rw [equal]
    exact spanning_address_and_full_tuple.1
  · rw [equal]
    exact new_spanning_eligible

end Potkin.Examples.MaterialComposition

#print axioms Potkin.Examples.MaterialComposition.spanning_coefficient_positive
#print axioms Potkin.Examples.MaterialComposition.old_operation_unavailable_in_target
#print axioms Potkin.Examples.MaterialComposition.new_operation_unavailable_in_source
#print axioms Potkin.Examples.MaterialComposition.fixture_installed_sum
#print axioms Potkin.Examples.MaterialComposition.actual_staged_available
#print axioms Potkin.Examples.MaterialComposition.staged_installed_application
#print axioms Potkin.Examples.MaterialComposition.inherited_exact_witness
#print axioms Potkin.Examples.MaterialComposition.inherited_address_and_eligibility_gain

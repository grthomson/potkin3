import Potkin.Exploration.CutGeometry
import Potkin.Exploration.ResidualContracts
import Potkin.Exploration.CutLinearization
import Potkin.SparseMaterialObservation

/-!
# Cross-check of the native exploration bridges

A literal remainder determines a cut only when its complete source is fixed.
The two existing obstructions below keep that guard visible. These are proofs
about existing native carriers, not an erased reconstruction experiment.
-/

namespace Potkin.Exploration

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData} {G : Hypersequent sigma}

/-- A feasible native residual has exactly one occurrence-resolved witness,
provided the complete source and literal typed remainder are fixed. -/
theorem nativeResidual_unique_witness {P : EquippedPresentation T}
    {A : CKForest sigma InstanceData → Prop}
    {source remainder : CKTree sigma InstanceData G}
    (related : NativeResidual P A source remainder) :
    ∃! cut : CKCut source, A cut.detachedForest ∧ cut.remainder = remainder := by
  rcases related with ⟨_, cut, coefficient, equal⟩
  refine ⟨cut, ⟨coefficient, equal⟩, ?_⟩
  intro other otherProperties
  exact CKCut.eq_of_remainder_eq other cut (otherProperties.2.trans equal.symm)

/-- The contract witness also names a genuine nonzero native coefficient.
No choice of an address is made from an aggregated forest value. -/
theorem nativeResidual_coefficient {P : EquippedPresentation T}
    {A : CKForest sigma InstanceData → Prop}
    {source remainder : CKTree sigma InstanceData G}
    (related : NativeResidual P A source remainder) :
    ∃ cut : CKCut source, A cut.detachedForest ∧ cut.remainder = remainder ∧
      cutCoefficients source cut.sourceOrdinary
        (cutBasis (ExtensionalCKCut.ofCKCut cut)) = 1 ∧
      cut.fill cut.plan.detached = source := by
  rcases related with ⟨_, cut, coefficient, equal⟩
  refine ⟨cut, coefficient, equal, ?_, cut.fill_detached_reconstructs⟩
  exact coefficient_at_native_cut (ExtensionalCKCut.ofCKCut cut)

/-- Dropping the fixed-source guard is genuinely false, even with one registry,
the same literal remainder, and the same full commutative coefficient forest. -/
theorem varying_source_ambiguity :
    Examples.InverseCut.leftCut.remainder = Examples.InverseCut.twoHoles ∧
    Examples.InverseCut.rightCut.remainder = Examples.InverseCut.twoHoles ∧
    Examples.InverseCut.leftCut.orderedAddresses = [[0]] ∧
    Examples.InverseCut.rightCut.orderedAddresses = [[1]] ∧
    Examples.InverseCut.leftCut.detachedForest = Examples.InverseCut.rightCut.detachedForest ∧
    Examples.InverseCut.twoHoles.fillAssignment Examples.InverseCut.leftOnly ≠
      Examples.InverseCut.twoHoles.fillAssignment Examples.InverseCut.rightOnly :=
  Examples.InverseCut.left_right_ambiguity

/-- Generic admitted native positive material proofs, not only a ground fixture:
an identity/Cut detour preserves the island record but not the CK observation. -/
theorem admitted_identity_cut_obstruction {Origin : Type}
    (tree : AtomicIdentityFragment.NamedTree Origin)
    (fragment : AtomicIdentityFragment.ClosedFragment tree.native)
    (ordinary : tree.native.IsOrdinary) (pure : tree.native.AllVerticesMaterial)
    (cutName identityName : Origin) :
    LocallyAdmittedTree AtomicIdentityFragment.presentation tree.native ∧
    LocallyAdmittedTree AtomicIdentityFragment.presentation
      (AtomicIdentityFragment.namedIdentityCut cutName identityName tree).native ∧
    SparseMaterialObservation.record tree = SparseMaterialObservation.record
      (AtomicIdentityFragment.namedIdentityCut cutName identityName tree) ∧
    SparseMaterialObservation.standardObservation tree ordinary ≠
      SparseMaterialObservation.standardObservation
        (AtomicIdentityFragment.namedIdentityCut cutName identityName tree) (by trivial) :=
  SparseMaterialObservation.admitted_pure_identity_detour_countertheorem
    tree fragment ordinary pure cutName identityName

end Potkin.Exploration

#print axioms Potkin.Exploration.nativeResidual_unique_witness
#print axioms Potkin.Exploration.nativeResidual_coefficient
#print axioms Potkin.Exploration.varying_source_ambiguity
#print axioms Potkin.Exploration.admitted_identity_cut_obstruction

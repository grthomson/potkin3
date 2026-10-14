import Potkin.AtomicIdentityFragment
import Potkin.SparseTopTerm

/-!
# Sparse records and the ordinary CK endpoint obstruction

The sparse record is defined independently by native maximal material islands
and the independently generated atomic identity/Cut observer.  The finite
observation enumerates PUBLIC native nonroot antichains exactly once, filters
actual detached factors, and retains collected multiplicities and full origin
annotations.  It includes the empty cut.  The global whole endpoint is added
separately, never fabricated as a native root cut.

`Option` tags an existing typed remainder (`some`) versus the algebraic unit
(`none`).  It is not a proof, cut, context or forest carrier.  In particular a
typed Box is not mapped to the algebraic unit by fiat.  These finite multisets
are nonnegative formal sums, not an asserted linear/coaction-law implementation.

The unrefined sparse-record theorem is FALSE for this ordinary endpoint
convention, already for a genuine checked atomic identity-Cut detour.  The
paper's pointed whole opening would instead retain a named typed Box on the
right.  Changing to that observation, or proving sufficiency of a
purity-refined record, requires an additional theorem.
-/

namespace Potkin.SparseMaterialObservation

open AtomicIdentityFragment

abbrev Monomial (Origin : Type) :=
  OriginForest sigma Data Origin × Option (NamedTree Origin)

/-- Full islands, complete interfaces, origins, and an independently observed
shell. There is no stored source or decoder/cut witness in this record. -/
noncomputable def record {Origin : Type} (tree : NamedTree Origin) :
    OriginForest sigma Data Origin × NamedTree Origin :=
  let maximal := tree.native.maximalMaterialBranch
  (Multiset.ofList (maximal.originFactors tree.names),
    observe ⟨maximal.remainder, maximal.originRemainder tree.names⟩)

noncomputable def belowRootObservation {Origin : Type}
    (tree : NamedTree Origin) (ordinary : tree.native.IsOrdinary) :
    Multiset (Monomial Origin) := by
  classical
  exact Multiset.ofList (((ExtensionalCKCut.enumerate tree.native ordinary).filter
    (fun cut => cut.compiled.PureDetached)).map (fun cut =>
      (cut.compiled.originForest tree.names,
        some (observe (cut.compiled.enrichedRemainder tree.names)))))

def wholeForest {Origin : Type} (tree : NamedTree Origin)
    (ordinary : tree.native.IsOrdinary) : OriginForest sigma Data Origin :=
  {tree.asComponent ordinary}

/-- Ordinary CK's separately projected whole endpoint has right unit, not a
puncture. Exact material selection retains it precisely for a pure source. -/
noncomputable def wholeObservation {Origin : Type}
    (tree : NamedTree Origin) (ordinary : tree.native.IsOrdinary) :
    Multiset (Monomial Origin) := by
  classical
  exact if tree.native.AllVerticesMaterial then
    {(wholeForest tree ordinary, none)} else 0

noncomputable def standardObservation {Origin : Type}
    (tree : NamedTree Origin) (ordinary : tree.native.IsOrdinary) :
    Multiset (Monomial Origin) :=
  belowRootObservation tree ordinary + wholeObservation tree ordinary

theorem pure_maximal_branch : {G : Hypersequent sigma} →
    (tree : CKTree sigma Data G) → (ordinary : tree.IsOrdinary) →
    tree.AllVerticesMaterial → tree.maximalMaterialBranch = .detach ordinary
  | _, .interface _, ordinary, _ => False.elim ordinary
  | _, .ordinary _ _, _, pure => by
      simp [CKTree.maximalMaterialBranch, pure]

/-- Whole-host extraction retains the full composite, not its primitive
inventory. The remaining Box has the same full boundary and persistent seam. -/
theorem record_of_pure {Origin : Type} (tree : NamedTree Origin)
    (ordinary : tree.native.IsOrdinary) (pure : tree.native.AllVerticesMaterial) :
    record tree = (wholeForest tree ordinary,
      namedHole (tree.native.rootOrigin tree.names)) := by
  unfold record
  rw [pure_maximal_branch tree.native ordinary pure]
  rfl

/-- A family, not just a leaf example: any positive pure composite can have
an exact atomic identity-Cut detour without changing its sparse record. -/
theorem pure_identity_detour_records_equal {Origin : Type}
    (tree : NamedTree Origin) (ordinary : tree.native.IsOrdinary)
    (pure : tree.native.AllVerticesMaterial) (cutName axName : Origin) :
    record tree = record (namedIdentityCut cutName axName tree) := by
  classical
  have notPure : ¬ (identityCut tree.native).AllVerticesMaterial := by
    simp [identityCut, CKTree.AllVerticesMaterial, cutOccurrence]
  have axImpure : ¬ identityTree.AllVerticesMaterial := by decide
  rw [record_of_pure tree ordinary pure]
  simp only [record, namedIdentityCut, identityCut, CKTree.maximalMaterialBranch,
    dif_neg notPure, CKChildren.maximalMaterialCuts]
  rw [pure_maximal_branch tree.native ordinary pure]
  simp only [identityTree, CKTree.maximalMaterialBranch, dif_neg axImpure,
    CKChildren.maximalMaterialCuts, CKBranchCut.originFactors, CKCutPlan.originFactors,
    CKChildCuts.originFactors, CKBranchCut.remainder, CKCutPlan.remainder,
    CKChildCuts.remainder, CKBranchCut.originRemainder, CKCutPlan.originRemainder,
    CKChildCuts.originRemainder, List.append_nil]
  change (wholeForest tree ordinary, namedHole (tree.native.rootOrigin tree.names)) =
    (wholeForest tree ordinary,
      observe (namedIdentityCut cutName axName (namedHole (tree.native.rootOrigin tree.names))))
  rw [observe_identityCut, observe_hole]

theorem right_unit_not_belowRoot {Origin : Type}
    (tree : NamedTree Origin) (ordinary : tree.native.IsOrdinary)
    (forest : OriginForest sigma Data Origin) :
    (forest, none) ∉ belowRootObservation tree ordinary := by
  classical
  intro member
  change (forest, none) ∈ Multiset.ofList _ at member
  rw [Multiset.mem_coe] at member
  rcases List.mem_map.mp member with ⟨cut, _, equal⟩
  have impossible := congrArg Prod.snd equal
  cases impossible

/-- This coordinate diagnoses the endpoint distinction for ALL positive
native sources in the fixed registry, without bounded fixture enumeration. -/
theorem right_unit_mem_iff {Origin : Type}
    (tree : NamedTree Origin) (ordinary : tree.native.IsOrdinary)
    (forest : OriginForest sigma Data Origin) :
    (forest, none) ∈ standardObservation tree ordinary ↔
      tree.native.AllVerticesMaterial ∧ forest = wholeForest tree ordinary := by
  classical
  have absent := right_unit_not_belowRoot tree ordinary forest
  simp only [standardObservation, Multiset.mem_add]
  rw [or_iff_right absent]
  unfold wholeObservation
  split_ifs with pure
  · simp [pure, eq_comm]
  · simp [pure]

theorem observed_equality_preserves_root_purity {Origin : Type}
    (left right : NamedTree Origin)
    (hl : left.native.IsOrdinary) (hr : right.native.IsOrdinary)
    (equal : standardObservation left hl = standardObservation right hr) :
    left.native.AllVerticesMaterial ↔ right.native.AllVerticesMaterial := by
  constructor
  · intro pure
    have member := (right_unit_mem_iff left hl (wholeForest left hl)).mpr ⟨pure, rfl⟩
    rw [equal] at member
    exact ((right_unit_mem_iff right hr _).mp member).1
  · intro pure
    have member := (right_unit_mem_iff right hr (wholeForest right hr)).mpr ⟨pure, rfl⟩
    rw [← equal] at member
    exact ((right_unit_mem_iff left hl _).mp member).1

/-- The obstruction applies to arbitrary positive pure composites. On
ClosedFragment inputs both sides are admitted by the same exact presentation. -/
theorem pure_identity_detour_countertheorem {Origin : Type}
    (tree : NamedTree Origin) (ordinary : tree.native.IsOrdinary)
    (pure : tree.native.AllVerticesMaterial) (cutName axName : Origin) :
    record tree = record (namedIdentityCut cutName axName tree) ∧
      standardObservation tree ordinary ≠
        standardObservation (namedIdentityCut cutName axName tree) (by trivial) := by
  refine ⟨pure_identity_detour_records_equal tree ordinary pure cutName axName, ?_⟩
  intro equal
  have impure : ¬ (identityCut tree.native).AllVerticesMaterial := by
    simp [identityCut, CKTree.AllVerticesMaterial, cutOccurrence]
  exact impure ((observed_equality_preserves_root_purity tree
    (namedIdentityCut cutName axName tree) ordinary (by trivial) equal).mp pure)

theorem admitted_pure_identity_detour_countertheorem {Origin : Type}
    (tree : NamedTree Origin) (fragment : ClosedFragment tree.native)
    (ordinary : tree.native.IsOrdinary) (pure : tree.native.AllVerticesMaterial)
    (cutName axName : Origin) :
    LocallyAdmittedTree presentation tree.native ∧
    LocallyAdmittedTree presentation (namedIdentityCut cutName axName tree).native ∧
    record tree = record (namedIdentityCut cutName axName tree) ∧
    standardObservation tree ordinary ≠
      standardObservation (namedIdentityCut cutName axName tree) (by trivial) :=
  ⟨fragment.locallyAdmitted, (ClosedFragment.identityCut fragment).locallyAdmitted,
    pure_identity_detour_countertheorem tree ordinary pure cutName axName⟩

theorem composite_endpoint_countertheorem :
    record fused = record (namedIdentityCut 3 4 fused) ∧
      standardObservation fused (by trivial) ≠
        standardObservation (namedIdentityCut 3 4 fused) (by trivial) :=
  pure_identity_detour_countertheorem fused (by trivial)
    unsafe_fusion_maximal_islands.1 3 4

/-- Ordinary logical cut elimination is not itself a congruence for this
material observation, even in the checked positive-arity native fragment.
Consequently a module-reuse rule cannot use ordinary logical equality alone. -/
theorem logical_equality_not_material_observation :
    LogicalEq separated fused ∧
    standardObservation separated (by trivial) ≠
      standardObservation fused (by trivial) := by
  refine ⟨actual_logical_fusion, ?_⟩
  intro equal
  have samePurity := observed_equality_preserves_root_purity separated fused
    (by trivial) (by trivial) equal
  exact unsafe_fusion_maximal_islands.2.1 (samePurity.mpr unsafe_fusion_maximal_islands.1)

def leaf : NamedTree Nat := named₀ 0
def detour : NamedTree Nat := namedIdentityCut 1 2 leaf

theorem leaf_fragment : ClosedFragment leaf.native := .ground₀
theorem detour_fragment : ClosedFragment detour.native := .identityCut .ground₀

theorem leaf_pure : leaf.native.AllVerticesMaterial := by decide
theorem detour_impure : ¬ detour.native.AllVerticesMaterial := by decide

theorem leaf_fresh : leaf.Fresh := by
  change ([0] : List Nat).Nodup
  decide
theorem detour_fresh : detour.Fresh := by
  change ([1, 0, 2] : List Nat).Nodup
  decide

theorem leaf_check_succeeds : CheckResult.Succeeded
    (presentation.checkAt closedBoundary raw₀) := by decide
theorem detour_check_succeeds : CheckResult.Succeeded
    (presentation.checkAt closedBoundary (rawIdentityCut raw₀)) := by decide

def checkedLeaf : CheckedDerivation presentation closedBoundary :=
  CheckResult.get leaf_check_succeeds
def checkedDetour : CheckedDerivation presentation closedBoundary :=
  CheckResult.get detour_check_succeeds

theorem leaf_native_checked : leaf.native = checkedLeaf.realize := rfl
theorem detour_native_checked : detour.native = checkedDetour.realize := rfl

/-- The genuinely logical detour preserves K: its one maximal island is the
same full ground packet; the punctured Cut/identity shell observes to Box₀. -/
theorem endpoint_records_equal : record leaf = record detour := by
  exact pure_identity_detour_records_equal leaf (by trivial) leaf_pure 1 2

/-- A universal theorem claim is refuted by exact checked native proofs, not
by a guessed carrier or finite agreement. The right unit exposes the failure. -/
theorem endpoint_observations_different :
    standardObservation leaf (by trivial) ≠
      standardObservation detour (by trivial) := by
  intro equal
  have iffPure := observed_equality_preserves_root_purity leaf detour
    (by trivial) (by trivial) equal
  exact detour_impure (iffPure.mp leaf_pure)

theorem ordinary_sparse_record_countertheorem :
    record leaf = record detour ∧
    standardObservation leaf (by trivial) ≠
      standardObservation detour (by trivial) :=
  ⟨endpoint_records_equal, endpoint_observations_different⟩

/-- The detour's island is an existing proper native witness at premise 1
(internal address `[0]`), not the witness-free global endpoint. -/
def detourIslandCut : CKCut detour.native where
  sourceOrdinary := by trivial
  plan := .ordinary cutOccurrence _ (.cons tree₀ _ (.detach (by trivial))
    (.cons identityTree .nil (.descend (.ordinary identityOccurrence .nil .nil)) .nil))

theorem detourIslandCut_ordered_tuple :
    detourIslandCut.detachedTuple =
      [⟨[0], closedBoundary, tree₀, by trivial⟩] := rfl

theorem detourIslandCut_full_factor :
    detourIslandCut.originForest detour.names = wholeForest leaf (by trivial) := rfl

theorem detourIslandCut_observed_remainder :
    observe (detourIslandCut.enrichedRemainder detour.names) = namedHole 0 := by
  change observe (namedIdentityCut 1 2 (namedHole 0)) = namedHole 0
  rw [observe_identityCut, observe_hole]

theorem detourIslandCut_refill :
    detourIslandCut.fill detourIslandCut.plan.detached = checkedDetour.realize :=
  detourIslandCut.fill_detached_reconstructs

theorem detourIslandCut_origin_refill :
    OriginTree.decode (detourIslandCut.originForest detour.names)
      (detourIslandCut.enrichedRemainder detour.names).native
      (detourIslandCut.enrichedRemainder detour.names).names = detour :=
  detourIslandCut.decode_collected detour.names detour_fresh

/-- Inherited typed holes are the degree-zero record, not positive factors. -/
theorem record_inherited_hole {Origin : Type} (name : Origin) :
    record (namedHole name) = (0, namedHole name) := rfl

end Potkin.SparseMaterialObservation

#print axioms Potkin.SparseMaterialObservation.right_unit_mem_iff
#print axioms Potkin.SparseMaterialObservation.endpoint_records_equal
#print axioms Potkin.SparseMaterialObservation.ordinary_sparse_record_countertheorem
#print axioms Potkin.SparseMaterialObservation.pure_identity_detour_countertheorem

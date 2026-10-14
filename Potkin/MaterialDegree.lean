import Potkin.MaterialRegions

/-!
# The greatest-degree material cut: the native combinatorial ingredient

This proves a genuine part of the proposed sparse-record argument, not its
logical-quotient or linear-coaction conclusion. No such quotient/coaction is
present in the current repository. Purity means every ordinary vertex has
material kind; on a locally admitted source this gives exact base membership.

The proofs recurse through the existing native cut constructors. Interfaces
are zero-vertex vacancies, not selectable factors. Equality is at the public
address-cut level; it does not reconstruct alignment from a commutative forest.
-/

namespace Potkin

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-- Every actually detached positive factor is wholly material. -/
def CKCutPlan.DetachedAllVerticesMaterial {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCutPlan tree) : Prop :=
  ∀ site : cut.Site, (cut.detached site).AllVerticesMaterial

/-- Ordered-child version of actual detached-factor purity. -/
def CKChildCuts.DetachedAllVerticesMaterial
    {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (cuts : CKChildCuts children) : Prop :=
  ∀ site : cuts.Site, (cuts.detached site).AllVerticesMaterial

mutual

/-- The maximal native material plan maximizes total detached vertex degree.
Any tie has exactly its address finset, not merely the same inventory. -/
theorem CKCutPlan.materialDegree_optimal : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
    cut.DetachedAllVerticesMaterial →
    cut.detachedDegreeSum ≤ tree.maximalMaterialPlan.detachedDegreeSum ∧
      (cut.detachedDegreeSum = tree.maximalMaterialPlan.detachedDegreeSum →
        cut.addressFinset = tree.maximalMaterialPlan.addressFinset)
  | _, _, .interface _, _ => by
      simp [CKCutPlan.detachedDegreeSum, CKTree.maximalMaterialPlan,
        CKCutPlan.addressFinset]
  | _, _, .ordinary _ children cuts, pure => by
      exact CKChildCuts.materialDegree_optimal cuts pure

/-- Independent ordered premises combine their exact optima; equality of
the nonnegative sums forces equality in every premise. -/
theorem CKChildCuts.materialDegree_optimal :
    {boundaries : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData boundaries} →
    (cuts : CKChildCuts children) → cuts.DetachedAllVerticesMaterial →
    cuts.detachedDegreeSum ≤ children.maximalMaterialCuts.detachedDegreeSum ∧
      (cuts.detachedDegreeSum = children.maximalMaterialCuts.detachedDegreeSum →
        cuts.addressFinset = children.maximalMaterialCuts.addressFinset)
  | _, _, .nil, _ => by
      simp [CKChildCuts.detachedDegreeSum, CKChildren.maximalMaterialCuts,
        CKChildCuts.addressFinset]
  | _, _, .cons head tail headCut tailCuts, pure => by
      have headPure : headCut.DetachedAllVerticesMaterial :=
        fun site => pure (.inl site)
      have tailPure : tailCuts.DetachedAllVerticesMaterial :=
        fun site => pure (.inr site)
      obtain ⟨headBound, headUnique⟩ := CKBranchCut.materialDegree_optimal headCut headPure
      obtain ⟨tailBound, tailUnique⟩ := CKChildCuts.materialDegree_optimal tailCuts tailPure
      constructor
      · exact Nat.add_le_add headBound tailBound
      · intro equal
        change headCut.detachedDegreeSum + tailCuts.detachedDegreeSum =
          head.maximalMaterialBranch.detachedDegreeSum +
            tail.maximalMaterialCuts.detachedDegreeSum at equal
        have headEqual : headCut.detachedDegreeSum =
            head.maximalMaterialBranch.detachedDegreeSum := by omega
        have tailEqual : tailCuts.detachedDegreeSum =
            tail.maximalMaterialCuts.detachedDegreeSum := by omega
        simp only [CKChildCuts.addressFinset, CKChildren.maximalMaterialCuts]
        rw [headUnique headEqual, tailUnique tailEqual]

/-- At a pure positive branch, detaching its root strictly beats every
descent: the latter retains at least the one ordinary root vertex. -/
theorem CKBranchCut.materialDegree_optimal : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
    cut.DetachedAllVerticesMaterial →
    cut.detachedDegreeSum ≤ tree.maximalMaterialBranch.detachedDegreeSum ∧
      (cut.detachedDegreeSum = tree.maximalMaterialBranch.detachedDegreeSum →
        cut.relativeAddressFinset = tree.maximalMaterialBranch.relativeAddressFinset)
  | _, tree, .detach ordinary, pure => by
      have wholePure : tree.AllVerticesMaterial := pure PUnit.unit
      cases tree with
      | interface _ => exact False.elim ordinary
      | ordinary o children =>
          simp [CKTree.maximalMaterialBranch, wholePure]
  | _, _, .descend cut, pure => by
      cases cut with
      | interface G =>
          simp [CKTree.maximalMaterialBranch, CKBranchCut.detachedDegreeSum,
            CKCutPlan.detachedDegreeSum, CKBranchCut.relativeAddressFinset,
            CKCutPlan.addressFinset]
      | ordinary o children cuts =>
          by_cases wholePure : (CKTree.ordinary o children).AllVerticesMaterial
          · have partition := cuts.degree_partition
            have strict : cuts.detachedDegreeSum < children.degree + 1 := by omega
            simp only [CKTree.maximalMaterialBranch, dif_pos wholePure,
              CKBranchCut.detachedDegreeSum, CKCutPlan.detachedDegreeSum,
              CKTree.degree]
            refine ⟨Nat.le_of_lt strict, ?_⟩
            intro equal
            exact False.elim ((Nat.ne_of_lt strict) equal)
          · simpa [CKTree.maximalMaterialBranch, wholePure,
              CKBranchCut.detachedDegreeSum, CKBranchCut.relativeAddressFinset]
              using CKCutPlan.materialDegree_optimal (.ordinary o children cuts) pure

end

namespace CKCut

/-- Purity of the actual occurrence-indexed detached tuple. -/
def PureDetached {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCut tree) : Prop := cut.plan.DetachedAllVerticesMaterial

/-- The maximum is unique as an extensional native cut. The source must be
non-pure to identify this nonroot plan with all maximal material islands;
the pure whole-root endpoint is intentionally not manufactured here. -/
theorem materialDegree_le_and_eq_addresses {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (ordinary : tree.IsOrdinary)
    (notPure : ¬ tree.AllVerticesMaterial) (cut : CKCut tree)
    (pure : cut.PureDetached) :
    cut.detachedDegreeSum ≤ (tree.maximalMaterialCut ordinary notPure).detachedDegreeSum ∧
      (cut.detachedDegreeSum = (tree.maximalMaterialCut ordinary notPure).detachedDegreeSum →
        cut.validAddressCut = (tree.maximalMaterialCut ordinary notPure).validAddressCut) := by
  obtain ⟨bound, unique⟩ := cut.plan.materialDegree_optimal pure
  refine ⟨bound, ?_⟩
  intro equal
  apply ValidAddressCut.ext
  exact unique equal

end CKCut

namespace ExtensionalCKCut

/-- Among native cuts with wholly material detached factors there is one
greatest-degree public cut, including the empty degree-zero case. -/
theorem unique_materialDegree_maximizer {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (notPure : ¬ tree.AllVerticesMaterial) :
    ∃! cut : ExtensionalCKCut tree,
      ∃ witness : CKCut tree, ofCKCut witness = cut ∧ witness.PureDetached ∧
        ∀ other : CKCut tree, other.PureDetached →
          other.detachedDegreeSum ≤ witness.detachedDegreeSum := by
  let maximum := tree.maximalMaterialCut ordinary notPure
  have maximumPure : maximum.PureDetached :=
    tree.maximalMaterialPlan_detached_allVerticesMaterial
  refine ⟨ofCKCut maximum, ⟨maximum, rfl, maximumPure, ?_⟩, ?_⟩
  · intro other pure
    exact (other.materialDegree_le_and_eq_addresses ordinary notPure pure).1
  · intro other data
    obtain ⟨witness, represents, pure, greatest⟩ := data
    have facts := witness.materialDegree_le_and_eq_addresses ordinary notPure pure
    have reverseBound := greatest maximum maximumPure
    have equal : witness.detachedDegreeSum = maximum.detachedDegreeSum :=
      Nat.le_antisymm facts.1 reverseBound
    rw [← represents]
    apply ExtensionalCKCut.ext
    exact congrArg (fun c : ValidAddressCut tree => c.addresses) (facts.2 equal)

end ExtensionalCKCut
end Potkin

#print axioms Potkin.CKCutPlan.materialDegree_optimal
#print axioms Potkin.CKCut.materialDegree_le_and_eq_addresses
#print axioms Potkin.ExtensionalCKCut.unique_materialDegree_maximizer

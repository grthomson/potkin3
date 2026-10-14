import Potkin.CKCutValidity
import Potkin.CompositeCutExpansion

/-!
# Intrinsic identity of one native CK cut

The independent public address antichain determines the existing constructor
witness uniquely.  The proof decomposes exact ordered premise slots; it does
not identify cuts after forest collection or by a finite enumeration check.
-/

namespace Potkin
universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual

/-- Exact physical addresses determine the complete native cut plan. -/
theorem CKCutPlan.eq_of_addressFinset_eq :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (left right : CKCutPlan tree) →
      left.addressFinset = right.addressFinset → left = right
  | _, .interface G, left, right, _ =>
      left.contents_reconstructs.symm.trans right.contents_reconstructs
  | _, .ordinary o children, left, right, equal => by
      have leftAddress := congrArg CKCutPlan.addressFinset left.contents_reconstructs
      have rightAddress := congrArg CKCutPlan.addressFinset right.contents_reconstructs
      change left.contents.addressFinset = left.addressFinset at leftAddress
      change right.contents.addressFinset = right.addressFinset at rightAddress
      have equalCuts : left.contents = right.contents := by
        apply CKChildCuts.ext_branchAt
        intro i
        apply CKBranchCut.eq_of_relativeAddressFinset_eq
        apply Finset.ext
        intro address
        rw [← CKChildCuts.mem_addressFinset_branchAt_iff left.contents i address,
          ← CKChildCuts.mem_addressFinset_branchAt_iff right.contents i address,
          leftAddress, rightAddress, equal]
      exact left.contents_reconstructs.symm.trans
        ((congrArg (CKCutPlan.ordinary o children) equalCuts).trans
          right.contents_reconstructs)
termination_by _ tree _ _ _ => 2 * tree.degree
decreasing_by
  exact CKChildren.branchMeasure_lt_parent children _

/-- Root detachment and strict descent are distinguished by the root address. -/
theorem CKBranchCut.eq_of_relativeAddressFinset_eq :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (left right : CKBranchCut tree) →
      left.relativeAddressFinset = right.relativeAddressFinset → left = right
  | _, _, .detach _, .detach _, _ => rfl
  | _, _, .detach _, .descend right, equal => by
      change {[]} = right.addressFinset at equal
      have rootMember : [] ∈ right.addressFinset := by
        rw [← equal]
        simp [CKBranchCut.relativeAddressFinset]
      exact (right.nonroot_of_mem_addressFinset rootMember rfl).elim
  | _, _, .descend left, .detach _, equal => by
      change left.addressFinset = {[]} at equal
      have rootMember : [] ∈ left.addressFinset := by
        rw [equal]
        simp [CKBranchCut.relativeAddressFinset]
      exact (left.nonroot_of_mem_addressFinset rootMember rfl).elim
  | _, _, .descend left, .descend right, equal =>
      congrArg CKBranchCut.descend
        (CKCutPlan.eq_of_addressFinset_eq left right equal)
termination_by _ tree _ _ _ => 2 * tree.degree + 1
decreasing_by omega

end

/-- Exact slot-by-slot native branching is determined by the selected addresses. -/
theorem CKChildCuts.eq_of_addressFinset_eq
    {Gs : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData Gs}
    (left right : CKChildCuts children)
    (equal : left.addressFinset = right.addressFinset) : left = right := by
  apply CKChildCuts.ext_branchAt
  intro i
  apply CKBranchCut.eq_of_relativeAddressFinset_eq
  apply Finset.ext
  intro address
  rw [← CKChildCuts.mem_addressFinset_branchAt_iff left i address,
    ← CKChildCuts.mem_addressFinset_branchAt_iff right i address, equal]

namespace CKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

@[ext]
theorem ext_plan {left right : CKCut tree} (equal : left.plan = right.plan) :
    left = right := by
  cases left
  cases right
  cases equal
  rfl

theorem eq_of_addressFinset_eq (left right : CKCut tree)
    (equal : left.plan.addressFinset = right.plan.addressFinset) :
    left = right :=
  ext_plan (CKCutPlan.eq_of_addressFinset_eq left.plan right.plan equal)

end CKCut

namespace ExtensionalCKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Canonical public compilation returns the original intrinsic witness. -/
@[simp]
theorem compiled_ofCKCut (cut : CKCut tree) :
    (ofCKCut cut).compiled = cut := by
  apply CKCut.eq_of_addressFinset_eq
  exact (ofCKCut cut).compiled_addressFinset

theorem ofCKCut_injective :
    Function.Injective (ofCKCut : CKCut tree → ExtensionalCKCut tree) := by
  intro left right equal
  have compiled := congrArg (fun cut : ExtensionalCKCut tree => cut.compiled) equal
  simpa only [compiled_ofCKCut] using compiled

/-- The existing legacy enumeration is already unique at public identity. -/
theorem rawEnumerate_nodup (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) : (rawEnumerate tree ordinary).Nodup :=
  (CKCut.enumerate_nodup tree ordinary).map ofCKCut_injective

end ExtensionalCKCut

namespace CKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Both existing native cut representations have exactly one physical witness. -/
def extensionalEquiv : CKCut tree ≃ ExtensionalCKCut tree where
  toFun := ExtensionalCKCut.ofCKCut
  invFun := ExtensionalCKCut.compiled
  left_inv := ExtensionalCKCut.compiled_ofCKCut
  right_inv := ExtensionalCKCut.ofCKCut_compiled

end CKCut
end Potkin

#print axioms Potkin.CKCutPlan.eq_of_addressFinset_eq
#print axioms Potkin.ExtensionalCKCut.compiled_ofCKCut
#print axioms Potkin.CKCut.extensionalEquiv

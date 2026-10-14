import Potkin.MaterialInstallation
import Mathlib.Data.Multiset.Count

/-!
# Finite exact material cut observations, with separate endpoint conventions

These are positive finite coefficient sums on EXISTING native forests and
typed origin-enriched proof states. Public physical cuts are enumerated once;
equal output monomials are collected with multiplicity, never deduplicated.
No Hopf algebra or comodule laws are assumed by these definitions.

The pointed whole opening retains a typed named Box. The ordinary coefficient
whole endpoint instead has empty right forest. These are separate summands
in separate codomains, not an equation identifying Box with the algebra unit.
-/

namespace Potkin.MaterialObservations
universe u v w z
variable {sigma : Signature.{u, v}} {InstanceData : Type w} {Origin : Type z}
variable {pi : PrimitiveFragment sigma} {G : Hypersequent sigma}

abbrev Operation (sigma : Signature.{u, v}) (InstanceData : Type w)
    (Origin : Type z) (G : Hypersequent sigma) :=
  OriginForest sigma InstanceData Origin × OriginTree sigma InstanceData Origin G

def cutTerm {tree : CKTree sigma InstanceData G} (cut : CKCut tree)
    (names : tree.OriginNames Origin) : Operation sigma InstanceData Origin G :=
  (cut.originForest names, cut.enrichedRemainder names)

/-- All nonroot native cuts, including the empty cut. The fixed profile is an
exact occurrence predicate. Admission is a separate native proof obligation. -/
noncomputable def cutSum (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (names : tree.OriginNames Origin) :
    Multiset (Operation sigma InstanceData Origin G) := by
  classical
  exact Multiset.ofList (((ExtensionalCKCut.enumerate tree ordinary).filter
    (fun cut => decide (cut.compiled.plan.DetachedInBase B))).map
      (fun cut => cutTerm cut.compiled names))

/-- Actual complete operations, not merely coefficient trees or primitive
inventories. This retains their full typed residual and physical origins. -/
def Available (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (names : tree.OriginNames Origin)
    (operation : Operation sigma InstanceData Origin G) : Prop :=
  ∃ cut : ExtensionalCKCut tree,
    cut.compiled.plan.DetachedInBase B ∧ cutTerm cut.compiled names = operation

theorem mem_cutSum_iff (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (names : tree.OriginNames Origin) (operation : Operation sigma InstanceData Origin G) :
    operation ∈ cutSum B tree ordinary names ↔ Available B tree names operation := by
  classical
  change operation ∈ Multiset.ofList _ ↔ _
  rw [Multiset.mem_coe]
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨cut, member, equal⟩
    exact ⟨cut, of_decide_eq_true (List.mem_filter.mp member).2, equal⟩
  · rintro ⟨cut, eligible, equal⟩
    apply List.mem_map.mpr
    refine ⟨cut, List.mem_filter.mpr ⟨?_, by simpa using eligible⟩, equal⟩
    exact cut.mem_enumerate

/-- Exact positive coefficient detects availability; physical operations
with equal observed monomials still contribute separately to the count. -/
theorem coefficient_pos_iff_available (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (names : tree.OriginNames Origin) (operation : Operation sigma InstanceData Origin G)
    [DecidableEq (Operation sigma InstanceData Origin G)] :
    0 < (cutSum B tree ordinary names).count operation ↔
      Available B tree names operation := by
  classical
  rw [Multiset.count_pos, mem_cutSum_iff]

def wholePacket (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (names : tree.OriginNames Origin) : OriginForest sigma InstanceData Origin :=
  {(⟨tree, names⟩ : OriginTree sigma InstanceData Origin G).asComponent ordinary}

def wholeVacancy (tree : CKTree sigma InstanceData G)
    (names : tree.OriginNames Origin) : OriginTree sigma InstanceData Origin G :=
  ⟨.interface G, tree.rootOrigin names⟩

/-- A separately labelled pointed WHOLE opening, never a native root cut. -/
noncomputable def pointedWhole (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (names : tree.OriginNames Origin) :
    Multiset (Operation sigma InstanceData Origin G) := by
  classical
  exact if tree.AllVerticesInBase B then
    {(wholePacket tree ordinary names, wholeVacancy tree names)} else 0

noncomputable def pointedSum (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (names : tree.OriginNames Origin) :=
  cutSum B tree ordinary names + pointedWhole B tree ordinary names

/-- The typed vacancy's finite observation is 1 tensor that SAME vacancy;
there is no positive factor and no whole-tree contribution. -/
noncomputable def pointedStateSum (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → (tree : CKTree sigma InstanceData G) →
    tree.OriginNames Origin → Multiset (Operation sigma InstanceData Origin G)
  | G, .interface _, names => {(0, ⟨.interface G, names⟩)}
  | _, .ordinary o children, names => pointedSum B (.ordinary o children) (by trivial) names

/-- Ordinary coefficient cut sum on one positive, possibly OPEN component.
Proper/empty residuals are positive native components; the global whole
endpoint instead has EMPTY right forest. No coassociativity is claimed. -/
noncomputable def coefficientCutSum (B : MaterialBase sigma InstanceData pi)
    (component : OriginComponent sigma InstanceData Origin) :
    Multiset (OriginForest sigma InstanceData Origin × OriginForest sigma InstanceData Origin) := by
  classical
  let tree := component.native.tree
  let below : List (OriginForest sigma InstanceData Origin ×
      OriginForest sigma InstanceData Origin) :=
    ((ExtensionalCKCut.enumerate tree component.native.ordinary).filter
    (fun cut => decide (cut.compiled.plan.DetachedInBase B))).map (fun cut =>
      (cut.compiled.originForest component.names,
        {(cut.compiled.enrichedRemainder component.names).asComponent
          cut.compiled.remainder_isOrdinary}))
  exact Multiset.ofList below + if tree.AllVerticesInBase B then ({({component}, 0)}) else 0

theorem vacancy_has_only_empty (B : MaterialBase sigma InstanceData pi)
    (name : Origin) :
    pointedStateSum B (.interface G : CKTree sigma InstanceData G) name =
      {(0, (⟨.interface G, name⟩ : OriginTree sigma InstanceData Origin G))} := rfl

end Potkin.MaterialObservations

#print axioms Potkin.MaterialObservations.mem_cutSum_iff
#print axioms Potkin.MaterialObservations.coefficient_pos_iff_available

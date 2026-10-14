import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Filter
import Potkin.IntrinsicCutIdentity
import Potkin.CompositeCutExpansion

/-!
# Public cut sums from independent composite choices

The production enumeration recurses on the installation, using native branch
cuts only for the payloads. It never enumerates cuts of the completed proof.
The theorem compares that independent enumeration to the public native cut
enumeration. Arbitrary filtered multiset-valued continuations preserve every
coefficient, even when many different cut witnesses have the same image.
Neither enumeration includes the separately adjoined global whole endpoint.
-/

namespace Potkin
universe u v w z
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual

def CKCutPlan.enumerateExpansionChoices :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      List (installation.ExpansionChoices fillers)
  | _, _, .interface _, _ => [PUnit.unit]
  | _, _, .ordinary _ _ children, fillers =>
      children.enumerateExpansionChoices fillers

def CKChildCuts.enumerateExpansionChoices :
    {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      List (installation.ExpansionChoices fillers)
  | _, _, .nil, _ => [PUnit.unit]
  | _, _, .cons _ _ head tail, fillers =>
      (head.enumerateExpansionChoices (fun s => fillers (.inl s))).product
        (tail.enumerateExpansionChoices (fun s => fillers (.inr s)))

def CKBranchCut.enumerateExpansionChoices :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      List (installation.ExpansionChoices fillers)
  | _, _, .detach _, fillers => (fillers PUnit.unit).enumerateBranchCuts
  | _, _, .descend plan, fillers => by
      cases plan with
      | interface _ => exact [PUnit.unit]
      | ordinary _ _ children =>
          exact Sum.inl PUnit.unit ::
            (children.enumerateExpansionChoices fillers).map Sum.inr

end

mutual

theorem CKCutPlan.enumerateExpansionChoices_nodup :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      (installation.enumerateExpansionChoices fillers).Nodup
  | _, _, .interface _, _ => by simp [CKCutPlan.enumerateExpansionChoices]
  | _, _, .ordinary _ _ children, fillers =>
      children.enumerateExpansionChoices_nodup fillers

theorem CKChildCuts.enumerateExpansionChoices_nodup :
    {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      (installation.enumerateExpansionChoices fillers).Nodup
  | _, _, .nil, _ => by simp [CKChildCuts.enumerateExpansionChoices]
  | _, _, .cons _ _ head tail, fillers =>
      (head.enumerateExpansionChoices_nodup (fun s => fillers (.inl s))).product
        (tail.enumerateExpansionChoices_nodup (fun s => fillers (.inr s)))

theorem CKBranchCut.enumerateExpansionChoices_nodup :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      (installation.enumerateExpansionChoices fillers).Nodup
  | _, _, .detach _, fillers => (fillers PUnit.unit).enumerateBranchCuts_nodup
  | _, _, .descend plan, fillers => by
      cases plan with
      | interface _ => simp [CKBranchCut.enumerateExpansionChoices]
      | ordinary _ _ children =>
          apply List.nodup_cons.mpr
          constructor
          · intro member
            rcases List.mem_map.mp member with ⟨choice, _, impossible⟩
            cases impossible
          · exact (children.enumerateExpansionChoices_nodup fillers).map
              (fun _ _ equal => Sum.inr.inj equal)

end

mutual

theorem CKCutPlan.mem_enumerateExpansionChoices :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (choice : installation.ExpansionChoices fillers) →
      choice ∈ installation.enumerateExpansionChoices fillers
  | _, _, .interface _, _, choice => by cases choice; simp [CKCutPlan.enumerateExpansionChoices]
  | _, _, .ordinary _ _ children, fillers, choice =>
      children.mem_enumerateExpansionChoices fillers choice

theorem CKChildCuts.mem_enumerateExpansionChoices :
    {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (choice : installation.ExpansionChoices fillers) →
      choice ∈ installation.enumerateExpansionChoices fillers
  | _, _, .nil, _, choice => by cases choice; simp [CKChildCuts.enumerateExpansionChoices]
  | _, _, .cons _ _ head tail, fillers, choice =>
      List.mem_product.mpr
        ⟨head.mem_enumerateExpansionChoices (fun s => fillers (.inl s)) choice.1,
          tail.mem_enumerateExpansionChoices (fun s => fillers (.inr s)) choice.2⟩

theorem CKBranchCut.mem_enumerateExpansionChoices :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (choice : installation.ExpansionChoices fillers) →
      choice ∈ installation.enumerateExpansionChoices fillers
  | _, _, .detach _, _, choice => choice.mem_enumerate
  | _, _, .descend plan, fillers, choice => by
      cases plan with
      | interface _ => cases choice; simp [CKBranchCut.enumerateExpansionChoices]
      | ordinary _ _ children =>
          cases choice with
          | inl unit => cases unit; simp [CKBranchCut.enumerateExpansionChoices]
          | inr choice =>
              apply List.mem_cons_of_mem
              exact List.mem_map.mpr
                ⟨choice, children.mem_enumerateExpansionChoices fillers choice, rfl⟩

end

namespace CKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Public physical cuts of the completed native proof have unique choices. -/
def installedPublicCutEquiv (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site)) :
    ExtensionalCKCut (installation.fill fillers) ≃
      installation.plan.ExpansionChoices fillers :=
  CKCut.extensionalEquiv.symm.trans (installation.installedCutEquiv fillers)

@[simp]
theorem installedPublicCutEquiv_symm_apply (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choice : installation.plan.ExpansionChoices fillers) :
    (installation.installedPublicCutEquiv fillers).symm choice =
      ExtensionalCKCut.ofCKCut (installation.expandedCut fillers choice) := rfl

@[simp]
theorem compiled_installedPublicCutEquiv_symm (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choice : installation.plan.ExpansionChoices fillers) :
    ((installation.installedPublicCutEquiv fillers).symm choice).compiled =
      installation.expandedCut fillers choice :=
  ExtensionalCKCut.compiled_ofCKCut _

/-- Independent choice enumeration equals public cut enumeration before any
forest or coefficient collection. Order of enumeration need not be identical. -/
theorem publicEnumerate_perm_expandedChoices (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site)) :
    (ExtensionalCKCut.enumerate (installation.fill fillers)
      (installation.fill_isOrdinary fillers)).Perm
        ((installation.plan.enumerateExpansionChoices fillers).map
          (installation.installedPublicCutEquiv fillers).symm) := by
  let equiv := installation.installedPublicCutEquiv fillers
  apply (List.perm_ext_iff_of_nodup
    (ExtensionalCKCut.enumerate_nodup _ _)
    ((installation.plan.enumerateExpansionChoices_nodup fillers).map
      equiv.symm.injective)).mpr
  intro cut
  constructor
  · intro _
    exact List.mem_map.mpr
      ⟨equiv cut, installation.plan.mem_enumerateExpansionChoices fillers (equiv cut),
        equiv.symm_apply_apply cut⟩
  · intro _
    exact cut.mem_enumerate

/-- Exact equality of the native cut multisets, without deduplicating any later
projection. This is the coefficient-comparison bridge, not a fixture check. -/
theorem publicEnumerate_eq_expandedChoices (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site)) :
    (↑(ExtensionalCKCut.enumerate (installation.fill fillers)
      (installation.fill_isOrdinary fillers)) : Multiset _) =
      (↑(installation.plan.enumerateExpansionChoices fillers) : Multiset _).map
        (installation.installedPublicCutEquiv fillers).symm :=
  Multiset.coe_eq_coe.mpr (installation.publicEnumerate_perm_expandedChoices fillers)

/-- Arbitrary eligibility filtering and multiset-valued coefficient continuation
commute with the explicit bijection. The continuation may perform further
native cuts on each ACTUAL expanded factor; matching is retained before bind. -/
theorem publicEnumerate_filter_bind_expandedChoices
    {Basis : Type z} (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (eligible : ExtensionalCKCut (installation.fill fillers) → Prop)
    [DecidablePred eligible]
    (weight : ExtensionalCKCut (installation.fill fillers) → Multiset Basis) :
    ((↑(ExtensionalCKCut.enumerate (installation.fill fillers)
      (installation.fill_isOrdinary fillers)) : Multiset _).filter eligible).bind weight =
      ((↑(installation.plan.enumerateExpansionChoices fillers) : Multiset _).filter
        (fun choice => eligible ((installation.installedPublicCutEquiv fillers).symm choice))).bind
          (fun choice => weight ((installation.installedPublicCutEquiv fillers).symm choice)) := by
  rw [installation.publicEnumerate_eq_expandedChoices fillers,
    Multiset.filter_map, Multiset.bind_map]
  rfl

end CKCut
end Potkin

#print axioms Potkin.CKCutPlan.enumerateExpansionChoices_nodup
#print axioms Potkin.CKCutPlan.mem_enumerateExpansionChoices
#print axioms Potkin.CKCut.publicEnumerate_filter_bind_expandedChoices

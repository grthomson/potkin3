import Potkin.CutExpansionSums

/-!
# Precisely admitted inherited cuts under native payload replacement

An inherited cut may select a replacement seam root, select a retained
ancestor, or leave a payload untouched. A proper cut inside a replaced
payload has no inherited counterpart and is explicitly excluded. The
transport consumes the old public physical cut and evidence of this exact
domain. It never claims equality of all old/new coefficients or factors.
-/

namespace Potkin
universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual
def CKTree.emptyCutPlan : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → CKCutPlan tree
  | _, .interface G => .interface G
  | _, .ordinary o children => .ordinary o children children.emptyChildCuts

def CKChildren.emptyChildCuts : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → CKChildCuts children
  | _, .nil => .nil
  | _, .cons head tail =>
      .cons head tail (.descend head.emptyCutPlan) tail.emptyChildCuts
end

mutual
@[simp]
theorem CKTree.emptyCutPlan_addresses : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → tree.emptyCutPlan.addressFinset = ∅
  | _, .interface _ => rfl
  | _, .ordinary _ children => children.emptyChildCuts_addresses

@[simp]
theorem CKChildren.emptyChildCuts_addresses :
    {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) →
      children.emptyChildCuts.addressFinset = ∅
  | _, .nil => rfl
  | _, .cons head tail => by
      simp only [CKChildren.emptyChildCuts, CKChildCuts.addressFinset,
        CKBranchCut.relativeAddressFinset, head.emptyCutPlan_addresses,
        tail.emptyChildCuts_addresses, Finset.image_empty, Finset.empty_union]
end

mutual
def CKCutPlan.SafeExpansion : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers → Prop
  | _, _, .interface _, _, _ => True
  | _, _, .ordinary _ _ children, fillers, choice =>
      children.SafeExpansion fillers choice

def CKChildCuts.SafeExpansion : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers → Prop
  | _, _, .nil, _, _ => True
  | _, _, .cons _ _ head tail, fillers, choice =>
      head.SafeExpansion (fun s => fillers (.inl s)) choice.1 ∧
        tail.SafeExpansion (fun s => fillers (.inr s)) choice.2

def CKBranchCut.SafeExpansion : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers → Prop
  | _, _, .detach _, _, choice =>
      match choice with
      | .detach _ => True
      | .descend cut => cut.addressFinset = ∅
  | _, _, .descend plan, fillers, choice => by
      cases plan with
      | interface _ => exact True
      | ordinary _ _ children =>
          exact match choice with
          | .inl _ => True
          | .inr inner => children.SafeExpansion fillers inner
end

mutual
def CKCutPlan.transportSafeExpansion : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKCutPlan tree) →
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    ((site : installation.Site) → (newFillers site).IsOrdinary) →
    (choice : installation.ExpansionChoices oldFillers) →
    installation.SafeExpansion oldFillers choice → installation.ExpansionChoices newFillers
  | _, _, .interface _, _, _, _, _, _ => PUnit.unit
  | _, _, .ordinary _ _ children, oldFillers, newFillers, positive, choice, safe =>
      children.transportSafeExpansion oldFillers newFillers positive choice safe

def CKChildCuts.transportSafeExpansion : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    ((site : installation.Site) → (newFillers site).IsOrdinary) →
    (choice : installation.ExpansionChoices oldFillers) →
    installation.SafeExpansion oldFillers choice → installation.ExpansionChoices newFillers
  | _, _, .nil, _, _, _, _, _ => PUnit.unit
  | _, _, .cons _ _ head tail, oldFillers, newFillers, positive, choice, safe =>
      (head.transportSafeExpansion (fun s => oldFillers (.inl s))
          (fun s => newFillers (.inl s)) (fun s => positive (.inl s)) choice.1 safe.1,
        tail.transportSafeExpansion (fun s => oldFillers (.inr s))
          (fun s => newFillers (.inr s)) (fun s => positive (.inr s)) choice.2 safe.2)

def CKBranchCut.transportSafeExpansion : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (installation : CKBranchCut tree) →
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    ((site : installation.Site) → (newFillers site).IsOrdinary) →
    (choice : installation.ExpansionChoices oldFillers) →
    installation.SafeExpansion oldFillers choice → installation.ExpansionChoices newFillers
  | _, _, .detach _, _, newFillers, positive, choice, _ =>
      match choice with
      | .detach _ => .detach (positive PUnit.unit)
      | .descend _ => .descend (newFillers PUnit.unit).emptyCutPlan
  | _, _, .descend plan, oldFillers, newFillers, positive, choice, safe => by
      cases plan with
      | interface _ => exact PUnit.unit
      | ordinary _ _ children =>
          exact match choice, safe with
          | .inl _, _ => .inl PUnit.unit
          | .inr inner, safe => .inr
              (children.transportSafeExpansion oldFillers newFillers positive inner safe)
end

mutual
theorem CKCutPlan.transportSafeExpansion_addresses :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (positive : (site : installation.Site) → (newFillers site).IsOrdinary) →
    (choice : installation.ExpansionChoices oldFillers) →
    (safe : installation.SafeExpansion oldFillers choice) →
    (installation.expandCut newFillers
      (installation.transportSafeExpansion oldFillers newFillers positive choice safe)).addressFinset =
        (installation.expandCut oldFillers choice).addressFinset
  | _, _, .interface _, _, _, _, _, _ => rfl
  | _, _, .ordinary _ _ children, oldFillers, newFillers, positive, choice, safe =>
      children.transportSafeExpansion_addresses oldFillers newFillers positive choice safe

theorem CKChildCuts.transportSafeExpansion_addresses :
    {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (positive : (site : installation.Site) → (newFillers site).IsOrdinary) →
    (choice : installation.ExpansionChoices oldFillers) →
    (safe : installation.SafeExpansion oldFillers choice) →
    (installation.expandCut newFillers
      (installation.transportSafeExpansion oldFillers newFillers positive choice safe)).addressFinset =
        (installation.expandCut oldFillers choice).addressFinset
  | _, _, .nil, _, _, _, _, _ => rfl
  | _, _, .cons _ _ head tail, oldFillers, newFillers, positive, choice, safe => by
      change _ ∪ _ = _ ∪ _
      simp only [CKChildCuts.transportSafeExpansion]
      rw [head.transportSafeExpansion_addresses
        (fun s => oldFillers (.inl s)) (fun s => newFillers (.inl s))
        (fun s => positive (.inl s)) choice.1 safe.1,
        tail.transportSafeExpansion_addresses
        (fun s => oldFillers (.inr s)) (fun s => newFillers (.inr s))
        (fun s => positive (.inr s)) choice.2 safe.2]

theorem CKBranchCut.transportSafeExpansion_addresses :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
    (positive : (site : installation.Site) → (newFillers site).IsOrdinary) →
    (choice : installation.ExpansionChoices oldFillers) →
    (safe : installation.SafeExpansion oldFillers choice) →
    (installation.expandCut newFillers
      (installation.transportSafeExpansion oldFillers newFillers positive choice safe)).relativeAddressFinset =
        (installation.expandCut oldFillers choice).relativeAddressFinset
  | _, _, .detach _, _, newFillers, _, choice, safe => by
      cases choice with
      | detach _ => rfl
      | descend cut =>
          change (newFillers PUnit.unit).emptyCutPlan.addressFinset = cut.addressFinset
          rw [CKTree.emptyCutPlan_addresses]
          exact safe.symm
  | _, _, .descend plan, oldFillers, newFillers, positive, choice, safe => by
      cases plan with
      | interface _ => rfl
      | ordinary _ _ children =>
          cases choice with
          | inl _ => rfl
          | inr inner =>
              exact children.transportSafeExpansion_addresses
                oldFillers newFillers positive inner safe
end

namespace CKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- The exact partial transport domain is tested on the old physical cut's
unique decomposition. Proper cuts INSIDE any changed payload are excluded. -/
def InheritedDomain (installation : CKCut tree)
    (oldFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (cut : ExtensionalCKCut (installation.fill oldFillers)) : Prop :=
  installation.plan.SafeExpansion oldFillers
    (installation.installedPublicCutEquiv oldFillers cut)

/-- Existing public cut → existing public cut, with its precise admitted
domain supplied. Selecting the new seam root requires a positive payload. -/
def transportInherited (installation : CKCut tree)
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (positive : (site : installation.Site) → (newFillers site).IsOrdinary)
    (cut : ExtensionalCKCut (installation.fill oldFillers))
    (safe : installation.InheritedDomain oldFillers cut) :
    ExtensionalCKCut (installation.fill newFillers) :=
  (installation.installedPublicCutEquiv newFillers).symm
    (installation.plan.transportSafeExpansion oldFillers newFillers positive
      (installation.installedPublicCutEquiv oldFillers cut) safe)

/-- Inherited transport preserves exact physical addresses, not only forest
cardinality. The native target witness consequently retains ordered matching. -/
theorem transportInherited_addresses (installation : CKCut tree)
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (positive : (site : installation.Site) → (newFillers site).IsOrdinary)
    (cut : ExtensionalCKCut (installation.fill oldFillers))
    (safe : installation.InheritedDomain oldFillers cut) :
    (installation.transportInherited oldFillers newFillers positive cut safe).addresses =
      cut.addresses := by
  let choice := installation.installedPublicCutEquiv oldFillers cut
  have native := installation.plan.transportSafeExpansion_addresses
    oldFillers newFillers positive choice safe
  have oldCompiled : installation.plan.expandCut oldFillers choice = cut.compiled.plan := by
    exact installation.plan.expand_decompose oldFillers cut.compiled.plan
  calc
    (installation.transportInherited oldFillers newFillers positive cut safe).addresses =
        (installation.plan.expandCut newFillers
          (installation.plan.transportSafeExpansion oldFillers newFillers positive choice safe)).addressFinset := rfl
    _ = (installation.plan.expandCut oldFillers choice).addressFinset := native
    _ = cut.compiled.plan.addressFinset := congrArg CKCutPlan.addressFinset oldCompiled
    _ = cut.addresses := cut.compiled_addressFinset

/-- No two distinct inherited physical cuts can collide after transport. -/
theorem transportInherited_injective (installation : CKCut tree)
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (positive : (site : installation.Site) → (newFillers site).IsOrdinary)
    (left right : ExtensionalCKCut (installation.fill oldFillers))
    (safeLeft : installation.InheritedDomain oldFillers left)
    (safeRight : installation.InheritedDomain oldFillers right)
    (equal : installation.transportInherited oldFillers newFillers positive left safeLeft =
      installation.transportInherited oldFillers newFillers positive right safeRight) :
    left = right := by
  apply ExtensionalCKCut.ext
  have addresses := congrArg ExtensionalCKCut.addresses equal
  simpa only [transportInherited_addresses] using addresses

/-- The transported certificate carries its actual ordered tuple and typed
remainder, whose native aligned refill reconstructs the new installed proof. -/
theorem transportInherited_reconstructs (installation : CKCut tree)
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (positive : (site : installation.Site) → (newFillers site).IsOrdinary)
    (cut : ExtensionalCKCut (installation.fill oldFillers))
    (safe : installation.InheritedDomain oldFillers cut) :
    let target := (installation.transportInherited oldFillers newFillers positive cut safe).compiled
    target.fill target.plan.detached = installation.fill newFillers :=
  ExtensionalCKCut.compiled (installation.transportInherited oldFillers newFillers positive cut safe)
    |>.fill_detached_reconstructs

end CKCut
end Potkin

#print axioms Potkin.CKCutPlan.transportSafeExpansion_addresses
#print axioms Potkin.CKCut.transportInherited_addresses
#print axioms Potkin.CKCut.transportInherited_reconstructs

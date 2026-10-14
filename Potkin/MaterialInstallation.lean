import Potkin.CompositeCutExpansion

/-!
# Exact material eligibility after native installation

The chosen base is an exact occurrence predicate, not a rule-name inventory.
The material test is performed AFTER filling. An opened impure old subtree
has disappeared; remaining old vertices and entire supplied payloads determine
whether a newly spanning connected factor is eligible. Inherited interfaces
are vacant, so contribute no occurrence. All proofs use the existing native
tree, cut and filling carriers.
-/

namespace Potkin
universe u v w z
variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {pi : PrimitiveFragment sigma} {Origin : Type z}

mutual
/-- Exact selected-base purity of a native tree, including positive-arity
occurrences and complete boundary/instance/incidence identity. -/
def CKTree.AllVerticesInBase (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → CKTree sigma InstanceData G → Prop
  | _, .interface _ => True
  | _, .ordinary o children => B.Member o ∧ children.AllVerticesInBase B
def CKChildren.AllVerticesInBase (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → CKChildren sigma InstanceData Gs → Prop
  | _, .nil => True
  | _, .cons head tail => head.AllVerticesInBase B ∧ tail.AllVerticesInBase B
end

mutual
/-- Kind-purity is an exact-base test ONLY in this admitted sector of one
fixed equipped presentation. This is not an arbitrary-profile cast. -/
theorem CKTree.inBase_iff_material_of_admitted {T : ProofTheory sigma InstanceData}
    {P : EquippedPresentation T} : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → LocallyAdmittedTree P tree →
      (tree.AllVerticesInBase T.base ↔ tree.AllVerticesMaterial)
  | _, .interface _, _ => Iff.rfl
  | _, .ordinary o children, admitted => by
      constructor
      · intro pure
        exact ⟨T.base.member_material pure.1,
          (children.inBase_iff_material_of_admitted admitted.2).mp pure.2⟩
      · intro pure
        exact ⟨(P.admitted o admitted.1).materialMembership_of_kind pure.1,
          (children.inBase_iff_material_of_admitted admitted.2).mpr pure.2⟩
theorem CKChildren.inBase_iff_material_of_admitted {T : ProofTheory sigma InstanceData}
    {P : EquippedPresentation T} : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → LocallyAdmittedChildren P children →
      (children.AllVerticesInBase T.base ↔ children.AllVerticesMaterial)
  | _, .nil, _ => Iff.rfl
  | _, .cons head tail, admitted =>
      and_congr (head.inBase_iff_material_of_admitted admitted.1)
        (tail.inBase_iff_material_of_admitted admitted.2)
end

mutual
/-- Independent selected-base recurrence on the installation, not its
completed proof: retained ordinary roots and entire actual fillers are tested. -/
def CKCutPlan.FilledInBase (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    ((site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → Prop
  | _, _, .interface _, _ => True
  | _, _, .ordinary o _ children, fillers => B.Member o ∧ children.FilledInBase B fillers
def CKChildCuts.FilledInBase (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    ((site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → Prop
  | _, _, .nil, _ => True
  | _, _, .cons _ _ head tail, fillers =>
      head.FilledInBase B (fun s => fillers (.inl s)) ∧
        tail.FilledInBase B (fun s => fillers (.inr s))
def CKBranchCut.FilledInBase (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    ((site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → Prop
  | _, _, .detach _, fillers => (fillers PUnit.unit).AllVerticesInBase B
  | _, _, .descend plan, fillers => plan.FilledInBase B fillers
end

mutual
theorem CKCutPlan.filledInBase_iff (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      (installation.fill fillers).AllVerticesInBase B ↔ installation.FilledInBase B fillers
  | _, _, .interface _, _ => Iff.rfl
  | _, _, .ordinary _ _ children, fillers =>
      and_congr Iff.rfl (children.filledInBase_iff B fillers)
theorem CKChildCuts.filledInBase_iff (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      (installation.fill fillers).AllVerticesInBase B ↔ installation.FilledInBase B fillers
  | _, _, .nil, _ => Iff.rfl
  | _, _, .cons _ _ head tail, fillers =>
      and_congr (head.filledInBase_iff B (fun s => fillers (.inl s)))
        (tail.filledInBase_iff B (fun s => fillers (.inr s)))
theorem CKBranchCut.filledInBase_iff (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      (installation.fill fillers).AllVerticesInBase B ↔ installation.FilledInBase B fillers
  | _, _, .detach _, _ => Iff.rfl
  | _, _, .descend plan, fillers => plan.filledInBase_iff B fillers
end

mutual
/-- The exact completion criterion: only the retained skeleton is tested;
discarded old impure regions impose NO purity hypothesis. -/
theorem CKCutPlan.filledInBase_partition (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      installation.FilledInBase B fillers ↔
      installation.remainder.AllVerticesInBase B ∧
        (∀ site, (fillers site).AllVerticesInBase B)
  | _, _, .interface _, _ => by
      constructor
      · intro _; exact ⟨trivial, fun site => nomatch site⟩
      · intro _; trivial
  | _, _, .ordinary _ _ children, fillers => by
      constructor
      · rintro ⟨root, below⟩
        have result := (children.filledInBase_partition B fillers).mp below
        exact ⟨⟨root, result.1⟩, result.2⟩
      · rintro ⟨⟨root, below⟩, supplied⟩
        exact ⟨root, (children.filledInBase_partition B fillers).mpr ⟨below, supplied⟩⟩
theorem CKChildCuts.filledInBase_partition (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      installation.FilledInBase B fillers ↔
      installation.remainder.AllVerticesInBase B ∧
        (∀ site, (fillers site).AllVerticesInBase B)
  | _, _, .nil, _ => by
      constructor
      · intro _; exact ⟨trivial, fun site => nomatch site⟩
      · intro _; trivial
  | _, _, .cons _ _ head tail, fillers => by
      constructor
      · rintro ⟨h, t⟩
        have hp := (head.filledInBase_partition B (fun s => fillers (.inl s))).mp h
        have tp := (tail.filledInBase_partition B (fun s => fillers (.inr s))).mp t
        refine ⟨⟨hp.1, tp.1⟩, ?_⟩
        intro site
        cases site with
        | inl s => exact hp.2 s
        | inr s => exact tp.2 s
      · rintro ⟨⟨h, t⟩, supplied⟩
        exact ⟨(head.filledInBase_partition B (fun s => fillers (.inl s))).mpr
          ⟨h, fun s => supplied (.inl s)⟩,
          (tail.filledInBase_partition B (fun s => fillers (.inr s))).mpr
            ⟨t, fun s => supplied (.inr s)⟩⟩
theorem CKBranchCut.filledInBase_partition (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) →
      installation.FilledInBase B fillers ↔
      installation.remainder.AllVerticesInBase B ∧
        (∀ site, (fillers site).AllVerticesInBase B)
  | _, _, .detach _, fillers => by
      constructor
      · intro pure
        exact ⟨trivial, fun site => by cases site; exact pure⟩
      · intro pure; exact pure.2 PUnit.unit
  | _, _, .descend plan, fillers => plan.filledInBase_partition B fillers
end

def CKCutPlan.DetachedInBase (B : MaterialBase sigma InstanceData pi)
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G} (cut : CKCutPlan tree) :
    Prop := ∀ site, (cut.detached site).AllVerticesInBase B
def CKChildCuts.DetachedInBase (B : MaterialBase sigma InstanceData pi)
    {Gs : List (Hypersequent sigma)} {children : CKChildren sigma InstanceData Gs}
    (cut : CKChildCuts children) : Prop := ∀ site, (cut.detached site).AllVerticesInBase B
def CKBranchCut.DetachedInBase (B : MaterialBase sigma InstanceData pi)
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree) :
    Prop := ∀ site, (cut.detached site).AllVerticesInBase B

mutual
/-- Eligibility is independent of the expansion map. A selected old root
tests the completed connected subtree; internal filler choices test their
actual full detached factors. -/
def CKCutPlan.EligibleExpansion (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers → Prop
  | _, _, .interface _, _, _ => True
  | _, _, .ordinary _ _ children, fillers, choices =>
      children.EligibleExpansion B fillers choices
def CKChildCuts.EligibleExpansion (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers → Prop
  | _, _, .nil, _, _ => True
  | _, _, .cons _ _ head tail, fillers, choices =>
      head.EligibleExpansion B (fun s => fillers (.inl s)) choices.1 ∧
        tail.EligibleExpansion B (fun s => fillers (.inr s)) choices.2
def CKBranchCut.EligibleExpansion (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → installation.ExpansionChoices fillers → Prop
  | _, _, .detach _, _, cut => cut.DetachedInBase B
  | _, _, .descend plan, fillers, choices => by
      cases plan with
      | interface _ => exact True
      | ordinary o children cuts =>
          exact match choices with
          | .inl _ => B.Member o ∧ cuts.FilledInBase B fillers
          | .inr choices => cuts.EligibleExpansion B fillers choices
end

mutual
theorem CKCutPlan.expanded_eligible_iff (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKCutPlan tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
      (installation.expandCut fillers choices).DetachedInBase B ↔
        installation.EligibleExpansion B fillers choices
  | _, _, .interface _, _, _ => by
      constructor
      · intro _; trivial
      · intro _ site; exact nomatch site
  | _, _, .ordinary _ _ children, fillers, choices =>
      children.expanded_eligible_iff B fillers choices
theorem CKChildCuts.expanded_eligible_iff (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → {children : CKChildren sigma InstanceData Gs} →
    (installation : CKChildCuts children) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
      (installation.expandCut fillers choices).DetachedInBase B ↔
        installation.EligibleExpansion B fillers choices
  | _, _, .nil, _, _ => by
      constructor
      · intro _; trivial
      · intro _ site; exact nomatch site
  | _, _, .cons _ _ head tail, fillers, choices => by
      constructor
      · intro pure
        exact ⟨(head.expanded_eligible_iff B (fun s => fillers (.inl s)) choices.1).mp
          (fun s => pure (.inl s)),
          (tail.expanded_eligible_iff B (fun s => fillers (.inr s)) choices.2).mp
            (fun s => pure (.inr s))⟩
      · rintro ⟨h, t⟩ site
        cases site with
        | inl s => exact
            (head.expanded_eligible_iff B (fun s => fillers (.inl s)) choices.1).mpr h s
        | inr s => exact
            (tail.expanded_eligible_iff B (fun s => fillers (.inr s)) choices.2).mpr t s
theorem CKBranchCut.expanded_eligible_iff (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (installation : CKBranchCut tree) →
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) → (choices : installation.ExpansionChoices fillers) →
      (installation.expandCut fillers choices).DetachedInBase B ↔
        installation.EligibleExpansion B fillers choices
  | _, _, .detach _, _, _ => Iff.rfl
  | _, _, .descend plan, fillers, choices => by
      cases plan with
      | interface _ =>
          constructor
          · intro _; trivial
          · intro _ site; exact nomatch site
      | ordinary o children cuts =>
          cases choices with
          | inl value =>
              constructor
              · intro pure
                have result := pure PUnit.unit
                exact ⟨result.1, (cuts.filledInBase_iff B fillers).mp result.2⟩
              · rintro ⟨root, below⟩ site
                cases site
                exact ⟨root, (cuts.filledInBase_iff B fillers).mpr below⟩
          | inr choices => exact cuts.expanded_eligible_iff B fillers choices
end

/-- On an admitted fixed presentation this exact-base cut criterion is
precisely the existing native material-kind cut criterion. -/
theorem CKCutPlan.detachedInBase_iff_material_of_admitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCutPlan tree) (admitted : LocallyAdmittedTree P tree) :
    cut.DetachedInBase T.base ↔ cut.DetachedAllVerticesMaterial := by
  constructor
  · intro pure site
    exact ((cut.detached site).inBase_iff_material_of_admitted
      (cut.detachedLocallyAdmitted admitted site)).mp (pure site)
  · intro pure site
    exact ((cut.detached site).inBase_iff_material_of_admitted
      (cut.detachedLocallyAdmitted admitted site)).mpr (pure site)

mutual
/-- Native extraction preserves exact base membership of the entire factor;
this includes arbitrary internal nonprimitive cuts of a pure payload. -/
theorem CKCutPlan.detachedInBase_of_inBase (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (cut : CKCutPlan tree) → tree.AllVerticesInBase B → cut.DetachedInBase B
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ children, pure, site =>
      children.detachedInBase_of_inBase B pure.2 site
theorem CKChildCuts.detachedInBase_of_inBase (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → {children : CKChildren sigma InstanceData Gs} →
    (cut : CKChildCuts children) → children.AllVerticesInBase B → cut.DetachedInBase B
  | _, _, .nil, _, site => nomatch site
  | _, _, .cons _ _ head tail, pure, site => by
      cases site with
      | inl s => exact head.detachedInBase_of_inBase B pure.1 s
      | inr s => exact tail.detachedInBase_of_inBase B pure.2 s
theorem CKBranchCut.detachedInBase_of_inBase (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (cut : CKBranchCut tree) → tree.AllVerticesInBase B → cut.DetachedInBase B
  | _, _, .detach _, pure, _ => pure
  | _, _, .descend plan, pure, site => plan.detachedInBase_of_inBase B pure site
end

mutual
/-- Subsequent actual extraction also preserves the entire positive open
middle factor's exact membership, with inherited and new holes vacuous. -/
theorem CKCutPlan.remainderInBase_of_inBase (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (cut : CKCutPlan tree) → tree.AllVerticesInBase B → cut.remainder.AllVerticesInBase B
  | _, _, .interface _, _ => trivial
  | _, _, .ordinary _ _ children, pure =>
      ⟨pure.1, children.remainderInBase_of_inBase B pure.2⟩
theorem CKChildCuts.remainderInBase_of_inBase (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → {children : CKChildren sigma InstanceData Gs} →
    (cut : CKChildCuts children) → children.AllVerticesInBase B →
      cut.remainder.AllVerticesInBase B
  | _, _, .nil, _ => trivial
  | _, _, .cons _ _ head tail, pure =>
      ⟨head.remainderInBase_of_inBase B pure.1, tail.remainderInBase_of_inBase B pure.2⟩
theorem CKBranchCut.remainderInBase_of_inBase (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (cut : CKBranchCut tree) → tree.AllVerticesInBase B → cut.remainder.AllVerticesInBase B
  | _, _, .detach _, _ => trivial
  | _, _, .descend plan, pure => plan.remainderInBase_of_inBase B pure
end

/-- Eligibility of an intact old-root composite spanning ANY NUMBER of
supplied sites is exactly retained-skeleton membership plus full filler
membership. No hypothesis tests discarded old probe bodies. -/
theorem CKBranchCut.spanning_available_iff (B : MaterialBase sigma InstanceData pi)
    (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (installation : CKChildCuts children)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site)) :
    (CKBranchCut.descend (.ordinary o children installation)).EligibleExpansion B
      fillers (.inl PUnit.unit) ↔
      (CKTree.ordinary o installation.remainder).AllVerticesInBase B ∧
        (∀ site, (fillers site).AllVerticesInBase B) :=
  (CKCutPlan.ordinary o children installation).filledInBase_partition B fillers

/-- The same named OLD-root operation can be eligible before replacement
and ineligible afterwards. The two statuses are aligned by the common native
installation and old ancestor; a universal nonnegative-defect claim is false. -/
theorem CKBranchCut.spanning_replacement_loss
    (B : MaterialBase sigma InstanceData pi) (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (installation : CKChildCuts children)
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site))
    (retainedPure : (CKTree.ordinary o installation.remainder).AllVerticesInBase B)
    (oldPure : ∀ site, (oldFillers site).AllVerticesInBase B)
    (newImpure : ∃ site, ¬ (newFillers site).AllVerticesInBase B) :
    (CKBranchCut.descend (.ordinary o children installation)).EligibleExpansion B
      oldFillers (.inl PUnit.unit) ∧
    ¬ (CKBranchCut.descend (.ordinary o children installation)).EligibleExpansion B
      newFillers (.inl PUnit.unit) := by
  constructor
  · exact (spanning_available_iff B o children installation oldFillers).mpr
      ⟨retainedPure, oldPure⟩
  · intro eligible
    rcases newImpure with ⟨site, notPure⟩
    exact notPure (((spanning_available_iff B o children installation newFillers).mp
      eligible).2 site)

/-- Conversely pure replacements can COMPLETE an impure old region and
create its intact material extraction operation. -/
theorem CKBranchCut.spanning_replacement_gain
    (B : MaterialBase sigma InstanceData pi) (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (installation : CKChildCuts children)
    (oldFillers newFillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.siteBoundary site))
    (retainedPure : (CKTree.ordinary o installation.remainder).AllVerticesInBase B)
    (oldImpure : ∃ site, ¬ (oldFillers site).AllVerticesInBase B)
    (newPure : ∀ site, (newFillers site).AllVerticesInBase B) :
    ¬ (CKBranchCut.descend (.ordinary o children installation)).EligibleExpansion B
      oldFillers (.inl PUnit.unit) ∧
    (CKBranchCut.descend (.ordinary o children installation)).EligibleExpansion B
      newFillers (.inl PUnit.unit) := by
  have result := spanning_replacement_loss B o children installation newFillers
    oldFillers retainedPure newPure oldImpure
  exact ⟨result.2, result.1⟩

/-- Replacing a probe by an intact composite exposes that WHOLE actual
module precisely when every exact vertex is selected. Internal payload cuts
remain separate choices and are not removed by this criterion. -/
theorem CKBranchCut.wholePayload_available_iff
    (B : MaterialBase sigma InstanceData pi) {G : Hypersequent sigma}
    {probe : CKTree sigma InstanceData G} (probeOrdinary : probe.IsOrdinary)
    (payload : CKTree sigma InstanceData G) (payloadOrdinary : payload.IsOrdinary) :
    (CKBranchCut.detach probeOrdinary).EligibleExpansion B (fun _ => payload)
      (CKBranchCut.detach payloadOrdinary) ↔ payload.AllVerticesInBase B := by
  constructor
  · intro eligible; exact eligible PUnit.unit
  · intro pure site; cases site; exact pure

/-- On a pure supplied composite EVERY native branch cut remains eligible,
including whole, empty and genuinely internal nonprimitive selections. -/
theorem CKBranchCut.purePayload_all_inner_choices
    (B : MaterialBase sigma InstanceData pi) {G : Hypersequent sigma}
    {probe : CKTree sigma InstanceData G} (probeOrdinary : probe.IsOrdinary)
    (payload : CKTree sigma InstanceData G) (pure : payload.AllVerticesInBase B)
    (inner : CKBranchCut payload) :
    (CKBranchCut.detach probeOrdinary).EligibleExpansion B (fun _ => payload) inner :=
  inner.detachedInBase_of_inBase B pure

namespace CKCut
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Fixed-base, checked-sector material eligibility for every expansion.
Native admission makes the exact selected-base test agree with the existing
kind predicate; no rule-name or kind-only guess is accepted as evidence. -/
theorem expanded_material_iff {T : ProofTheory sigma InstanceData}
    {P : EquippedPresentation T} (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choices : installation.plan.ExpansionChoices fillers)
    (sourceAdmitted : LocallyAdmittedTree P tree)
    (fillersAdmitted : ∀ site, LocallyAdmittedTree P (fillers site)) :
    (installation.expandedCut fillers choices).plan.DetachedAllVerticesMaterial ↔
      installation.plan.EligibleExpansion T.base fillers choices := by
  have admitted := installation.fill_locallyAdmitted fillers sourceAdmitted fillersAdmitted
  exact (CKCutPlan.detachedInBase_iff_material_of_admitted
    (installation.expandedCut fillers choices).plan admitted).symm.trans
      (installation.plan.expanded_eligible_iff T.base fillers choices)

end CKCut

end Potkin

#print axioms Potkin.CKCutPlan.expanded_eligible_iff
#print axioms Potkin.CKCutPlan.filledInBase_partition
#print axioms Potkin.CKCutPlan.detachedInBase_iff_material_of_admitted
#print axioms Potkin.CKCut.expanded_material_iff
#print axioms Potkin.CKBranchCut.spanning_available_iff
#print axioms Potkin.CKBranchCut.spanning_replacement_gain
#print axioms Potkin.CKBranchCut.spanning_replacement_loss
#print axioms Potkin.CKCutPlan.remainderInBase_of_inBase
#print axioms Potkin.CKCutPlan.detachedInBase_of_inBase

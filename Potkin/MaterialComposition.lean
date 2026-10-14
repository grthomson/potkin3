import Potkin.MaterialObservations
import Potkin.CutExpansionSums

/-!
# Exact material coefficient composition and intact staged availability

The RHS recurses on the installation and actual payload branch cuts, not on
the completed proof. It retains complete connected factors, typed residuals,
origins and natural-number multiplicities. This is a finite coefficient-sum
theorem, NOT an instantiated Hopf algebra or a coaction-law assertion.

The staged application observes lower factors, intact positive OPEN middle
factors and the original typed root remainder. It describes available actual
operations, rather than only showing that decoding recovers the source.
-/

namespace Potkin.MaterialObservations
universe u v w z a
variable {sigma : Signature.{u, v}} {InstanceData : Type w} {Origin : Type z}
variable {pi : PrimitiveFragment sigma} {G : Hypersequent sigma}
variable {tree : CKTree sigma InstanceData G}

def expansionTerm (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choice : installation.plan.ExpansionChoices fillers)
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    Operation sigma InstanceData Origin G :=
  (Multiset.ofList (installation.plan.expansionOriginFactors fillers choice names innerNames),
    installation.plan.expansionOriginRemainder fillers choice names innerNames)

theorem expanded_cutTerm (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (choice : installation.plan.ExpansionChoices fillers)
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    cutTerm (installation.expandedCut fillers choice)
      (installation.plan.fillOriginNames fillers names innerNames) =
        expansionTerm installation fillers choice names innerNames := by
  apply Prod.ext
  · exact congrArg Multiset.ofList
      (installation.plan.expand_originFactors fillers choice names innerNames)
  · exact installation.plan.expand_originRemainder fillers choice names innerNames

noncomputable def expansionSum (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    Multiset (Operation sigma InstanceData Origin G) := by
  classical
  exact ((↑(installation.plan.enumerateExpansionChoices fillers) : Multiset _).filter
    (installation.plan.EligibleExpansion B fillers)).map
      (fun choice => expansionTerm installation fillers choice names innerNames)

private theorem cutSum_filter_map (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (names : tree.OriginNames Origin) :
    cutSum B tree ordinary names =
      (by
        classical
        exact ((↑(ExtensionalCKCut.enumerate tree ordinary) :
          Multiset (ExtensionalCKCut tree)).filter
            (fun cut => cut.compiled.plan.DetachedInBase B)).map
              (fun cut => cutTerm cut.compiled names)) := by
  classical
  rfl

/-- THE finite material coefficient identity. Each physical cut occurs once;
equal full observations collect with multiplicity. No freshness hypothesis
is needed for equality; unique decoding additionally needs global freshness. -/
theorem material_cutSum_composition (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    cutSum B (installation.fill fillers) (installation.fill_isOrdinary fillers)
      (installation.plan.fillOriginNames fillers names innerNames) =
        expansionSum B installation fillers names innerNames := by
  classical
  rw [cutSum_filter_map, installation.publicEnumerate_eq_expandedChoices fillers,
    Multiset.filter_map, Multiset.map_map]
  simp only [Function.comp_def, CKCut.compiled_installedPublicCutEquiv_symm]
  unfold expansionSum
  apply Multiset.map_congr
  · exact Multiset.filter_congr (fun choice _ =>
      installation.plan.expanded_eligible_iff B fillers choice)
  · intro choice _
    exact expanded_cutTerm installation fillers choice names innerNames

/-- The separately labelled typed whole opening uses POST-installation purity,
including the retained root. This independently specified endpoint is not
part of the proper-cut choice enumeration. -/
noncomputable def expansionWhole (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    Multiset (Operation sigma InstanceData Origin G) := by
  classical
  exact if installation.plan.FilledInBase B fillers then
    {(wholePacket (installation.fill fillers) (installation.fill_isOrdinary fillers)
        (installation.plan.fillOriginNames fillers names innerNames),
      wholeVacancy (installation.fill fillers)
        (installation.plan.fillOriginNames fillers names innerNames))} else 0

/-- The separately labelled typed whole opening uses POST-installation purity,
including the retained root. It is never inserted in the proper-cut bijection. -/
theorem pointed_sum_composition (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin) :
    pointedSum B (installation.fill fillers) (installation.fill_isOrdinary fillers)
      (installation.plan.fillOriginNames fillers names innerNames) =
    expansionSum B installation fillers names innerNames +
      expansionWhole B installation fillers names innerNames := by
  classical
  unfold pointedSum pointedWhole expansionWhole
  rw [material_cutSum_composition]
  by_cases eligible : installation.plan.FilledInBase B fillers
  · have pure : (installation.fill fillers).AllVerticesInBase B :=
      (installation.plan.filledInBase_iff B fillers).mpr eligible
    simp only [eligible, pure, if_true]
  · have impure : ¬ (installation.fill fillers).AllVerticesInBase B :=
      fun pure => eligible ((installation.plan.filledInBase_iff B fillers).mp pure)
    simp only [eligible, impure, if_false]

/-- Arbitrary actual native continuations may observe subsequent cuts of the
full factors. This aligns witnesses BEFORE continuation or collection. -/
theorem installed_available_with_iff (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (continuation : CKCut (installation.fill fillers) → Prop) :
    (∃ cut : ExtensionalCKCut (installation.fill fillers),
      cut.compiled.plan.DetachedInBase B ∧ continuation cut.compiled) ↔
    ∃ choice : installation.plan.ExpansionChoices fillers,
      installation.plan.EligibleExpansion B fillers choice ∧
        continuation (installation.expandedCut fillers choice) := by
  constructor
  · rintro ⟨cut, eligible, available⟩
    let choice := installation.installedPublicCutEquiv fillers cut
    have equal : installation.expandedCut fillers choice = cut.compiled := by
      have publicEqual := (installation.installedPublicCutEquiv fillers).symm_apply_apply cut
      have compiled := congrArg (fun c => c.compiled) publicEqual
      simpa only [CKCut.compiled_installedPublicCutEquiv_symm] using compiled
    refine ⟨choice, ?_, ?_⟩
    · apply (installation.plan.expanded_eligible_iff B fillers choice).mp
      have plans : installation.plan.expandCut fillers choice = cut.compiled.plan :=
        congrArg CKCut.plan equal
      exact plans.symm ▸ eligible
    · rw [equal]
      exact available
  · rintro ⟨choice, eligible, available⟩
    refine ⟨ExtensionalCKCut.ofCKCut (installation.expandedCut fillers choice), ?_, ?_⟩
    · simpa only [ExtensionalCKCut.compiled_ofCKCut] using
        (installation.plan.expanded_eligible_iff B fillers choice).mpr eligible
    · simpa only [ExtensionalCKCut.compiled_ofCKCut] using available

/-- A requested complete operation has positive coefficient iff some actual
compatible outer/inner choice exposes exactly its full factor AND remainder. -/
theorem installed_operation_available_iff (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (operation : Operation sigma InstanceData Origin G) :
    Available B (installation.fill fillers)
      (installation.plan.fillOriginNames fillers names innerNames) operation ↔
    ∃ choice : installation.plan.ExpansionChoices fillers,
      installation.plan.EligibleExpansion B fillers choice ∧
        expansionTerm installation fillers choice names innerNames = operation := by
  unfold Available
  simpa only [expanded_cutTerm] using
    (installed_available_with_iff B installation fillers
      (fun cut => cutTerm cut (installation.plan.fillOriginNames fillers names innerNames) = operation))

abbrev TwoStageOperation (sigma : Signature.{u, v}) (InstanceData : Type w)
    (Origin : Type z) (G : Hypersequent sigma) :=
  OriginForest sigma InstanceData Origin ×
    OriginForest sigma InstanceData Origin × OriginTree sigma InstanceData Origin G

/-- Lower factors, full positive middle residual factors, root typed state.
The family is indexed by PHYSICAL outer sites, not a collected coefficient. -/
def stagedTerm (outer : CKCut tree) (names : tree.OriginNames Origin)
    (inner : (site : outer.Site) → CKCut (outer.plan.detached site)) :
    TwoStageOperation sigma InstanceData Origin G :=
  (Multiset.ofList (outer.orderedSites.flatMap (fun site =>
      (inner site).plan.originFactors (outer.plan.originDetached names site))),
    Multiset.ofList (outer.orderedSites.map (fun site =>
      ((inner site).enrichedRemainder (outer.plan.originDetached names site)).asComponent
        (inner site).remainder_isOrdinary)),
    outer.enrichedRemainder names)

def StagedContinuation (B : MaterialBase sigma InstanceData pi)
    (outer : CKCut tree) (names : tree.OriginNames Origin)
    (operation : TwoStageOperation sigma InstanceData Origin G) : Prop :=
  ∃ inner : (site : outer.Site) → CKCut (outer.plan.detached site),
    (∀ site, (inner site).plan.DetachedInBase B) ∧ stagedTerm outer names inner = operation

def StagedAvailable (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (names : tree.OriginNames Origin)
    (operation : TwoStageOperation sigma InstanceData Origin G) : Prop :=
  ∃ outer : ExtensionalCKCut tree,
    outer.compiled.plan.DetachedInBase B ∧
      StagedContinuation B outer.compiled names operation

/-- Intact pure composite factors permit EVERY subsequent native proper/empty
extraction. Both the lower forest and the full positive OPEN middle factors
remain in the SAME exact base. This is an operational heredity law. -/
theorem pure_outer_all_stages (B : MaterialBase sigma InstanceData pi)
    (outer : CKCut tree) (pure : outer.plan.DetachedInBase B)
    (inner : (site : outer.Site) → CKCut (outer.plan.detached site)) :
    (∀ site, (inner site).plan.DetachedInBase B) ∧
      (∀ site, (inner site).remainder.AllVerticesInBase B) := by
  exact ⟨fun site => (inner site).plan.detachedInBase_of_inBase B (pure site),
    fun site => (inner site).plan.remainderInBase_of_inBase B (pure site)⟩

/-- Availability under installation commutes with ACTUAL subsequent extraction
inside intact composite coefficients. The target records the lower forest,
the full middle residual operations, and the root remainder, not just refill. -/
theorem staged_available_composition_iff (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (operation : TwoStageOperation sigma InstanceData Origin G) :
    StagedAvailable B (installation.fill fillers)
      (installation.plan.fillOriginNames fillers names innerNames) operation ↔
    ∃ choice : installation.plan.ExpansionChoices fillers,
      installation.plan.EligibleExpansion B fillers choice ∧
      ∃ inner : (site : (installation.expandedCut fillers choice).Site) →
          CKCut ((installation.expandedCut fillers choice).plan.detached site),
        stagedTerm (installation.expandedCut fillers choice)
          (installation.plan.fillOriginNames fillers names innerNames) inner = operation := by
  unfold StagedAvailable
  rw [installed_available_with_iff B installation fillers
    (fun cut => StagedContinuation B cut
      (installation.plan.fillOriginNames fillers names innerNames) operation)]
  constructor
  · rintro ⟨choice, eligible, inner, _, equal⟩
    exact ⟨choice, eligible, inner, equal⟩
  · rintro ⟨choice, eligible, inner, equal⟩
    refine ⟨choice, eligible, inner, ?_, equal⟩
    exact (pure_outer_all_stages B (installation.expandedCut fillers choice)
      ((installation.plan.expanded_eligible_iff B fillers choice).mpr eligible) inner).1

/-- The exact finite sum specializes to one native admitted presentation.
Admission is explicit: matching displayed boundaries alone is not evidence.
This does not identify local admission with hole-free checker completeness. -/
theorem admitted_material_composition {T : ProofTheory sigma InstanceData}
    {P : EquippedPresentation T} (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (sourceAdmitted : LocallyAdmittedTree P tree)
    (fillersAdmitted : ∀ site, LocallyAdmittedTree P (fillers site)) :
    LocallyAdmittedTree P (installation.fill fillers) ∧
    cutSum T.base (installation.fill fillers) (installation.fill_isOrdinary fillers)
      (installation.plan.fillOriginNames fillers names innerNames) =
      expansionSum T.base installation fillers names innerNames ∧
    (∀ choice, (installation.expandedCut fillers choice).plan.DetachedAllVerticesMaterial ↔
      installation.plan.EligibleExpansion T.base fillers choice) :=
  ⟨installation.fill_locallyAdmitted fillers sourceAdmitted fillersAdmitted,
    material_cutSum_composition T.base installation fillers names innerNames,
    fun choice => installation.expanded_material_iff fillers choice sourceAdmitted fillersAdmitted⟩

/-- Coefficients of the full monomial agree exactly, including collisions. -/
theorem installed_coefficient_eq (B : MaterialBase sigma InstanceData pi)
    (installation : CKCut tree)
    (fillers : (site : installation.Site) → CKTree sigma InstanceData
      (installation.plan.siteBoundary site))
    (names : tree.OriginNames Origin)
    (innerNames : (site : installation.Site) → (fillers site).OriginNames Origin)
    (operation : Operation sigma InstanceData Origin G)
    [DecidableEq (Operation sigma InstanceData Origin G)] :
    (cutSum B (installation.fill fillers) (installation.fill_isOrdinary fillers)
      (installation.plan.fillOriginNames fillers names innerNames)).count operation =
      (expansionSum B installation fillers names innerNames).count operation := by
  rw [material_cutSum_composition]

/-- An available full operation is reconstructive when FILLED physical origins
are globally fresh. This is not inferred from separate filler freshness. -/
theorem available_decodes (B : MaterialBase sigma InstanceData pi)
    (tree : CKTree sigma InstanceData G) (names : tree.OriginNames Origin)
    (operation : Operation sigma InstanceData Origin G)
    (fresh : (tree.originList names).Nodup)
    (available : Available B tree names operation) :
    OriginTree.decode operation.1 operation.2.native operation.2.names =
      (⟨tree, names⟩ : OriginTree sigma InstanceData Origin G) := by
  rcases available with ⟨cut, _, equal⟩
  rw [← equal]
  exact cut.compiled.decode_collected names fresh

end Potkin.MaterialObservations

#print axioms Potkin.MaterialObservations.material_cutSum_composition
#print axioms Potkin.MaterialObservations.pointed_sum_composition
#print axioms Potkin.MaterialObservations.installed_operation_available_iff
#print axioms Potkin.MaterialObservations.staged_available_composition_iff
#print axioms Potkin.MaterialObservations.pure_outer_all_stages
#print axioms Potkin.MaterialObservations.admitted_material_composition
#print axioms Potkin.MaterialObservations.installed_coefficient_eq
#print axioms Potkin.MaterialObservations.available_decodes

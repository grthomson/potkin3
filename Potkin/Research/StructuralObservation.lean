import Potkin.AllHoleFilling
import Potkin.Research.StructuralReduction

/-!
# Independent restricted-rule observation and its exact cheap baseline

`RulesAllowed allow` is an independently specified structural fragment: every
actual registered occurrence in a derivation must satisfy `allow`. For example,
`allow` may permit Gentzen Cut exactly at a declared set of formulas, and permit
contraction exactly at declared formulas. It is NOT defined from CK cuts,
coefficients, or a material support condition.

This file proves a negative application result. The complete exact occurrence
inventory already decides this observer, even after nonlinear copying. It is a
stronger baseline than the project's material-only profile, which deliberately
omits logical and structural occurrences. No same-inventory separator for this
observer can exist. This does not claim that inventories determine addressed CK
cuts, their typed remainders, or opaque-module replay.

The native all-hole filling theorem proves contextual propagation from local
constructor obligations. It does not assume compatibility under every context.
The theorem concerns one-step preservation, not confluence/path independence.
-/

namespace Potkin.Research.StructuralObservation

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual
/-- Independent restricted-rule judgment on the native open carrier. -/
def RulesAllowed (allow : LocalOccurrence sigma InstanceData → Prop) :
    {G : Hypersequent sigma} → CKTree sigma InstanceData G → Prop
  | _, .interface _ => True
  | _, .ordinary occurrence children =>
      allow occurrence ∧ ChildRulesAllowed allow children

def ChildRulesAllowed (allow : LocalOccurrence sigma InstanceData → Prop) :
    {Gs : List (Hypersequent sigma)} → CKChildren sigma InstanceData Gs → Prop
  | _, .nil => True
  | _, .cons head tail => RulesAllowed allow head ∧ ChildRulesAllowed allow tail
end

mutual
/-- Exact rule inventory before forgetting order; all kinds are retained. -/
def ruleList : {G : Hypersequent sigma} → CKTree sigma InstanceData G →
    List (LocalOccurrence sigma InstanceData)
  | _, .interface _ => []
  | _, .ordinary occurrence children => occurrence :: childRuleList children

def childRuleList : {Gs : List (Hypersequent sigma)} →
    CKChildren sigma InstanceData Gs → List (LocalOccurrence sigma InstanceData)
  | _, .nil => []
  | _, .cons head tail => ruleList head ++ childRuleList tail
end

/-- Cheap address/order-forgetting summary retaining every exact occurrence
with multiplicity. This is a multiset of decorations, NOT a new proof carrier. -/
def exactRuleInventory {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) : Multiset (LocalOccurrence sigma InstanceData) :=
  ↑(ruleList tree)

/-- The independent observer evaluated directly on its cheap summary. -/
def InventoryAllowed (allow : LocalOccurrence sigma InstanceData → Prop)
    (inventory : Multiset (LocalOccurrence sigma InstanceData)) : Prop :=
  ∀ occurrence ∈ inventory, allow occurrence

mutual
theorem rulesAllowed_iff_ruleList (allow : LocalOccurrence sigma InstanceData → Prop) :
    {G : Hypersequent sigma} → (tree : CKTree sigma InstanceData G) →
      (RulesAllowed allow tree ↔ ∀ occurrence ∈ ruleList tree, allow occurrence)
  | _, .interface _ => by simp [RulesAllowed, ruleList]
  | _, .ordinary occurrence children => by
      rw [RulesAllowed, ruleList, childRulesAllowed_iff_childRuleList allow children]
      simp only [List.mem_cons, forall_eq_or_imp]

theorem childRulesAllowed_iff_childRuleList
    (allow : LocalOccurrence sigma InstanceData → Prop) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma InstanceData Gs) →
      (ChildRulesAllowed allow children ↔
        ∀ occurrence ∈ childRuleList children, allow occurrence)
  | _, .nil => by simp [ChildRulesAllowed, childRuleList]
  | _, .cons head tail => by
      rw [ChildRulesAllowed, childRuleList,
        rulesAllowed_iff_ruleList allow head,
        childRulesAllowed_iff_childRuleList allow tail]
      simp only [List.mem_append, or_imp, forall_and]
end

/-- Universal factorization through the all-rule exact occurrence inventory. -/
theorem rulesAllowed_factorization
    (allow : LocalOccurrence sigma InstanceData → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    RulesAllowed allow tree ↔ InventoryAllowed allow (exactRuleInventory tree) := by
  simpa [InventoryAllowed, exactRuleInventory] using rulesAllowed_iff_ruleList allow tree

/-- A separator with equal exact inventory is mathematically impossible for
this observer, independently of tree shape or duplication histories. -/
theorem no_same_inventory_separator
    (allow : LocalOccurrence sigma InstanceData → Prop)
    {G H : Hypersequent sigma} (left : CKTree sigma InstanceData G)
    (right : CKTree sigma InstanceData H)
    (same : exactRuleInventory left = exactRuleInventory right) :
    RulesAllowed allow left ↔ RulesAllowed allow right := by
  rw [rulesAllowed_factorization allow left, rulesAllowed_factorization allow right, same]

/-- Explicit whole-boundary transport changes only the dependent type index,
not the independent occurrence predicate. -/
theorem rulesAllowed_transport
    (allow : LocalOccurrence sigma InstanceData → Prop)
    {G H : Hypersequent sigma} (boundary : G = H)
    (tree : CKTree sigma InstanceData G) :
    RulesAllowed allow (boundary ▸ tree) ↔ RulesAllowed allow tree := by
  cases boundary
  rfl

mutual
/-- Local constructor recurrence propagated through every native typed
all-hole context. It retains registry admission as a separate obligation. -/
theorem rulesAllowed_fillAssignment
    (allow : LocalOccurrence sigma InstanceData → Prop) :
    {G : Hypersequent sigma} → (context : CKTree sigma InstanceData G) →
    (assignment : context.LeafAssignment) →
      (RulesAllowed allow (context.fillAssignment assignment) ↔
        RulesAllowed allow context ∧ ∀ hole, RulesAllowed allow (assignment hole))
  | _, .interface _, assignment => by
      change RulesAllowed allow (assignment PUnit.unit) ↔
        True ∧ ∀ hole : PUnit, RulesAllowed allow (assignment hole)
      constructor
      · intro accepted
        exact ⟨trivial, fun hole => by cases hole; exact accepted⟩
      · intro accepted
        exact accepted.2 PUnit.unit
  | _, .ordinary occurrence children, assignment => by
      change (allow occurrence ∧ ChildRulesAllowed allow (children.fillAssignment assignment)) ↔
        (allow occurrence ∧ ChildRulesAllowed allow children) ∧
          ∀ hole, RulesAllowed allow (assignment hole)
      rw [childRulesAllowed_fillAssignment allow children assignment]
      exact and_assoc.symm

theorem childRulesAllowed_fillAssignment
    (allow : LocalOccurrence sigma InstanceData → Prop) :
    {Gs : List (Hypersequent sigma)} → (context : CKChildren sigma InstanceData Gs) →
    (assignment : context.LeafAssignment) →
      (ChildRulesAllowed allow (context.fillAssignment assignment) ↔
        ChildRulesAllowed allow context ∧ ∀ hole, RulesAllowed allow (assignment hole))
  | _, .nil, _ => by
      constructor
      · intro _
        exact ⟨trivial, fun hole => nomatch hole⟩
      · intro _
        trivial
  | _, .cons head tail, assignment => by
      change (RulesAllowed allow (head.fillAssignment (fun h => assignment (.inl h))) ∧
        ChildRulesAllowed allow (tail.fillAssignment (fun h => assignment (.inr h)))) ↔
        (RulesAllowed allow head ∧ ChildRulesAllowed allow tail) ∧
          ∀ hole, RulesAllowed allow (assignment hole)
      rw [rulesAllowed_fillAssignment allow head,
        childRulesAllowed_fillAssignment allow tail]
      constructor
      · intro accepted
        refine ⟨⟨accepted.1.1, accepted.2.1⟩, ?_⟩
        intro hole
        cases hole with
        | inl hole => exact accepted.1.2 hole
        | inr hole => exact accepted.2.2 hole
      · intro accepted
        exact ⟨⟨accepted.1.1, fun h => accepted.2 (.inl h)⟩,
          ⟨accepted.1.2, fun h => accepted.2 (.inr h)⟩⟩
end

/-- Checkable local replacement obligations imply one-step contextual
preservation. The proof works for independent physical occurrences; it does
not infer copying/name-sharing compatibility from a logical port label. -/
theorem contextual_replacement_preserves
    (allow : LocalOccurrence sigma InstanceData → Prop)
    {G : Hypersequent sigma} (context : CKTree sigma InstanceData G)
    (before after : context.LeafAssignment)
    (localProof : ∀ hole, RulesAllowed allow (before hole) → RulesAllowed allow (after hole)) :
    RulesAllowed allow (context.fillAssignment before) →
      RulesAllowed allow (context.fillAssignment after) := by
  intro source
  obtain ⟨skeleton, payloads⟩ :=
    (rulesAllowed_fillAssignment allow context before).mp source
  exact (rulesAllowed_fillAssignment allow context after).mpr
    ⟨skeleton, fun hole => localProof hole (payloads hole)⟩

section GenuineContraction

open Potkin.Research.StructuralReduction

/-- Precisely the four fully instantiated Gentzen Cut occurrences whose
boundaries are certified by `StructuralReduction.exact_gentzen_instances`.
The exact occurrence, not its name/kind/Data tag, is the membership key. -/
def registeredCutInstances : List (LocalOccurrence StructuralReduction.sigma StructuralReduction.Data) :=
  [cutContractedOccurrence, cutRemainingOccurrence, cutDuplicatedOccurrence,
    cutIdentityOccurrence]

/-- Cut-formula restriction in this exact finite registry. Every registered
Gentzen Cut is at `a`; remaining admitted stock is unrestricted. Interpretation
as a calculus fragment requires native admission in `presentation`; arbitrary
foreign ambient occurrences are not claimed to be classified by this stock. -/
def CutFormulaAllowed (Allowed : Formula StructuralReduction.sigma → Prop)
    (occurrence : LocalOccurrence StructuralReduction.sigma StructuralReduction.Data) : Prop :=
  occurrence ∈ registeredCutInstances → Allowed a

private theorem cutFormulaAllowed_sourceCut (Allowed : Formula StructuralReduction.sigma → Prop) :
    CutFormulaAllowed Allowed cutContractedOccurrence ↔ Allowed a := by
  simp [CutFormulaAllowed, registeredCutInstances]

private theorem cutFormulaAllowed_innerCut (Allowed : Formula StructuralReduction.sigma → Prop) :
    CutFormulaAllowed Allowed cutRemainingOccurrence ↔ Allowed a := by
  simp [CutFormulaAllowed, registeredCutInstances]

private theorem cutFormulaAllowed_outerCut (Allowed : Formula StructuralReduction.sigma → Prop) :
    CutFormulaAllowed Allowed cutDuplicatedOccurrence ↔ Allowed a := by
  simp [CutFormulaAllowed, registeredCutInstances]

private theorem cutFormulaAllowed_identityCut (Allowed : Formula StructuralReduction.sigma → Prop) :
    CutFormulaAllowed Allowed cutIdentityOccurrence ↔ Allowed a := by
  simp [CutFormulaAllowed, registeredCutInstances]

private theorem cutFormulaAllowed_contractions (Allowed : Formula StructuralReduction.sigma → Prop) :
    CutFormulaAllowed Allowed contractAOccurrence ∧ CutFormulaAllowed Allowed contractDOccurrence := by
  constructor <;>
    simp [CutFormulaAllowed, registeredCutInstances, contractAOccurrence, contractDOccurrence,
      cutContractedOccurrence, cutRemainingOccurrence, cutDuplicatedOccurrence, cutIdentityOccurrence]

private theorem cutFormulaAllowed_identity (Allowed : Formula StructuralReduction.sigma → Prop) :
    CutFormulaAllowed Allowed identityOccurrence := by
  simp [CutFormulaAllowed, registeredCutInstances, identityOccurrence,
    cutContractedOccurrence, cutRemainingOccurrence, cutDuplicatedOccurrence, cutIdentityOccurrence]

/-- The exact source inventory, including its fixed Cut and contraction. -/
theorem contraction_source_inventory
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary) :
    exactRuleInventory (source P Q) =
      ↑([cutContractedOccurrence] ++ ruleList P ++ [contractAOccurrence] ++ ruleList Q) := by
  simp [exactRuleInventory, source, contractA, ruleList, childRuleList, List.append_assoc]
  exact List.Perm.refl _

/-- Exact multiplicity: P's inventory occurs twice, with distinct physical
positions in the native reduct, even though this summary forgets addresses. -/
theorem contraction_target_inventory
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary) :
    exactRuleInventory (target P Q) =
      ↑([contractDOccurrence, cutDuplicatedOccurrence] ++ ruleList P ++
        [cutRemainingOccurrence] ++ ruleList P ++ ruleList Q) := by
  simp [exactRuleInventory, target, contractD, outerCut, innerCut, ruleList,
    childRuleList, List.append_assoc]
  exact List.Perm.refl _

/-- Exact source formula for the independently declared Gentzen reduction. -/
theorem contraction_source_allowed_iff
    (allow : LocalOccurrence StructuralReduction.sigma StructuralReduction.Data → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary) :
    RulesAllowed allow (source P Q) ↔
      allow cutContractedOccurrence ∧ RulesAllowed allow P ∧
        allow contractAOccurrence ∧ RulesAllowed allow Q := by
  simp only [source, contractA, RulesAllowed, ChildRulesAllowed, and_true]
  exact Iff.rfl

/-- Exact nonlinear reduct formula. The two physical copies of P are checked
independently; this particular observer is idempotent under repeated permission
tests. That fact does NOT identify their native CK cut choices. -/
theorem contraction_target_allowed_iff
    (allow : LocalOccurrence StructuralReduction.sigma StructuralReduction.Data → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary) :
    RulesAllowed allow (target P Q) ↔
      allow contractDOccurrence ∧ allow cutDuplicatedOccurrence ∧
        RulesAllowed allow P ∧ allow cutRemainingOccurrence ∧ RulesAllowed allow Q := by
  simp only [target, contractD, outerCut, innerCut, RulesAllowed, ChildRulesAllowed, and_true]
  constructor
  · rintro ⟨allowedIC, allowedOuter, allowedP, allowedInner, _, allowedQ⟩
    exact ⟨allowedIC, allowedOuter, allowedP, allowedInner, allowedQ⟩
  · rintro ⟨allowedIC, allowedOuter, allowedP, allowedInner, allowedQ⟩
    exact ⟨allowedIC, allowedOuter, allowedP, allowedInner, allowedP, allowedQ⟩

/-- Schema-local, checkable guards imply preservation for arbitrary payloads.
These are exact occurrence conditions, not a premise asserting global context
compatibility. Admission is separately established by StructuralReduction. -/
theorem contraction_fragment_preserved
    (allow : LocalOccurrence StructuralReduction.sigma StructuralReduction.Data → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary)
    (newFixed : allow contractDOccurrence ∧ allow cutDuplicatedOccurrence ∧
      allow cutRemainingOccurrence) :
    RulesAllowed allow (source P Q) → RulesAllowed allow (target P Q) := by
  intro accepted
  obtain ⟨_, payloadP, _, payloadQ⟩ :=
    (contraction_source_allowed_iff allow P Q).mp accepted
  exact (contraction_target_allowed_iff allow P Q).mpr
    ⟨newFixed.1, newFixed.2.1, payloadP, newFixed.2.2, payloadQ⟩

/-- Exact finite schema obligations, with nonvacuity witnessed by the two
admitted ground payloads. This proves necessity as well as sufficiency for
one-step restricted-rule preservation; it is NOT a CK coideal criterion. -/
theorem contraction_uniform_fragment_iff
    (allow : LocalOccurrence StructuralReduction.sigma StructuralReduction.Data → Prop)
    (oldFixed : allow cutContractedOccurrence ∧ allow contractAOccurrence)
    (groundAllowed : RulesAllowed allow groundP ∧ RulesAllowed allow groundQ) :
    (∀ (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
       (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary),
       LocallyAdmittedTree presentation P → LocallyAdmittedTree presentation Q →
       RulesAllowed allow (source P Q) → RulesAllowed allow (target P Q)) ↔
      allow contractDOccurrence ∧ allow cutDuplicatedOccurrence ∧ allow cutRemainingOccurrence := by
  constructor
  · intro preserves
    have gp : LocallyAdmittedTree presentation groundP :=
      ⟨by simp [presentation], trivial⟩
    have gq : LocallyAdmittedTree presentation groundQ :=
      ⟨by simp [presentation], trivial⟩
    have sourceAllowed := (contraction_source_allowed_iff allow groundP groundQ).mpr
      ⟨oldFixed.1, groundAllowed.1, oldFixed.2, groundAllowed.2⟩
    obtain ⟨allowedIC, allowedOuter, _, allowedInner, _⟩ :=
      (contraction_target_allowed_iff allow groundP groundQ).mp
        (preserves groundP groundQ gp gq sourceAllowed)
    exact ⟨allowedIC, allowedOuter, allowedInner⟩
  · intro newFixed P Q _ _
    exact contraction_fragment_preserved allow P Q newFixed

/-- Even in the actual nonlinear logical reduction context, payloads with the
same full exact rule inventory cannot have different restricted-rule outcomes.
This is the requested universal failed-payoff test, not a finite search. -/
theorem contraction_no_inventory_separator
    (allow : LocalOccurrence StructuralReduction.sigma StructuralReduction.Data → Prop)
    (P R : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary)
    (same : exactRuleInventory P = exactRuleInventory R) :
    RulesAllowed allow (target P Q) ↔ RulesAllowed allow (target R Q) := by
  rw [contraction_target_allowed_iff, contraction_target_allowed_iff,
    no_same_inventory_separator allow P R same]

/-- Linear identity elimination only removes its two fixed rule occurrences.
It cannot introduce a forbidden rule in this independent fragment observer. -/
theorem linear_fragment_preserved
    (allow : LocalOccurrence StructuralReduction.sigma StructuralReduction.Data → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary) :
    RulesAllowed allow (linearSource P) → RulesAllowed allow P := by
  intro accepted
  exact accepted.2.1

/-- Independent Cut-formula observer: contraction reduction preserves exactly
the same condition, universally over arbitrary admitted payloads. -/
theorem contraction_source_cutFormula_iff
    (Allowed : Formula StructuralReduction.sigma → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary) :
    RulesAllowed (CutFormulaAllowed Allowed) (source P Q) ↔
      Allowed a ∧ RulesAllowed (CutFormulaAllowed Allowed) P ∧
        RulesAllowed (CutFormulaAllowed Allowed) Q := by
  rw [contraction_source_allowed_iff, cutFormulaAllowed_sourceCut]
  simp only [(cutFormulaAllowed_contractions Allowed).1, true_and]

theorem contraction_target_cutFormula_iff
    (Allowed : Formula StructuralReduction.sigma → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary) :
    RulesAllowed (CutFormulaAllowed Allowed) (target P Q) ↔
      Allowed a ∧ RulesAllowed (CutFormulaAllowed Allowed) P ∧
        RulesAllowed (CutFormulaAllowed Allowed) Q := by
  rw [contraction_target_allowed_iff, cutFormulaAllowed_outerCut,
    cutFormulaAllowed_innerCut]
  simp only [(cutFormulaAllowed_contractions Allowed).2, true_and]
  constructor
  · rintro ⟨allowedA, allowedP, _, allowedQ⟩
    exact ⟨allowedA, allowedP, allowedQ⟩
  · rintro ⟨allowedA, allowedP, allowedQ⟩
    exact ⟨allowedA, allowedP, allowedA, allowedQ⟩

theorem contraction_cutFormula_preserved
    (Allowed : Formula StructuralReduction.sigma → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary) :
    RulesAllowed (CutFormulaAllowed Allowed) (source P Q) ↔
      RulesAllowed (CutFormulaAllowed Allowed) (target P Q) := by
  rw [contraction_source_cutFormula_iff, contraction_target_cutFormula_iff]

/-- Explicit failed-payoff result for this narrow exact stock: all declared
Cut instances have the same formula `a`. Thus the actual source/reduct observer
collapses to permitting `a`; it cannot expose any richer CK application. -/
theorem contraction_cutFormula_scope_collapse
    (Allowed : Formula StructuralReduction.sigma → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
    (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary) :
    (RulesAllowed (CutFormulaAllowed Allowed) (source P Q) ↔ Allowed a) ∧
      (RulesAllowed (CutFormulaAllowed Allowed) (target P Q) ↔ Allowed a) := by
  have everyPayload {G : Hypersequent StructuralReduction.sigma}
      (tree : CKTree StructuralReduction.sigma StructuralReduction.Data G)
      (allowedA : Allowed a) : RulesAllowed (CutFormulaAllowed Allowed) tree :=
    (rulesAllowed_factorization (CutFormulaAllowed Allowed) tree).mpr
      (fun _ _ _ => allowedA)
  constructor
  · rw [contraction_source_cutFormula_iff]
    exact ⟨fun accepted => accepted.1,
      fun allowedA => ⟨allowedA, everyPayload P allowedA, everyPayload Q allowedA⟩⟩
  · rw [contraction_target_cutFormula_iff]
    exact ⟨fun accepted => accepted.1,
      fun allowedA => ⟨allowedA, everyPayload P allowedA, everyPayload Q allowedA⟩⟩

theorem linear_source_cutFormula_iff
    (Allowed : Formula StructuralReduction.sigma → Prop)
    (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary) :
    RulesAllowed (CutFormulaAllowed Allowed) (linearSource P) ↔
      Allowed a ∧ RulesAllowed (CutFormulaAllowed Allowed) P := by
  simp only [linearSource, identityTree, RulesAllowed, ChildRulesAllowed, and_true]
  rw [cutFormulaAllowed_identityCut]
  simp only [cutFormulaAllowed_identity Allowed, and_true]
  exact Iff.rfl

/-- One-step propagation of the actual nonlinear schema through arbitrary
native typed all-hole contexts. In each physical hole the independent guard
equivalence comes from the concrete logical reduction, not a global assumption.
Local admission of the context and both fillings remains a separate judgment. -/
theorem contraction_cutFormula_contextual
    (Allowed : Formula StructuralReduction.sigma → Prop)
    {G : Hypersequent StructuralReduction.sigma}
    (context : CKTree StructuralReduction.sigma StructuralReduction.Data G)
    (before after : context.LeafAssignment)
    (steps : ∀ hole, before hole = after hole ∨
      ∃ (boundary : resultBoundary = context.leafBoundary hole)
        (P : CKTree StructuralReduction.sigma StructuralReduction.Data PBoundary)
        (Q : CKTree StructuralReduction.sigma StructuralReduction.Data QBoundary),
        before hole = (boundary ▸ source P Q) ∧
          after hole = (boundary ▸ target P Q)) :
    RulesAllowed (CutFormulaAllowed Allowed) (context.fillAssignment before) →
      RulesAllowed (CutFormulaAllowed Allowed) (context.fillAssignment after) := by
  apply contextual_replacement_preserves
  intro hole accepted
  rcases steps hole with unchanged | ⟨boundary, P, Q, hbefore, hafter⟩
  · simpa [← unchanged] using accepted
  · rw [hbefore] at accepted
    rw [hafter]
    exact (rulesAllowed_transport (CutFormulaAllowed Allowed) boundary (target P Q)).mpr
      ((contraction_cutFormula_preserved Allowed P Q).mp
        ((rulesAllowed_transport (CutFormulaAllowed Allowed) boundary (source P Q)).mp accepted))

end GenuineContraction

end Potkin.Research.StructuralObservation

#print axioms Potkin.Research.StructuralObservation.rulesAllowed_factorization
#print axioms Potkin.Research.StructuralObservation.no_same_inventory_separator
#print axioms Potkin.Research.StructuralObservation.rulesAllowed_fillAssignment
#print axioms Potkin.Research.StructuralObservation.contextual_replacement_preserves
#print axioms Potkin.Research.StructuralObservation.contraction_target_allowed_iff
#print axioms Potkin.Research.StructuralObservation.contraction_fragment_preserved
#print axioms Potkin.Research.StructuralObservation.contraction_uniform_fragment_iff
#print axioms Potkin.Research.StructuralObservation.contraction_no_inventory_separator
#print axioms Potkin.Research.StructuralObservation.linear_fragment_preserved
#print axioms Potkin.Research.StructuralObservation.contraction_source_inventory
#print axioms Potkin.Research.StructuralObservation.contraction_target_inventory
#print axioms Potkin.Research.StructuralObservation.contraction_source_cutFormula_iff
#print axioms Potkin.Research.StructuralObservation.contraction_target_cutFormula_iff
#print axioms Potkin.Research.StructuralObservation.contraction_cutFormula_preserved
#print axioms Potkin.Research.StructuralObservation.contraction_cutFormula_scope_collapse
#print axioms Potkin.Research.StructuralObservation.linear_source_cutFormula_iff
#print axioms Potkin.Research.StructuralObservation.contraction_cutFormula_contextual

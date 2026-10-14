import Potkin.GeneralFilling
import Potkin.Examples.Anonymous

/-!
# Exact Gentzen Cut/contraction reduction on the native carrier

The atomic fragment below is deliberately exact, not an implementation of all
LJ/LK. Write `d,a,c` for three distinct atoms. The independently specified step
is

    Cut(P : d => a, IC_a(Q : a,a => c))
      --> IC_d(Cut(P, Cut(P,Q))) : d => c.

The inner Cut concludes d,a => c; the next concludes d,d => c. Thus the last
contraction is a genuine antecedent contraction of the copied d-assumption.
Premises are ordered. The two copies of P occupy distinct physical addresses;
equal native payload values are not a shared proof vertex. The linear control
is the standard identity step Cut(P, Id_a) --> P.

These are standard sequent reductions by derivation substitution: replace the
two distinguished a-assumptions of Q by two uses of P, then contract the two
copies of the singleton context {d}. No semantic claim follows from component
incidence: every boundary here has one component, so incidence records only
the contribution of each ordered premise to that component. Formula routing
is specified separately by the exact rule shapes and the reduction schema.

The material provider stock is an explicit axiomatic/module stock. Its unary
and binary operations supply arbitrary-depth P payloads, not logical
contraction. All contractions below are unary and have the genuine distinct
premise/conclusion antecedent multiplicities.
-/

namespace Potkin.Research.StructuralReduction

abbrev sigma := Examples.Anonymous.signature
abbrev d : Formula sigma := Examples.Anonymous.formulaS
abbrev a : Formula sigma := Examples.Anonymous.formulaT
abbrev c : Formula sigma := Examples.Anonymous.formulaU

inductive Data where
  | groundP | groundQ | payloadUnaryP | payloadBinaryP | identity
  | cutContracted | cutRemaining | cutDuplicated | cutIdentity
  | contractA | contractD
deriving DecidableEq, Repr

def pSequent : Sequent sigma := ⟨{d}, {a}⟩
def qSequent : Sequent sigma := ⟨{a,a}, {c}⟩
def contractedQSequent : Sequent sigma := ⟨{a}, {c}⟩
def middleSequent : Sequent sigma := ⟨{d,a}, {c}⟩
def duplicatedSequent : Sequent sigma := ⟨{d,d}, {c}⟩
def resultSequent : Sequent sigma := ⟨{d}, {c}⟩
def identitySequent : Sequent sigma := ⟨{a}, {a}⟩

def PBoundary : Hypersequent sigma := .singleton pSequent
def QBoundary : Hypersequent sigma := .singleton qSequent
def contractedQBoundary : Hypersequent sigma := .singleton contractedQSequent
def middleBoundary : Hypersequent sigma := .singleton middleSequent
def duplicatedBoundary : Hypersequent sigma := .singleton duplicatedSequent
def resultBoundary : Hypersequent sigma := .singleton resultSequent
def identityBoundary : Hypersequent sigma := .singleton identitySequent

private def singletonProfile (s : Sequent sigma) :
    ComponentProfile (.singleton s) := ⟨[s], rfl⟩

def nullaryShape (out : Sequent sigma) : OccurrenceShape sigma :=
  ⟨[], .singleton out⟩
def unaryShape (input out : Sequent sigma) : OccurrenceShape sigma :=
  ⟨[.singleton input], .singleton out⟩
def binaryShape (left right out : Sequent sigma) : OccurrenceShape sigma :=
  ⟨[.singleton left, .singleton right], .singleton out⟩

private def nullaryIncidence (out : Sequent sigma) :
    ComponentIncidence (nullaryShape out) where
  profiles := { premise := fun i => Fin.elim0 i
                conclusion := singletonProfile out }
  edges := ∅

private def unaryProfiles (input out : Sequent sigma) :
    OccurrenceProfiles (unaryShape input out) where
  premise := fun i => Fin.cases (singletonProfile input) (fun j => Fin.elim0 j) i
  conclusion := singletonProfile out

private def unaryIncidence (input out : Sequent sigma) :
    ComponentIncidence (unaryShape input out) where
  profiles := unaryProfiles input out
  edges := {⟨⟨0, by change 0 < 1; decide⟩,
    ⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩⟩}

private def binaryProfiles (left right out : Sequent sigma) :
    OccurrenceProfiles (binaryShape left right out) where
  premise := fun i => Fin.cases (singletonProfile left)
    (fun j => Fin.cases (singletonProfile right) (fun k => Fin.elim0 k) j) i
  conclusion := singletonProfile out

private def binaryIncidence (left right out : Sequent sigma) :
    ComponentIncidence (binaryShape left right out) where
  profiles := binaryProfiles left right out
  edges := {⟨⟨0, by change 0 < 2; decide⟩,
    ⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩⟩,
    ⟨⟨1, by change 1 < 2; decide⟩,
      ⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩⟩}

def groundPOccurrence : LocalOccurrence sigma Data :=
  ⟨200, .material, nullaryShape pSequent, .groundP,
    some (nullaryIncidence pSequent)⟩
def groundQOccurrence : LocalOccurrence sigma Data :=
  ⟨201, .material, nullaryShape qSequent, .groundQ,
    some (nullaryIncidence qSequent)⟩
def payloadUnaryPOccurrence : LocalOccurrence sigma Data :=
  ⟨202, .material, unaryShape pSequent pSequent, .payloadUnaryP,
    some (unaryIncidence pSequent pSequent)⟩
def payloadBinaryPOccurrence : LocalOccurrence sigma Data :=
  ⟨203, .material, binaryShape pSequent pSequent pSequent, .payloadBinaryP,
    some (binaryIncidence pSequent pSequent pSequent)⟩
def identityOccurrence : LocalOccurrence sigma Data :=
  ⟨204, .logical, nullaryShape identitySequent, .identity,
    some (nullaryIncidence identitySequent)⟩
def cutContractedOccurrence : LocalOccurrence sigma Data :=
  ⟨205, .logical, binaryShape pSequent contractedQSequent resultSequent,
    .cutContracted, some (binaryIncidence pSequent contractedQSequent resultSequent)⟩
def cutRemainingOccurrence : LocalOccurrence sigma Data :=
  ⟨206, .logical, binaryShape pSequent qSequent middleSequent,
    .cutRemaining, some (binaryIncidence pSequent qSequent middleSequent)⟩
def cutDuplicatedOccurrence : LocalOccurrence sigma Data :=
  ⟨207, .logical, binaryShape pSequent middleSequent duplicatedSequent,
    .cutDuplicated, some (binaryIncidence pSequent middleSequent duplicatedSequent)⟩
def cutIdentityOccurrence : LocalOccurrence sigma Data :=
  ⟨208, .logical, binaryShape pSequent identitySequent pSequent,
    .cutIdentity, some (binaryIncidence pSequent identitySequent pSequent)⟩
def contractAOccurrence : LocalOccurrence sigma Data :=
  ⟨209, .structural, unaryShape qSequent contractedQSequent, .contractA,
    some (unaryIncidence qSequent contractedQSequent)⟩
def contractDOccurrence : LocalOccurrence sigma Data :=
  ⟨210, .structural, unaryShape duplicatedSequent resultSequent, .contractD,
    some (unaryIncidence duplicatedSequent resultSequent)⟩

/-- Standard single-succedent Gentzen Cut boundary, independent of CK. -/
def gentzenShape (Delta Gamma : Context sigma) (A C : Formula sigma) :
    OccurrenceShape sigma :=
  ⟨[.singleton ⟨Delta, {A}⟩, .singleton ⟨Gamma + {A}, {C}⟩],
    .singleton ⟨Delta + Gamma, {C}⟩⟩

/-- Standard internal antecedent contraction boundary, independent of CK. -/
def contractionShape (Gamma : Context sigma) (A C : Formula sigma) :
    OccurrenceShape sigma :=
  ⟨[.singleton ⟨Gamma + {A,A}, {C}⟩], .singleton ⟨Gamma + {A}, {C}⟩⟩

theorem atoms_distinct : d ≠ a ∧ d ≠ c ∧ a ≠ c := by decide

/-- Exact instances, not a kind/name test. The second Cut uses multiset
exchange to designate the remaining a-assumption next to d. -/
theorem exact_gentzen_instances :
    cutContractedOccurrence.shape = gentzenShape {d} 0 a c ∧
    cutRemainingOccurrence.shape = gentzenShape {d} {a} a c ∧
    cutDuplicatedOccurrence.shape = gentzenShape {d} {d} a c ∧
    cutIdentityOccurrence.shape = gentzenShape {d} 0 a a := by
  simp [cutContractedOccurrence, cutRemainingOccurrence, cutDuplicatedOccurrence,
    cutIdentityOccurrence, binaryShape, gentzenShape, pSequent,
    contractedQSequent, qSequent, middleSequent, duplicatedSequent,
    resultSequent, identitySequent, Multiset.singleton_add]

theorem exact_contraction_instances :
    contractAOccurrence.shape = contractionShape 0 a c ∧
    contractDOccurrence.shape = contractionShape 0 d c := by
  simp [contractAOccurrence, contractDOccurrence, unaryShape, contractionShape,
    qSequent, contractedQSequent, duplicatedSequent, resultSequent]

theorem supplied_component_incidence :
    (binaryIncidence pSequent qSequent middleSequent).edges.card = 2 ∧
    (unaryIncidence qSequent contractedQSequent).edges.card = 1 ∧
    cutRemainingOccurrence.incidence =
      some (binaryIncidence pSequent qSequent middleSequent) ∧
    contractAOccurrence.incidence = some (unaryIncidence qSequent contractedQSequent) := by
  exact ⟨by decide, by decide, rfl, rfl⟩

inductive MaterialMember : LocalOccurrence sigma Data → Prop where
  | groundP : MaterialMember groundPOccurrence
  | groundQ : MaterialMember groundQOccurrence
  | unaryP : MaterialMember payloadUnaryPOccurrence
  | binaryP : MaterialMember payloadBinaryPOccurrence

private theorem atomic_formula (f : Formula sigma) :
    PrimitiveFragment.atoms.primitive f := by
  cases f with
  | atom _ => trivial
  | app op _ => nomatch op

private theorem atomic_boundary (G : Hypersequent sigma) :
    PrimitiveFragment.atoms.SupportsHypersequent G := by
  intro S _
  exact ⟨fun f _ => atomic_formula f, fun f _ => atomic_formula f⟩

def base : MaterialBase sigma Data PrimitiveFragment.atoms where
  Member := MaterialMember
  member_material := by intro o h; cases h <;> rfl
  member_primitiveBoundary := fun {o} _ =>
    ⟨fun i => atomic_boundary (o.shape.premises.get i), atomic_boundary _⟩

def logicalStock : List (LocalOccurrence sigma Data) :=
  [identityOccurrence, cutContractedOccurrence, cutRemainingOccurrence,
    cutDuplicatedOccurrence, cutIdentityOccurrence]
def structuralStock : List (LocalOccurrence sigma Data) :=
  [contractAOccurrence, contractDOccurrence]

def theory : ProofTheory sigma Data where
  primitive := .atoms
  base := base
  rules := { logical := fun o => o ∈ logicalStock
             structural := fun o => o ∈ structuralStock }
  initial := fun _ => False

def presentation : EquippedPresentation theory where
  registry := [groundPOccurrence, groundQOccurrence, payloadUnaryPOccurrence,
    payloadBinaryPOccurrence, identityOccurrence, cutContractedOccurrence,
    cutRemainingOccurrence, cutDuplicatedOccurrence, cutIdentityOccurrence,
    contractAOccurrence, contractDOccurrence]
  uniqueIds := by decide
  admitted := by
    intro o h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .material .groundP
    · exact .material .groundQ
    · exact .material .unaryP
    · exact .material .binaryP
    · exact .logical rfl (by simp [theory, logicalStock])
    · exact .logical rfl (by simp [theory, logicalStock])
    · exact .logical rfl (by simp [theory, logicalStock])
    · exact .logical rfl (by simp [theory, logicalStock])
    · exact .logical rfl (by simp [theory, logicalStock])
    · exact .structural rfl (by simp [theory, structuralStock])
    · exact .structural rfl (by simp [theory, structuralStock])

def groundP : CKTree sigma Data PBoundary := .ordinary groundPOccurrence .nil
def groundQ : CKTree sigma Data QBoundary := .ordinary groundQOccurrence .nil
def payloadUnaryP (P : CKTree sigma Data PBoundary) : CKTree sigma Data PBoundary :=
  .ordinary payloadUnaryPOccurrence (.cons P .nil)
def payloadBinaryP (P R : CKTree sigma Data PBoundary) : CKTree sigma Data PBoundary :=
  .ordinary payloadBinaryPOccurrence (.cons P (.cons R .nil))
def identityTree : CKTree sigma Data identityBoundary := .ordinary identityOccurrence .nil
def contractA (Q : CKTree sigma Data QBoundary) : CKTree sigma Data contractedQBoundary :=
  .ordinary contractAOccurrence (.cons Q .nil)
def innerCut (P : CKTree sigma Data PBoundary) (Q : CKTree sigma Data QBoundary) :
    CKTree sigma Data middleBoundary :=
  .ordinary cutRemainingOccurrence (.cons P (.cons Q .nil))
def outerCut (P : CKTree sigma Data PBoundary) (R : CKTree sigma Data middleBoundary) :
    CKTree sigma Data duplicatedBoundary :=
  .ordinary cutDuplicatedOccurrence (.cons P (.cons R .nil))
def contractD (R : CKTree sigma Data duplicatedBoundary) : CKTree sigma Data resultBoundary :=
  .ordinary contractDOccurrence (.cons R .nil)
def source (P : CKTree sigma Data PBoundary) (Q : CKTree sigma Data QBoundary) :
    CKTree sigma Data resultBoundary :=
  .ordinary cutContractedOccurrence (.cons P (.cons (contractA Q) .nil))
def target (P : CKTree sigma Data PBoundary) (Q : CKTree sigma Data QBoundary) :
    CKTree sigma Data resultBoundary := contractD (outerCut P (innerCut P Q))
def linearSource (P : CKTree sigma Data PBoundary) : CKTree sigma Data PBoundary :=
  .ordinary cutIdentityOccurrence (.cons P (.cons identityTree .nil))

/-- This independently specified local logical step does not inspect CK cuts
or material sums. It is not a critical pair or a quotient/comodule law. -/
inductive Reduction : {G : Hypersequent sigma} →
    CKTree sigma Data G → CKTree sigma Data G → Prop where
  | contraction (P : CKTree sigma Data PBoundary) (Q : CKTree sigma Data QBoundary) :
      Reduction (source P Q) (target P Q)
  | identity (P : CKTree sigma Data PBoundary) : Reduction (linearSource P) P

theorem source_admitted {P : CKTree sigma Data PBoundary}
    {Q : CKTree sigma Data QBoundary}
    (hp : LocallyAdmittedTree presentation P) (hq : LocallyAdmittedTree presentation Q) :
    LocallyAdmittedTree presentation (source P Q) := by
  exact ⟨by simp [presentation], hp,
    ⟨by simp [presentation], hq, trivial⟩, trivial⟩

theorem target_admitted {P : CKTree sigma Data PBoundary}
    {Q : CKTree sigma Data QBoundary}
    (hp : LocallyAdmittedTree presentation P) (hq : LocallyAdmittedTree presentation Q) :
    LocallyAdmittedTree presentation (target P Q) := by
  exact ⟨by simp [presentation],
    ⟨by simp [presentation], hp,
      ⟨by simp [presentation], hp, hq, trivial⟩, trivial⟩, trivial⟩

theorem linearSource_admitted {P : CKTree sigma Data PBoundary}
    (hp : LocallyAdmittedTree presentation P) :
    LocallyAdmittedTree presentation (linearSource P) := by
  exact ⟨by simp [presentation], hp, ⟨by simp [presentation], trivial⟩, trivial⟩

theorem source_complete {P : CKTree sigma Data PBoundary}
    {Q : CKTree sigma Data QBoundary} (hp : P.IsComplete) (hq : Q.IsComplete) :
    (source P Q).IsComplete := ⟨hp, ⟨hq, trivial⟩, trivial⟩

theorem target_complete {P : CKTree sigma Data PBoundary}
    {Q : CKTree sigma Data QBoundary} (hp : P.IsComplete) (hq : Q.IsComplete) :
    (target P Q).IsComplete := ⟨⟨hp, ⟨hp, hq, trivial⟩, trivial⟩, trivial⟩

theorem linearSource_complete {P : CKTree sigma Data PBoundary} (hp : P.IsComplete) :
    (linearSource P).IsComplete := ⟨hp, trivial, trivial⟩

/-- Universal admitted elaboration for arbitrary native payloads, not a
finite-tree test. Completeness can be supplied separately via the theorems above. -/
theorem admitted_contraction_reduction
    {P : CKTree sigma Data PBoundary} {Q : CKTree sigma Data QBoundary}
    (hp : LocallyAdmittedTree presentation P) (hq : LocallyAdmittedTree presentation Q) :
    LocallyAdmittedTree presentation (source P Q) ∧
    LocallyAdmittedTree presentation (target P Q) ∧ Reduction (source P Q) (target P Q) :=
  ⟨source_admitted hp hq, target_admitted hp hq, .contraction P Q⟩

/-- Integration for arbitrary existing native checked proofs in this exact
immutable registry. Nothing privately constructs a checked node: their
realizations supply admission and completeness through the existing API. -/
theorem checked_payload_contraction_reduction
    (P : CheckedDerivation presentation PBoundary)
    (Q : CheckedDerivation presentation QBoundary) :
    LocallyAdmittedTree presentation (source P.realize Q.realize) ∧
    LocallyAdmittedTree presentation (target P.realize Q.realize) ∧
    (source P.realize Q.realize).IsComplete ∧
    (target P.realize Q.realize).IsComplete ∧
    Reduction (source P.realize Q.realize) (target P.realize Q.realize) :=
  ⟨source_admitted P.realizeLocallyAdmitted Q.realizeLocallyAdmitted,
    target_admitted P.realizeLocallyAdmitted Q.realizeLocallyAdmitted,
    source_complete P.realizeIsComplete Q.realizeIsComplete,
    target_complete P.realizeIsComplete Q.realizeIsComplete,
    .contraction P.realize Q.realize⟩

theorem checked_payload_linear_reduction
    (P : CheckedDerivation presentation PBoundary) :
    LocallyAdmittedTree presentation (linearSource P.realize) ∧
    (linearSource P.realize).IsComplete ∧ Reduction (linearSource P.realize) P.realize :=
  ⟨linearSource_admitted P.realizeLocallyAdmitted,
    linearSource_complete P.realizeIsComplete, .identity P.realize⟩

def rawP : RawDerivation sigma := .node groundPOccurrence.id .nil
def rawQ : RawDerivation sigma := .node groundQOccurrence.id .nil
def rawSource : RawDerivation sigma :=
  .node cutContractedOccurrence.id (.cons rawP (.cons
    (.node contractAOccurrence.id (.cons rawQ .nil)) .nil))
def rawTarget : RawDerivation sigma :=
  .node contractDOccurrence.id (.cons
    (.node cutDuplicatedOccurrence.id (.cons rawP (.cons
      (.node cutRemainingOccurrence.id (.cons rawP (.cons rawQ .nil))) .nil))) .nil)
def rawLinearSource : RawDerivation sigma :=
  .node cutIdentityOccurrence.id (.cons rawP (.cons (.node identityOccurrence.id .nil) .nil))

theorem rawSource_succeeds :
    CheckResult.Succeeded (presentation.checkAt resultBoundary rawSource) := by decide
theorem rawTarget_succeeds :
    CheckResult.Succeeded (presentation.checkAt resultBoundary rawTarget) := by decide
theorem rawLinearSource_succeeds :
    CheckResult.Succeeded (presentation.checkAt PBoundary rawLinearSource) := by decide
theorem rawP_succeeds :
    CheckResult.Succeeded (presentation.checkAt PBoundary rawP) := by decide

def checkedSource : CheckedDerivation presentation resultBoundary :=
  CheckResult.get rawSource_succeeds
def checkedTarget : CheckedDerivation presentation resultBoundary :=
  CheckResult.get rawTarget_succeeds
def checkedLinearSource : CheckedDerivation presentation PBoundary :=
  CheckResult.get rawLinearSource_succeeds
def checkedP : CheckedDerivation presentation PBoundary := CheckResult.get rawP_succeeds

theorem checkedSource_literal : checkedSource.realize = source groundP groundQ := rfl
theorem checkedTarget_literal : checkedTarget.realize = target groundP groundQ := rfl
theorem checkedLinearSource_literal : checkedLinearSource.realize = linearSource groundP := rfl
theorem checkedP_literal : checkedP.realize = groundP := rfl

theorem checked_contraction_reduction : Reduction checkedSource.realize checkedTarget.realize :=
  .contraction groundP groundQ
theorem checked_linear_reduction : Reduction checkedLinearSource.realize checkedP.realize :=
  .identity groundP

end Potkin.Research.StructuralReduction

#print axioms Potkin.Research.StructuralReduction.exact_gentzen_instances
#print axioms Potkin.Research.StructuralReduction.exact_contraction_instances
#print axioms Potkin.Research.StructuralReduction.admitted_contraction_reduction
#print axioms Potkin.Research.StructuralReduction.checked_payload_contraction_reduction
#print axioms Potkin.Research.StructuralReduction.checked_payload_linear_reduction
#print axioms Potkin.Research.StructuralReduction.checked_contraction_reduction
#print axioms Potkin.Research.StructuralReduction.checked_linear_reduction

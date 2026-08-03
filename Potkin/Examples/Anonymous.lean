import Mathlib.Data.Finset.Card
import Potkin.RootProjection

/-!
# Tiny anonymous vertical-slice fixture

The nullary, unary, and binary rules below test only the generic machinery.
They are not a featured calculus and carry no paper-specific logic.
-/

namespace Potkin.Examples.Anonymous

inductive Atom where
  | s
  | t
  | u
deriving DecidableEq, Repr

inductive InstanceData where
  | baseS
  | baseT
  | merge
  | lift
deriving DecidableEq, Repr

def signature : Signature where
  Atom := Atom
  Op := fun _ => Empty

instance : DecidableEq (Formula signature)
  | .atom a, .atom b =>
      if h : (show Atom from a) = (show Atom from b) then
        isTrue (by cases h; rfl)
      else
        isFalse (by intro hab; cases hab; exact h rfl)
  | .atom _, .app op _ => nomatch op
  | .app op _, _ => nomatch op

def formulaS : Formula signature := .atom .s
def formulaT : Formula signature := .atom .t
def formulaU : Formula signature := .atom .u

def S : Sequent signature := ⟨0, {formulaS}⟩
def T : Sequent signature := ⟨0, {formulaT}⟩
def U : Sequent signature := ⟨0, {formulaU}⟩

def GS : Hypersequent signature := .singleton S
def GT : Hypersequent signature := .singleton T
def GST : Hypersequent signature := .pair S T
def GU : Hypersequent signature := .singleton U

def baseSShape : OccurrenceShape signature := ⟨[], GS⟩
def baseTShape : OccurrenceShape signature := ⟨[], GT⟩
def mergeShape : OccurrenceShape signature := ⟨[GS, GT], GST⟩
def liftShape : OccurrenceShape signature := ⟨[GST], GU⟩

def singletonProfile (X : Sequent signature) :
    ComponentProfile (Hypersequent.singleton X) where
  displayed := [X]
  exact := rfl

def pairProfile (X Y : Sequent signature) :
    ComponentProfile (Hypersequent.pair X Y) where
  displayed := [X, Y]
  exact := rfl

def baseSKnownEmptyIncidence : ComponentIncidence baseSShape where
  profiles := {
    premise := fun i => Fin.elim0 i
    conclusion := singletonProfile S }
  edges := ∅

def baseSOccurrence : LocalOccurrence signature InstanceData where
  id := 10
  kind := .material
  shape := baseSShape
  instanceData := .baseS
  incidence := some baseSKnownEmptyIncidence

def baseTOccurrence : LocalOccurrence signature InstanceData where
  id := 11
  kind := .material
  shape := baseTShape
  instanceData := .baseT
  incidence := none

def mergeOccurrence : LocalOccurrence signature InstanceData where
  id := 20
  kind := .logical
  shape := mergeShape
  instanceData := .merge
  incidence := none

def liftOccurrence : LocalOccurrence signature InstanceData where
  id := 30
  kind := .structural
  shape := liftShape
  instanceData := .lift
  incidence := none

theorem unknown_incidence_ne_known_empty :
    (none : Option (ComponentIncidence baseSShape)) ≠
      some baseSKnownEmptyIncidence := by simp

inductive MaterialEvidence : Hypersequent signature -> Type where
  | s : MaterialEvidence GS
  | t : MaterialEvidence GT

def materialBase : MaterialBase signature where
  Evidence := MaterialEvidence

def rules : RuleSystem signature InstanceData where
  logical := fun o => o.id = 20
  structural := fun o => o.id = 30

def theory : ProofTheory signature InstanceData where
  base := materialBase
  rules := rules
  initial := fun _ => False

def admitsBaseS : theory.Admits baseSOccurrence :=
  .material rfl rfl ⟨.s⟩

def admitsBaseT : theory.Admits baseTOccurrence :=
  .material rfl rfl ⟨.t⟩

def admitsMerge : theory.Admits mergeOccurrence :=
  .logical rfl rfl

def admitsLift : theory.Admits liftOccurrence :=
  .structural rfl rfl

def presentation : EquippedPresentation theory where
  registry := [baseSOccurrence, baseTOccurrence, mergeOccurrence, liftOccurrence]
  uniqueIds := by decide
  admitted := by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact admitsBaseS
    · exact admitsBaseT
    · exact admitsMerge
    · exact admitsLift

def rawS : RawDerivation signature := .node 10 .nil
def rawT : RawDerivation signature := .node 11 .nil
def rawBinary : RawDerivation signature :=
  .node 20 (.cons rawS (.cons rawT .nil))
def rawUnary : RawDerivation signature :=
  .node 30 (.cons rawBinary .nil)

theorem rawS_succeeds : CheckResult.Succeeded (presentation.checkAt GS rawS) := by
  decide

def checkedS : CheckedDerivation presentation GS :=
  CheckResult.get rawS_succeeds

theorem rawT_succeeds : CheckResult.Succeeded (presentation.checkAt GT rawT) := by
  decide

def checkedT : CheckedDerivation presentation GT :=
  CheckResult.get rawT_succeeds

theorem rawBinary_succeeds :
    CheckResult.Succeeded (presentation.checkAt GST rawBinary) := by
  decide

def checkedBinary : CheckedDerivation presentation GST :=
  CheckResult.get rawBinary_succeeds

theorem rawUnary_succeeds :
    CheckResult.Succeeded (presentation.checkAt GU rawUnary) := by
  decide

def checkedUnary : CheckedDerivation presentation GU :=
  CheckResult.get rawUnary_succeeds

/-- The executable checker validates the anonymous binary candidate exactly. -/
theorem rawBinary_checks :
    presentation.checkAt GST rawBinary = .ok checkedBinary :=
  CheckResult.eq_ok_get rawBinary_succeeds

/-- The same registry also validates the unary wrapper. -/
theorem rawUnary_checks :
    presentation.checkAt GU rawUnary = .ok checkedUnary :=
  CheckResult.eq_ok_get rawUnary_succeeds

theorem checkedBinary_boundary_correct :
    checkedBinary.rootOccurrence.shape.conclusion = GST :=
  checkedBinary.boundaryCorrect

def binaryChildren : CKChildren signature InstanceData [GS, GT] :=
  .cons checkedS.realize (.cons checkedT.realize .nil)

def binaryConstruction : RootConstruction signature InstanceData where
  occurrence := mergeOccurrence
  children := binaryChildren

theorem realized_binary_is_binaryConstruction :
    checkedBinary.realize = binaryConstruction.tree := rfl

def binaryCut : RootCut binaryConstruction where
  sites := {⟨0, by decide⟩, ⟨1, by decide⟩}
  nonempty := by simp
  selectedOrdinary := by
    intro i _
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) j) i
    · simpa [binaryConstruction, binaryChildren, RootConstruction.child, CKChildren.get]
        using checkedS.realize_isOrdinary
    · simpa [binaryConstruction, binaryChildren, RootConstruction.child, CKChildren.get]
        using checkedT.realize_isOrdinary

def site0 : binaryCut.Site := ⟨⟨0, by decide⟩, by simp [binaryCut]⟩
def site1 : binaryCut.Site := ⟨⟨1, by decide⟩, by simp [binaryCut]⟩

theorem binaryCut_has_two_sites : binaryCut.sites.card = 2 := by
  simp [binaryCut]

theorem binaryCut_addresses_exist :
    (binaryConstruction.tree).VertexAt (binaryCut.address site0) ∧
      (binaryConstruction.tree).VertexAt (binaryCut.address site1) :=
  ⟨binaryCut.address_exists site0, binaryCut.address_exists site1⟩

theorem binaryCut_addresses_nonroot :
    binaryCut.address site0 ≠ [] ∧ binaryCut.address site1 ≠ [] :=
  ⟨binaryCut.address_nonroot site0, binaryCut.address_nonroot site1⟩

theorem site0_ne_site1 : site0 ≠ site1 := by
  intro h
  have := congrArg (fun q : binaryCut.Site => q.1.1) h
  simp [site0, site1] at this

theorem binaryCut_addresses_prefixFree :
    PrefixIncomparable (binaryCut.address site0) (binaryCut.address site1) :=
  binaryCut.addresses_prefixFree site0_ne_site1

theorem binaryCut_punctures_are_exact :
    (binaryCut.retainedChild site0.1 = .interface (binaryCut.requirement site0) ∧
      binaryCut.detached site0 = binaryConstruction.child site0.1) ∧
    (binaryCut.retainedChild site1.1 = .interface (binaryCut.requirement site1) ∧
      binaryCut.detached site1 = binaryConstruction.child site1.1) :=
  ⟨binaryCut.puncture_matches_detached site0,
    binaryCut.puncture_matches_detached site1⟩

theorem binaryCut_reconstructs :
    binaryCut.fill binaryCut.detached = binaryConstruction.tree :=
  binaryCut.fill_detached_reconstructs

inductive ExtendedEvidence : Hypersequent signature -> Type where
  | old {G} : MaterialEvidence G -> ExtendedEvidence G
  | extra : ExtendedEvidence GU

def extendedBase : MaterialBase signature where
  Evidence := ExtendedEvidence

def baseInclusion : BaseHom materialBase extendedBase where
  mapEvidence := ExtendedEvidence.old

def mappedCheckedBinary :
    CheckedDerivation (presentation.mapBase baseInclusion) GST :=
  checkedBinary.mapBase baseInclusion

theorem realization_commutes_with_base_map :
    mappedCheckedBinary.realize = checkedBinary.realize := by
  simp [mappedCheckedBinary]

theorem erasure_commutes_with_base_map :
    CKTree.erase mappedCheckedBinary.realize =
      CKTree.erase checkedBinary.realize := by
  simp [mappedCheckedBinary]

def connectedComponent : CKComponent signature InstanceData where
  boundary := GST
  tree := checkedBinary.realize
  ordinary := checkedBinary.realize_isOrdinary

def leftComponent : CKComponent signature InstanceData where
  boundary := GS
  tree := checkedS.realize
  ordinary := checkedS.realize_isOrdinary

def rightComponent : CKComponent signature InstanceData where
  boundary := GT
  tree := checkedT.realize
  ordinary := checkedT.realize_isOrdinary

theorem connected_vs_separate_root_projections :
    CKForest.flattenedRoots ({connectedComponent} : CKForest signature InstanceData) =
        CKForest.flattenedRoots ({leftComponent} + {rightComponent}) ∧
      CKForest.blockRoots ({connectedComponent} : CKForest signature InstanceData) ≠
        CKForest.blockRoots ({leftComponent} + {rightComponent}) :=
  CKForest.connected_pair_root_projection_distinction
    S T connectedComponent leftComponent rightComponent rfl rfl rfl

end Potkin.Examples.Anonymous

import Potkin.Research.HLJContraction
import Potkin.Research.StructuralLemmaCuts
import Potkin.Research.ContractionCompilerCuts

/-!
# Admitted Communication, structural compilation, and a native lemma frontier

This joins the strict reached-instance theorem to checked simultaneous filling
and the physical CK frontier. The concrete three-entry presentation below is
an actual admitted Communication proof, universally parameterized by A and B.
It is not evidence for the unimplemented finite allocation of every optimized
compiler output. All public results keep that registration obligation explicit.
-/
namespace Potkin.Research.HLJStructuralApplication
open HLJStructural HLJContraction ContractionPlans ContractionBoundaries
open ContractionPostponement StructuralLemmaCuts ContractionCompilerCuts
universe u v
variable {sigma : Signature.{u, v}}

def communication (A B : Formula sigma) : Communication sigma where
  phi := {A}
  psi := {B}
  gamma₁ := 0
  gamma₂ := 0
  pi₁ := {A}
  pi₂ := {B}
  single₁ := by simp
  single₂ := by simp

noncomputable def identityOccurrence (id : Nat) (A : Formula sigma) := occurrence id (.identity A)
noncomputable def comOccurrence (A B : Formula sigma) := occurrence 2
  (.com 0 {A} {B} 0 0 {A} {B})

@[simp] theorem identity_premises (id : Nat) (A : Formula sigma) :
    (identityOccurrence id A).shape.premises = [] := rfl
@[simp] theorem identity_conclusion (id : Nat) (A : Formula sigma) :
    (identityOccurrence id A).shape.conclusion = .singleton ⟨{A}, {A}⟩ := rfl

theorem identity_admitted (id : Nat) (A : Formula sigma) :
    (theory sigma).Admits (identityOccurrence id A) := by
  apply strict_admits id (.identity A) trivial
  change WholeValid (identityOccurrence id A)
  rw [WholeValid, identity_premises, identity_conclusion]
  simp [ValidBoundary, ValidComponents, Single]

noncomputable def presentation (A B : Formula sigma) : EquippedPresentation (theory sigma) where
  registry := [identityOccurrence 0 A, identityOccurrence 1 B, comOccurrence A B]
  uniqueIds := by change ([0, 1, 2] : List Nat).Nodup; decide
  admitted := by
    intro o member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact identity_admitted _ _
    · exact identity_admitted _ _
    · exact com_strict (communication A B) 2 0 (by simp)

noncomputable def identityTree (id : Nat) (A : Formula sigma) :
    CKTree sigma (Data sigma) (.singleton ⟨{A}, {A}⟩) :=
  node (identityOccurrence id A) (identity_premises id A) (identity_conclusion id A) .nil

noncomputable def communicationTree (A B : Formula sigma) :
    CKTree sigma (Data sigma) (communication A B).output :=
  node (comOccurrence A B)
    (by simpa [comOccurrence, leftInput, rightInput] using
      com_premises 2 (0 : Multiset (Sequent sigma)) {A} {B} 0 0 {A} {B})
    (by simpa [comOccurrence, communication, Communication.output, leftOutput, rightOutput] using
      com_conclusion 2 (0 : Multiset (Sequent sigma)) {A} {B} 0 0 {A} {B})
    (.cons (identityTree 0 A) (.cons (identityTree 1 B) .nil))

theorem communication_complete (A B : Formula sigma) : (communicationTree A B).IsComplete := by
  simp [communicationTree, identityTree, CKChildren.IsComplete]

theorem communication_registered (A B : Formula sigma) :
    LocallyAdmittedTree (presentation A B) (communicationTree A B) := by
  apply (RuleInterface.registered_all _).mp
  simp [communicationTree, identityTree, AllChildren, presentation]

noncomputable def checkedCommunication [DecidableEq (Hypersequent sigma)] (A B : Formula sigma) :
    CheckedDerivation (presentation A B) (communication A B).output :=
  CompleteQuotation.checkedOfComplete (presentation A B) (communicationTree A B)
    (communication_registered A B) (communication_complete A B)

theorem checkedCommunication_realize [DecidableEq (Hypersequent sigma)] (A B : Formula sigma) :
    (checkedCommunication A B).realize = communicationTree A B :=
  CompleteQuotation.quote_realize _ _ _ _

theorem communication_degree (A B : Formula sigma) : (communicationTree A B).degree = 3 := by
  simp [communicationTree, identityTree, CKChildren.degree]

private theorem positive_ordinary {G : Hypersequent sigma}
    (tree : CKTree sigma (Data sigma) G) (positive : 0 < tree.degree) : tree.IsOrdinary := by
  cases tree with
  | interface => exact (Nat.not_lt_zero _ positive).elim
  | ordinary => trivial

section Compiler
variable (c : Communication sigma) (key : Data sigma → Nat) (m : State 2)
  (positive : ∀ i, 1 ≤ m i) (G : Multiset (Sequent sigma))
  (extra : Fin 2 → Multiset (Sequent sigma))
  (support : ∀ i S, S ∈ extra i → S ∈ G)

local notation "p" => c.problem m positive G extra support
local notation "r" => c.assembler key m positive G extra support

variable [DecidableEq (Hypersequent sigma)]

/-- The closed-donor front end checks the assembled output in the same strict registry. -/
noncomputable def compileStrict (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :=
  HLJContraction.checkedFinish c key m positive G extra support P
    (fun i => (donors i).realize) (fun i => (donors i).realizeIsComplete) plan registered

theorem compileStrict_realize (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    (compileStrict c key m positive G extra support P donors plan registered).realize =
      (r).finish (fun i => (donors i).realize) plan :=
  checkedFinish_realize c key m positive G extra support P _ _ plan registered

theorem compileStrict_degree (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    (compileStrict c key m positive G extra support P donors plan registered).realize.degree =
      plan.nodes (fun alpha i => (donors i).realize.degree + (p).stopWeight alpha i) +
        ((p).extras.card + (quota m - 1) * (p).H.components.card) := by
  rw [compileStrict_realize]
  exact (r).finish_degree _ plan

theorem compileStrict_Q {R : Type*} [CommSemiring R] (z : R)
    (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    ContractionCutObservation.Q z
      (compileStrict c key m positive G extra support P donors plan registered).realize =
      planQ z p (fun i => ContractionCutObservation.Q z (donors i).realize) plan +
        (((p).extras.card + (quota m - 1) * (p).H.components.card : Nat) : R) * z := by
  rw [compileStrict_realize]
  exact Q_finish (r) z _ plan

/-- A real open native compiler output, with one Box per physical donor use. -/
noncomputable def scaffold (plan : Plan m (fun _ => 0)) : CKTree sigma (Data sigma) (p).terminal :=
  (r).finish (fun i => .interface ((p).donorBoundary i)) plan

theorem scaffold_strict (valid : ValidComponents G) (plan : Plan m (fun _ => 0)) :
    AllNodes (theory sigma).Admits (scaffold c key m positive G extra support plan) :=
  finish_strict c key m positive G extra support valid
    (fun i => CKTree.interface ((p).donorBoundary i)) (fun _ => trivial) plan

theorem scaffold_ordinary (plan : Plan m (fun _ => 0)) :
    (scaffold c key m positive G extra support plan).IsOrdinary := by
  have cost := (r).finish_degree (fun i => CKTree.interface (InstanceData := Data sigma)
    ((p).donorBoundary i)) plan
  have nonzero : 0 < plan.nodes (fun alpha i => 0 + (p).stopWeight alpha i) := by
    cases plan with
    | stop i threshold bounded => have hp := positive i; simp at threshold; omega
    | next before children => simp only [Plan.nodes]; omega
  have degreePositive : 0 < (scaffold c key m positive G extra support plan).degree := by
    change 0 < ((r).finish _ plan).degree
    rw [cost]
    exact Nat.lt_of_lt_of_le nonzero (Nat.le_add_right _ _)
  exact positive_ordinary _ degreePositive

/-- Public proof-producing open compiler; fillers are indexed by physical holes. -/
noncomputable def compileAtHoles (P : EquippedPresentation (theory sigma))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P (scaffold c key m positive G extra support plan))
    (fillers : (h : (scaffold c key m positive G extra support plan).LeafOccurrence) →
      CheckedDerivation P ((scaffold c key m positive G extra support plan).leafBoundary h)) :=
  checkedFill P _ registered fillers

theorem compileAtHoles_realize (P : EquippedPresentation (theory sigma))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P (scaffold c key m positive G extra support plan))
    (fillers : (h : (scaffold c key m positive G extra support plan).LeafOccurrence) →
      CheckedDerivation P ((scaffold c key m positive G extra support plan).leafBoundary h)) :
    (compileAtHoles c key m positive G extra support P plan registered fillers).realize =
      (scaffold c key m positive G extra support plan).fillAssignment
        (fun h => (fillers h).realize) := checkedFill_realize P _ registered fillers

noncomputable def donorFrontier (P : EquippedPresentation (theory sigma))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P (scaffold c key m positive G extra support plan))
    (fillers : (h : (scaffold c key m positive G extra support plan).LeafOccurrence) →
      CheckedDerivation P ((scaffold c key m positive G extra support plan).leafBoundary h)) :
    CKCut (compileAtHoles c key m positive G extra support P plan registered fillers).realize := by
  rw [compileAtHoles_realize]
  exact properFrontier _ (scaffold_ordinary c key m positive G extra support plan) _
    (fun h => complete_ordinary _ (fillers h).realizeIsComplete)

theorem compileAtHoles_degree (P : EquippedPresentation (theory sigma))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P (scaffold c key m positive G extra support plan))
    (fillers : (h : (scaffold c key m positive G extra support plan).LeafOccurrence) →
      CheckedDerivation P ((scaffold c key m positive G extra support plan).leafBoundary h)) :
    (compileAtHoles c key m positive G extra support P plan registered fillers).realize.degree =
      (scaffold c key m positive G extra support plan).degree +
        ((scaffold c key m positive G extra support plan).leafOrder.map
          (fun h => (fillers h).realize.degree)).sum := by
  rw [compileAtHoles_realize]
  exact filling_degree _ _

/-- A proper addressed native certificate, not a count or fabricated root cut. -/
theorem certifiedFrontier (P : EquippedPresentation (theory sigma))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P (scaffold c key m positive G extra support plan))
    (fillers : (h : (scaffold c key m positive G extra support plan).LeafOccurrence) →
      CheckedDerivation P ((scaffold c key m positive G extra support plan).leafBoundary h)) :
    ∃ cut : CKCut (compileAtHoles c key m positive G extra support P plan registered fillers).realize,
      cut.plan.remainder = scaffold c key m positive G extra support plan ∧
      cut.plan.siteOrder.length = (scaffold c key m positive G extra support plan).leafOrder.length ∧
      cut.fill cut.plan.detached =
        (compileAtHoles c key m positive G extra support P plan registered fillers).realize := by
  rw [compileAtHoles_realize]
  exact ⟨properFrontier _ (scaffold_ordinary c key m positive G extra support plan) _
    (fun h => complete_ordinary _ (fillers h).realizeIsComplete),
    proper_remainder _ _ _ _, proper_length _ _ _ _, native_refill _ _ _ _⟩

end Compiler

/-- The previously verified K law propagates the exact signed CK change.
This is not coproduct preservation or coefficientwise positivity. -/
theorem contextual_ck_difference {G H : Hypersequent sigma}
    {context : CKTree sigma (Data sigma) G} {address : InternalAddress}
    (hole : CKTree.PunctureAt H context address) (S T : CKTree sigma (Data sigma) H) :
    ContextCutAction.delta (FreeAbelianGroup.of (hole.insert S) - FreeAbelianGroup.of (hole.insert T)) =
      ContextCutAction.K hole
        (ContextCutAction.delta (FreeAbelianGroup.of S) -
          ContextCutAction.delta (FreeAbelianGroup.of T)) := by
  have law := DFunLike.congr_fun (ContextCutAction.delta_K hole)
    (FreeAbelianGroup.of S - FreeAbelianGroup.of T)
  simpa only [AddMonoidHom.comp_apply, ContextCutAction.G, map_sub,
    FreeAbelianGroup.lift_apply_of] using law

#check @scaffold_strict
#check @compileAtHoles_realize
#check @certifiedFrontier
#print axioms checkedCommunication_realize
#print axioms scaffold_strict
#print axioms scaffold_ordinary
#print axioms compileAtHoles_realize
#print axioms donorFrontier
#print axioms certifiedFrontier
#print axioms compileAtHoles_degree
#print axioms compileStrict_Q
#print axioms compileStrict_degree
#print axioms contextual_ck_difference
end Potkin.Research.HLJStructuralApplication

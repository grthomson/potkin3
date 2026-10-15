import Potkin.Research.ContractionDonorFilling
import Potkin.Research.HLJStructuralApplication

/-!
# One checked compiler output with its cost and physical CK decomposition

Original donor indices are supplied by the Plan's construction history.
The existing index-uniform and physical-hole front ends agree literally on
native realizations. The CK and quantitative consequences are transferred,
not independently recomputed.
-/
namespace Potkin.Research.HLJDonorIntegration
open ContractionPlans ContractionBoundaries ContractionPostponement
open HLJStructural HLJContraction HLJStructuralApplication StructuralLemmaCuts
open ContractionDonorFilling
universe u v w
variable {sigma : Signature.{u, v}} {D : Type w} {n : Nat}

theorem realize_cast {T : ProofTheory sigma D} {P : EquippedPresentation T}
    {G H : Hypersequent sigma} (equal : G = H) (proof : CheckedDerivation P G) :
    (equal ▸ proof).realize = equal ▸ proof.realize := by cases equal; rfl

def checkedSupply {T : ProofTheory sigma D} (P : EquippedPresentation T)
    {B : Fin n → Hypersequent sigma} {G : Hypersequent sigma} {tree : CKTree sigma D G}
    (labels : Labels B tree) (donors : (i : Fin n) → CheckedDerivation P (B i)) :
    (h : tree.LeafOccurrence) → CheckedDerivation P (tree.leafBoundary h) :=
  fun h => (labels h).2 ▸ donors (labels h).1

theorem checkedSupply_realize {T : ProofTheory sigma D} (P : EquippedPresentation T)
    {B : Fin n → Hypersequent sigma} {G : Hypersequent sigma} {tree : CKTree sigma D G}
    (labels : Labels B tree) (donors : (i : Fin n) → CheckedDerivation P (B i)) :
    (fun h => (checkedSupply P labels donors h).realize) = supply labels (fun i => (donors i).realize) := by
  funext h
  exact realize_cast (labels h).2 (donors (labels h).1)

mutual
/-- Filling may add occurrences but cannot hide an unregistered scaffold node. -/
theorem admitted_scaffold {T : ProofTheory sigma D} (P : EquippedPresentation T) :
    {G : Hypersequent sigma} → (tree : CKTree sigma D G) → (fillers : tree.LeafAssignment) →
    LocallyAdmittedTree P (tree.fillAssignment fillers) → LocallyAdmittedTree P tree
  | _, .interface _, _, _ => trivial
  | _, .ordinary _ children, fillers, admitted =>
      ⟨admitted.1, admitted_childScaffold P children fillers admitted.2⟩

theorem admitted_childScaffold {T : ProofTheory sigma D} (P : EquippedPresentation T) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma D Gs) →
    (fillers : children.LeafAssignment) → LocallyAdmittedChildren P (children.fillAssignment fillers) →
    LocallyAdmittedChildren P children
  | _, .nil, _, _ => trivial
  | _, .cons head tail, fillers, admitted =>
      ⟨admitted_scaffold P head (fun h => fillers (.inl h)) admitted.1,
        admitted_childScaffold P tail (fun h => fillers (.inr h)) admitted.2⟩
end

section Application
variable (c : Communication sigma) (key : Data sigma → Nat) (m : State 2)
    (positive : ∀ i, 1 ≤ m i) (G : Multiset (Sequent sigma))
    (extra : Fin 2 → Multiset (Sequent sigma))
    (support : ∀ i S, S ∈ extra i → S ∈ G)
    [DecidableEq (Hypersequent sigma)]

local notation "p" => c.problem m positive G extra support
local notation "r" => c.assembler key m positive G extra support
local notation "M" => scaffold c key m positive G extra support

noncomputable def donorLabels (plan : Plan m (fun _ => 0)) :
    Labels (p).donorBoundary (M plan) :=
  ContractionDonorFilling.RuleInterface.finishLabels (r) plan

noncomputable def originalDonors (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0)) :
    (h : (M plan).LeafOccurrence) → CheckedDerivation P ((M plan).leafBoundary h) :=
  checkedSupply P (donorLabels c key m positive G extra support plan) donors

theorem original_fill (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0)) :
    (M plan).fillAssignment (fun h => (originalDonors c key m positive G extra support P donors plan h).realize) =
      (r).finish (fun i => (donors i).realize) plan := by
  rw [show (fun h => (originalDonors c key m positive G extra support P donors plan h).realize) =
      supply (donorLabels c key m positive G extra support plan) (fun i => (donors i).realize) from
        checkedSupply_realize P _ donors]
  exact ContractionDonorFilling.RuleInterface.finish_fill (r) _ plan

theorem scaffold_registered (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    LocallyAdmittedTree P (M plan) := by
  apply admitted_scaffold P (M plan)
    (fun h => (originalDonors c key m positive G extra support P donors plan h).realize)
  rw [original_fill]
  exact registered

theorem checked_frontends_agree (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    (compileAtHoles c key m positive G extra support P plan
      (scaffold_registered c key m positive G extra support P donors plan registered)
      (originalDonors c key m positive G extra support P donors plan)).realize =
    (compileStrict c key m positive G extra support P donors plan registered).realize := by
  rw [compileAtHoles_realize, compileStrict_realize, original_fill]

/-- The native detached provider recovers the history-selected original donor family. -/
theorem original_provider_matching (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0)) :
    alignedDetached (M plan) (scaffold_ordinary c key m positive G extra support plan)
      (fun h => (originalDonors c key m positive G extra support P donors plan h).realize)
      (fun h => (originalDonors c key m positive G extra support P donors plan h).realizeIsComplete) =
      supply (donorLabels c key m positive G extra support plan) (fun i => (donors i).realize) := by
  rw [alignedDetached_eq]
  exact checkedSupply_realize P _ donors

/-- The costed original-donor output itself has the physical proper CK frontier. -/
theorem canonical_frontier (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    ∃ cut : CKCut (compileStrict c key m positive G extra support P donors plan registered).realize,
      cut.plan.remainder = M plan ∧
      cut.plan.siteOrder.length = (M plan).leafOrder.length ∧
      cut.fill cut.plan.detached =
        (compileStrict c key m positive G extra support P donors plan registered).realize := by
  have result := certifiedFrontier c key m positive G extra support P plan
    (scaffold_registered c key m positive G extra support P donors plan registered)
    (originalDonors c key m positive G extra support P donors plan)
  rw [checked_frontends_agree] at result
  exact result

/-- The actual native witness on the closed-donor compiler output. -/
noncomputable def compiledFrontier (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    CKCut (compileStrict c key m positive G extra support P donors plan registered).realize := by
  rw [← checked_frontends_agree c key m positive G extra support P donors plan registered]
  exact donorFrontier c key m positive G extra support P plan
    (scaffold_registered c key m positive G extra support P donors plan registered)
    (originalDonors c key m positive G extra support P donors plan)

/-- All proper cut plans of this SAME output have the existing installed-cut classification. -/
noncomputable def compiledExtractionEquiv (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    CKCutPlan (compileStrict c key m positive G extra support P donors plan registered).realize ≃
      (compiledFrontier c key m positive G extra support P donors plan registered).plan.ExpansionChoices
        (compiledFrontier c key m positive G extra support P donors plan registered).plan.detached :=
  (Equiv.cast (congrArg (fun tree : CKTree sigma (Data sigma) (p).terminal => CKCutPlan tree)
    (compiledFrontier c key m positive G extra support P donors plan registered).fill_detached_reconstructs.symm)).trans
      ((compiledFrontier c key m positive G extra support P donors plan registered).plan.compositeCutEquiv
        (compiledFrontier c key m positive G extra support P donors plan registered).plan.detached)

/-- One proof, one native cut, and the already proved quantitative laws. -/
theorem compiled_certificate {R : Type*} [CommSemiring R] (z : R)
    (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CheckedDerivation P ((p).donorBoundary i))
    (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish (fun i => (donors i).realize) plan)) :
    ∃ cut : CKCut (compileStrict c key m positive G extra support P donors plan registered).realize,
      cut.plan.remainder = M plan ∧
      cut.plan.siteOrder.length = (M plan).leafOrder.length ∧
      cut.fill cut.plan.detached =
        (compileStrict c key m positive G extra support P donors plan registered).realize ∧
      (compileStrict c key m positive G extra support P donors plan registered).realize.degree =
        plan.nodes (fun alpha i => (donors i).realize.degree + (p).stopWeight alpha i) +
          ((p).extras.card + (quota m - 1) * (p).H.components.card) ∧
      ContractionCutObservation.Q z
        (compileStrict c key m positive G extra support P donors plan registered).realize =
        ContractionCompilerCuts.planQ z p (fun i => ContractionCutObservation.Q z (donors i).realize) plan +
          (((p).extras.card + (quota m - 1) * (p).H.components.card : Nat) : R) * z := by
  obtain ⟨cut, remainder, length, refill⟩ := canonical_frontier c key m positive G extra support
    P donors plan registered
  exact ⟨cut, remainder, length, refill, compileStrict_degree c key m positive G extra support P donors plan registered,
    compileStrict_Q c key m positive G extra support z P donors plan registered⟩
end Application

#check @checked_frontends_agree
#check @compiled_certificate
#print axioms original_fill
#print axioms checked_frontends_agree
#print axioms canonical_frontier
#print axioms compiledFrontier
#print axioms original_provider_matching
#print axioms compiledExtractionEquiv
#print axioms compiled_certificate
end Potkin.Research.HLJDonorIntegration

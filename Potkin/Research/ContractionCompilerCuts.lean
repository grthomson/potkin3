import Potkin.Research.ContractionPostponement
import Potkin.Research.ContractionCutObservation

/-!
# Native compiler costs and full physical CK cuts

The scalar is a proved projection of native cut witnesses in
`ContractionCutObservation`, not a replacement cut or proof carrier. Every EW,
EC, and continued rule occurrence remains an actual native ordinary vertex.
The optimization scope is precisely the fixed opaque-donor `Plan` language.
Its selected minimum is noncomputable attainment, not an executable search.
-/

namespace Potkin.Research.ContractionCompilerCuts

open ContractionPlans ContractionBoundaries ContractionPostponement
open ContractionPostponement.RuleInterface
open ContractionCutObservation
open scoped BigOperators

universe u v w
variable {sigma : Signature.{u, v}} {D : Type w} {n : Nat}
variable {T : ProofTheory sigma D}
variable {R : Type*} [CommSemiring R]

noncomputable section

@[simp] theorem Q_transport (z : R) {G H : Hypersequent sigma} (h : G = H)
    (tree : CKTree sigma D G) : Q z (h ▸ tree) = Q z tree := by cases h; rfl

@[simp] theorem Q_node (z : R) {Gs : List (Hypersequent sigma)} {G : Hypersequent sigma}
    (o : LocalOccurrence sigma D) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (children : CKChildren sigma D Gs) :
    Q z (node o hp hc children) = z + QChildren z children := by
  subst Gs
  subst G
  rfl

@[simp] theorem family_Q (z : R) : {k : Nat} → (B : Fin k → Hypersequent sigma) →
    (f : (i : Fin k) → CKTree sigma D (B i)) →
    QChildren z (familyChildren B f) = ∏ i, Q z (f i)
  | 0, _, _ => by simp [familyChildren, QChildren]
  | k + 1, B, f => by
      simp [familyChildren, QChildren_cast, QChildren, family_Q, family_product_succ]

variable {p : Problem sigma n} (r : RuleInterface T p)

@[simp] theorem Q_weaken (z : R) (G : Hypersequent sigma) (S : Sequent sigma)
    (tree : CKTree sigma D G) : Q z (r.weaken G S tree) = Q z tree + z := by
  simp [weaken, QChildren, add_comm]

theorem Q_weakenList (z : R) (G : Hypersequent sigma) (added : List (Sequent sigma))
    (tree : CKTree sigma D G) :
    Q z (r.weakenList G added tree) = Q z tree + (added.length : R) * z := by
  induction added with
  | nil => simp [weakenList]
  | cons S rest ih =>
      simp only [weakenList, Q_transport, Q_weaken, ih, List.length_cons,
        Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      ac_rfl

theorem Q_stopTree (z : R) (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (alpha : State n) (i : Fin n) (threshold : p.m i ≤ alpha i)
    (bounded : mass alpha ≤ quota p.m) :
    Q z (r.stopTree donors alpha i threshold bounded) =
      Q z (donors i) + (p.stopWeight alpha i : R) * z := by
  simp [stopTree, Q_weakenList, p.stop_weight_exact alpha i threshold]

/-- Exact Plan scalar recurrence; native witnesses are retained by the
interpreter and are projected only through the proved `Q_interpret` adapter. -/
def planQ (z : R) (p : Problem sigma n) (donorQ : Fin n → R) :
    {alpha : State n} → Plan p.m alpha → R
  | alpha, .stop i _ _ => donorQ i + (p.stopWeight alpha i : R) * z
  | _, .next _ children => z + ∏ i, planQ z p donorQ (children i)

theorem Q_interpret (z : R) (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    {alpha : State n} (plan : Plan p.m alpha) :
    Q z (r.interpret donors plan) = planQ z p (fun i => Q z (donors i)) plan := by
  induction plan with
  | stop i threshold bounded => simp [interpret, planQ, Q_stopTree]
  | next before children ih => simp [interpret, planQ, ih]

theorem Q_contractList (z : R) (G : Hypersequent sigma) (removed : List (Sequent sigma))
    (support : ∀ S ∈ removed, S ∈ G.components)
    (tree : CKTree sigma D (extend (removed : Multiset (Sequent sigma)) G)) :
    Q z (r.contractList G removed support tree) =
      Q z tree + (removed.length : R) * z := by
  induction removed with
  | nil => simp [contractList]
  | cons S rest ih =>
      simp only [contractList, ih, Q_node, QChildren, Q_transport,
        mul_one, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      ac_rfl

/-- The exact terminal EC queue contributes one new full-root endpoint for
each physical EC vertex. No positive tensor defect is claimed. -/
theorem Q_finish (z : R) (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0)) :
    Q z (r.finish donors plan) = planQ z p (fun i => Q z (donors i)) plan +
      ((p.extras.card + (quota p.m - 1) * p.H.components.card : Nat) : R) * z := by
  simp [finish, Q_contractList, Q_interpret, p.terminal_cost]

def nodeWeight (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (alpha : State n) (i : Fin n) : Nat := (donors i).degree + p.stopWeight alpha i

def optimizedPlan (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i)) :
    Plan p.m (fun _ => 0) :=
  lexPlan p.m (nodeWeight donors) (fun _ => 0) (by simp)
    (fun plan => Q (1 : Nat) (r.finish donors plan))

/-- Lexicographic `(nodes,Q(1))` optimality of actual native compiled trees,
restricted to this fixed Plan language and these opaque donor interiors. -/
theorem finish_lex_optimal
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0)) :
    (r.finish donors (optimizedPlan r donors)).degree ≤ (r.finish donors plan).degree ∧
    ((r.finish donors plan).degree = (r.finish donors (optimizedPlan r donors)).degree →
      Q (1 : Nat) (r.finish donors (optimizedPlan r donors)) ≤
        Q (1 : Nat) (r.finish donors plan)) := by
  have optimum := lexPlan_optimal p.m (nodeWeight donors) (fun _ => 0) (by simp)
    (fun plan => Q (1 : Nat) (r.finish donors plan)) plan
  change (optimizedPlan r donors).nodes (nodeWeight donors) ≤
      plan.nodes (nodeWeight donors) ∧
    (plan.nodes (nodeWeight donors) = (optimizedPlan r donors).nodes (nodeWeight donors) →
      Q (1 : Nat) (r.finish donors (optimizedPlan r donors)) ≤
        Q (1 : Nat) (r.finish donors plan)) at optimum
  constructor
  · simpa only [finish_degree, nodeWeight] using
      Nat.add_le_add_right optimum.1
        (p.extras.card + (quota p.m - 1) * p.H.components.card)
  · intro tied
    apply optimum.2
    exact Nat.add_right_cancel (by simpa only [finish_degree, nodeWeight] using tied)

/-- The secondary minimum is literally the cardinality of physical native
full-cut witnesses, not merely agreement of a recurrence on some fixtures. -/
theorem finish_lex_cutCard_optimal
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0)) :
    (r.finish donors (optimizedPlan r donors)).degree ≤ (r.finish donors plan).degree ∧
    ((r.finish donors plan).degree = (r.finish donors (optimizedPlan r donors)).degree →
      Fintype.card (CKBranchCut (r.finish donors (optimizedPlan r donors))) ≤
        Fintype.card (CKBranchCut (r.finish donors plan))) := by
  simpa only [Q_one_card] using finish_lex_optimal r donors plan

/-- The integrated checked front end retains the exact same native scalar;
its explicit registry-membership gate is not weakened by optimization. -/
theorem compile_Q (z : R) [DecidableEq (Hypersequent sigma)] (P : EquippedPresentation T)
    (donors : (i : Fin n) → CheckedDerivation P (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0))
    (registered : AllNodes (fun o => o ∈ P.registry)
      (r.finish (fun i => (donors i).realize) plan)) :
    Q z (r.compile P donors plan registered).realize =
      planQ z p (fun i => Q z (donors i).realize) plan +
      ((p.extras.card + (quota p.m - 1) * p.H.components.card : Nat) : R) * z := by
  rw [compile_realize]
  exact Q_finish r z _ plan

#check @Q_interpret
#check @Q_finish
#check @finish_lex_optimal
#check @compile_Q
#print axioms Q_interpret
#print axioms Q_finish
#print axioms finish_lex_optimal
#print axioms finish_lex_cutCard_optimal
#print axioms compile_Q
#check @ContractionPlans.threshold_at_quota
#check @ContractionPlans.plan_exists
#check @ContractionPlans.minimum_attained
#check @ContractionPlans.bellman_alternative
#check @ContractionPlans.lexPlan_optimal
#print axioms ContractionPlans.threshold_at_quota
#print axioms ContractionPlans.plan_exists
#print axioms ContractionPlans.minimum_attained
#print axioms ContractionPlans.bellman_alternative
#print axioms ContractionPlans.lexPlan_optimal

end
end Potkin.Research.ContractionCompilerCuts

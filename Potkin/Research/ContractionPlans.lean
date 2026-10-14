import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# The canonical opaque-donor contraction-postponement language

`Plan` is compiler control data, not a proof, cut, forest or context carrier.
Its continuation constructor retains every ordered premise index.  The native
interpretation supplies the admitted rule instances and all whole boundaries.
The optimum below is restricted to this language, with fixed opaque donor costs.
-/

namespace Potkin.Research.ContractionPlans

open scoped BigOperators

theorem sum_le_sum_nat {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → Nat) (h : ∀ i ∈ s, f i ≤ g i) :
    (∑ i ∈ s, f i) ≤ ∑ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s notMem ih =>
      rw [Finset.sum_insert notMem, Finset.sum_insert notMem]
      exact Nat.add_le_add (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

abbrev State (n : Nat) := Fin n → Nat

def mass {n : Nat} (alpha : State n) : Nat := ∑ i, alpha i

def quota {n : Nat} (m : State n) : Nat := 1 + ∑ i, (m i - 1)

def bump {n : Nat} (alpha : State n) (i : Fin n) : State n :=
  Function.update alpha i (alpha i + 1)

@[simp] theorem bump_same {n : Nat} (alpha : State n) (i : Fin n) :
    bump alpha i i = alpha i + 1 := by simp [bump]

@[simp] theorem bump_other {n : Nat} (alpha : State n) {i j : Fin n} (h : j ≠ i) :
    bump alpha i j = alpha j := by simp [bump, h]

@[simp] theorem mass_zero {n : Nat} : mass (fun _ : Fin n => 0) = 0 := by
  simp [mass]

theorem mass_bump {n : Nat} (alpha : State n) (i : Fin n) :
    mass (bump alpha i) = mass alpha + 1 := by
  have h := Finset.sum_update_of_mem (Finset.mem_univ i) alpha (alpha i + 1)
  have h' := Finset.sum_update_of_mem (Finset.mem_univ i) alpha (alpha i)
  simp only [Function.update_eq_self] at h'
  simp only [mass, bump]
  rw [h, h']
  omega

theorem le_mass {n : Nat} (alpha : State n) (i : Fin n) : alpha i ≤ mass alpha := by
  have h := Finset.sum_update_of_mem (Finset.mem_univ i) alpha (alpha i)
  simp only [Function.update_eq_self] at h
  change mass alpha = alpha i + _ at h
  omega

/-- Pigeonhole at the exact stopping depth; no finite fixture is involved. -/
theorem threshold_at_quota {n : Nat} (m alpha : State n)
    (h : mass alpha = quota m) : ∃ i, m i ≤ alpha i := by
  classical
  by_contra no
  have small : ∀ i, alpha i ≤ m i - 1 := by
    intro i
    have notLe : ¬m i ≤ alpha i := fun hi => no ⟨i, hi⟩
    omega
  have bound := sum_le_sum_nat Finset.univ alpha (fun i => m i - 1)
    (fun i (_ : i ∈ Finset.univ) => small i)
  change (∑ i, alpha i) ≤ (∑ i, (m i - 1)) at bound
  simp only [mass, quota] at h
  omega

/-- Every recursive child is the ordered increment of its own premise index. -/
inductive Plan {n : Nat} (m : State n) : State n → Type
  | stop {alpha : State n} (i : Fin n) (threshold : m i ≤ alpha i)
      (bounded : mass alpha ≤ quota m) : Plan m alpha
  | next {alpha : State n} (before : mass alpha < quota m)
      (children : (i : Fin n) → Plan m (bump alpha i)) : Plan m alpha

theorem Plan.bounded {n : Nat} {m alpha : State n} (plan : Plan m alpha) :
    mass alpha ≤ quota m := by
  cases plan with
  | stop _ _ bounded => exact bounded
  | next before _ => exact Nat.le_of_lt before

/-- The remaining-depth rank strictly decreases at every continued premise. -/
theorem rank_decreases {n : Nat} {m alpha : State n}
    (before : mass alpha < quota m) (i : Fin n) :
    quota m - mass (bump alpha i) < quota m - mass alpha := by
  rw [mass_bump]
  omega

/-- A Plan exists for every reachable bounded state.  The proof constructs the
uniform continuation until the pigeonhole threshold, without enumerating plans. -/
theorem plan_exists {n : Nat} (m alpha : State n)
    (bounded : mass alpha ≤ quota m) : Nonempty (Plan m alpha) := by
  classical
  have construct : ∀ depth : Nat, ∀ alpha : State n,
      quota m - mass alpha = depth → mass alpha ≤ quota m →
      Nonempty (Plan m alpha) := by
    intro depth
    induction depth with
    | zero =>
        intro alpha rank bounded
        have equality : mass alpha = quota m := by omega
        obtain ⟨i, threshold⟩ := threshold_at_quota m alpha equality
        exact ⟨.stop i threshold bounded⟩
    | succ depth ih =>
        intro alpha rank bounded
        have before : mass alpha < quota m := by omega
        refine ⟨.next before (fun i => Classical.choice (ih (bump alpha i) ?_ ?_))⟩
        · rw [mass_bump]
          omega
        · rw [mass_bump]
          omega
  exact construct (quota m - mass alpha) alpha rfl bounded

/-- Exact node objective once the native stop script's cost has been supplied. -/
def Plan.nodes {n : Nat} {m : State n} (stopWeight : State n → Fin n → Nat) :
    {alpha : State n} → Plan m alpha → Nat
  | alpha, .stop i _ _ => stopWeight alpha i
  | _, .next _ children => 1 + ∑ i, (children i).nodes stopWeight

@[simp] theorem Plan.nodes_stop {n : Nat} {m alpha : State n}
    (stopWeight : State n → Fin n → Nat) (i : Fin n)
    (threshold : m i ≤ alpha i) (bounded : mass alpha ≤ quota m) :
    (Plan.stop i threshold bounded).nodes stopWeight = stopWeight alpha i := rfl

@[simp] theorem Plan.nodes_next {n : Nat} {m alpha : State n}
    (stopWeight : State n → Fin n → Nat) (before : mass alpha < quota m)
    (children : (i : Fin n) → Plan m (bump alpha i)) :
    (Plan.next before children).nodes stopWeight =
      1 + ∑ i, (children i).nodes stopWeight := rfl

private theorem cost_exists {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) :
    ∃ cost, ∃ plan : Plan m alpha, plan.nodes stopWeight = cost := by
  obtain ⟨plan⟩ := plan_exists m alpha bounded
  exact ⟨plan.nodes stopWeight, plan, rfl⟩

/-- Attained Bellman value.  Classical choice affects selection, not the
optimality theorem; this is not a claim about proofs outside `Plan`. -/
noncomputable def minimum {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) : Nat := by
  classical
  exact Nat.find (cost_exists m stopWeight alpha bounded)

theorem minimum_attained {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) :
    ∃ plan : Plan m alpha, plan.nodes stopWeight = minimum m stopWeight alpha bounded := by
  classical
  exact Nat.find_spec (cost_exists m stopWeight alpha bounded)

noncomputable def optimalPlan {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) : Plan m alpha :=
  Classical.choose (minimum_attained m stopWeight alpha bounded)

@[simp] theorem optimalPlan_nodes {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) :
    (optimalPlan m stopWeight alpha bounded).nodes stopWeight =
      minimum m stopWeight alpha bounded :=
  Classical.choose_spec (minimum_attained m stopWeight alpha bounded)

theorem minimum_le_plan {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) (plan : Plan m alpha) :
    minimum m stopWeight alpha bounded ≤ plan.nodes stopWeight := by
  classical
  exact Nat.find_min' (cost_exists m stopWeight alpha bounded) ⟨plan, rfl⟩

theorem minimum_le_stop {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) (i : Fin n) (threshold : m i ≤ alpha i) :
    minimum m stopWeight alpha bounded ≤ stopWeight alpha i :=
  minimum_le_plan m stopWeight alpha bounded (.stop i threshold bounded)

theorem bump_bounded {n : Nat} {m alpha : State n}
    (before : mass alpha < quota m) (i : Fin n) :
    mass (bump alpha i) ≤ quota m := by rw [mass_bump]; omega

/-- The continuation Bellman candidate uses an optimal child at every ordered
premise, not just one branch, and includes exactly one new rule vertex. -/
theorem minimum_le_continue {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) (before : mass alpha < quota m) :
    minimum m stopWeight alpha bounded ≤
      1 + ∑ i, minimum m stopWeight (bump alpha i) (bump_bounded before i) := by
  let children := fun i => optimalPlan m stopWeight (bump alpha i) (bump_bounded before i)
  simpa [children] using
    minimum_le_plan m stopWeight alpha bounded (.next before children)

/-- Bellman's alternatives: an attained minimum is one legal stop candidate,
or the exact sum of the optimal ordered child candidates. -/
theorem bellman_alternative {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) :
    (∃ i, m i ≤ alpha i ∧ minimum m stopWeight alpha bounded = stopWeight alpha i) ∨
    (∃ before : mass alpha < quota m,
      minimum m stopWeight alpha bounded =
        1 + ∑ i, minimum m stopWeight (bump alpha i) (bump_bounded before i)) := by
  obtain ⟨plan, attained⟩ := minimum_attained m stopWeight alpha bounded
  cases plan with
  | stop i threshold bound => exact .inl ⟨i, threshold, attained.symm⟩
  | next before children =>
      refine .inr ⟨before, Nat.le_antisymm
        (minimum_le_continue m stopWeight alpha bounded before) ?_⟩
      rw [← attained]
      simp only [Plan.nodes_next]
      exact Nat.add_le_add_left (sum_le_sum_nat Finset.univ _ _ (fun i _ =>
        minimum_le_plan m stopWeight (bump alpha i) (bump_bounded before i) (children i))) 1

private theorem secondary_exists {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) (secondary : Plan m alpha → Nat) :
    ∃ score, ∃ plan : Plan m alpha,
      plan.nodes stopWeight = minimum m stopWeight alpha bounded ∧ secondary plan = score := by
  exact ⟨secondary (optimalPlan m stopWeight alpha bounded),
    optimalPlan m stopWeight alpha bounded, optimalPlan_nodes _ _ _ _, rfl⟩

/-- A secondary optimum among the node-minimal plans.  Instantiating `secondary`
with the native full-cut scalar gives the requested `(nodes,Q(1))` objective. -/
noncomputable def lexPlan {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) (secondary : Plan m alpha → Nat) : Plan m alpha := by
  classical
  exact Classical.choose (Nat.find_spec (secondary_exists m stopWeight alpha bounded secondary))

theorem lexPlan_nodes {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) (secondary : Plan m alpha → Nat) :
    (lexPlan m stopWeight alpha bounded secondary).nodes stopWeight =
      minimum m stopWeight alpha bounded := by
  classical
  exact (Classical.choose_spec
    (Nat.find_spec (secondary_exists m stopWeight alpha bounded secondary))).1

/-- Lexicographic attainment and optimality, only among fixed-language plans. -/
theorem lexPlan_optimal {n : Nat} (m : State n)
    (stopWeight : State n → Fin n → Nat) (alpha : State n)
    (bounded : mass alpha ≤ quota m) (secondary : Plan m alpha → Nat)
    (plan : Plan m alpha) :
    (lexPlan m stopWeight alpha bounded secondary).nodes stopWeight ≤ plan.nodes stopWeight ∧
    (plan.nodes stopWeight = (lexPlan m stopWeight alpha bounded secondary).nodes stopWeight →
      secondary (lexPlan m stopWeight alpha bounded secondary) ≤ secondary plan) := by
  classical
  constructor
  · rw [lexPlan_nodes]
    exact minimum_le_plan _ _ _ _ plan
  · intro tied
    have tied' : plan.nodes stopWeight = minimum m stopWeight alpha bounded := by
      simpa only [lexPlan_nodes] using tied
    have chosen := (Classical.choose_spec
      (Nat.find_spec (secondary_exists m stopWeight alpha bounded secondary))).2
    change secondary (lexPlan m stopWeight alpha bounded secondary) = _ at chosen
    rw [chosen]
    exact Nat.find_min' (secondary_exists m stopWeight alpha bounded secondary) ⟨plan, tied', rfl⟩

end Potkin.Research.ContractionPlans

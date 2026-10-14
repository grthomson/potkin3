import Potkin.Research.ContractionPlans
import Potkin.GeneralFilling
import Mathlib.Data.Multiset.Replicate

/-!
# Exact multiset boundaries for the opaque-donor compiler

These are boundary and script data, not a second proof carrier. External
context support means membership, not multiset inclusion. All counts retain
equal component occurrences. The continuing rule's admission is supplied in
`ContractionPostponement`, not inferred from these boundary equalities.
-/

namespace Potkin.Research.ContractionBoundaries

open ContractionPlans
open scoped BigOperators
universe u v
variable {sigma : Signature.{u, v}} {n : Nat}

def extend (K : Multiset (Sequent sigma)) (H : Hypersequent sigma) :
    Hypersequent sigma where
  components := K + H.components
  nonempty := by
    intro h
    have := Multiset.card_eq_zero.mpr h
    simp only [Multiset.card_add] at this
    exact H.nonempty (Multiset.card_eq_zero.mp (by omega))

@[simp] theorem extend_components (K : Multiset (Sequent sigma))
    (H : Hypersequent sigma) : (extend K H).components = K + H.components := rfl

@[simp] theorem extend_zero (H : Hypersequent sigma) : extend 0 H = H := by
  apply Hypersequent.ext
  simp [extend]

theorem extend_extend (K L : Multiset (Sequent sigma)) (H : Hypersequent sigma) :
    extend K (extend L H) = extend (K + L) H := by
  apply Hypersequent.ext
  simp [extend, add_assoc]

structure Problem (sigma : Signature.{u, v}) (n : Nat) where
  positive : 0 < n
  m : State n
  m_positive : ∀ i, 1 ≤ m i
  G : Multiset (Sequent sigma)
  extra : Fin n → Multiset (Sequent sigma)
  extra_support : ∀ i S, S ∈ extra i → S ∈ G
  C : Fin n → Sequent sigma
  H : Hypersequent sigma

namespace Problem

variable (p : Problem sigma n)

private theorem single_sum_le {A : Type _} (s : Finset A)
    (f : A → Multiset (Sequent sigma)) (i : A) (hi : i ∈ s) :
    f i ≤ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hi
  | @insert a s ha ih =>
      rcases Finset.mem_insert.mp hi with h | h
      · subst i
        simpa [Finset.sum_insert ha] using Multiset.le_add_right (f a) (∑ j ∈ s, f j)
      · have hle := (ih h).trans (Multiset.le_add_left (∑ j ∈ s, f j) (f a))
        simpa [Finset.sum_insert ha] using hle

private theorem single_nat_sum_le {A : Type _} (s : Finset A)
    (f : A → Nat) (i : A) (hi : i ∈ s) : f i ≤ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hi
  | @insert a s ha ih =>
      rcases Finset.mem_insert.mp hi with h | h
      · subst i; simp [Finset.sum_insert ha]
      · have hle := ih h
        rw [Finset.sum_insert ha]
        omega

def extras : Multiset (Sequent sigma) := ∑ i, p.extra i
def active (alpha : State n) : Multiset (Sequent sigma) :=
  ∑ i, Multiset.replicate (alpha i) (p.C i)
def components (alpha : State n) : Multiset (Sequent sigma) :=
  p.G + p.extras + (quota p.m - mass alpha) • p.H.components + p.active alpha

private theorem card_sum {A : Type _} (s : Finset A)
    (f : A → Multiset (Sequent sigma)) :
    (∑ i ∈ s, f i).card = ∑ i ∈ s, (f i).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem card_smul (k : Nat) (M : Multiset (Sequent sigma)) :
    (k • M).card = k * M.card := by
  induction k with
  | zero => simp
  | succ k ih => simp [succ_nsmul, Multiset.card_add, ih, Nat.succ_mul]

@[simp] theorem active_card (alpha : State n) : (p.active alpha).card = mass alpha := by
  unfold active mass
  simpa using card_sum Finset.univ (fun i => Multiset.replicate (alpha i) (p.C i))

theorem components_card (alpha : State n) :
    (p.components alpha).card = p.G.card + p.extras.card +
      (quota p.m - mass alpha) * p.H.components.card + mass alpha := by
  simp only [components, Multiset.card_add, card_smul, active_card]

theorem components_nonempty (alpha : State n) (bounded : mass alpha ≤ quota p.m) :
    p.components alpha ≠ 0 := by
  intro h
  have hz := congrArg Multiset.card h
  rw [components_card] at hz
  have hH : 0 < p.H.components.card := by
    have := p.H.nonempty
    exact Nat.pos_of_ne_zero (fun h => this (Multiset.card_eq_zero.mp h))
  have hq : 0 < quota p.m := by unfold quota; omega
  by_cases hm : mass alpha = 0
  · have hp : 0 < (quota p.m - mass alpha) * p.H.components.card :=
      Nat.mul_pos (by omega) hH
    simp only [Multiset.card_zero] at hz
    omega
  · simp only [Multiset.card_zero] at hz
    omega

def boundary (alpha : State n) (bounded : mass alpha ≤ quota p.m) :
    Hypersequent sigma := ⟨p.components alpha, p.components_nonempty alpha bounded⟩

def donorBoundary (i : Fin n) : Hypersequent sigma where
  components := p.G + p.extra i + Multiset.replicate (p.m i) (p.C i)
  nonempty := by
    intro h
    have hc := congrArg Multiset.card h
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_zero] at hc
    have := p.m_positive i
    omega

def common (alpha : State n) : Multiset (Sequent sigma) :=
  p.G + p.extras + (quota p.m - mass alpha - 1) • p.H.components + p.active alpha

theorem active_bump (alpha : State n) (i : Fin n) :
    p.active (bump alpha i) = p.active alpha + {p.C i} := by
  classical
  unfold active
  calc
    _ = ∑ j : Fin n, (Multiset.replicate (alpha j) (p.C j) +
        if j = i then {p.C i} else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst j
        simp only [bump_same, ite_true, Multiset.replicate_add, Multiset.replicate_one]
      · simp [bump_other alpha h, h]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem boundary_continue (alpha : State n) (h : mass alpha < quota p.m) :
    p.boundary alpha (Nat.le_of_lt h) = extend (p.common alpha) p.H := by
  apply Hypersequent.ext
  change p.components alpha = p.common alpha + p.H.components
  have hk : quota p.m - mass alpha = (quota p.m - mass alpha - 1) + 1 := by omega
  have hs : (quota p.m - mass alpha) • p.H.components =
      (quota p.m - mass alpha - 1) • p.H.components + p.H.components := by
    conv_lhs => rw [hk, add_nsmul, one_nsmul]
  simp only [components, common, hs]
  ac_rfl

theorem boundary_child (alpha : State n) (h : mass alpha < quota p.m) (i : Fin n) :
    p.boundary (bump alpha i) (by rw [mass_bump]; omega) =
      extend (p.common alpha) (Hypersequent.singleton (p.C i)) := by
  apply Hypersequent.ext
  change p.components (bump alpha i) = p.common alpha + {p.C i}
  have hk : quota p.m - mass (bump alpha i) = quota p.m - mass alpha - 1 := by
    rw [mass_bump]; omega
  simp only [components, common, hk, active_bump]
  ac_rfl

theorem donor_le_state (alpha : State n) (i : Fin n) (threshold : p.m i ≤ alpha i) :
    (p.donorBoundary i).components ≤ p.components alpha := by
  classical
  have he : p.extra i ≤ p.extras :=
    single_sum_le Finset.univ p.extra i (Finset.mem_univ i)
  have ha : Multiset.replicate (p.m i) (p.C i) ≤ p.active alpha :=
    (Multiset.replicate_le_replicate (p.C i)).mpr threshold |>.trans
      (single_sum_le Finset.univ (fun j => Multiset.replicate (alpha j) (p.C j)) i
        (Finset.mem_univ i))
  calc
    _ ≤ (p.G + p.extras) + p.active alpha :=
      add_le_add (Multiset.add_le_add_left he) ha
    _ ≤ p.components alpha := by
      unfold components
      exact Multiset.add_le_add_right (Multiset.le_add_right _ _)

noncomputable def stopComponents (alpha : State n) (i : Fin n) :
    Multiset (Sequent sigma) := by
  classical
  exact p.components alpha - (p.donorBoundary i).components

theorem stop_components_exact (alpha : State n) (i : Fin n)
    (threshold : p.m i ≤ alpha i) :
    p.stopComponents alpha i + (p.donorBoundary i).components = p.components alpha := by
  classical
  exact Multiset.sub_add_cancel (p.donor_le_state alpha i threshold)

def stopWeight (alpha : State n) (i : Fin n) : Nat :=
  p.extras.card - (p.extra i).card + (quota p.m - mass alpha) * p.H.components.card +
    mass alpha - p.m i

theorem stop_weight_exact (alpha : State n) (i : Fin n)
    (threshold : p.m i ≤ alpha i) :
    (p.stopComponents alpha i).card = p.stopWeight alpha i := by
  classical
  have hc := congrArg Multiset.card (p.stop_components_exact alpha i threshold)
  simp only [Multiset.card_add, components_card, donorBoundary,
    Multiset.card_replicate] at hc
  have he : (p.extra i).card ≤ p.extras.card :=
    Multiset.card_mono (single_sum_le Finset.univ p.extra i (Finset.mem_univ i))
  have hi : alpha i ≤ mass alpha :=
    single_nat_sum_le Finset.univ alpha i (Finset.mem_univ i)
  unfold stopWeight
  omega

def terminal : Hypersequent sigma := extend p.G p.H
def terminalComponents : Multiset (Sequent sigma) :=
  p.extras + (quota p.m - 1) • p.H.components

theorem terminal_boundary : p.components (fun _ => 0) =
    p.terminalComponents + p.terminal.components := by
  have hq : quota p.m = quota p.m - 1 + 1 := by unfold quota; omega
  have hs : quota p.m • p.H.components =
      (quota p.m - 1) • p.H.components + p.H.components := by
    conv_lhs => rw [hq, add_nsmul, one_nsmul]
  simp only [components, terminalComponents, terminal, extend_components,
    mass, Finset.sum_const_zero, Nat.sub_zero, active, Multiset.replicate_zero,
    Finset.sum_const_zero, add_zero, hs]
  ac_rfl

theorem terminal_cost : p.terminalComponents.card =
    p.extras.card + (quota p.m - 1) * p.H.components.card := by
  simp only [terminalComponents, Multiset.card_add, card_smul]

end Problem
end Potkin.Research.ContractionBoundaries

#check Potkin.Research.ContractionBoundaries.Problem.boundary_child
#print axioms Potkin.Research.ContractionBoundaries.Problem.boundary_child
#print axioms Potkin.Research.ContractionBoundaries.Problem.stop_weight_exact
#print axioms Potkin.Research.ContractionBoundaries.Problem.terminal_boundary

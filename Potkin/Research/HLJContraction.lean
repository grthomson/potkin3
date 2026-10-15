import Potkin.Research.HLJStructural
import Potkin.Research.D3RegistryAdmission

/-!
# Strict HLJ admission of the existing structural compiler

The old unguarded RuleInterface is used ONLY as a native raw-tree assembler.
This module proves that every reached occurrence satisfies strict HLJ admission.
Quotation is always into `HLJStructural.theory`, never the assembly envelope.
Owner-free schema data and plans are metadata, not new derivation carriers.
-/
namespace Potkin.Research.HLJContraction
open ContractionPlans ContractionBoundaries ContractionPostponement HLJStructural
open scoped BigOperators
universe u v
variable {sigma : Signature.{u, v}}

/-- The actual antecedent-repartition instance, with its ordered active inputs. -/
structure Communication (sigma : Signature.{u, v}) where
  phi : Context sigma
  psi : Context sigma
  gamma₁ : Context sigma
  gamma₂ : Context sigma
  pi₁ : Context sigma
  pi₂ : Context sigma
  single₁ : pi₁.card ≤ 1
  single₂ : pi₂.card ≤ 1

def Communication.inputs (c : Communication sigma) : Fin 2 → Sequent sigma :=
  Fin.cases (leftInput c.phi c.gamma₁ c.pi₁)
    (fun _ => rightInput c.psi c.gamma₂ c.pi₂)

def Communication.output (c : Communication sigma) : Hypersequent sigma :=
  .pair (leftOutput c.psi c.gamma₁ c.pi₁) (rightOutput c.phi c.gamma₂ c.pi₂)

def Communication.problem (c : Communication sigma) (m : State 2)
    (positive : ∀ i, 1 ≤ m i) (G : Multiset (Sequent sigma))
    (extra : Fin 2 → Multiset (Sequent sigma))
    (support : ∀ i S, S ∈ extra i → S ∈ G) : Problem sigma 2 :=
  ⟨by decide, m, positive, G, extra, support, c.inputs, c.output⟩

noncomputable def Communication.assembler (c : Communication sigma)
    (key : Data sigma → Nat) (m : State 2) (positive : ∀ i, 1 ≤ m i)
    (G : Multiset (Sequent sigma)) (extra : Fin 2 → Multiset (Sequent sigma))
    (support : ∀ i S, S ∈ extra i → S ∈ G) :
    RuleInterface (assemblyTheory sigma) (c.problem m positive G extra support) where
  rule K := occurrence (key (.com K c.phi c.psi c.gamma₁ c.gamma₂ c.pi₁ c.pi₂))
    (.com K c.phi c.psi c.gamma₁ c.gamma₂ c.pi₁ c.pi₂)
  rule_premises K := by
    rw [com_premises]
    simp [Communication.problem, Communication.inputs, List.ofFn_succ]
  rule_conclusion K := com_conclusion _ _ _ _ _ _ _ _
  rule_admitted K := assembly_admits _ _ trivial
  rule_incidence K := rfl
  ew G S := occurrence (key (.ew G S)) (.ew G S)
  ew_kind G S := rfl
  ew_premises G S := ew_premises _ _ _
  ew_conclusion G S := ew_conclusion _ _ _
  ew_admitted G S := assembly_admits _ _ trivial
  ew_incidence G S := rfl
  ec G S h := occurrence (key (.ec G S (retainedIndex G S h).val))
    (.ec G S (retainedIndex G S h).val)
  ec_kind G S h := rfl
  ec_premises G S h := ec_premises _ _ _ _
  ec_conclusion G S h := ec_conclusion _ _ _ _
  ec_admitted G S h := assembly_admits _ _ ⟨retainedIndex G S h, rfl, retainedIndex_get G S h⟩
  ec_incidence G S h := rfl

theorem com_strict (c : Communication sigma) (key : Nat)
    (K : Multiset (Sequent sigma)) (valid : ValidComponents K) :
    (theory sigma).Admits (occurrence key
      (.com K c.phi c.psi c.gamma₁ c.gamma₂ c.pi₁ c.pi₂)) := by
  apply strict_admits key (.com K c.phi c.psi c.gamma₁ c.gamma₂ c.pi₁ c.pi₂) trivial
  rw [WholeValid, com_premises, com_conclusion]
  constructor
  · intro G member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (valid_extend _ _).mpr ⟨valid, fun S h => by
        have : S = leftInput c.phi c.gamma₁ c.pi₁ := Multiset.mem_singleton.mp h
        subst S; exact c.single₁⟩
    · exact (valid_extend _ _).mpr ⟨valid, fun S h => by
        have : S = rightInput c.psi c.gamma₂ c.pi₂ := Multiset.mem_singleton.mp h
        subst S; exact c.single₂⟩
  · apply (valid_extend _ _).mpr
    refine ⟨valid, ?_⟩
    intro S h
    have h' : S = leftOutput c.psi c.gamma₁ c.pi₁ ∨
        S = rightOutput c.phi c.gamma₂ c.pi₂ := by simpa [Hypersequent.pair] using h
    rcases h' with rfl | rfl
    · exact c.single₁
    · exact c.single₂

theorem ew_strict (key : Nat) (G : Hypersequent sigma) (S : Sequent sigma)
    (valid : ValidBoundary G) (single : Single S) :
    (theory sigma).Admits (occurrence key (.ew G S)) := by
  apply strict_admits key (.ew G S) trivial
  simpa [WholeValid] using And.intro valid (And.intro single valid)

theorem ec_strict (key : Nat) (G : Hypersequent sigma) (S : Sequent sigma)
    (member : S ∈ G.components) (valid : ValidBoundary G) :
    (theory sigma).Admits (occurrence key (.ec G S (retainedIndex G S member).val)) := by
  apply strict_admits key (.ec G S (retainedIndex G S member).val)
    ⟨retainedIndex G S member, rfl, retainedIndex_get G S member⟩
  simpa [WholeValid] using And.intro (And.intro (valid S member) valid) valid

section Guards
variable {n : Nat} (p : Problem sigma n)

def WellFormed : Prop := ValidComponents p.G ∧ (∀ i, Single (p.C i)) ∧ ValidBoundary p.H

theorem valid_extra (well : WellFormed p) (i : Fin n) : ValidComponents (p.extra i) :=
  fun S member => well.1 S (p.extra_support i S member)

theorem valid_extras (well : WellFormed p) : ValidComponents p.extras := by
  intro S member
  obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp member
  exact valid_extra p well i S hi

theorem valid_active (well : WellFormed p) (alpha : State n) :
    ValidComponents (p.active alpha) := by
  intro S member
  obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp member
  have eq : S = p.C i := (Multiset.mem_replicate.mp hi).2
  subst S
  exact well.2.1 i

theorem valid_state (well : WellFormed p) (alpha : State n) :
    ValidComponents (p.components alpha) := by
  unfold Problem.components
  exact (valid_add _ _).mpr ⟨(valid_add _ _).mpr
    ⟨(valid_add _ _).mpr ⟨well.1, valid_extras p well⟩,
      valid_nsmul _ well.2.2⟩, valid_active p well alpha⟩

theorem valid_common (well : WellFormed p) (alpha : State n) :
    ValidComponents (p.common alpha) := by
  unfold Problem.common
  exact (valid_add _ _).mpr ⟨(valid_add _ _).mpr
    ⟨(valid_add _ _).mpr ⟨well.1, valid_extras p well⟩,
      valid_nsmul _ well.2.2⟩, valid_active p well alpha⟩

theorem valid_donor (well : WellFormed p) (i : Fin n) : ValidBoundary (p.donorBoundary i) := by
  intro S member
  simp only [Problem.donorBoundary, Multiset.mem_add] at member
  rcases member with (h | h) | h
  · exact well.1 S h
  · exact valid_extra p well i S h
  · obtain ⟨_, rfl⟩ := Multiset.mem_replicate.mp h
    exact well.2.1 i

theorem valid_stop (well : WellFormed p) (alpha : State n) (i : Fin n) :
    ValidComponents (p.stopComponents alpha i) := by
  classical
  exact valid_of_le (Multiset.sub_le_self _ _) (valid_state p well alpha)

theorem valid_terminal (well : WellFormed p) : ValidBoundary p.terminal :=
  (valid_extend _ _).mpr ⟨well.1, well.2.2⟩
end Guards

section Compiler
variable (c : Communication sigma) (key : Data sigma → Nat) (m : State 2)
  (positive : ∀ i, 1 ≤ m i) (G : Multiset (Sequent sigma))
  (extra : Fin 2 → Multiset (Sequent sigma))
  (support : ∀ i S, S ∈ extra i → S ∈ G)

local notation "p" => c.problem m positive G extra support
local notation "r" => c.assembler key m positive G extra support

theorem problem_wellFormed (valid : ValidComponents G) : WellFormed p := by
  refine ⟨valid, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact c.single₁
    | succ i => exact c.single₂
  · intro S member
    have member' : S = leftOutput c.psi c.gamma₁ c.pi₁ ∨
        S = rightOutput c.phi c.gamma₂ c.pi₂ := by
      simpa [Communication.problem, Communication.output, Hypersequent.pair] using member
    rcases member' with rfl | rfl
    · exact c.single₁
    · exact c.single₂

theorem weakenList_strict (base : Hypersequent sigma) (added : List (Sequent sigma))
    (valid : ValidBoundary base) (addValid : ValidComponents (added : Multiset (Sequent sigma)))
    (tree : CKTree sigma (Data sigma) base) (ht : AllNodes (theory sigma).Admits tree) :
    AllNodes (theory sigma).Admits ((r).weakenList base added tree) := by
  induction added with
  | nil => simpa [RuleInterface.weakenList] using ht
  | cons S rest ih =>
      have both : Single S ∧ ValidComponents (rest : Multiset (Sequent sigma)) := by
        refine ⟨addValid S (by simp), ?_⟩
        intro X hx
        exact addValid X (by simp only [Multiset.mem_coe, List.mem_cons]; exact Or.inr hx)
      have tailValid := (valid_extend _ _).mpr ⟨both.2, valid⟩
      have admitted := ew_strict (key (.ew (extend (rest : Multiset (Sequent sigma)) base) S))
        (extend (rest : Multiset (Sequent sigma)) base) S tailValid both.1
      simpa [RuleInterface.weakenList, RuleInterface.weaken, AllChildren,
        Communication.assembler] using And.intro admitted (ih both.2)

theorem interpret_strict (valid : ValidComponents G)
    (donors : (i : Fin 2) → CKTree sigma (Data sigma) ((p).donorBoundary i))
    (hd : ∀ i, AllNodes (theory sigma).Admits (donors i))
    {alpha : State 2} (plan : Plan m alpha) :
    AllNodes (theory sigma).Admits ((r).interpret donors plan) := by
  have well := problem_wellFormed c m positive G extra support valid
  induction plan with
  | stop i threshold bounded =>
      simpa [RuleInterface.interpret, RuleInterface.stopTree] using
        weakenList_strict c key m positive G extra support ((p).donorBoundary i)
          ((p).stopComponents _ i).toList (valid_donor p well i)
          (by simpa using valid_stop p well _ i) (donors i) (hd i)
  | @next beta before children ih =>
      have admitted := com_strict c (key (.com ((p).common beta) c.phi c.psi c.gamma₁
        c.gamma₂ c.pi₁ c.pi₂)) ((p).common beta) (valid_common p well beta)
      simpa [RuleInterface.interpret, Communication.assembler, ih] using
        And.intro admitted (show ∀ i, AllNodes (theory sigma).Admits
          ((r).interpret donors (children i)) from ih)

theorem contractList_strict (base : Hypersequent sigma) (removed : List (Sequent sigma))
    (support' : ∀ S ∈ removed, S ∈ base.components) (valid : ValidBoundary base)
    (tree : CKTree sigma (Data sigma) (extend (removed : Multiset (Sequent sigma)) base))
    (ht : AllNodes (theory sigma).Admits tree) :
    AllNodes (theory sigma).Admits ((r).contractList base removed support' tree) := by
  induction removed with
  | nil => simpa [RuleInterface.contractList] using ht
  | cons S rest ih =>
      have restValid : ValidComponents (rest : Multiset (Sequent sigma)) :=
        fun X h => valid X (support' X (by simp only [List.mem_cons]; exact Or.inr h))
      have tailValid := (valid_extend _ _).mpr ⟨restValid, valid⟩
      simp only [RuleInterface.contractList]
      apply ih (fun S h => support' S (List.mem_cons_of_mem _ h))
      simpa [AllChildren, Communication.assembler] using
        And.intro (ec_strict _ _ _ _ tailValid) ht

theorem finish_strict (valid : ValidComponents G)
    (donors : (i : Fin 2) → CKTree sigma (Data sigma) ((p).donorBoundary i))
    (hd : ∀ i, AllNodes (theory sigma).Admits (donors i))
    (plan : Plan m (fun _ => 0)) : AllNodes (theory sigma).Admits ((r).finish donors plan) := by
  unfold RuleInterface.finish
  apply contractList_strict c key m positive G extra support
    (p).terminal (p).terminalComponents.toList _
    (valid_terminal p (problem_wellFormed c m positive G extra support valid))
  simpa using interpret_strict c key m positive G extra support valid donors hd plan

/-- The strict registry is a separate exact gate; the assembly envelope is not evidence. -/
noncomputable def checkedFinish [DecidableEq (Hypersequent sigma)]
    (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CKTree sigma (Data sigma) ((p).donorBoundary i))
    (complete : ∀ i, (donors i).IsComplete) (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish donors plan)) : CheckedDerivation P (p).terminal :=
  CompleteQuotation.checkedOfComplete P ((r).finish donors plan) registered
    ((r).finish_complete donors complete plan)

theorem checkedFinish_realize [DecidableEq (Hypersequent sigma)]
    (P : EquippedPresentation (theory sigma))
    (donors : (i : Fin 2) → CKTree sigma (Data sigma) ((p).donorBoundary i))
    (complete : ∀ i, (donors i).IsComplete) (plan : Plan m (fun _ => 0))
    (registered : LocallyAdmittedTree P ((r).finish donors plan)) :
    (checkedFinish c key m positive G extra support P donors complete plan registered).realize =
      (r).finish donors plan := CompleteQuotation.quote_realize P _ _ _
end Compiler

#check @finish_strict
#print axioms finish_strict
#print axioms checkedFinish_realize
#print axioms problem_wellFormed
end Potkin.Research.HLJContraction

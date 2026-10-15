import Potkin.Research.RecursiveSysComSourceFilling

/-!
# Actual recursively prepared Sys(com) instances

The three-origin nested source is the earlier X/Y class. The four-origin
balanced source is a different member of the recursive grammar, with three
genuine bottom instances and Cartesian translation at both child phases.
-/
namespace Potkin.Research.RecursiveSysComExamples
open D3SourceEncoding D3SourceAdequacy RecursiveSysComSource
abbrev Formula := D3SourceEncoding.Formula
abbrev Context := D3SourceEncoding.Context
abbrev Sequent := D3SourceEncoding.Sequent
abbrev Parameters := D3SourceEncoding.Parameters

abbrev PairOrigins := PUnit ⊕ PUnit
abbrev BalancedOrigins := PairOrigins ⊕ PairOrigins
abbrev NestedOrigins := PairOrigins ⊕ PUnit

def parameters (A B : Formula) : Parameters := ⟨{A}, {B}⟩
def gammaL (A B C : Formula) : Context := {A} + {A} + {B} + {C}
def gammaR (A B C : Formula) : Context := {A} + {B} + {B} + {C}
def common (A B C : Formula) (pi : Context) : Sequent :=
  ⟨{A} + {A} + {B} + {B} + {C}, pi⟩

def childSpecL (A B C : Formula) (pi : Context) (single : pi.card ≤ 1) :
    TopSpec 0 (parameters A B) (common A B C pi) where
  gamma := gammaL A B C
  pi := pi
  single := single
  output := by simp [topOutput, parameters, gammaL, common, add_assoc, add_comm, add_left_comm,
    Multiset.cons_swap]

def childSpecR (A B C : Formula) (pi : Context) (single : pi.card ≤ 1) :
    TopSpec 1 (parameters A B) (common A B C pi) where
  gamma := gammaR A B C
  pi := pi
  single := single
  output := by simp [topOutput, parameters, gammaR, common, add_assoc, add_comm, add_left_comm,
    Multiset.cons_swap]

def childBounds (A B C : Formula) (pi : Context) (single : pi.card ≤ 1) : PairOrigins → Sequent :=
  Sum.elim (fun _ => (childSpecL A B C pi single).input)
    (fun _ => (childSpecR A B C pi single).input)

def child (bottomKey uid : Nat) (A B C : Formula) (pi : Context) (single : pi.card ≤ 1) :
    Source (common A B C pi) PairOrigins (childBounds A B C pi single) :=
  Source.phase bottomKey uid (parameters A B) (common A B C pi) single
    (.leaf _) (.leaf _) (fun o => match o with | .inl _ => bottomKey + 1 | .inr _ => bottomKey + 3)
    (fun _ => childSpecL A B C pi single) (fun _ => childSpecR A B C pi single)

def outerLeftSpec (A B C : Formula) (pi : Context) (single : pi.card ≤ 1) :
    (o : PairOrigins) → TopSpec 0 (parameters A B) (childBounds A B C pi single o)
  | .inl _ =>
      ⟨{A} + {A} + {A} + {C}, pi, single, by
        simp [topOutput, topInput, parameters, childBounds, TopSpec.input, childSpecL,
          gammaL, add_assoc, add_comm, add_left_comm, Multiset.cons_swap]⟩
  | .inr _ =>
      ⟨{A} + {B} + {B} + {C}, pi, single, by
        simp [topOutput, topInput, parameters, childBounds, TopSpec.input, childSpecR,
          gammaR, add_assoc, add_comm, add_left_comm, Multiset.cons_swap]⟩

def outerRightSpec (A B C : Formula) (pi : Context) (single : pi.card ≤ 1) :
    (o : PairOrigins) → TopSpec 1 (parameters A B) (childBounds A B C pi single o)
  | .inl _ =>
      ⟨{A} + {A} + {B} + {C}, pi, single, by
        simp [topOutput, topInput, parameters, childBounds, TopSpec.input, childSpecL,
          gammaL, add_assoc, add_comm, add_left_comm, Multiset.cons_swap]⟩
  | .inr _ =>
      ⟨{B} + {B} + {B} + {C}, pi, single, by
        simp [topOutput, topInput, parameters, childBounds, TopSpec.input, childSpecR,
          gammaR, add_assoc, add_comm, add_left_comm, Multiset.cons_swap]⟩

def balancedBounds (A B C : Formula) : BalancedOrigins → Sequent :=
  Sum.elim (fun o => (outerLeftSpec A B C {C} (by simp) o).input)
    (fun o => (outerRightSpec A B C {C} (by simp) o).input)

def balanced (A B C : Formula) :
    Source (common A B C {C}) BalancedOrigins (balancedBounds A B C) :=
  .phase 1000 0 (parameters A B) (common A B C {C}) (by simp [common])
    (child 1100 1 A B C {C} (by simp)) (child 1200 2 A B C {C} (by simp))
    (fun o => match o with
      | .inl (.inl _) => 1001 | .inl (.inr _) => 1002
      | .inr (.inl _) => 1003 | .inr (.inr _) => 1004)
    (outerLeftSpec A B C {C} (by simp)) (outerRightSpec A B C {C} (by simp))

def nestedBounds (A B C : Formula) : NestedOrigins → Sequent :=
  Sum.elim (fun o => (outerLeftSpec A B C {A} (by simp) o).input)
    (fun _ => (childSpecR A B C {A} (by simp)).input)

/-- The old X/Y preparation, now an instance of the unbounded source grammar. -/
def nested (A B C : Formula) :
    Source (common A B C {A}) NestedOrigins (nestedBounds A B C) :=
  .phase 100 0 (parameters A B) (common A B C {A}) (by simp [common])
    (child 101 1 A B C {A} (by simp)) (.leaf _)
    (fun o => match o with
      | .inl (.inl _) => 103 | .inl (.inr _) => 105 | .inr _ => 106)
    (outerLeftSpec A B C {A} (by simp)) (fun _ => childSpecR A B C {A} (by simp))

theorem balanced_scoped (A B C : Formula) : WellScoped (balanced A B C) := by
  simp [balanced, child, WellScoped, Source.owners, List.disjoint_left]

theorem nested_scoped (A B C : Formula) : WellScoped (nested A B C) := by
  simp [nested, child, WellScoped, Source.owners, List.disjoint_left]

theorem balanced_correct (A B C : Formula) : SourceCorrect (balanced A B C).erase :=
  (balanced A B C).correct (balanced_scoped A B C)

theorem nested_correct (A B C : Formula) : SourceCorrect (nested A B C).erase :=
  (nested A B C).correct (nested_scoped A B C)

theorem balanced_prepared (A B C : Formula) :
    PreparedSysComSource.Prepared (events (balanced A B C).erase []) :=
  (balanced A B C).prepared (balanced_scoped A B C)

theorem nested_prepared (A B C : Formula) :
    PreparedSysComSource.Prepared (events (nested A B C).erase []) :=
  (nested A B C).prepared (nested_scoped A B C)

theorem balanced_origins (A B C : Formula) : (balanced A B C).origins.length = 4 := rfl
theorem nested_origins (A B C : Formula) : (nested A B C).origins.length = 3 := rfl

def balancedWord (A B C : Formula) : BalancedOrigins → List Formula
  | .inl (.inl _) => [A,A,A,A]
  | .inl (.inr _) => [A,A,B,B]
  | .inr (.inl _) => [A,A,B,B]
  | .inr (.inr _) => [B,B,B,B]

theorem balanced_donor_boundary (A B C : Formula) (o : BalancedOrigins) :
    (⟨PreparedSysComSource.wordContext C (balancedWord A B C o), {C}⟩ : Sequent) =
      balancedBounds A B C o := by
  cases o with
  | inl o => cases o <;> simp [balancedBounds, outerLeftSpec, TopSpec.input, topInput,
      parameters, balancedWord, PreparedSysComSource.wordContext, add_assoc, add_comm, add_left_comm,
      Multiset.cons_swap]
  | inr o => cases o <;> simp [balancedBounds, outerRightSpec, TopSpec.input, topInput,
      parameters, balancedWord, PreparedSysComSource.wordContext, add_assoc, add_comm, add_left_comm,
      Multiset.cons_swap]

def balancedDonor (A B C : Formula) (o : BalancedOrigins) : Diagram (balancedBounds A B C o) :=
  PreparedSysComSource.transport (balanced_donor_boundary A B C o)
    (PreparedSysComSource.wordTree 2000 C (balancedWord A B C o))

theorem balancedDonor_ordinary (A B C : Formula) (o : BalancedOrigins) :
    PreparedSysComSource.Ordinary (balancedDonor A B C o) :=
  PreparedSysComSource.ordinary_transport _ _ (PreparedSysComSource.wordTree_ordinary _ _ _)

def balancedClosed (A B C : Formula) : Diagram (common A B C {C}) :=
  (balanced A B C).filled (balancedDonor A B C)

theorem balancedClosed_correct (A B C : Formula) : CompleteSourceCorrect (balancedClosed A B C) :=
  (balanced A B C).filled_correct (balanced_scoped A B C) _ (balancedDonor_ordinary A B C)

theorem balancedClosed_prepared (A B C : Formula) :
    PreparedSysComSource.Prepared (events (balancedClosed A B C) []) :=
  (balanced A B C).filled_prepared (balanced_scoped A B C) _ (balancedDonor_ordinary A B C)

def nestedWord (A B C : Formula) : NestedOrigins → List Formula
  | .inl (.inl _) => [C,A,A,A]
  | .inl (.inr _) => [C,B,B,A]
  | .inr _ => [C,B,B,B]

theorem nested_donor_boundary (A B C : Formula) (o : NestedOrigins) :
    (⟨PreparedSysComSource.wordContext A (nestedWord A B C o), {A}⟩ : Sequent) =
      nestedBounds A B C o := by
  cases o with
  | inl o => cases o <;> simp [nestedBounds, outerLeftSpec, TopSpec.input, topInput,
      parameters, nestedWord, PreparedSysComSource.wordContext, add_assoc, add_comm, add_left_comm,
      Multiset.cons_swap]
  | inr o => simp [nestedBounds, childSpecR, gammaR, TopSpec.input, topInput,
      parameters, nestedWord, PreparedSysComSource.wordContext, add_assoc, add_comm, add_left_comm,
      Multiset.cons_swap]

def nestedDonor (A B C : Formula) (o : NestedOrigins) : Diagram (nestedBounds A B C o) :=
  PreparedSysComSource.transport (nested_donor_boundary A B C o)
    (PreparedSysComSource.wordTree
      (match o with | .inl (.inl _) => 10 | .inl (.inr _) => 20 | .inr _ => 30)
      A (nestedWord A B C o))

theorem nestedDonor_ordinary (A B C : Formula) (o : NestedOrigins) :
    PreparedSysComSource.Ordinary (nestedDonor A B C o) :=
  PreparedSysComSource.ordinary_transport _ _ (PreparedSysComSource.wordTree_ordinary _ _ _)

def nestedClosed (A B C : Formula) : Diagram (common A B C {A}) :=
  (nested A B C).filled (nestedDonor A B C)

theorem nestedClosed_correct (A B C : Formula) : CompleteSourceCorrect (nestedClosed A B C) :=
  (nested A B C).filled_correct (nested_scoped A B C) _ (nestedDonor_ordinary A B C)

theorem nestedClosed_prepared (A B C : Formula) :
    PreparedSysComSource.Prepared (events (nestedClosed A B C) []) :=
  (nested A B C).filled_prepared (nested_scoped A B C) _ (nestedDonor_ordinary A B C)

#print axioms balanced_correct
#print axioms balanced_prepared
#print axioms balancedDonor_ordinary
#print axioms balancedClosed_correct
#print axioms balancedClosed_prepared
#print axioms nestedClosed_correct

end Potkin.Research.RecursiveSysComExamples

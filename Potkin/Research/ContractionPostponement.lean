import Potkin.Research.ContractionBoundaries
import Potkin.CompleteQuotation

/-!
# Parameterized native contraction postponement

No HLJ+com/EW/EC schema is installed in the present native stock. `RuleInterface`
therefore records the exact supplied instances, their whole ordered boundaries,
and actual proof-theory admission. It is NOT an admission theorem. An immutable
finite registry is required only for the finitely reached compiled tree; the
interface does not require infinitely many context extensions in that registry.

The output is a native CKTree and, after exact finite registration, a quotation
checked by the existing public checker. Donors stay opaque, and repeated uses
are physical copies. Plan metadata is not a replacement proof carrier.
-/

namespace Potkin.Research.ContractionPostponement

open ContractionPlans ContractionBoundaries
open scoped BigOperators
universe u v w
variable {sigma : Signature.{u, v}} {D : Type w} {n : Nat}
variable {T : ProofTheory sigma D}

structure RuleInterface (T : ProofTheory sigma D) (p : Problem sigma n) where
  rule : Multiset (Sequent sigma) → LocalOccurrence sigma D
  rule_premises : ∀ K, (rule K).shape.premises =
    List.ofFn (fun i => extend K (Hypersequent.singleton (p.C i)))
  rule_conclusion : ∀ K, (rule K).shape.conclusion = extend K p.H
  rule_admitted : ∀ K, T.Admits (rule K)
  rule_incidence : ∀ K, (rule K).incidence.isSome
  ew : Hypersequent sigma → Sequent sigma → LocalOccurrence sigma D
  ew_kind : ∀ G S, (ew G S).kind = .structural
  ew_premises : ∀ G S, (ew G S).shape.premises = [G]
  ew_conclusion : ∀ G S, (ew G S).shape.conclusion = extend {S} G
  ew_admitted : ∀ G S, T.Admits (ew G S)
  ew_incidence : ∀ G S, (ew G S).incidence.isSome
  ec : (G : Hypersequent sigma) → (S : Sequent sigma) → S ∈ G.components →
    LocalOccurrence sigma D
  ec_kind : ∀ G S h, (ec G S h).kind = .structural
  ec_premises : ∀ G S h, (ec G S h).shape.premises = [extend {S} G]
  ec_conclusion : ∀ G S h, (ec G S h).shape.conclusion = G
  ec_admitted : ∀ G S h, T.Admits (ec G S h)
  ec_incidence : ∀ G S h, (ec G S h).incidence.isSome

mutual
def AllNodes (R : LocalOccurrence sigma D → Prop) :
    {G : Hypersequent sigma} → CKTree sigma D G → Prop
  | _, .interface _ => True
  | _, .ordinary o children => R o ∧ AllChildren R children
def AllChildren (R : LocalOccurrence sigma D → Prop) :
    {Gs : List (Hypersequent sigma)} → CKChildren sigma D Gs → Prop
  | _, .nil => True
  | _, .cons head tail => AllNodes R head ∧ AllChildren R tail
end

@[simp] theorem degree_transport {G H : Hypersequent sigma} (h : G = H)
    (tree : CKTree sigma D G) : (h ▸ tree).degree = tree.degree := by cases h; rfl

@[simp] theorem all_transport {G H : Hypersequent sigma} (h : G = H)
    (tree : CKTree sigma D G) (R : LocalOccurrence sigma D → Prop) :
    AllNodes R (h ▸ tree) ↔ AllNodes R tree := by cases h; rfl

@[simp] theorem complete_transport {G H : Hypersequent sigma} (h : G = H)
    (tree : CKTree sigma D G) : (h ▸ tree).IsComplete ↔ tree.IsComplete := by cases h; rfl

@[simp] theorem children_degree_transport {Gs Hs : List (Hypersequent sigma)} (h : Gs = Hs)
    (children : CKChildren sigma D Gs) : (h ▸ children).degree = children.degree := by
  cases h; rfl

@[simp] theorem children_all_transport {Gs Hs : List (Hypersequent sigma)} (h : Gs = Hs)
    (children : CKChildren sigma D Gs) (R : LocalOccurrence sigma D → Prop) :
    AllChildren R (h ▸ children) ↔ AllChildren R children := by cases h; rfl

@[simp] theorem children_complete_transport {Gs Hs : List (Hypersequent sigma)} (h : Gs = Hs)
    (children : CKChildren sigma D Gs) :
    (h ▸ children).IsComplete ↔ children.IsComplete := by cases h; rfl

def node {Gs : List (Hypersequent sigma)} {G : Hypersequent sigma}
    (o : LocalOccurrence sigma D) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (children : CKChildren sigma D Gs) : CKTree sigma D G :=
  hc ▸ CKTree.ordinary o (hp.symm ▸ children)

@[simp] theorem node_degree {Gs : List (Hypersequent sigma)} {G : Hypersequent sigma}
    (o : LocalOccurrence sigma D) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (children : CKChildren sigma D Gs) :
    (node o hp hc children).degree = children.degree + 1 := by
  subst Gs; subst G; rfl

@[simp] theorem node_all {Gs : List (Hypersequent sigma)} {G : Hypersequent sigma}
    (o : LocalOccurrence sigma D) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (children : CKChildren sigma D Gs)
    (R : LocalOccurrence sigma D → Prop) :
    AllNodes R (node o hp hc children) ↔ R o ∧ AllChildren R children := by
  subst Gs; subst G; rfl

@[simp] theorem node_complete {Gs : List (Hypersequent sigma)} {G : Hypersequent sigma}
    (o : LocalOccurrence sigma D) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (children : CKChildren sigma D Gs) :
    (node o hp hc children).IsComplete ↔ children.IsComplete := by
  subst Gs; subst G; rfl

def familyChildren : {k : Nat} → (B : Fin k → Hypersequent sigma) →
    ((i : Fin k) → CKTree sigma D (B i)) → CKChildren sigma D (List.ofFn B)
  | 0, _, _ => .nil
  | k + 1, B, f =>
      (show List.ofFn B = B 0 :: List.ofFn (fun i => B i.succ)
        from List.ofFn_succ).symm ▸
        CKChildren.cons (f 0) (familyChildren (fun i => B i.succ) (fun i => f i.succ))

private theorem univ_fin_succ (k : Nat) :
    (Finset.univ : Finset (Fin (k + 1))) =
      insert 0 ((Finset.univ : Finset (Fin k)).image Fin.succ) := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

theorem family_sum_succ {A : Type _} [AddCommMonoid A] (k : Nat) (f : Fin (k + 1) → A) :
    (∑ i, f i) = f 0 + ∑ i : Fin k, f i.succ := by
  classical
  rw [univ_fin_succ, Finset.sum_insert (by simp), Finset.sum_image]
  intro a _ b _ h
  exact Fin.succ_inj.mp h

theorem family_product_succ {A : Type _} [CommMonoid A] (k : Nat) (f : Fin (k + 1) → A) :
    (∏ i, f i) = f 0 * ∏ i : Fin k, f i.succ := by
  classical
  rw [univ_fin_succ, Finset.prod_insert (by simp), Finset.prod_image]
  intro a _ b _ h
  exact Fin.succ_inj.mp h

@[simp] theorem family_degree : {k : Nat} → (B : Fin k → Hypersequent sigma) →
    (f : (i : Fin k) → CKTree sigma D (B i)) →
    (familyChildren B f).degree = ∑ i, (f i).degree
  | 0, _, _ => by simp [familyChildren, CKChildren.degree]
  | k + 1, B, f => by
      simp [familyChildren, CKChildren.degree, family_degree, family_sum_succ]

@[simp] theorem family_all : {k : Nat} → (B : Fin k → Hypersequent sigma) →
    (f : (i : Fin k) → CKTree sigma D (B i)) → (R : LocalOccurrence sigma D → Prop) →
    AllChildren R (familyChildren B f) ↔ ∀ i, AllNodes R (f i)
  | 0, _, _, _ => by simp [familyChildren, AllChildren]
  | k + 1, B, f, R => by
      simp [familyChildren, AllChildren, family_all, Fin.forall_fin_succ]

@[simp] theorem family_complete : {k : Nat} → (B : Fin k → Hypersequent sigma) →
    (f : (i : Fin k) → CKTree sigma D (B i)) →
    (familyChildren B f).IsComplete ↔ ∀ i, (f i).IsComplete
  | 0, _, _ => by simp [familyChildren, CKChildren.IsComplete]
  | k + 1, B, f => by
      simp [familyChildren, CKChildren.IsComplete, family_complete, Fin.forall_fin_succ]

namespace RuleInterface

variable {p : Problem sigma n} (r : RuleInterface T p)

def weaken (G : Hypersequent sigma) (S : Sequent sigma) (tree : CKTree sigma D G) :
    CKTree sigma D (extend {S} G) :=
  node (r.ew G S) (r.ew_premises G S) (r.ew_conclusion G S) (.cons tree .nil)

def weakenList (r : RuleInterface T p) (G : Hypersequent sigma) : (added : List (Sequent sigma)) →
    CKTree sigma D G → CKTree sigma D (extend (added : Multiset (Sequent sigma)) G)
  | [], tree => (extend_zero G).symm ▸ tree
  | S :: rest, tree => by
      have equality : extend {S} (extend (rest : Multiset (Sequent sigma)) G) =
          extend ((S :: rest : List (Sequent sigma)) : Multiset (Sequent sigma)) G := by
        apply Hypersequent.ext
        change {S} + ((rest : Multiset (Sequent sigma)) + G.components) =
          ({S} + (rest : Multiset (Sequent sigma))) + G.components
        exact (add_assoc _ _ _).symm
      exact equality ▸ r.weaken _ S (r.weakenList G rest tree)

@[simp] theorem weakenList_degree (G : Hypersequent sigma)
    (added : List (Sequent sigma)) (tree : CKTree sigma D G) :
    (r.weakenList G added tree).degree = tree.degree + added.length := by
  induction added with
  | nil => simp [weakenList]
  | cons S rest ih => simp [weakenList, weaken, CKChildren.degree, ih, Nat.add_assoc]

theorem weakenList_all (R : LocalOccurrence sigma D → Prop)
    (hew : ∀ G S, R (r.ew G S)) (G : Hypersequent sigma)
    (added : List (Sequent sigma)) (tree : CKTree sigma D G) (ht : AllNodes R tree) :
    AllNodes R (r.weakenList G added tree) := by
  induction added with
  | nil => simpa [weakenList] using ht
  | cons S rest ih => simpa [weakenList, weaken, AllChildren] using And.intro (hew _ S) ih

theorem weakenList_complete (G : Hypersequent sigma) (added : List (Sequent sigma))
    (tree : CKTree sigma D G) (ht : tree.IsComplete) :
    (r.weakenList G added tree).IsComplete := by
  induction added with
  | nil => simpa [weakenList] using ht
  | cons S rest ih => simpa [weakenList, weaken, CKChildren.IsComplete] using ih

noncomputable def stopTree (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (alpha : State n) (i : Fin n) (threshold : p.m i ≤ alpha i)
    (bounded : mass alpha ≤ quota p.m) : CKTree sigma D (p.boundary alpha bounded) := by
  have equality : extend ((p.stopComponents alpha i).toList : Multiset (Sequent sigma))
      (p.donorBoundary i) =
      p.boundary alpha bounded := by
    apply Hypersequent.ext
    rw [extend_components, Multiset.coe_toList]
    exact p.stop_components_exact alpha i threshold
  exact equality ▸ r.weakenList (p.donorBoundary i) (p.stopComponents alpha i).toList (donors i)

@[simp] theorem stopTree_degree (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (alpha : State n) (i : Fin n) (threshold : p.m i ≤ alpha i)
    (bounded : mass alpha ≤ quota p.m) :
    (r.stopTree donors alpha i threshold bounded).degree =
      (donors i).degree + p.stopWeight alpha i := by
  simp [stopTree, p.stop_weight_exact alpha i threshold]

noncomputable def interpret (r : RuleInterface T p)
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i)) :
    {alpha : State n} → (plan : Plan p.m alpha) → CKTree sigma D (p.boundary alpha plan.bounded)
  | alpha, .stop i threshold bounded => r.stopTree donors alpha i threshold bounded
  | alpha, .next before children =>
      node (r.rule (p.common alpha))
        ((r.rule_premises _).trans (by
          apply congrArg List.ofFn
          funext i
          exact (p.boundary_child alpha before i).symm))
        ((r.rule_conclusion _).trans (p.boundary_continue alpha before).symm)
        (familyChildren (fun i => p.boundary (bump alpha i) (children i).bounded)
          (fun i => r.interpret donors (children i)))

theorem interpret_all (R : LocalOccurrence sigma D → Prop)
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (hd : ∀ i, AllNodes R (donors i)) (hew : ∀ G S, R (r.ew G S))
    (hr : ∀ K, R (r.rule K)) {alpha : State n} (plan : Plan p.m alpha) :
    AllNodes R (r.interpret donors plan) := by
  induction plan with
  | stop i threshold bounded =>
      simpa [interpret, stopTree] using
        r.weakenList_all R hew (p.donorBoundary i) (p.stopComponents _ i).toList (donors i) (hd i)
  | next before children ih => simp [interpret, hr, ih]

theorem interpret_complete (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (hd : ∀ i, (donors i).IsComplete) {alpha : State n} (plan : Plan p.m alpha) :
    (r.interpret donors plan).IsComplete := by
  induction plan with
  | stop i threshold bounded =>
      simpa [interpret, stopTree] using
        r.weakenList_complete (p.donorBoundary i) (p.stopComponents _ i).toList (donors i) (hd i)
  | next before children ih => simp [interpret, ih]

theorem interpret_degree (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    {alpha : State n} (plan : Plan p.m alpha) :
    (r.interpret donors plan).degree =
      plan.nodes (fun alpha i => (donors i).degree + p.stopWeight alpha i) := by
  induction plan with
  | stop i threshold bounded => simp [interpret, Plan.nodes]
  | next before children ih => simp [interpret, Plan.nodes, ih, Nat.add_comm]

/-- Exact logical-Cut/EC predicates are parameters. Neither rule kinds nor
names prove their absence. This theorem covers the pre-terminal compiler. -/
theorem interpret_avoids (bad : LocalOccurrence sigma D → Prop)
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (hd : ∀ i, AllNodes (fun o => ¬ bad o) (donors i))
    (hew : ∀ G S, ¬ bad (r.ew G S)) (hr : ∀ K, ¬ bad (r.rule K))
    {alpha : State n} (plan : Plan p.m alpha) :
    AllNodes (fun o => ¬ bad o) (r.interpret donors plan) :=
  r.interpret_all _ donors hd hew hr plan

mutual
theorem registered_all {P : EquippedPresentation T} : {G : Hypersequent sigma} →
    (tree : CKTree sigma D G) →
    AllNodes (fun o => o ∈ P.registry) tree ↔ LocallyAdmittedTree P tree
  | _, .interface _ => Iff.rfl
  | _, .ordinary _ children => by
      simp only [AllNodes, LocallyAdmittedTree, registered_children children]
theorem registered_children {P : EquippedPresentation T} :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma D Gs) →
    AllChildren (fun o => o ∈ P.registry) children ↔ LocallyAdmittedChildren P children
  | _, .nil => Iff.rfl
  | _, .cons head tail => by
      simp only [AllChildren, LocallyAdmittedChildren, registered_all head,
        registered_children tail]
end

/-- Finite reached-instance registration is checked explicitly; there is no
silent cast from an abstract rule schema into an equipped presentation. -/
noncomputable def checkedInterpret [DecidableEq (Hypersequent sigma)]
    (P : EquippedPresentation T)
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (complete : ∀ i, (donors i).IsComplete) {alpha : State n} (plan : Plan p.m alpha)
    (registered : AllNodes (fun o => o ∈ P.registry) (r.interpret donors plan)) :
    CheckedDerivation P (p.boundary alpha plan.bounded) :=
  CompleteQuotation.checkedOfComplete P (r.interpret donors plan)
    ((registered_all _).mp registered) (r.interpret_complete donors complete plan)

def contractList (r : RuleInterface T p) (G : Hypersequent sigma) : (removed : List (Sequent sigma)) →
    (∀ S ∈ removed, S ∈ G.components) →
    CKTree sigma D (extend (removed : Multiset (Sequent sigma)) G) → CKTree sigma D G
  | [], _, tree => extend_zero G ▸ tree
  | S :: rest, support, tree => by
      have hS : S ∈ (extend (rest : Multiset (Sequent sigma)) G).components :=
        Multiset.mem_add.mpr (Or.inr (support S (by simp)))
      have input : extend {S} (extend (rest : Multiset (Sequent sigma)) G) =
          extend ((S :: rest : List (Sequent sigma)) : Multiset (Sequent sigma)) G := by
        apply Hypersequent.ext
        change {S} + ((rest : Multiset (Sequent sigma)) + G.components) =
          ({S} + (rest : Multiset (Sequent sigma))) + G.components
        exact (add_assoc _ _ _).symm
      let contracted := node (r.ec _ S hS) (r.ec_premises _ S hS)
        (r.ec_conclusion _ S hS) (.cons (input.symm ▸ tree) .nil)
      exact r.contractList G rest (fun S h => support S (List.mem_cons_of_mem _ h)) contracted

theorem contractList_degree (G : Hypersequent sigma) (removed : List (Sequent sigma))
    (support : ∀ S ∈ removed, S ∈ G.components)
    (tree : CKTree sigma D (extend (removed : Multiset (Sequent sigma)) G)) :
    (r.contractList G removed support tree).degree = tree.degree + removed.length := by
  induction removed with
  | nil => simp [contractList]
  | cons S rest ih =>
      simp [contractList, ih, CKChildren.degree, Nat.add_assoc]
      omega

theorem contractList_all (R : LocalOccurrence sigma D → Prop)
    (hec : ∀ G S h, R (r.ec G S h)) (G : Hypersequent sigma)
    (removed : List (Sequent sigma)) (support : ∀ S ∈ removed, S ∈ G.components)
    (tree : CKTree sigma D (extend (removed : Multiset (Sequent sigma)) G))
    (ht : AllNodes R tree) : AllNodes R (r.contractList G removed support tree) := by
  induction removed with
  | nil => simpa [contractList] using ht
  | cons S rest ih =>
      simp only [contractList]
      apply ih (fun S h => support S (List.mem_cons_of_mem _ h))
      simpa [AllChildren] using And.intro (hec _ _ _) ht

theorem contractList_complete (G : Hypersequent sigma) (removed : List (Sequent sigma))
    (support : ∀ S ∈ removed, S ∈ G.components)
    (tree : CKTree sigma D (extend (removed : Multiset (Sequent sigma)) G))
    (ht : tree.IsComplete) : (r.contractList G removed support tree).IsComplete := by
  induction removed with
  | nil => simpa [contractList] using ht
  | cons S rest ih =>
      simp only [contractList]
      apply ih (fun S h => support S (List.mem_cons_of_mem _ h))
      simpa [CKChildren.IsComplete] using ht

theorem terminal_support (S : Sequent sigma) (h : S ∈ p.terminalComponents) :
    S ∈ p.terminal.components := by
  rcases Multiset.mem_add.mp h with he | hh
  · obtain ⟨i, _, hi⟩ := Multiset.mem_sum.mp he
    exact Multiset.mem_add.mpr (Or.inl (p.extra_support i S hi))
  · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_of_mem_nsmul hh))

noncomputable def finish (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0)) : CKTree sigma D p.terminal := by
  have hb : p.boundary (fun _ => 0) plan.bounded =
      extend (p.terminalComponents.toList : Multiset (Sequent sigma)) p.terminal := by
    apply Hypersequent.ext
    rw [extend_components, Multiset.coe_toList]
    exact p.terminal_boundary
  exact r.contractList p.terminal p.terminalComponents.toList
    (fun S h => terminal_support S (Multiset.mem_toList.mp h))
    (hb ▸ r.interpret donors plan)

theorem finish_degree (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0)) :
    (r.finish donors plan).degree =
      plan.nodes (fun alpha i => (donors i).degree + p.stopWeight alpha i) +
        (p.extras.card + (quota p.m - 1) * p.H.components.card) := by
  simp [finish, r.contractList_degree, r.interpret_degree, p.terminal_cost]

theorem finish_complete (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (complete : ∀ i, (donors i).IsComplete) (plan : Plan p.m (fun _ => 0)) :
    (r.finish donors plan).IsComplete := by
  unfold finish
  apply r.contractList_complete
  simpa using r.interpret_complete donors complete plan

theorem finish_all (R : LocalOccurrence sigma D → Prop)
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (hd : ∀ i, AllNodes R (donors i)) (hew : ∀ G S, R (r.ew G S))
    (hr : ∀ K, R (r.rule K)) (hec : ∀ G S h, R (r.ec G S h))
    (plan : Plan p.m (fun _ => 0)) : AllNodes R (r.finish donors plan) := by
  unfold finish
  apply r.contractList_all R hec
  simpa using r.interpret_all R donors hd hew hr plan

/-- Logical-Cut freedom survives the terminal EC queue as well, provided all
three supplied rule families avoid the exact logical-Cut predicate. -/
theorem finish_avoids (bad : LocalOccurrence sigma D → Prop)
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (hd : ∀ i, AllNodes (fun o => ¬ bad o) (donors i))
    (hew : ∀ G S, ¬ bad (r.ew G S)) (hr : ∀ K, ¬ bad (r.rule K))
    (hec : ∀ G S h, ¬ bad (r.ec G S h)) (plan : Plan p.m (fun _ => 0)) :
    AllNodes (fun o => ¬ bad o) (r.finish donors plan) :=
  r.finish_all _ donors hd hew hr hec plan

/-- This is an actual whole checked proof, conditional on registering exactly
its finite occurrences. The public checker retains its full native realization. -/
noncomputable def checkedFinish [DecidableEq (Hypersequent sigma)]
    (P : EquippedPresentation T)
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (complete : ∀ i, (donors i).IsComplete) (plan : Plan p.m (fun _ => 0))
    (registered : AllNodes (fun o => o ∈ P.registry) (r.finish donors plan)) :
    CheckedDerivation P p.terminal :=
  CompleteQuotation.checkedOfComplete P (r.finish donors plan)
    ((registered_all _).mp registered) (r.finish_complete donors complete plan)

theorem checkedFinish_realize [DecidableEq (Hypersequent sigma)]
    (P : EquippedPresentation T)
    (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (complete : ∀ i, (donors i).IsComplete) (plan : Plan p.m (fun _ => 0))
    (registered : AllNodes (fun o => o ∈ P.registry) (r.finish donors plan)) :
    (r.checkedFinish P donors complete plan registered).realize = r.finish donors plan :=
  CompleteQuotation.quote_realize P _ _ _

/-- Front end for native checked donors in the same exact immutable registry.
Reached structural instances must still pass the explicit registration gate. -/
noncomputable def compile [DecidableEq (Hypersequent sigma)] (P : EquippedPresentation T)
    (donors : (i : Fin n) → CheckedDerivation P (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0))
    (registered : AllNodes (fun o => o ∈ P.registry)
      (r.finish (fun i => (donors i).realize) plan)) : CheckedDerivation P p.terminal :=
  r.checkedFinish P (fun i => (donors i).realize)
    (fun i => (donors i).realizeIsComplete) plan registered

theorem compile_realize [DecidableEq (Hypersequent sigma)] (P : EquippedPresentation T)
    (donors : (i : Fin n) → CheckedDerivation P (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0))
    (registered : AllNodes (fun o => o ∈ P.registry)
      (r.finish (fun i => (donors i).realize) plan)) :
    (r.compile P donors plan registered).realize =
      r.finish (fun i => (donors i).realize) plan :=
  r.checkedFinish_realize P _ _ _ _

end RuleInterface
end Potkin.Research.ContractionPostponement

#check Potkin.Research.ContractionPostponement.RuleInterface.interpret_degree
#print axioms Potkin.Research.ContractionPostponement.RuleInterface.interpret_degree
#print axioms Potkin.Research.ContractionPostponement.RuleInterface.interpret_avoids
#print axioms Potkin.Research.ContractionPostponement.RuleInterface.interpret_complete
#print axioms Potkin.Research.ContractionPostponement.RuleInterface.finish_degree
#print axioms Potkin.Research.ContractionPostponement.RuleInterface.finish_avoids
#print axioms Potkin.Research.ContractionPostponement.RuleInterface.checkedFinish_realize
#print axioms Potkin.Research.ContractionPostponement.RuleInterface.compile_realize

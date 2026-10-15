import Potkin.Research.ContractionPostponement
import Potkin.AllHoleFilling

/-!
# Construction-history donor assignment for the native compiler

Labels are functions on existing physical interfaces, carrying a donor index
and a boundary equality. They are not inferred from boundary equality, and
are not another proof or context carrier. The same rule-instance choices are
used on the open and filled sides of every equation.
-/
namespace Potkin.Research.ContractionDonorFilling
open ContractionPlans ContractionBoundaries ContractionPostponement
universe u v w
variable {sigma : Signature.{u, v}} {D : Type w} {n : Nat}

abbrev Labels (B : Fin n → Hypersequent sigma) {G : Hypersequent sigma}
    (tree : CKTree sigma D G) :=
  (h : tree.LeafOccurrence) → {i : Fin n // B i = tree.leafBoundary h}

abbrev ChildLabels (B : Fin n → Hypersequent sigma) {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma D Gs) :=
  (h : children.LeafOccurrence) → {i : Fin n // B i = children.leafBoundary h}

variable {B : Fin n → Hypersequent sigma}

def supply {G : Hypersequent sigma} {tree : CKTree sigma D G}
    (labels : Labels B tree) (donors : (i : Fin n) → CKTree sigma D (B i)) : tree.LeafAssignment :=
  fun h => (labels h).2 ▸ donors (labels h).1

def childSupply {Gs : List (Hypersequent sigma)} {children : CKChildren sigma D Gs}
    (labels : ChildLabels B children) (donors : (i : Fin n) → CKTree sigma D (B i)) :
    children.LeafAssignment := fun h => (labels h).2 ▸ donors (labels h).1

def plug {G : Hypersequent sigma} (tree : CKTree sigma D G) (labels : Labels B tree)
    (donors : (i : Fin n) → CKTree sigma D (B i)) := tree.fillAssignment (supply labels donors)

def plugChildren {Gs : List (Hypersequent sigma)} (children : CKChildren sigma D Gs)
    (labels : ChildLabels B children) (donors : (i : Fin n) → CKTree sigma D (B i)) :=
  children.fillAssignment (childSupply labels donors)

def castLabels {G H : Hypersequent sigma} (equal : G = H)
    (tree : CKTree sigma D G) (labels : Labels B tree) : Labels B (equal ▸ tree) := by
  cases equal; exact labels

@[simp] theorem plug_cast {G H : Hypersequent sigma} (equal : G = H)
    (tree : CKTree sigma D G) (labels : Labels B tree)
    (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plug (equal ▸ tree) (castLabels equal tree labels) donors = equal ▸ plug tree labels donors := by
  cases equal; rfl

def childCastLabels {Gs Hs : List (Hypersequent sigma)} (equal : Gs = Hs)
    (children : CKChildren sigma D Gs) (labels : ChildLabels B children) :
    ChildLabels B (equal ▸ children) := by cases equal; exact labels

@[simp] theorem plugChildren_cast {Gs Hs : List (Hypersequent sigma)} (equal : Gs = Hs)
    (children : CKChildren sigma D Gs) (labels : ChildLabels B children)
    (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plugChildren (equal ▸ children) (childCastLabels equal children labels) donors =
      equal ▸ plugChildren children labels donors := by cases equal; rfl

def nilLabels : ChildLabels B (.nil : CKChildren sigma D []) := fun h => nomatch h

def consLabels {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
    {head : CKTree sigma D G} {tail : CKChildren sigma D Gs}
    (headLabels : Labels B head) (tailLabels : ChildLabels B tail) :
    ChildLabels B (.cons head tail) := fun h => match h with
  | .inl h => headLabels h
  | .inr h => tailLabels h

@[simp] theorem plugChildren_nil (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plugChildren .nil nilLabels donors = .nil := rfl

@[simp] theorem plugChildren_cons {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
    (head : CKTree sigma D G) (tail : CKChildren sigma D Gs)
    (headLabels : Labels B head) (tailLabels : ChildLabels B tail)
    (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plugChildren (.cons head tail) (consLabels headLabels tailLabels) donors =
      .cons (plug head headLabels donors) (plugChildren tail tailLabels donors) := rfl

def nodeLabels {Gs : List (Hypersequent sigma)} {G : Hypersequent sigma}
    (o : LocalOccurrence sigma D) (hp : o.shape.premises = Gs) (hc : o.shape.conclusion = G)
    (children : CKChildren sigma D Gs) (labels : ChildLabels B children) :
    Labels B (node o hp hc children) := by subst Gs; subst G; exact labels

@[simp] theorem plug_node {Gs : List (Hypersequent sigma)} {G : Hypersequent sigma}
    (o : LocalOccurrence sigma D) (hp : o.shape.premises = Gs) (hc : o.shape.conclusion = G)
    (children : CKChildren sigma D Gs) (labels : ChildLabels B children)
    (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plug (node o hp hc children) (nodeLabels o hp hc children labels) donors =
      node o hp hc (plugChildren children labels donors) := by subst Gs; subst G; rfl

def familyLabels : {k : Nat} → (bounds : Fin k → Hypersequent sigma) →
    (trees : (i : Fin k) → CKTree sigma D (bounds i)) →
    ((i : Fin k) → Labels B (trees i)) → ChildLabels B (familyChildren bounds trees)
  | 0, _, _, _ => nilLabels
  | k + 1, bounds, trees, labels =>
      childCastLabels (show List.ofFn bounds = bounds 0 :: List.ofFn (fun i => bounds i.succ)
        from List.ofFn_succ).symm _
        (consLabels (labels 0) (familyLabels _ _ (fun i => labels i.succ)))

@[simp] theorem plug_family : {k : Nat} → (bounds : Fin k → Hypersequent sigma) →
    (trees : (i : Fin k) → CKTree sigma D (bounds i)) →
    (labels : (i : Fin k) → Labels B (trees i)) →
    (donors : (i : Fin n) → CKTree sigma D (B i)) →
    plugChildren (familyChildren bounds trees) (familyLabels bounds trees labels) donors =
      familyChildren bounds (fun i => plug (trees i) (labels i) donors)
  | 0, _, _, _, _ => rfl
  | k + 1, bounds, trees, labels, donors => by
      simp only [familyLabels, familyChildren, plugChildren_cast, plugChildren_cons, plug_family]

def boxLabels (i : Fin n) : Labels B (.interface (InstanceData := D) (B i)) := fun _ => ⟨i, rfl⟩

@[simp] theorem plug_box (i : Fin n) (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plug (.interface (B i)) (boxLabels i) donors = donors i := rfl

namespace RuleInterface
variable {T : ProofTheory sigma D} {p : Problem sigma n} (r : ContractionPostponement.RuleInterface T p)

def weakenLabels (G : Hypersequent sigma) (S : Sequent sigma)
    (tree : CKTree sigma D G) (labels : Labels B tree) : Labels B (r.weaken G S tree) :=
  nodeLabels _ _ _ _ (consLabels labels nilLabels)

@[simp] theorem plug_weaken (G : Hypersequent sigma) (S : Sequent sigma)
    (tree : CKTree sigma D G) (labels : Labels B tree)
    (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plug (r.weaken G S tree) (weakenLabels r G S tree labels) donors =
      r.weaken G S (plug tree labels donors) := by
  simp only [ContractionPostponement.RuleInterface.weaken, weakenLabels, plug_node,
    plugChildren_cons, plugChildren_nil]

def weakenListLabels (G : Hypersequent sigma) : (added : List (Sequent sigma)) →
    (tree : CKTree sigma D G) → Labels B tree → Labels B (r.weakenList G added tree)
  | [], tree, labels => castLabels (extend_zero G).symm tree labels
  | S :: rest, tree, labels => by
      have equal : extend {S} (extend (rest : Multiset (Sequent sigma)) G) =
          extend ((S :: rest : List (Sequent sigma)) : Multiset (Sequent sigma)) G := by
        apply Hypersequent.ext
        exact (add_assoc _ _ _).symm
      exact castLabels equal _ (weakenLabels r _ S _ (weakenListLabels G rest tree labels))

@[simp] theorem plug_weakenList (G : Hypersequent sigma) (added : List (Sequent sigma))
    (tree : CKTree sigma D G) (labels : Labels B tree)
    (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plug (r.weakenList G added tree) (weakenListLabels r G added tree labels) donors =
      r.weakenList G added (plug tree labels donors) := by
  induction added with
  | nil => exact plug_cast (extend_zero G).symm tree labels donors
  | cons S rest ih =>
      simp only [ContractionPostponement.RuleInterface.weakenList, weakenListLabels,
        plug_cast, plug_weaken, ih]

noncomputable def stopLabels (alpha : State n) (i : Fin n) (threshold : p.m i ≤ alpha i)
    (bounded : mass alpha ≤ quota p.m) :
    Labels p.donorBoundary (r.stopTree (fun j => .interface (p.donorBoundary j)) alpha i threshold bounded) := by
  have equal : extend ((p.stopComponents alpha i).toList : Multiset (Sequent sigma))
      (p.donorBoundary i) = p.boundary alpha bounded := by
    apply Hypersequent.ext
    rw [extend_components, Multiset.coe_toList]
    exact p.stop_components_exact alpha i threshold
  exact castLabels equal _ (weakenListLabels r _ _ (.interface (p.donorBoundary i)) (boxLabels i))

@[simp] theorem plug_stop (alpha : State n) (i : Fin n) (threshold : p.m i ≤ alpha i)
    (bounded : mass alpha ≤ quota p.m)
    (donors : (j : Fin n) → CKTree sigma D (p.donorBoundary j)) :
    plug (r.stopTree (fun j => .interface (p.donorBoundary j)) alpha i threshold bounded)
      (stopLabels r alpha i threshold bounded) donors = r.stopTree donors alpha i threshold bounded := by
  simp only [stopLabels, ContractionPostponement.RuleInterface.stopTree, plug_cast,
    plug_weakenList, plug_box]

noncomputable def interpretLabels : {alpha : State n} → (plan : Plan p.m alpha) →
    Labels p.donorBoundary (r.interpret (fun j => .interface (p.donorBoundary j)) plan)
  | alpha, .stop i threshold bounded => stopLabels r alpha i threshold bounded
  | alpha, .next before children =>
      nodeLabels (r.rule (p.common alpha))
        ((r.rule_premises _).trans (by
          apply congrArg List.ofFn
          funext i
          exact (p.boundary_child alpha before i).symm))
        ((r.rule_conclusion _).trans (p.boundary_continue alpha before).symm)
        (familyChildren (fun i => p.boundary (bump alpha i) (children i).bounded)
          (fun i => r.interpret (fun j => .interface (p.donorBoundary j)) (children i)))
        (familyLabels _ _ (fun i => interpretLabels (children i)))

theorem interpret_fill (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    {alpha : State n} (plan : Plan p.m alpha) :
    plug (r.interpret (fun j => .interface (p.donorBoundary j)) plan)
      (interpretLabels r plan) donors = r.interpret donors plan := by
  induction plan with
  | stop i threshold bounded => exact plug_stop r _ i threshold bounded donors
  | next before children ih =>
      simp only [interpretLabels, ContractionPostponement.RuleInterface.interpret,
        plug_node, plug_family]
      simp only [ih]

def contractListLabels (G : Hypersequent sigma) : (removed : List (Sequent sigma)) →
    (support : ∀ S ∈ removed, S ∈ G.components) →
    (tree : CKTree sigma D (extend (removed : Multiset (Sequent sigma)) G)) →
    Labels B tree → Labels B (r.contractList G removed support tree)
  | [], _, tree, labels => castLabels (extend_zero G) tree labels
  | S :: rest, support, tree, labels => by
      have hS : S ∈ (extend (rest : Multiset (Sequent sigma)) G).components :=
        Multiset.mem_add.mpr (Or.inr (support S (by simp)))
      have input : extend {S} (extend (rest : Multiset (Sequent sigma)) G) =
          extend ((S :: rest : List (Sequent sigma)) : Multiset (Sequent sigma)) G := by
        apply Hypersequent.ext
        exact (add_assoc _ _ _).symm
      let contracted := node (r.ec _ S hS) (r.ec_premises _ S hS)
        (r.ec_conclusion _ S hS) (.cons (input.symm ▸ tree) .nil)
      let labelled := nodeLabels (r.ec _ S hS) (r.ec_premises _ S hS)
        (r.ec_conclusion _ S hS) _ (consLabels (castLabels input.symm tree labels) nilLabels)
      exact contractListLabels G rest (fun S h => support S (List.mem_cons_of_mem _ h))
        contracted labelled

@[simp] theorem plug_contractList (G : Hypersequent sigma) (removed : List (Sequent sigma))
    (support : ∀ S ∈ removed, S ∈ G.components)
    (tree : CKTree sigma D (extend (removed : Multiset (Sequent sigma)) G))
    (labels : Labels B tree) (donors : (i : Fin n) → CKTree sigma D (B i)) :
    plug (r.contractList G removed support tree) (contractListLabels r G removed support tree labels) donors =
      r.contractList G removed support (plug tree labels donors) := by
  induction removed with
  | nil => exact plug_cast (extend_zero G) tree labels donors
  | cons S rest ih =>
      simp only [contractListLabels, ContractionPostponement.RuleInterface.contractList]
      rw [ih]
      simp only [plug_node, plugChildren_cons, plugChildren_nil, plug_cast]

noncomputable def finishLabels (plan : Plan p.m (fun _ => 0)) :
    Labels p.donorBoundary (r.finish (fun j => .interface (p.donorBoundary j)) plan) := by
  have equal : p.boundary (fun _ => 0) plan.bounded =
      extend (p.terminalComponents.toList : Multiset (Sequent sigma)) p.terminal := by
    apply Hypersequent.ext
    rw [extend_components, Multiset.coe_toList]
    exact p.terminal_boundary
  exact contractListLabels r p.terminal p.terminalComponents.toList
    (fun S h => ContractionPostponement.RuleInterface.terminal_support S (Multiset.mem_toList.mp h))
    _ (castLabels equal _ (interpretLabels r plan))

/-- Universal literal filling equation for the original donor-indexed compiler. -/
theorem finish_fill (donors : (i : Fin n) → CKTree sigma D (p.donorBoundary i))
    (plan : Plan p.m (fun _ => 0)) :
    plug (r.finish (fun j => .interface (p.donorBoundary j)) plan) (finishLabels r plan) donors =
      r.finish donors plan := by
  simp only [finishLabels, ContractionPostponement.RuleInterface.finish,
    plug_contractList, plug_cast, interpret_fill]

/-- Construction history, not a boundary classifier; need not be injective, and no bijection is assumed. -/
noncomputable def donorIndex (plan : Plan p.m (fun _ => 0))
    (hole : (r.finish (fun j => .interface (p.donorBoundary j)) plan).LeafOccurrence) : Fin n :=
  (finishLabels r plan hole).1

theorem donorIndex_boundary (plan : Plan p.m (fun _ => 0))
    (hole : (r.finish (fun j => .interface (p.donorBoundary j)) plan).LeafOccurrence) :
    p.donorBoundary (donorIndex r plan hole) =
      (r.finish (fun j => .interface (p.donorBoundary j)) plan).leafBoundary hole :=
  (finishLabels r plan hole).2

end RuleInterface
#check @RuleInterface.finish_fill
#print axioms plug_family
#print axioms RuleInterface.plug_weakenList
#print axioms RuleInterface.interpret_fill
#print axioms RuleInterface.finish_fill
#print axioms RuleInterface.donorIndex_boundary
end Potkin.Research.ContractionDonorFilling

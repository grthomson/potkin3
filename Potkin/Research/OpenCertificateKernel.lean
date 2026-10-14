import Potkin.Research.RevivalInterface
import Potkin.AllHoleFilling
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Physical open continuation certificates in the native right-ghost fragment

Providers are indexed by existing physical interfaces, their actual absolute
address and the inherited owner scope. They are metadata, not checked proofs.
A vacant interface processes no conclusion. A genuine node advances inherited
checkpoints before introducing its own owner, whose single colour is shared
by both ordered premises. Ghost assignments retain their actual scope index.
-/

namespace Potkin.Research.OpenCertificateKernel

open RevivalInterface

abbrev Provider {G : Hypersequent sigma} (tree : CKTree sigma Data G) :=
  tree.LeafOccurrence → InternalAddress → List OwnerSlot → Type

abbrev ChildrenProvider {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs) :=
  children.LeafOccurrence → InternalAddress → List OwnerSlot → Type

/-- The index, rather than the slot value, retains distinct equal-colour
ancestor choices and hence their occurrence multiplicity. -/
abbrev EligibleOwner (colour : Atom) (env : List OwnerSlot) :=
  {index : Fin env.length // compatibleRight colour (env.get index) = true}

mutual
def Kernel : {G : Hypersequent sigma} → (tree : CKTree sigma Data G) →
    Provider tree → InternalAddress → List OwnerSlot → Type
  | _, .interface _, provider, address, env => provider PUnit.unit address env
  | _, .ordinary o children, provider, address, env =>
      let inherited := advance (emptyConclusion o.instanceData) env
      match o.instanceData with
      | .ghostP => GhostKernel children .p inherited
      | .ghostQ => GhostKernel children .q inherited
      | .owner => OwnerKernel children provider address inherited
      | _ => ChildrenKernel children provider address 0 inherited

/-- A genuine ghost initial is nullary. An ambient node with a ghost label
and premises has no certificate; exact local admission excludes that shape. -/
def GhostKernel : {Gs : List (Hypersequent sigma)} →
    CKChildren sigma Data Gs → Atom → List OwnerSlot → Type
  | _, .nil, colour, env => EligibleOwner colour env
  | _, .cons _ _, _, _ => PEmpty

def ChildrenKernel : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → ChildrenProvider children →
    InternalAddress → Nat → List OwnerSlot → Type
  | _, .nil, _, _, _, _ => PUnit
  | _, .cons head tail, provider, address, slot, env =>
      Kernel head (fun hole => provider (.inl hole)) (address ++ [slot]) env ×
        ChildrenKernel tail (fun hole => provider (.inr hole)) address (slot + 1) env

def OwnerKernel : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → ChildrenProvider children →
    InternalAddress → List OwnerSlot → Type
  | _, .nil, _, _, _ => PEmpty
  | _, .cons _ .nil, _, _, _ => PEmpty
  | _, .cons left (.cons right .nil), provider, address, env =>
      Σ colour : Atom,
        Kernel left (fun hole => provider (.inl hole)) (address ++ [0])
            (enterOwner address colour false env) ×
          Kernel right (fun hole => provider (.inr (.inl hole))) (address ++ [1])
            (enterOwner address colour true env)
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _ => PEmpty
end

def emptyProvider {G : Hypersequent sigma} (tree : CKTree sigma Data G) :
    Provider tree := fun _ _ _ => PEmpty

abbrev ClosedKernel {G : Hypersequent sigma} (tree : CKTree sigma Data G)
    (address : InternalAddress) (env : List OwnerSlot) :=
  Kernel tree (emptyProvider tree) address env

mutual
/-- Pointwise continuation equivalences transport actual witness choices,
without forgetting addresses, scope entries or shared owner colours. -/
def providerEquiv : {G : Hypersequent sigma} → (tree : CKTree sigma Data G) →
    (left right : Provider tree) →
    (∀ hole address env, left hole address env ≃ right hole address env) →
    (address : InternalAddress) → (env : List OwnerSlot) →
    Kernel tree left address env ≃ Kernel tree right address env
  | _, .interface _, left, right, change, address, env =>
      change PUnit.unit address env
  | _, .ordinary o children, left, right, change, address, env => by
      cases label : o.instanceData <;>
        simp only [Kernel, label]
      all_goals first
        | exact Equiv.refl _
        | exact ownerProviderEquiv children left right change address _
        | exact childrenProviderEquiv children left right change address 0 _

def childrenProviderEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) →
    (left right : ChildrenProvider children) →
    (∀ hole address env, left hole address env ≃ right hole address env) →
    (address : InternalAddress) → (slot : Nat) → (env : List OwnerSlot) →
    ChildrenKernel children left address slot env ≃
      ChildrenKernel children right address slot env
  | _, .nil, _, _, _, _, _, _ => Equiv.refl _
  | _, .cons head tail, left, right, change, address, slot, env =>
      Equiv.prodCongr
        (providerEquiv head (fun h => left (.inl h)) (fun h => right (.inl h))
          (fun h => change (.inl h)) (address ++ [slot]) env)
        (childrenProviderEquiv tail (fun h => left (.inr h)) (fun h => right (.inr h))
          (fun h => change (.inr h)) address (slot + 1) env)

def ownerProviderEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) →
    (left right : ChildrenProvider children) →
    (∀ hole address env, left hole address env ≃ right hole address env) →
    (address : InternalAddress) → (env : List OwnerSlot) →
    OwnerKernel children left address env ≃ OwnerKernel children right address env
  | _, .nil, _, _, _, _, _ => Equiv.refl _
  | _, .cons _ .nil, _, _, _, _, _ => Equiv.refl _
  | _, .cons head (.cons tail .nil), left, right, change, address, env =>
      Equiv.sigmaCongrRight fun colour => Equiv.prodCongr
        (providerEquiv head (fun h => left (.inl h)) (fun h => right (.inl h))
          (fun h => change (.inl h)) (address ++ [0])
          (enterOwner address colour false env))
        (providerEquiv tail (fun h => left (.inr (.inl h)))
          (fun h => right (.inr (.inl h))) (fun h => change (.inr (.inl h)))
          (address ++ [1]) (enterOwner address colour true env))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, _ => Equiv.refl _
end

def factorClosedProvider {G : Hypersequent sigma} (tree : CKTree sigma Data G)
    (fillers : tree.LeafAssignment) : Provider tree :=
  fun hole address env => ClosedKernel (fillers hole) address env

mutual
/-- Actual constructor gluing for simultaneous native all-hole filling.
At a seam the callback starts its detached root with the unchanged scope;
that genuine root performs its conclusion processing exactly once. -/
def fillEquiv : {G : Hypersequent sigma} → (tree : CKTree sigma Data G) →
    (fillers : tree.LeafAssignment) →
    (address : InternalAddress) → (env : List OwnerSlot) →
    ClosedKernel (tree.fillAssignment fillers) address env ≃
      Kernel tree (factorClosedProvider tree fillers) address env
  | _, .interface _, _, _, _ => Equiv.refl _
  | _, .ordinary o children, fillers, address, env => by
      cases label : o.instanceData <;>
        simp only [ClosedKernel, CKTree.fillAssignment, Kernel, label]
      all_goals first
        | exact ghostFillEquiv children _ _ fillers
        | exact ownerFillEquiv children fillers address _
        | exact childrenFillEquiv children fillers address 0 _

def ghostFillEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (colour : Atom) →
    (env : List OwnerSlot) → (fillers : children.LeafAssignment) →
    GhostKernel (children.fillAssignment fillers) colour env ≃
      GhostKernel children colour env
  | _, .nil, _, _, _ => Equiv.refl _
  | _, .cons _ _, _, _, _ => Equiv.refl _

def childrenFillEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (fillers : children.LeafAssignment) →
    (address : InternalAddress) → (slot : Nat) → (env : List OwnerSlot) →
    ChildrenKernel (children.fillAssignment fillers) (fun _ _ _ => PEmpty)
        address slot env ≃
      ChildrenKernel children (fun hole abs scope =>
        ClosedKernel (fillers hole) abs scope) address slot env
  | _, .nil, _, _, _, _ => Equiv.refl _
  | _, .cons head tail, fillers, address, slot, env =>
      Equiv.prodCongr
        (fillEquiv head (fun h => fillers (.inl h)) (address ++ [slot]) env)
        (childrenFillEquiv tail (fun h => fillers (.inr h)) address (slot + 1) env)

def ownerFillEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (fillers : children.LeafAssignment) →
    (address : InternalAddress) → (env : List OwnerSlot) →
    OwnerKernel (children.fillAssignment fillers) (fun _ _ _ => PEmpty) address env ≃
      OwnerKernel children (fun hole abs scope =>
        ClosedKernel (fillers hole) abs scope) address env
  | _, .nil, _, _, _ => Equiv.refl _
  | _, .cons _ .nil, _, _, _ => Equiv.refl _
  | _, .cons left (.cons right .nil), fillers, address, env =>
      Equiv.sigmaCongrRight fun colour => Equiv.prodCongr
        (fillEquiv left (fun h => fillers (.inl h)) (address ++ [0])
          (enterOwner address colour false env))
        (fillEquiv right (fun h => fillers (.inr (.inl h))) (address ++ [1])
          (enterOwner address colour true env))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _ => Equiv.refl _
end

private theorem eligible_nonempty (colour : Atom) (env : List OwnerSlot) :
    Nonempty (EligibleOwner colour env) ↔
      ∃ slot ∈ env, compatibleRight colour slot = true := by
  constructor
  · rintro ⟨⟨index, eligible⟩⟩
    exact ⟨env.get index, List.get_mem env index, eligible⟩
  · rintro ⟨slot, member, eligible⟩
    rcases List.get_of_mem member with ⟨index, equal⟩
    exact ⟨⟨index, by simpa only [equal] using eligible⟩⟩

private theorem ghost_nonempty_iff {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs) (arity : Gs = [])
    (colour : Atom) (env : List OwnerSlot) :
    Nonempty (GhostKernel children colour env) ↔
      ∃ slot ∈ env, compatibleRight colour slot = true := by
  subst Gs
  cases children
  exact eligible_nonempty colour env

private theorem registered_exact (o : LocalOccurrence sigma Data)
    (registered : o ∈ registry) : o = occurrence o.instanceData := by
  rcases List.mem_map.mp registered with ⟨label, _, rfl⟩
  cases label <;> rfl

private theorem nonempty_product (A B : Type) :
    Nonempty (A × B) ↔ Nonempty A ∧ Nonempty B := by
  constructor
  · rintro ⟨⟨a,b⟩⟩; exact ⟨⟨a⟩,⟨b⟩⟩
  · rintro ⟨⟨a⟩,⟨b⟩⟩; exact ⟨a,b⟩

private theorem nonempty_sigma (B : Atom → Type) :
    Nonempty (Σ colour, B colour) ↔ ∃ colour, Nonempty (B colour) := by
  constructor
  · rintro ⟨⟨colour, witness⟩⟩; exact ⟨colour,⟨witness⟩⟩
  · rintro ⟨colour,⟨witness⟩⟩; exact ⟨colour,witness⟩

mutual
/-- Existence agreement with the old Prop relation. The exact registry
hypothesis excludes malformed ghost nodes which that scalar observer ignores.
This theorem does not quotient the Type-valued witness multiplicities. -/
theorem closed_nonempty_iff : {G : Hypersequent sigma} →
    (tree : CKTree sigma Data G) → LocallyAdmittedTree presentation tree →
    (address : InternalAddress) → (env : List OwnerSlot) →
    (Nonempty (ClosedKernel tree address env) ↔ HasScopedCertificate tree address env)
  | _, .interface _, _, _, _ => by
      simp [ClosedKernel, Kernel, emptyProvider, HasScopedCertificate]
  | _, .ordinary o children, admitted, address, env => by
      have exactOccurrence : o = occurrence o.instanceData :=
        registered_exact o admitted.1
      cases label : o.instanceData <;>
        simp only [ClosedKernel, Kernel, HasScopedCertificate, label]
      all_goals first
        | exact closedOwner_nonempty_iff children admitted.2 address _
        | exact closedChildren_nonempty_iff children admitted.2 address 0 _
        | skip
      all_goals
        have arity : o.shape.premises = [] := by
          rw [exactOccurrence, label]
          rfl
        exact ghost_nonempty_iff children arity _ _

theorem closedChildren_nonempty_iff : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) →
    LocallyAdmittedChildren presentation children →
    (address : InternalAddress) → (slot : Nat) → (env : List OwnerSlot) →
    (Nonempty (ChildrenKernel children (fun _ _ _ => PEmpty) address slot env) ↔
      ChildrenCertificate children address slot env)
  | _, .nil, _, _, _, _ => by
      exact ⟨fun _ => True.intro, fun _ => ⟨PUnit.unit⟩⟩
  | _, .cons head tail, admitted, address, slot, env => by
      simp only [ChildrenKernel, ChildrenCertificate, nonempty_product]
      exact and_congr (closed_nonempty_iff head admitted.1 (address ++ [slot]) env)
        (closedChildren_nonempty_iff tail admitted.2 address (slot + 1) env)

theorem closedOwner_nonempty_iff : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) →
    LocallyAdmittedChildren presentation children →
    (address : InternalAddress) → (env : List OwnerSlot) →
    (Nonempty (OwnerKernel children (fun _ _ _ => PEmpty) address env) ↔
      OwnerCertificate children address env)
  | _, .nil, _, _, _ => by simp [OwnerKernel, OwnerCertificate]
  | _, .cons _ .nil, _, _, _ => by simp [OwnerKernel, OwnerCertificate]
  | _, .cons left (.cons right .nil), admitted, address, env => by
      simp only [OwnerKernel, OwnerCertificate, nonempty_sigma, nonempty_product]
      apply exists_congr
      intro colour
      exact and_congr
        (closed_nonempty_iff left admitted.1 (address ++ [0])
          (enterOwner address colour false env))
        (closed_nonempty_iff right admitted.2.1 (address ++ [1])
          (enterOwner address colour true env))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _ => by
      simp [OwnerKernel, OwnerCertificate]
end

theorem closed_positive_iff {G : Hypersequent sigma}
    (tree : CKTree sigma Data G) (admitted : LocallyAdmittedTree presentation tree)
    (address : InternalAddress) (env : List OwnerSlot) :
    0 < certificateCount tree address env ↔ Nonempty (ClosedKernel tree address env) :=
  (count_positive_iff tree address env).trans
    (closed_nonempty_iff tree admitted address env).symm

/-! ## Exact finite multiplicity, without quotienting certificates to Prop

The result below is an actual equivalence with `Fin certificateCount`, not a
bounded evaluation or an assertion that a Prop retains all its witnesses.
The chosen finite palette and every indexed ancestor assignment are retained.
-/

private abbrev SelectedIndex {A : Type} (test : A → Bool) (xs : List A) :=
  {index : Fin xs.length // test (xs.get index) = true}

private def selectedConsEquiv {A : Type} (test : A → Bool) (head : A)
    (tail : List A) :
    SelectedIndex test (head :: tail) ≃
      ({token : PUnit.{1} // test head = true} ⊕ SelectedIndex test tail) where
  toFun := fun chosen =>
    (Fin.cases (motive := fun index =>
      test ((head :: tail).get index) = true →
        ({token : PUnit.{1} // test head = true} ⊕ SelectedIndex test tail))
      (fun eligible => Sum.inl ⟨PUnit.unit, eligible⟩)
      (fun index eligible => Sum.inr ⟨index, eligible⟩)
      chosen.1) chosen.2
  invFun := fun chosen => match chosen with
    | .inl chosen => ⟨0, chosen.2⟩
    | .inr chosen => ⟨chosen.1.succ, chosen.2⟩
  left_inv := by
    rintro ⟨index, eligible⟩
    refine Fin.cases ?_ ?_ index eligible
    · intro eligible; rfl
    · intro index eligible; rfl
  right_inv := by
    rintro (⟨token, eligible⟩ | ⟨index, eligible⟩)
    · cases token; rfl
    · rfl

private def flagFinEquiv (flag : Bool) :
    {token : PUnit.{1} // flag = true} ≃ Fin (if flag then 1 else 0) := by
  cases flag with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact { toFun := fun witness => False.elim (by cases witness.2)
              invFun := fun index => Fin.elim0 index
              left_inv := fun witness => False.elim (by cases witness.2)
              right_inv := fun index => Fin.elim0 index }
  | true =>
      simp only [eq_self_iff_true, ite_true]
      exact { toFun := fun _ => 0
              invFun := fun _ => ⟨PUnit.unit, True.intro⟩
              left_inv := fun witness => Subsingleton.elim _ witness
              right_inv := fun index => Subsingleton.elim _ index }

/-- Filtering never identifies equal list values: this equivalence counts
eligible *indices*, so repeated physical ancestors remain separate choices. -/
private def selectedFinEquiv {A : Type} (test : A → Bool) :
    (xs : List A) → SelectedIndex test xs ≃ Fin (xs.filter test).length
  | [] =>
      { toFun := fun chosen => Fin.elim0 chosen.1
        invFun := fun index => Fin.elim0 index
        left_inv := fun chosen => Fin.elim0 chosen.1
        right_inv := fun index => Fin.elim0 index }
  | head :: tail =>
      ((selectedConsEquiv test head tail).trans
        (Equiv.sumCongr (flagFinEquiv (test head)) (selectedFinEquiv test tail))).trans
          (finSumFinEquiv.trans (Equiv.cast (by
            cases equal : test head <;> simp [equal, Nat.add_comm])))

def eligibleCountEquiv (colour : Atom) (env : List OwnerSlot) :
    EligibleOwner colour env ≃ Fin (env.filter (compatibleRight colour)).length :=
  selectedFinEquiv (compatibleRight colour) env

private def atomSigmaEquiv (family : Atom → Type) :
    (Σ colour : Atom, family colour) ≃ family .p ⊕ family .q where
  toFun := fun witness => match witness with
    | ⟨.p, witness⟩ => .inl witness
    | ⟨.q, witness⟩ => .inr witness
  invFun := fun witness => match witness with
    | .inl witness => ⟨.p, witness⟩
    | .inr witness => ⟨.q, witness⟩
  left_inv := by rintro ⟨colour, witness⟩; cases colour <;> rfl
  right_inv := by rintro (witness | witness) <;> rfl

private def emptyFinEquiv : PEmpty ≃ Fin 0 where
  toFun := PEmpty.elim
  invFun := Fin.elim0
  left_inv := fun witness => nomatch witness
  right_inv := fun index => Fin.elim0 index

private def unitFinEquiv : PUnit ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => PUnit.unit
  left_inv := fun witness => Subsingleton.elim _ witness
  right_inv := fun index => Subsingleton.elim _ index

private def ghostCountEquiv {Gs : List (Hypersequent sigma)}
    (children : CKChildren sigma Data Gs) (arity : Gs = [])
    (colour : Atom) (env : List OwnerSlot) :
    GhostKernel children colour env ≃ Fin (env.filter (compatibleRight colour)).length := by
  subst Gs
  cases children
  exact eligibleCountEquiv colour env

mutual
/-- Exact finite-cardinality bridge for every admitted native source in the
fixed right-ghost fragment. The inverses recover shared colour and indexed
ghost assignments, including unused-owner choices and equal-colour ancestors.
This is stronger than existence agreement and does not count revived proofs. -/
def closedCountEquiv : {G : Hypersequent sigma} →
    (tree : CKTree sigma Data G) → LocallyAdmittedTree presentation tree →
    (address : InternalAddress) → (env : List OwnerSlot) →
    ClosedKernel tree address env ≃ Fin (certificateCount tree address env)
  | _, .interface _, _, _, _ => emptyFinEquiv
  | _, .ordinary o children, admitted, address, env => by
      have exactOccurrence : o = occurrence o.instanceData :=
        registered_exact o admitted.1
      cases label : o.instanceData <;>
        simp only [ClosedKernel, Kernel, certificateCount, label]
      all_goals first
        | exact ownerCountEquiv children admitted.2 address _
        | exact childrenCountEquiv children admitted.2 address 0 _
        | skip
      all_goals
        have arity : o.shape.premises = [] := by
          rw [exactOccurrence, label]
          rfl
        exact ghostCountEquiv children arity _ _

def childrenCountEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) →
    LocallyAdmittedChildren presentation children →
    (address : InternalAddress) → (slot : Nat) → (env : List OwnerSlot) →
    ChildrenKernel children (fun _ _ _ => PEmpty) address slot env ≃
      Fin (childrenCount children address slot env)
  | _, .nil, _, _, _, _ => unitFinEquiv
  | _, .cons head tail, admitted, address, slot, env =>
      (Equiv.prodCongr
        (closedCountEquiv head admitted.1 (address ++ [slot]) env)
        (childrenCountEquiv tail admitted.2 address (slot + 1) env)).trans finProdFinEquiv

def ownerCountEquiv : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) →
    LocallyAdmittedChildren presentation children →
    (address : InternalAddress) → (env : List OwnerSlot) →
    OwnerKernel children (fun _ _ _ => PEmpty) address env ≃
      Fin (ownerCount children address env)
  | _, .nil, _, _, _ => emptyFinEquiv
  | _, .cons _ .nil, _, _, _ => emptyFinEquiv
  | _, .cons left (.cons right .nil), admitted, address, env =>
      ((atomSigmaEquiv _).trans (Equiv.sumCongr
        ((Equiv.prodCongr
          (closedCountEquiv left admitted.1 (address ++ [0])
            (enterOwner address .p false env))
          (closedCountEquiv right admitted.2.1 (address ++ [1])
            (enterOwner address .p true env))).trans finProdFinEquiv)
        ((Equiv.prodCongr
          (closedCountEquiv left admitted.1 (address ++ [0])
            (enterOwner address .q false env))
          (closedCountEquiv right admitted.2.1 (address ++ [1])
            (enterOwner address .q true env))).trans finProdFinEquiv))).trans finSumFinEquiv
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _ => emptyFinEquiv
end

#check ClosedKernel
#check fillEquiv
#check providerEquiv
#print axioms fillEquiv
#print axioms providerEquiv
#print axioms closed_nonempty_iff
#print axioms closed_positive_iff
#check closedCountEquiv
#print axioms eligibleCountEquiv
#print axioms closedCountEquiv

end Potkin.Research.OpenCertificateKernel

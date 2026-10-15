import Potkin.Research.HLJStructural

/-!
# An additive strict HLJ internal-weakening schema

The old structural stock is embedded descriptor-for-descriptor, retaining its
entire supplied component incidence.  The extra descriptor is genuine internal
weakening with an arbitrary shared passive hypersequent.  This is an extension
of instance data and admission, not a second proof, cut, or context carrier.

The component incidence says which displayed component persists.  It does not
claim to record formula-occurrence resource action inside that component.
-/
namespace Potkin.Research.HLJInternalWeakening

open ContractionBoundaries
universe u v
variable {sigma : Signature.{u, v}}

structure IWData (sigma : Signature.{u, v}) where
  passive : Multiset (Sequent sigma)
  formula : Formula sigma
  gamma : Context sigma
  pi : Context sigma

abbrev Data (sigma : Signature.{u, v}) := HLJStructural.Data sigma ⊕ IWData sigma

def liftOccurrence (o : LocalOccurrence sigma (HLJStructural.Data sigma)) :
    LocalOccurrence sigma (Data sigma) :=
  ⟨o.id, o.kind, o.shape, .inl o.instanceData, o.incidence⟩

@[simp] theorem lift_id (o : LocalOccurrence sigma (HLJStructural.Data sigma)) :
    (liftOccurrence o).id = o.id := rfl
@[simp] theorem lift_kind (o : LocalOccurrence sigma (HLJStructural.Data sigma)) :
    (liftOccurrence o).kind = o.kind := rfl
@[simp] theorem lift_shape (o : LocalOccurrence sigma (HLJStructural.Data sigma)) :
    (liftOccurrence o).shape = o.shape := rfl
@[simp] theorem lift_incidence (o : LocalOccurrence sigma (HLJStructural.Data sigma)) :
    (liftOccurrence o).incidence = o.incidence := rfl

noncomputable def oldOccurrence (key : Nat) (d : HLJStructural.Data sigma) :
    LocalOccurrence sigma (Data sigma) := liftOccurrence (HLJStructural.occurrence key d)

@[simp] theorem old_premises (key : Nat) (d : HLJStructural.Data sigma) :
    (oldOccurrence key d).shape.premises =
      (HLJStructural.occurrence key d).shape.premises := rfl

@[simp] theorem old_conclusion (key : Nat) (d : HLJStructural.Data sigma) :
    (oldOccurrence key d).shape.conclusion =
      (HLJStructural.occurrence key d).shape.conclusion := rfl

@[simp] theorem old_id (key : Nat) (d : HLJStructural.Data sigma) :
    (oldOccurrence key d).id = key := rfl

def IWData.input (d : IWData sigma) : Hypersequent sigma :=
  extend d.passive (.singleton ⟨d.gamma, d.pi⟩)

def IWData.output (d : IWData sigma) : Hypersequent sigma :=
  extend d.passive (.singleton ⟨{d.formula} + d.gamma, d.pi⟩)

def IWData.shape (d : IWData sigma) : OccurrenceShape sigma :=
  ⟨[d.input], d.output⟩

private noncomputable def activeProfile (K : Multiset (Sequent sigma)) (S : Sequent sigma) :
    ComponentProfile (extend K (.singleton S)) where
  displayed := HLJStructural.contextList K ++ [S]
  exact := by
    change ((HLJStructural.contextList K ++ [S] : List (Sequent sigma)) :
      Multiset (Sequent sigma)) = K + {S}
    rw [← Multiset.coe_add, HLJStructural.contextList_exact]
    rfl

noncomputable def IWData.profiles (d : IWData sigma) : OccurrenceProfiles d.shape where
  premise := fun i => Fin.cases (activeProfile d.passive ⟨d.gamma, d.pi⟩)
    (fun j => Fin.elim0 j) i
  conclusion := by
    change ComponentProfile (extend d.passive (.singleton ⟨{d.formula} + d.gamma, d.pi⟩))
    exact activeProfile d.passive ⟨{d.formula} + d.gamma, d.pi⟩

noncomputable def IWData.incidence (d : IWData sigma) : ComponentIncidence d.shape where
  profiles := d.profiles
  edges := Finset.univ.image (fun j : Fin ((HLJStructural.contextList d.passive).length + 1) =>
    { premiseSlot := ⟨0, by change 0 < 1; decide⟩
      premiseComponent := ⟨j.val, by
        change j.val < (HLJStructural.contextList d.passive ++
          [(⟨d.gamma, d.pi⟩ : Sequent sigma)]).length
        simpa only [List.length_append, List.length_singleton] using j.isLt⟩
      conclusionComponent := ⟨j.val, by
        change j.val < (HLJStructural.contextList d.passive ++
          [(⟨{d.formula} + d.gamma, d.pi⟩ : Sequent sigma)]).length
        simpa only [List.length_append, List.length_singleton] using j.isLt⟩ })

noncomputable def iwOccurrence (key : Nat) (K : Multiset (Sequent sigma))
    (A : Formula sigma) (gamma pi : Context sigma) : LocalOccurrence sigma (Data sigma) :=
  let d : IWData sigma := ⟨K, A, gamma, pi⟩
  ⟨key, .structural, d.shape, .inr d, some d.incidence⟩

@[simp] theorem iw_id (key : Nat) (K : Multiset (Sequent sigma))
    (A : Formula sigma) (gamma pi : Context sigma) :
    (iwOccurrence key K A gamma pi).id = key := rfl

@[simp] theorem iw_premises (key : Nat) (K : Multiset (Sequent sigma))
    (A : Formula sigma) (gamma pi : Context sigma) :
    (iwOccurrence key K A gamma pi).shape.premises =
      [extend K (.singleton ⟨gamma, pi⟩)] := rfl

@[simp] theorem iw_conclusion (key : Nat) (K : Multiset (Sequent sigma))
    (A : Formula sigma) (gamma pi : Context sigma) :
    (iwOccurrence key K A gamma pi).shape.conclusion =
      extend K (.singleton ⟨{A} + gamma, pi⟩) := rfl

def IWData.Valid (d : IWData sigma) : Prop :=
  HLJStructural.ValidComponents d.passive ∧ d.pi.card ≤ 1

/-- Exact old admission or the entire canonical IW descriptor and incidence.
No rule-name or boundary-only test admits a fabricated occurrence. -/
def Accepted (o : LocalOccurrence sigma (Data sigma)) : Prop :=
  (∃ old, o = liftOccurrence old ∧ (HLJStructural.theory sigma).Admits old) ∨
  (∃ key K A gamma pi, o = iwOccurrence key K A gamma pi ∧
    HLJStructural.ValidComponents K ∧ pi.card ≤ 1)

def theory (sigma : Signature.{u, v}) : ProofTheory sigma (Data sigma) where
  primitive := .full
  base := ⟨fun _ => False, fun h => h.elim, fun h => h.elim⟩
  initial := fun _ => False
  rules :=
    { logical := fun o => Accepted o ∧ o.kind = .logical
      structural := fun o => Accepted o ∧ o.kind = .structural }

theorem lift_admitted (o : LocalOccurrence sigma (HLJStructural.Data sigma))
    (admitted : (HLJStructural.theory sigma).Admits o) :
    (theory sigma).Admits (liftOccurrence o) := by
  have exactOld : Accepted (liftOccurrence o) := .inl ⟨o, rfl, admitted⟩
  cases admitted with
  | material h => exact h.elim
  | initial _ _ h => exact h.elim
  | logical kind _ => exact .logical kind ⟨exactOld, kind⟩
  | structural kind _ => exact .structural kind ⟨exactOld, kind⟩

theorem old_admitted (key : Nat) (d : HLJStructural.Data sigma)
    (route : d.RouteValid) (valid : HLJStructural.WholeValid (HLJStructural.occurrence key d)) :
    (theory sigma).Admits (oldOccurrence key d) :=
  lift_admitted _ (HLJStructural.strict_admits key d route valid)

theorem iw_admitted (key : Nat) (K : Multiset (Sequent sigma))
    (A : Formula sigma) (gamma pi : Context sigma)
    (passive : HLJStructural.ValidComponents K) (single : pi.card ≤ 1) :
    (theory sigma).Admits (iwOccurrence key K A gamma pi) :=
  .structural rfl ⟨.inr ⟨key, K, A, gamma, pi, rfl, passive, single⟩, rfl⟩

theorem iw_wholeValid (key : Nat) (K : Multiset (Sequent sigma))
    (A : Formula sigma) (gamma pi : Context sigma)
    (passive : HLJStructural.ValidComponents K) (single : pi.card ≤ 1) :
    (∀ G ∈ (iwOccurrence key K A gamma pi).shape.premises, HLJStructural.ValidBoundary G) ∧
      HLJStructural.ValidBoundary (iwOccurrence key K A gamma pi).shape.conclusion := by
  constructor
  · intro G member
    simp only [iw_premises, List.mem_singleton] at member
    subst G
    exact (HLJStructural.valid_extend _ _).mpr ⟨passive, by
      simpa [HLJStructural.ValidBoundary, HLJStructural.Single] using single⟩
  · exact (HLJStructural.valid_extend _ _).mpr ⟨passive, by
      simpa [HLJStructural.ValidBoundary, HLJStructural.Single] using single⟩

#print axioms lift_admitted
#print axioms iw_admitted
#print axioms iw_wholeValid

end Potkin.Research.HLJInternalWeakening

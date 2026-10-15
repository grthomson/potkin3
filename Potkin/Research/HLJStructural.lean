import Potkin.Research.ContractionPostponement

/-!
# Genuine HLJ Communication and external structural instances

The independent schemas below specify entire ordered hypersequent boundaries.
Communication repartitions antecedent blocks, not succedents. Context components
are shared once in its conclusion. Canonical incidence is checked as part of
the entire occurrence, and is not used to infer formula movement.

`theory` enforces single-succedent validity in EVERY displayed component.
`assemblyTheory` is only an explicitly unchecked schema envelope for the old
compiler. No registry or checked derivation is constructed under that envelope.
-/
namespace Potkin.Research.HLJStructural
open ContractionBoundaries
universe u v
variable {sigma : Signature.{u, v}}

def Single (S : Sequent sigma) : Prop := S.rhs.card ≤ 1
def ValidComponents (G : Multiset (Sequent sigma)) : Prop := ∀ S ∈ G, Single S
def ValidBoundary (G : Hypersequent sigma) : Prop := ValidComponents G.components

@[simp] theorem valid_zero : ValidComponents (0 : Multiset (Sequent sigma)) := by
  intro S h; simp at h
@[simp] theorem valid_add (G H : Multiset (Sequent sigma)) :
    ValidComponents (G + H) ↔ ValidComponents G ∧ ValidComponents H := by
  simp only [ValidComponents, Multiset.mem_add]
  constructor
  · intro h; exact ⟨fun S hs => h S (.inl hs), fun S hs => h S (.inr hs)⟩
  · rintro ⟨hG, hH⟩ S (h | h)
    · exact hG S h
    · exact hH S h
@[simp] theorem valid_singleton (S : Sequent sigma) : ValidComponents {S} ↔ Single S := by
  simp [ValidComponents]
theorem valid_of_le {G H : Multiset (Sequent sigma)} (le : G ≤ H)
    (valid : ValidComponents H) : ValidComponents G :=
  fun S member => valid S (Multiset.mem_of_le le member)
theorem valid_nsmul (k : Nat) {G : Multiset (Sequent sigma)}
    (valid : ValidComponents G) : ValidComponents (k • G) :=
  fun S member => valid S (Multiset.mem_of_mem_nsmul member)
@[simp] theorem valid_extend (K : Multiset (Sequent sigma)) (G : Hypersequent sigma) :
    ValidBoundary (extend K G) ↔ ValidComponents K ∧ ValidBoundary G := valid_add _ _

/-- Payloads identify actual schemas, including the retained EC occurrence. -/
inductive Data (sigma : Signature.{u, v}) : Type (max u v) where
  | identity (A : Formula sigma)
  | com (K : Multiset (Sequent sigma)) (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma)
  | ew (G : Hypersequent sigma) (S : Sequent sigma)
  | ec (G : Hypersequent sigma) (S : Sequent sigma) (retained : Nat)

def leftInput (phi gamma pi : Context sigma) : Sequent sigma := ⟨phi + gamma, pi⟩
def rightInput (psi gamma pi : Context sigma) : Sequent sigma := ⟨psi + gamma, pi⟩
def leftOutput (psi gamma pi : Context sigma) : Sequent sigma := ⟨psi + gamma, pi⟩
def rightOutput (phi gamma pi : Context sigma) : Sequent sigma := ⟨phi + gamma, pi⟩

private def row (xs : List (Sequent sigma)) (positive : xs ≠ []) :
    Sigma (ComponentProfile (sigma := sigma)) := by
  let G : Hypersequent sigma := ⟨(xs : Multiset (Sequent sigma)), by
    intro empty
    have length := congrArg Multiset.card empty
    have : xs.length = 0 := by simpa using length
    exact positive (List.length_eq_zero_iff.mp this)⟩
  exact ⟨G, ⟨xs, rfl⟩⟩

noncomputable def contextList (K : Multiset (Sequent sigma)) : List (Sequent sigma) := K.toList
@[simp] theorem contextList_exact (K : Multiset (Sequent sigma)) :
    (contextList K : Multiset (Sequent sigma)) = K := Multiset.coe_toList K

private theorem contextList_positive (G : Hypersequent sigma) : contextList G.components ≠ [] := by
  intro empty
  have := contextList_exact G.components
  rw [empty] at this
  exact G.nonempty this.symm

noncomputable def Data.premiseRows : Data sigma → List (Sigma (ComponentProfile (sigma := sigma)))
  | .identity _ => []
  | .com K phi psi gamma₁ gamma₂ pi₁ pi₂ =>
      [row (contextList K ++ [leftInput phi gamma₁ pi₁]) (by simp),
       row (contextList K ++ [rightInput psi gamma₂ pi₂]) (by simp)]
  | .ew G _ => [row (contextList G.components) (contextList_positive G)]
  | .ec G S _ => [row (S :: contextList G.components) (by simp)]

noncomputable def Data.conclusionRow : Data sigma → Sigma (ComponentProfile (sigma := sigma))
  | .identity A => row [⟨{A}, {A}⟩] (by simp)
  | .com K phi psi gamma₁ gamma₂ pi₁ pi₂ =>
      row (contextList K ++ [leftOutput psi gamma₁ pi₁, rightOutput phi gamma₂ pi₂]) (by simp)
  | .ew G S => row (S :: contextList G.components) (by simp)
  | .ec G _ _ => row (contextList G.components) (contextList_positive G)

noncomputable def Data.shape (d : Data sigma) : OccurrenceShape sigma :=
  ⟨d.premiseRows.map Sigma.fst, d.conclusionRow.1⟩

private def rowProfiles : (xs : List (Sigma (ComponentProfile (sigma := sigma)))) →
    (i : Fin (xs.map Sigma.fst).length) → ComponentProfile ((xs.map Sigma.fst).get i)
  | [], i => Fin.elim0 i
  | x :: xs, i => Fin.cases x.2 (fun j => rowProfiles xs j) i

noncomputable def Data.profiles (d : Data sigma) : OccurrenceProfiles d.shape :=
  ⟨rowProfiles d.premiseRows, d.conclusionRow.2⟩

/-- Candidate component edges are bounds-checked, never guessed from formulae. -/
private def checkedEdge {shape : OccurrenceShape sigma} (p : OccurrenceProfiles shape)
    (slot source target : Nat) : Option (ComponentEdge p) :=
  if hs : slot < shape.premises.length then
    if hi : source < (p.premise ⟨slot, hs⟩).displayed.length then
      if ho : target < p.conclusion.displayed.length then
        some ⟨⟨slot, hs⟩, ⟨source, hi⟩, ⟨target, ho⟩⟩
      else none
    else none
  else none

noncomputable def Data.edgeRows : Data sigma → List (Nat × Nat × Nat)
  | .identity _ => []
  | .com K _ _ _ _ _ _ =>
      (List.range K.card).flatMap (fun j => [(0, j, j), (1, j, j)]) ++
        [(0, K.card, K.card), (0, K.card, K.card + 1),
         (1, K.card, K.card), (1, K.card, K.card + 1)]
  | .ew G _ => (List.range G.components.card).map (fun j => (0, j, j + 1))
  | .ec G _ retained => (0, 0, retained) ::
      (List.range G.components.card).map (fun j => (0, j + 1, j))

noncomputable def Data.incidence (d : Data sigma) : ComponentIncidence d.shape := by
  classical
  exact ⟨d.profiles, (d.edgeRows.filterMap
    (fun edge => checkedEdge d.profiles edge.1 edge.2.1 edge.2.2)).toFinset⟩

def Data.kind : Data sigma → OccurrenceKind
  | .identity _ => .logical
  | _ => .structural

noncomputable def occurrence (key : Nat) (d : Data sigma) : LocalOccurrence sigma (Data sigma) :=
  ⟨key, d.kind, d.shape, d, some d.incidence⟩

def Data.RouteValid : Data sigma → Prop
  | .ec G S retained => ∃ i : Fin (contextList G.components).length,
      i.val = retained ∧ (contextList G.components).get i = S
  | _ => True

def WholeValid (o : LocalOccurrence sigma (Data sigma)) : Prop :=
  (∀ G ∈ o.shape.premises, ValidBoundary G) ∧ ValidBoundary o.shape.conclusion

def Accepted (strict : Bool) (o : LocalOccurrence sigma (Data sigma)) : Prop :=
  ∃ key d, o = occurrence key d ∧ d.RouteValid ∧ (strict = true → WholeValid o)

private def equipment (strict : Bool) : ProofTheory sigma (Data sigma) where
  primitive := .full
  base := ⟨fun _ => False, fun h => h.elim, fun h => h.elim⟩
  initial := fun _ => False
  rules := ⟨fun o => Accepted strict o, fun o => Accepted strict o⟩

def theory (sigma : Signature.{u, v}) : ProofTheory sigma (Data sigma) := equipment true
def assemblyTheory (sigma : Signature.{u, v}) : ProofTheory sigma (Data sigma) := equipment false

theorem admits_canonical (strict : Bool) (key : Nat) (d : Data sigma)
    (route : d.RouteValid) (valid : strict = true → WholeValid (occurrence key d)) :
    (equipment strict).Admits (occurrence key d) := by
  have accepted : Accepted strict (occurrence key d) := ⟨key, d, rfl, route, valid⟩
  cases d with
  | identity A => exact .logical rfl accepted
  | com K phi psi gamma₁ gamma₂ pi₁ pi₂ => exact .structural rfl accepted
  | ew G S => exact .structural rfl accepted
  | ec G S retained => exact .structural rfl accepted

theorem assembly_admits (key : Nat) (d : Data sigma) (route : d.RouteValid) :
    (assemblyTheory sigma).Admits (occurrence key d) :=
  admits_canonical false key d route (by simp)

theorem strict_admits (key : Nat) (d : Data sigma) (route : d.RouteValid)
    (valid : WholeValid (occurrence key d)) : (theory sigma).Admits (occurrence key d) :=
  admits_canonical true key d route (fun _ => valid)

theorem strict_wholeValid {o : LocalOccurrence sigma (Data sigma)}
    (admitted : (theory sigma).Admits o) : WholeValid o := by
  cases admitted with
  | material h => exact h.elim
  | initial _ _ h => exact h.elim
  | logical _ h => exact h.choose_spec.choose_spec.2.2 rfl
  | structural _ h => exact h.choose_spec.choose_spec.2.2 rfl

@[simp] theorem com_premises (key : Nat) (K : Multiset (Sequent sigma))
    (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma) :
    (occurrence key (.com K phi psi gamma₁ gamma₂ pi₁ pi₂)).shape.premises =
      [extend K (.singleton (leftInput phi gamma₁ pi₁)),
       extend K (.singleton (rightInput psi gamma₂ pi₂))] := by
  change [_, _] = [_, _]
  apply congrArg₂ List.cons
  · apply Hypersequent.ext
    simp [row, extend, ← Multiset.coe_add, contextList]
  · apply congrArg₂ List.cons
    · apply Hypersequent.ext
      simp [row, extend, ← Multiset.coe_add, contextList]
    · rfl

@[simp] theorem com_conclusion (key : Nat) (K : Multiset (Sequent sigma))
    (phi psi gamma₁ gamma₂ pi₁ pi₂ : Context sigma) :
    (occurrence key (.com K phi psi gamma₁ gamma₂ pi₁ pi₂)).shape.conclusion =
      extend K (.pair (leftOutput psi gamma₁ pi₁) (rightOutput phi gamma₂ pi₂)) := by
  apply Hypersequent.ext
  simp [occurrence, Data.shape, Data.conclusionRow, row, extend,
    ← Multiset.coe_add, ← Multiset.cons_coe, contextList]

@[simp] theorem ew_premises (key : Nat) (G : Hypersequent sigma) (S : Sequent sigma) :
    (occurrence key (.ew G S)).shape.premises = [G] := by
  simp only [occurrence, Data.shape, Data.premiseRows, List.map_cons, List.map_nil,
    List.cons.injEq, and_true]
  apply Hypersequent.ext
  simp [row]
@[simp] theorem ew_conclusion (key : Nat) (G : Hypersequent sigma) (S : Sequent sigma) :
    (occurrence key (.ew G S)).shape.conclusion = extend {S} G := by
  apply Hypersequent.ext
  simp [occurrence, Data.shape, Data.conclusionRow, row, extend, ← Multiset.cons_coe, contextList]
@[simp] theorem ec_premises (key : Nat) (G : Hypersequent sigma) (S : Sequent sigma) (i : Nat) :
    (occurrence key (.ec G S i)).shape.premises = [extend {S} G] := by
  simp only [occurrence, Data.shape, Data.premiseRows, List.map_cons, List.map_nil,
    List.cons.injEq, and_true]
  apply Hypersequent.ext
  simp [row, extend, ← Multiset.cons_coe, contextList]
@[simp] theorem ec_conclusion (key : Nat) (G : Hypersequent sigma) (S : Sequent sigma) (i : Nat) :
    (occurrence key (.ec G S i)).shape.conclusion = G := by
  apply Hypersequent.ext
  simp [occurrence, Data.shape, Data.conclusionRow, row]

noncomputable def retainedIndex (G : Hypersequent sigma) (S : Sequent sigma)
    (member : S ∈ G.components) : Fin (contextList G.components).length :=
  Classical.choose (List.mem_iff_get.mp (Multiset.mem_toList.mpr member))
theorem retainedIndex_get (G : Hypersequent sigma) (S : Sequent sigma)
    (member : S ∈ G.components) : (contextList G.components).get (retainedIndex G S member) = S :=
  Classical.choose_spec (List.mem_iff_get.mp (Multiset.mem_toList.mpr member))

theorem no_unconditional_hlj_interface {n : Nat} (p : ContractionBoundaries.Problem sigma n)
    (A : Formula sigma) : ¬ Nonempty (ContractionPostponement.RuleInterface (theory sigma) p) := by
  rintro ⟨r⟩
  let G : Hypersequent sigma := .singleton ⟨{A}, {A}⟩
  let bad : Sequent sigma := ⟨0, {A, A}⟩
  have whole := (strict_wholeValid (r.ew_admitted G bad)).2
  rw [r.ew_conclusion] at whole
  have absurd := whole bad (by simp [extend])
  simp [Single, bad] at absurd

#check @no_unconditional_hlj_interface
#print axioms no_unconditional_hlj_interface
#print axioms com_premises
#print axioms com_conclusion
#print axioms strict_wholeValid
end Potkin.Research.HLJStructural

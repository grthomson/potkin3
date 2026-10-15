import Potkin.Research.PreparedSysComSource
import Potkin.Research.HLJInternalWeakening
import Potkin.Research.HLJStructuralApplication

/-!
# Actual identity/IW donor translation for the prepared Sys(com) application

Both source and target words follow the same list of formula additions.  An IW
at depth d retains key base+d; all target identities use the explicitly shared
descriptor 50.  This is a specified key translation, not a cast of checked
proofs between registries.  The target uses the existing native CKTree and the
strict additive identity/Com/EW/EC/IW admission layer.

The word family is universal in its formula list.  It does not claim a compiler
for every ordinary LJ rule or all prepared source derivations.
-/
namespace Potkin.Research.PreparedSysComGround

open ContractionBoundaries ContractionPostponement

abbrev Formula := D3SourceEncoding.Formula
abbrev Data := HLJInternalWeakening.Data D3SourceEncoding.signature

def wordBoundary (A : Formula) (xs : List Formula) : Hypersequent D3SourceEncoding.signature :=
  D3SourceEncoding.boundary ⟨PreparedSysComSource.wordContext A xs, {A}⟩

noncomputable def identityOccurrence (A : Formula) : LocalOccurrence D3SourceEncoding.signature Data :=
  HLJInternalWeakening.oldOccurrence 50 (.identity (D3SourceEncoding.encodeFormula A))

@[simp] theorem identity_id (A : Formula) : (identityOccurrence A).id = 50 := rfl
@[simp] theorem identity_premises (A : Formula) :
    (identityOccurrence A).shape.premises = [] := rfl

theorem identity_conclusion (A : Formula) :
    (identityOccurrence A).shape.conclusion = wordBoundary A [] := by
  change Hypersequent.singleton ⟨{D3SourceEncoding.encodeFormula A}, {D3SourceEncoding.encodeFormula A}⟩ = _
  simp [wordBoundary, D3SourceEncoding.boundary, D3SourceEncoding.encodeSequent, PreparedSysComSource.wordContext]

theorem identity_admitted (A : Formula) :
    (HLJInternalWeakening.theory D3SourceEncoding.signature).Admits (identityOccurrence A) :=
  HLJInternalWeakening.lift_admitted _ (HLJStructuralApplication.identity_admitted 50 (D3SourceEncoding.encodeFormula A))

noncomputable def wordOccurrence (key : Nat) (A x : Formula) (xs : List Formula) :
    LocalOccurrence D3SourceEncoding.signature Data :=
  HLJInternalWeakening.iwOccurrence key 0 (D3SourceEncoding.encodeFormula x) (D3SourceEncoding.encodeContext (PreparedSysComSource.wordContext A xs))
    {D3SourceEncoding.encodeFormula A}

@[simp] theorem wordOccurrence_id (key : Nat) (A x : Formula) (xs : List Formula) :
    (wordOccurrence key A x xs).id = key := rfl

theorem wordOccurrence_premises (key : Nat) (A x : Formula) (xs : List Formula) :
    (wordOccurrence key A x xs).shape.premises = [wordBoundary A xs] := by
  rw [wordOccurrence, HLJInternalWeakening.iw_premises, extend_zero]
  simp [wordBoundary, D3SourceEncoding.boundary, D3SourceEncoding.encodeSequent]

theorem wordOccurrence_conclusion (key : Nat) (A x : Formula) (xs : List Formula) :
    (wordOccurrence key A x xs).shape.conclusion = wordBoundary A (x :: xs) := by
  rw [wordOccurrence, HLJInternalWeakening.iw_conclusion, extend_zero]
  simp [wordBoundary, D3SourceEncoding.boundary, D3SourceEncoding.encodeSequent,
    PreparedSysComSource.wordContext, D3SourceEncoding.encodeContext]

theorem wordOccurrence_admitted (key : Nat) (A x : Formula) (xs : List Formula) :
    (HLJInternalWeakening.theory D3SourceEncoding.signature).Admits (wordOccurrence key A x xs) :=
  HLJInternalWeakening.iw_admitted _ _ _ _ _ (by simp) (by simp)

/-- Same constructor and formula order as `PreparedSysComSource.wordTree`.
The sole deliberate lookup-key change is identity base+length to 50. -/
noncomputable def wordTree (key : Nat) (A : Formula) : (xs : List Formula) →
    CKTree D3SourceEncoding.signature Data (wordBoundary A xs)
  | [] => node (identityOccurrence A) (identity_premises A) (identity_conclusion A) .nil
  | x :: xs => node (wordOccurrence key A x xs) (wordOccurrence_premises key A x xs)
      (wordOccurrence_conclusion key A x xs)
      (.cons (wordTree (key + 1) A xs) .nil)

/-- An actual source/target rule-constructor relation.  Its constructors pair
identity with identity and the same indexed source IW with its exact native IW.
It is not defined by equality of boundaries or by the theorem below. -/
inductive WordTranslation (A : Formula) :
    {gamma : D3SourceEncoding.Context} →
    D3SourceEncoding.Diagram ⟨gamma, {A}⟩ →
    CKTree D3SourceEncoding.signature Data (D3SourceEncoding.boundary ⟨gamma, {A}⟩) → Prop where
  | identity (key : Nat) :
      WordTranslation A (.rule key (.identity A) .nil)
        (node (identityOccurrence A) (identity_premises A) (identity_conclusion A) .nil)
  | weakening (key : Nat) (x : Formula) (xs : List Formula)
      {source : D3SourceEncoding.Diagram ⟨PreparedSysComSource.wordContext A xs, {A}⟩}
      {target : CKTree D3SourceEncoding.signature Data (wordBoundary A xs)}
      (translated : WordTranslation A source target) :
      WordTranslation A
        (.rule key (.weakening x (PreparedSysComSource.wordContext A xs) {A}) (.cons source .nil))
        (node (wordOccurrence key A x xs) (wordOccurrence_premises key A x xs)
          (wordOccurrence_conclusion key A x xs) (.cons target .nil))

theorem wordTree_translation (key : Nat) (A : Formula) (xs : List Formula) :
    WordTranslation A (PreparedSysComSource.wordTree key A xs) (wordTree key A xs) := by
  induction xs generalizing key with
  | nil => exact .identity key
  | cons x xs ih => exact .weakening key x xs (ih (key + 1))

noncomputable def wordStock (key : Nat) (A : Formula) : List Formula →
    List (LocalOccurrence D3SourceEncoding.signature Data)
  | [] => []
  | x :: xs => wordOccurrence key A x xs :: wordStock (key + 1) A xs

@[simp] theorem wordStock_length (key : Nat) (A : Formula) (xs : List Formula) :
    (wordStock key A xs).length = xs.length := by
  induction xs generalizing key with
  | nil => rfl
  | cons x xs ih => simp only [wordStock, List.length_cons, ih]

theorem wordStock_ids (key : Nat) (A : Formula) (xs : List Formula) :
    (wordStock key A xs).map LocalOccurrence.id = List.range' key xs.length := by
  induction xs generalizing key with
  | nil => rfl
  | cons x xs ih =>
      simp only [wordStock, List.map_cons, wordOccurrence_id, List.length_cons,
        List.range'_succ, ih]

theorem wordStock_admitted (key : Nat) (A : Formula) (xs : List Formula) :
    ∀ o ∈ wordStock key A xs, (HLJInternalWeakening.theory D3SourceEncoding.signature).Admits o := by
  induction xs generalizing key with
  | nil => intro o member; cases member
  | cons x xs ih =>
      intro o member
      rcases List.mem_cons.mp member with rfl | member
      · exact wordOccurrence_admitted _ _ _ _
      · exact ih _ o member

theorem wordTree_complete (key : Nat) (A : Formula) (xs : List Formula) :
    (wordTree key A xs).IsComplete := by
  induction xs generalizing key with
  | nil => simp [wordTree, CKChildren.IsComplete]
  | cons x xs ih => simp [wordTree, CKChildren.IsComplete, ih]

theorem wordTree_ordinary (key : Nat) (A : Formula) (xs : List Formula) :
    (wordTree key A xs).IsOrdinary :=
  StructuralLemmaCuts.complete_ordinary _ (wordTree_complete key A xs)

theorem wordTree_degree (key : Nat) (A : Formula) (xs : List Formula) :
    (wordTree key A xs).degree = xs.length + 1 := by
  induction xs generalizing key with
  | nil => simp [wordTree, CKChildren.degree]
  | cons x xs ih => simp [wordTree, CKChildren.degree, ih]

/-- Generic node predicate over this exact native constructor language. -/
theorem wordTree_all (R : LocalOccurrence D3SourceEncoding.signature Data → Prop)
    (key : Nat) (A : Formula) (xs : List Formula)
    (identity : R (identityOccurrence A))
    (stock : ∀ o ∈ wordStock key A xs, R o) : AllNodes R (wordTree key A xs) := by
  induction xs generalizing key with
  | nil => exact (node_all _ _ _ _ _).mpr ⟨identity, trivial⟩
  | cons x xs ih =>
      apply (node_all _ _ _ _ _).mpr
      refine ⟨stock _ List.mem_cons_self, ?_⟩
      exact ⟨ih (key + 1) (fun o member => stock o (List.mem_cons_of_mem _ member)), trivial⟩

theorem wordTree_admitted (key : Nat) (A : Formula) (xs : List Formula) :
    AllNodes ((HLJInternalWeakening.theory D3SourceEncoding.signature).Admits) (wordTree key A xs) :=
  wordTree_all _ key A xs (identity_admitted A) (wordStock_admitted key A xs)

theorem wordTree_members (key : Nat) (A : Formula) (xs : List Formula) :
    AllNodes (fun o => o ∈ wordStock key A xs ++ [identityOccurrence A])
      (wordTree key A xs) :=
  wordTree_all _ key A xs (by simp) (fun o member => List.mem_append_left _ member)

/-- Finite registry membership, not only schema admission, is required here. -/
theorem wordTree_registered (P : EquippedPresentation (HLJInternalWeakening.theory D3SourceEncoding.signature))
    (key : Nat) (A : Formula) (xs : List Formula)
    (identity : identityOccurrence A ∈ P.registry)
    (stock : ∀ o ∈ wordStock key A xs, o ∈ P.registry) :
    LocallyAdmittedTree P (wordTree key A xs) :=
  (ContractionPostponement.RuleInterface.registered_all _).mp
    (wordTree_all _ key A xs identity stock)

noncomputable def checkedWord [DecidableEq (Hypersequent D3SourceEncoding.signature)]
    (P : EquippedPresentation (HLJInternalWeakening.theory D3SourceEncoding.signature)) (key : Nat) (A : Formula) (xs : List Formula)
    (identity : identityOccurrence A ∈ P.registry)
    (stock : ∀ o ∈ wordStock key A xs, o ∈ P.registry) :
    CheckedDerivation P (wordBoundary A xs) :=
  CompleteQuotation.checkedOfComplete P (wordTree key A xs)
    (wordTree_registered P key A xs identity stock) (wordTree_complete key A xs)

theorem checkedWord_realize [DecidableEq (Hypersequent D3SourceEncoding.signature)]
    (P : EquippedPresentation (HLJInternalWeakening.theory D3SourceEncoding.signature)) (key : Nat) (A : Formula) (xs : List Formula)
    (identity : identityOccurrence A ∈ P.registry)
    (stock : ∀ o ∈ wordStock key A xs, o ∈ P.registry) :
    (checkedWord P key A xs identity stock).realize = wordTree key A xs :=
  CompleteQuotation.quote_realize _ _ _ _

#print axioms wordStock_admitted
#print axioms wordTree_translation
#print axioms wordTree_registered
#print axioms checkedWord_realize

end Potkin.Research.PreparedSysComGround

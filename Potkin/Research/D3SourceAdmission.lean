import Potkin.Research.D3SourceEncoding
import Potkin.Research.D3RegistryAdmission

/-!
# Conditional finite admission of the independently specified source fragment

One finite family is admitted with its descriptors and stable system tokens
unchanged. Consistent descriptor-key allocation remains an explicit hypothesis;
this is neither an allocator nor one finite stock for all formula instances.
-/

namespace Potkin.Research.D3SourceAdmission

open D3SourceEncoding D3RegistryAdmission OpenDischarge

def base : MaterialBase signature (Data signature) PrimitiveFragment.full where
  Member := fun _ => False
  member_material := fun h => False.elim h
  member_primitiveBoundary := fun h => False.elim h

def theory : ProofTheory signature (Data signature) where
  primitive := .full
  base := base
  rules := { logical := fun o => ExactInstance Imp o ∧ o.kind = .logical
             structural := fun o => ExactInstance Imp o ∧ o.kind = .structural }
  initial := fun _ => False

theorem rule_admitted (key : Nat) (r : Rule) (valid : r.Valid) :
    theory.Admits (occurrence key r) := by
  have exactRule : ExactInstance Imp (occurrence key r) :=
    (exact_instance_iff key r).mpr valid
  cases r <;>
    first | exact .logical rfl ⟨exactRule, rfl⟩
          | exact .structural rfl ⟨exactRule, rfl⟩

mutual
theorem descriptors_admitted : {S : D3SourceEncoding.Sequent} → (D : Diagram S) →
    LocallyCorrect D → ∀ o ∈ occurrences (encode D), theory.Admits o
  | _, .hole _, _, _, present => by cases present
  | _, .rule key r children, correct, o, present => by
      change o ∈ occurrence key r :: childOccurrences (encodeChildren children) at present
      rcases List.mem_cons.mp present with equal | present
      · cases equal
        exact rule_admitted key r correct.1
      · exact child_descriptors_admitted children correct.2 o present
theorem child_descriptors_admitted : {Ss : List D3SourceEncoding.Sequent} →
    (Ds : Children Ss) → ChildrenCorrect Ds →
      ∀ o ∈ childOccurrences (encodeChildren Ds), theory.Admits o
  | _, .nil, _, _, present => by cases present
  | _, .cons head tail, correct, o, present => by
      change o ∈ occurrences (encode head) ++ childOccurrences (encodeChildren tail) at present
      rcases List.mem_append.mp present with present | present
      · exact descriptors_admitted head correct.1 o present
      · exact child_descriptors_admitted tail correct.2 o present
end

def nativeFamily (family : List (Sigma Diagram)) :
    List (Sigma (CKTree signature (Data signature))) :=
  family.map fun p => ⟨boundary p.1, encode p.2⟩

/-- All family members share ONE validated immutable registry; physical uses
and lookup keys, including repeated exact descriptors, are unchanged. -/
theorem finite_source_admission (family : List (Sigma Diagram))
    (correct : ∀ p ∈ family, LocallyCorrect p.2)
    (keys : ConsistentKeys ((nativeFamily family).flatMap fun p => occurrences p.2)) :
    ∃ registry : EquippedPresentation theory,
      ∀ p ∈ family, LocallyAdmittedTree registry (encode p.2) := by
  have valid : ∀ o ∈ (nativeFamily family).flatMap (fun p => occurrences p.2),
      theory.Admits o := by
    intro o present
    rcases List.mem_flatMap.mp present with ⟨p, hp, present⟩
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact descriptors_admitted q.2 (correct q hq) o present
  rcases finite_family_admission theory (nativeFamily family) keys valid with
    ⟨registry, admitted⟩
  refine ⟨registry, ?_⟩
  intro p hp
  exact admitted ⟨boundary p.1, encode p.2⟩ (List.mem_map.mpr ⟨p, hp, rfl⟩)

variable [DecidableEq (Hypersequent signature)]

/-- A source vacancy is never quoted as a closed checked derivation. -/
def checkedSource (registry : EquippedPresentation theory)
    {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (admitted : LocallyAdmittedTree registry (encode D))
    (complete : (encode D).IsComplete) : CheckedDerivation registry (boundary S) :=
  CompleteQuotation.checkedOfComplete registry (encode D) admitted complete

theorem checkedSource_realize (registry : EquippedPresentation theory)
    {S : D3SourceEncoding.Sequent} (D : Diagram S)
    (admitted : LocallyAdmittedTree registry (encode D))
    (complete : (encode D).IsComplete) :
    (checkedSource registry D admitted complete).realize = encode D :=
  CompleteQuotation.quote_realize registry (encode D) admitted complete

#check @finite_source_admission
#print axioms rule_admitted
#print axioms descriptors_admitted
#print axioms finite_source_admission
#print axioms checkedSource_realize

end Potkin.Research.D3SourceAdmission

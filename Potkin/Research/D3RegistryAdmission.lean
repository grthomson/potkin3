import Potkin.CompleteQuotation
import Mathlib.Data.List.Dedup

/-!
# Finite exact-descriptor admission, separate from rule discharge

Keys belong to immutable rule descriptors, not to physical occurrences or
system owners. Repeated physical uses may share a key. A common registry
requires consistency of existing keys; this module never repairs a conflict by
changing an owner/reference token. Extension below means exact membership
preservation, not logical conservativity.
-/

namespace Potkin.Research.D3RegistryAdmission

universe u v w
variable {sigma : Signature.{u, v}} {D : Type w}

mutual
def occurrences : {G : Hypersequent sigma} → CKTree sigma D G →
    List (LocalOccurrence sigma D)
  | _, .interface _ => []
  | _, .ordinary o children => o :: childOccurrences children

def childOccurrences : {Gs : List (Hypersequent sigma)} → CKChildren sigma D Gs →
    List (LocalOccurrence sigma D)
  | _, .nil => []
  | _, .cons head tail => occurrences head ++ childOccurrences tail
end

/-- Consistent descriptor keys, allowing repeated uses of precisely one descriptor. -/
def ConsistentKeys (xs : List (LocalOccurrence sigma D)) : Prop :=
  ∀ o ∈ xs, ∀ p ∈ xs, o.id = p.id → o = p

noncomputable def finitePresentation (T : ProofTheory sigma D)
    (xs : List (LocalOccurrence sigma D)) (keys : ConsistentKeys xs)
    (valid : ∀ o ∈ xs, T.Admits o) : EquippedPresentation T := by
  classical
  exact {
    registry := xs.dedup
    uniqueIds := (List.nodup_dedup xs).map_on (by
      intro o ho p hp h
      exact keys o (List.mem_dedup.mp ho) p (List.mem_dedup.mp hp) h)
    admitted := fun o ho => valid o (List.mem_dedup.mp ho) }

@[simp] theorem mem_finitePresentation (T : ProofTheory sigma D)
    (xs : List (LocalOccurrence sigma D)) (keys : ConsistentKeys xs)
    (valid : ∀ o ∈ xs, T.Admits o) (o : LocalOccurrence sigma D) :
    o ∈ (finitePresentation T xs keys valid).registry ↔ o ∈ xs := by
  classical
  exact List.mem_dedup

mutual
theorem admitted_of_occurrences {T : ProofTheory sigma D} (P : EquippedPresentation T) :
    {G : Hypersequent sigma} → (tree : CKTree sigma D G) →
    (∀ o ∈ occurrences tree, o ∈ P.registry) → LocallyAdmittedTree P tree
  | _, .interface _, _ => trivial
  | _, .ordinary o children, included =>
      ⟨included o (by simp [occurrences]),
        admitted_children_of_occurrences P children (fun p hp =>
          included p (List.mem_cons_of_mem o hp))⟩

theorem admitted_children_of_occurrences {T : ProofTheory sigma D}
    (P : EquippedPresentation T) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma D Gs) →
    (∀ o ∈ childOccurrences children, o ∈ P.registry) →
      LocallyAdmittedChildren P children
  | _, .nil, _ => trivial
  | _, .cons head tail, included =>
      ⟨admitted_of_occurrences P head (fun o ho =>
          included o (List.mem_append_left _ ho)),
        admitted_children_of_occurrences P tail (fun o ho =>
          included o (List.mem_append_right _ ho))⟩
end

/-- Every member of one finite family uses the same unchanged descriptors. -/
theorem finite_family_admission (T : ProofTheory sigma D)
    (family : List (Sigma (CKTree sigma D)))
    (keys : ConsistentKeys (family.flatMap fun p => occurrences p.2))
    (valid : ∀ o ∈ family.flatMap (fun p => occurrences p.2), T.Admits o) :
    ∃ P : EquippedPresentation T,
      ∀ p ∈ family, LocallyAdmittedTree P p.2 := by
  let xs := family.flatMap fun p => occurrences p.2
  refine ⟨finitePresentation T xs keys valid, ?_⟩
  intro p hp
  apply admitted_of_occurrences
  intro o ho
  apply (mem_finitePresentation T xs keys valid o).mpr
  exact List.mem_flatMap.mpr ⟨p, hp, ho⟩

def ExactExtension {T U : ProofTheory sigma D}
    (P : EquippedPresentation T) (Q : EquippedPresentation U) : Prop :=
  ∀ o ∈ P.registry, o ∈ Q.registry

/-- Every successful old lookup retains the entire exact descriptor. -/
theorem lookup_preserved {T U : ProofTheory sigma D}
    {P : EquippedPresentation T} {Q : EquippedPresentation U}
    (extend : ExactExtension P Q) (id : Nat)
    (entry : EquippedPresentation.LookupResult P id) :
    (Q.lookup id).map (fun found => found.occurrence) = some entry.occurrence := by
  rcases entry with ⟨o, registered, rfl⟩
  exact CompleteQuotation.lookup_occurrence Q o (extend o registered)

mutual
theorem admission_extension {T U : ProofTheory sigma D}
    {P : EquippedPresentation T} {Q : EquippedPresentation U}
    (extend : ExactExtension P Q) :
    {G : Hypersequent sigma} → (tree : CKTree sigma D G) →
    LocallyAdmittedTree P tree → LocallyAdmittedTree Q tree
  | _, .interface _, _ => trivial
  | _, .ordinary o children, admitted =>
      ⟨extend o admitted.1, admission_children_extension extend children admitted.2⟩

theorem admission_children_extension {T U : ProofTheory sigma D}
    {P : EquippedPresentation T} {Q : EquippedPresentation U}
    (extend : ExactExtension P Q) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma D Gs) →
    LocallyAdmittedChildren P children → LocallyAdmittedChildren Q children
  | _, .nil, _ => trivial
  | _, .cons head tail, admitted =>
      ⟨admission_extension extend head admitted.1,
        admission_children_extension extend tail admitted.2⟩
end

variable [DecidableEq (Hypersequent sigma)]

/-- Requotation through the public checker, never a private checked constructor. -/
noncomputable def lift {T U : ProofTheory sigma D}
    {P : EquippedPresentation T} {Q : EquippedPresentation U}
    (extend : ExactExtension P Q) {G : Hypersequent sigma}
    (d : CheckedDerivation P G) : CheckedDerivation Q G :=
  CompleteQuotation.checkedOfComplete Q d.realize
    (admission_extension extend d.realize d.realizeLocallyAdmitted)
    d.realizeIsComplete

theorem lift_realize {T U : ProofTheory sigma D}
    {P : EquippedPresentation T} {Q : EquippedPresentation U}
    (extend : ExactExtension P Q) {G : Hypersequent sigma}
    (d : CheckedDerivation P G) : (lift extend d).realize = d.realize :=
  CompleteQuotation.quote_realize Q d.realize
    (admission_extension extend d.realize d.realizeLocallyAdmitted)
    d.realizeIsComplete

/-- Any observer of the decorated native tree, including summaries, is unchanged. -/
theorem lift_observation {T U : ProofTheory sigma D}
    {P : EquippedPresentation T} {Q : EquippedPresentation U}
    (extend : ExactExtension P Q) {G : Hypersequent sigma}
    (d : CheckedDerivation P G) {A : Sort*} (observe : CKTree sigma D G → A) :
    observe (lift extend d).realize = observe d.realize :=
  congrArg observe (lift_realize extend d)

omit [DecidableEq (Hypersequent sigma)] in
/-- Extending a finite stock preserves its entire old lookup domain exactly. -/
theorem finite_extension {T : ProofTheory sigma D}
    (P : EquippedPresentation T) (extra : List (LocalOccurrence sigma D))
    (keys : ConsistentKeys (P.registry ++ extra))
    (valid : ∀ o ∈ extra, T.Admits o) :
    ∃ Q : EquippedPresentation T, ExactExtension P Q ∧
      ∀ o ∈ extra, o ∈ Q.registry := by
  let allValid : ∀ o ∈ P.registry ++ extra, T.Admits o := by
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact P.admitted o ho
    · exact valid o ho
  refine ⟨finitePresentation T (P.registry ++ extra) keys allValid, ?_, ?_⟩
  · intro o ho
    exact (mem_finitePresentation _ _ _ _ o).mpr (List.mem_append_left _ ho)
  · intro o ho
    exact (mem_finitePresentation _ _ _ _ o).mpr (List.mem_append_right _ ho)

#check @finite_family_admission
#check @lift_realize
#check @lookup_preserved
#check @finite_extension
#print axioms finite_family_admission
#print axioms lift_realize
#print axioms lookup_preserved
#print axioms finite_extension
end Potkin.Research.D3RegistryAdmission

import Potkin.GeneralFilling
import Mathlib.Data.List.Nodup

/-!
# Public quotation of complete native proofs

Quotation keeps every ordered physical occurrence.  Local admission and
completeness are independent hypotheses: admitted typed Boxes are not proofs.
Only the existing public checker constructs the returned checked derivation.
-/

namespace Potkin.CompleteQuotation

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData}

mutual

/-- Quote native occurrences by their exact immutable-registry IDs. -/
def quote : {G : Hypersequent sigma} → CKTree sigma InstanceData G → RawDerivation sigma
  | _, .interface _ => .puncture
  | _, .ordinary o children => .node o.id (quoteChildren children)

/-- Native premise order and physical multiplicities are retained literally. -/
def quoteChildren : {Gs : List (Hypersequent sigma)} →
    CKChildren sigma InstanceData Gs → RawChildren sigma
  | _, .nil => .nil
  | _, .cons head tail => .cons (quote head) (quoteChildren tail)

end

@[simp] theorem quoteChildren_length : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) →
    (quoteChildren children).length = Gs.length
  | _, .nil => rfl
  | _, .cons _ tail => by
      simp [quoteChildren, RawChildren.length, quoteChildren_length tail]

/-- Registry uniqueness resolves an ID back to that exact decorated occurrence. -/
theorem lookup_occurrence (P : EquippedPresentation T)
    (o : LocalOccurrence sigma InstanceData) (registered : o ∈ P.registry) :
    (P.lookup o.id).map (fun entry => entry.occurrence) = some o := by
  rcases P with ⟨registry, unique, admitted⟩
  induction registry with
  | nil => cases registered
  | cons head tail ih =>
      have uniqueTail : (tail.map LocalOccurrence.id).Nodup :=
        (List.nodup_cons.mp unique).2
      have admittedTail : ∀ o, o ∈ tail → T.Admits o :=
        fun o ho => admitted o (List.mem_cons_of_mem head ho)
      by_cases same : head.id = o.id
      · have eq : head = o := List.inj_on_of_nodup_map unique
          (by simp) registered same
        subst o
        simp! [EquippedPresentation.lookup]
      · have memberTail : o ∈ tail := by
          rcases List.mem_cons.mp registered with h | h
          · subst o; exact False.elim (same rfl)
          · exact h
        have child := ih uniqueTail admittedTail memberTail
        unfold EquippedPresentation.lookup at child ⊢
        split at child <;> simp_all!

variable [DecidableEq (Hypersequent sigma)]

private theorem check_of_checkAt (P : EquippedPresentation T)
    {G : Hypersequent sigma} {raw : RawDerivation sigma}
    (d : CheckedDerivation P G) (hd : P.checkAt G raw = .ok d) :
    P.check raw = .ok ⟨G, d⟩ := by
  cases hc : P.check raw with
  | error error => simp [EquippedPresentation.checkAt, hc] at hd
  | ok result =>
      rcases result with ⟨actual, derivation⟩
      by_cases ha : actual = G
      · subst actual
        simp only [EquippedPresentation.checkAt, hc, dif_pos rfl, Except.ok.injEq] at hd
        cases hd
        rfl
      · simp [EquippedPresentation.checkAt, hc, ha] at hd

mutual

/-- Universal checker completeness, retaining the literal decorated realization. -/
theorem quote_correct (P : EquippedPresentation T) :
    {G : Hypersequent sigma} → (tree : CKTree sigma InstanceData G) →
    LocallyAdmittedTree P tree → tree.IsComplete →
    ∃ d : CheckedDerivation P G,
      P.checkAt G (quote tree) = .ok d ∧ d.realize = tree
  | _, .interface _, _, complete => False.elim complete
  | _, .ordinary o children, admitted, complete => by
      rcases quoteChildren_correct P children admitted.2 complete o.id 0 with
        ⟨checkedChildren, hc, realized⟩
      have lookupFact := lookup_occurrence P o admitted.1
      cases hl : P.lookup o.id with
      | none => simp [hl] at lookupFact
      | some entry =>
          have equal : entry.occurrence = o := by simpa [hl] using lookupFact
          rcases entry with ⟨found, registered, id_eq⟩
          dsimp at equal
          subst found
          cases hd : P.checkAt o.shape.conclusion (quote (.ordinary o children)) with
          | error error =>
              simp [quote, EquippedPresentation.checkAt, EquippedPresentation.check,
                hl, quoteChildren_length, hc] at hd
          | ok d =>
              refine ⟨d, rfl, ?_⟩
              simp [quote, EquippedPresentation.checkAt, EquippedPresentation.check,
                hl, quoteChildren_length, hc] at hd
              cases hd
              simpa [CheckedDerivation.realize] using congrArg (CKTree.ordinary o) realized

theorem quoteChildren_correct (P : EquippedPresentation T) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma InstanceData Gs) →
    LocallyAdmittedChildren P children → children.IsComplete →
    (parentId slot : Nat) →
    ∃ ds : CheckedChildren P Gs,
      P.checkChildren parentId slot Gs (quoteChildren children) = .ok ds ∧
      CheckedDerivation.CheckedChildren.realize ds = children
  | _, .nil, _, _, _, _ => by
      have success : CheckResult.Succeeded
          (P.checkChildren 0 0 [] (quoteChildren (.nil : CKChildren sigma InstanceData []))) :=
        trivial
      exact ⟨CheckResult.get success, rfl, rfl⟩
  | _, .cons head tail, admitted, complete, parentId, slot => by
      rcases quote_correct P head admitted.1 complete.1 with ⟨dh, hh, rh⟩
      rcases quoteChildren_correct P tail admitted.2 complete.2 parentId (slot + 1) with
        ⟨dt, ht, rt⟩
      have hh' := check_of_checkAt P dh hh
      cases hd : P.checkChildren parentId slot _ (quoteChildren (.cons head tail)) with
      | error error =>
          simp [quoteChildren, EquippedPresentation.checkChildren, hh', ht] at hd
      | ok ds =>
          refine ⟨ds, rfl, ?_⟩
          simp [quoteChildren, EquippedPresentation.checkChildren, hh', ht] at hd
          cases hd
          simp [CheckedDerivation.CheckedChildren.realize, rh, rt]

end

/-- Public checker success; a vacant Box fails the completeness hypothesis. -/
theorem quote_succeeds (P : EquippedPresentation T)
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (admitted : LocallyAdmittedTree P tree) (complete : tree.IsComplete) :
    CheckResult.Succeeded (P.checkAt G (quote tree)) := by
  rcases quote_correct P tree admitted complete with ⟨d, hd, _⟩
  simp [hd, CheckResult.Succeeded]

/-- Construct checked evidence through `checkAt`, never a private constructor. -/
def checkedOfComplete (P : EquippedPresentation T)
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (admitted : LocallyAdmittedTree P tree) (complete : tree.IsComplete) :
    CheckedDerivation P G := CheckResult.get (quote_succeeds P tree admitted complete)

/-- Public quotation preserves the entire native proof, not merely its boundary. -/
theorem quote_realize (P : EquippedPresentation T)
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (admitted : LocallyAdmittedTree P tree) (complete : tree.IsComplete) :
    (checkedOfComplete P tree admitted complete).realize = tree := by
  rcases quote_correct P tree admitted complete with ⟨d, hd, realized⟩
  have h : checkedOfComplete P tree admitted complete = d :=
    Except.ok.inj ((CheckResult.eq_ok_get
      (quote_succeeds P tree admitted complete)).symm.trans hd)
  exact (congrArg CheckedDerivation.realize h).trans realized

#print axioms lookup_occurrence
#print axioms quote_correct
#print axioms quote_succeeds
#print axioms quote_realize

end Potkin.CompleteQuotation

import Potkin.Research.OpenDischarge

/-!
# Independent finite rule-discharge grouping

This module checks an explicit bottom-up schedule of *physical* bottom
declarations.  The source adapter supplies ordered-tree ancestry as `Eligible`;
no native legality predicate or summary evaluator occurs in the definition.

At a bottom declaration `b`, its chosen set consists exactly of the still
pending physical tops assigned to `b`.  The check tests their role, parameter
and branch eligibility, removes them, and continues.  Unselected tops pass
through, a bottom may discharge no tops, and several tops may choose one bottom.
All physical declarations, including unused declarations, remain in the
schedule.  Assignment functions are Type-valued data; the checking predicate
does not identify different choices by proof irrelevance.

The schedule theorem is the finite elimination lemma used by a source-tree
adapter.  It is not by itself a local formula/rule adequacy theorem.
-/

namespace Potkin.Research.D3DischargeGrouping

universe u v
variable {Top : Type u} {Bottom : Type v} [DecidableEq Bottom]

/-- The actual selected occurrences, with original list multiplicities. -/
def selected (pending : List Top) (assignment : Top → Bottom) (b : Bottom) : List Top :=
  pending.filter (fun t => assignment t = b)

/-- A selected physical occurrence is removed; it cannot be discharged again. -/
def survivors (pending : List Top) (assignment : Top → Bottom) (b : Bottom) : List Top :=
  pending.filter (fun t => assignment t ≠ b)

/-- An independent inductive pending-discharge check.  `Eligible` is the source
rule's exact role/parameter/ordered-premise relation, not native `Legal`. -/
inductive PendingConstruction (Eligible : Top → Bottom → Prop)
    (assignment : Top → Bottom) : List Top → List Bottom → Prop where
  | done : PendingConstruction Eligible assignment [] []
  | step {pending : List Top} {b : Bottom} {bs : List Bottom}
      (admitted : ∀ t ∈ selected pending assignment b, Eligible t b)
      (rest : PendingConstruction Eligible assignment
        (survivors pending assignment b) bs) :
      PendingConstruction Eligible assignment pending (b :: bs)

/-- Exact invariant: a top is still pending iff its chosen bottom has not yet
been processed.  This is occurrence-resolved, not an inventory count. -/
def remaining (initial : List Top) (assignment : Top → Bottom)
    (processed : List Bottom) : List Top :=
  initial.filter (fun t => assignment t ∉ processed)

theorem remaining_nil (initial : List Top) (assignment : Top → Bottom) :
    remaining initial assignment [] = initial := by
  simp [remaining]

theorem remaining_step (initial : List Top) (assignment : Top → Bottom)
    (processed : List Bottom) (b : Bottom) :
    survivors (remaining initial assignment processed) assignment b =
      remaining initial assignment (processed ++ [b]) := by
  simp [survivors, remaining, List.filter_filter, Bool.and_comm, and_comm]

theorem mem_remaining (initial : List Top) (assignment : Top → Bottom)
    (processed : List Bottom) (t : Top) :
    t ∈ remaining initial assignment processed ↔
      t ∈ initial ∧ assignment t ∉ processed := by
  simp [remaining]

theorem selected_remaining_eq (initial : List Top) (assignment : Top → Bottom)
    (processed : List Bottom) (b : Bottom) (unprocessed : b ∉ processed) :
    selected (remaining initial assignment processed) assignment b =
      selected initial assignment b := by
  simp only [selected, remaining, List.filter_filter]
  apply congrArg (fun predicate : Top → Bool => initial.filter predicate)
  funext t
  by_cases chosen : assignment t = b
  · simp [chosen, unprocessed]
  · simp [chosen]

theorem remaining_append (left right : List Top) (assignment : Top → Bottom)
    (processed : List Bottom) :
    remaining (left ++ right) assignment processed =
      remaining left assignment processed ++ remaining right assignment processed := by
  simp [remaining]

theorem process_remaining (initial : List Top) (assignment : Top → Bottom)
    (processed schedule : List Bottom) :
    schedule.foldl (fun pending b => survivors pending assignment b)
      (remaining initial assignment processed) =
      remaining initial assignment (processed ++ schedule) := by
  induction schedule generalizing processed with
  | nil => simp
  | cons b bs ih =>
      simp only [List.foldl_cons]
      rw [remaining_step, ih]
      simp [List.append_assoc]

/-- Actual finite elimination computes the exact pending-outside invariant.
This is valid for any subtree inventory supplied by the source adapter, not
only a particular evaluated fixture. -/
theorem process_pending_outside (initial : List Top) (assignment : Top → Bottom)
    (subtreeBottoms : List Bottom) :
    subtreeBottoms.foldl (fun pending b => survivors pending assignment b) initial =
      initial.filter (fun t => assignment t ∉ subtreeBottoms) := by
  simpa [remaining] using process_remaining initial assignment [] subtreeBottoms

/-- The exact subtree invariant, once the source adapter has supplied the
physical bottom inventory of that subtree.  The list on the left retains
physical top occurrences and their original multiplicities. -/
theorem pending_outside_subtree (subtreeTops : List Top)
    (assignment : Top → Bottom) (subtreeBottoms : List Bottom) :
    remaining subtreeTops assignment subtreeBottoms =
      subtreeTops.filter (fun t => assignment t ∉ subtreeBottoms) := rfl

theorem selected_never_survives (pending : List Top) (assignment : Top → Bottom)
    (b : Bottom) (t : Top) (chosen : t ∈ selected pending assignment b) :
    t ∉ survivors pending assignment b := by
  have selectedData : t ∈ pending ∧ assignment t = b := by
    simpa [selected] using chosen
  intro remains
  have survivorData : t ∈ pending ∧ assignment t ≠ b := by
    simpa [survivors] using remains
  exact survivorData.2 selectedData.2

/-- The pending construction accepts exactly complete eligible assignments.
No nearest-owner condition, injectivity or surjectivity is imposed on the
assignment.  The schedule may include unused bottoms. -/
theorem pendingConstruction_iff (Eligible : Top → Bottom → Prop)
    (assignment : Top → Bottom) (pending : List Top) (schedule : List Bottom) :
    PendingConstruction Eligible assignment pending schedule ↔
      ∀ t ∈ pending, assignment t ∈ schedule ∧ Eligible t (assignment t) := by
  induction schedule generalizing pending with
  | nil =>
      constructor
      · intro checked
        cases checked
        simp
      · intro complete
        have empty : pending = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro t present
          exact List.not_mem_nil (complete t present).1
        subst pending
        exact .done
  | cons b bs ih =>
      constructor
      · intro checked
        cases checked with
        | step admitted rest =>
          have tail := (ih _).mp rest
          intro t present
          by_cases chosen : assignment t = b
          · exact ⟨List.mem_cons.mpr (Or.inl chosen),
              chosen.symm ▸ admitted t (by simp [selected, present, chosen])⟩
          · have h := tail t (by simp [survivors, present, chosen])
            exact ⟨List.mem_cons.mpr (Or.inr h.1), h.2⟩
      · intro complete
        apply PendingConstruction.step
        · intro t chosen
          have data : t ∈ pending ∧ assignment t = b := by
            simpa [selected] using chosen
          have h := (complete t data.1).2
          exact data.2 ▸ h
        · apply (ih _).mpr
          intro t remains
          have data : t ∈ pending ∧ assignment t ≠ b := by
            simpa [survivors] using remains
          have h := complete t data.1
          exact ⟨(List.mem_cons.mp h.1).resolve_left data.2, h.2⟩

/-- Grouping data retain the actual chosen bottom for each physical top.
For finite counting, the adapter must supply a complete physical inventory;
the later named theorem makes this assumption explicit. -/
structure Grouping (Eligible : Top → Bottom → Prop)
    (tops : List Top) (schedule : List Bottom) where
  assignment : Top → Bottom
  construction : PendingConstruction Eligible assignment tops schedule

/-- Geometric assignments are a separate specification. -/
structure EligibleAssignment (Eligible : Top → Bottom → Prop)
    (tops : List Top) (bottoms : List Bottom) where
  assignment : Top → Bottom
  correct : ∀ t ∈ tops, assignment t ∈ bottoms ∧ Eligible t (assignment t)

/-- Restriction and reconstruction are literal inverses on choices. -/
def groupingAssignmentEquiv (Eligible : Top → Bottom → Prop)
    (tops : List Top) (bottoms : List Bottom) :
    Grouping Eligible tops bottoms ≃ EligibleAssignment Eligible tops bottoms where
  toFun g := ⟨g.assignment, (pendingConstruction_iff _ _ _ _).mp g.construction⟩
  invFun a := ⟨a.assignment, (pendingConstruction_iff _ _ _ _).mpr a.correct⟩
  left_inv g := by cases g; rfl
  right_inv a := by cases a; rfl

/-- Naming every physical declaration supplies its top references.  It does
not discard unused declarations from the schedule. -/
def annotateGrouping (Eligible : Top → Bottom → Prop)
    (tops : List Top) (bottoms : List Bottom) (name : Bottom → Nat)
    (g : Grouping Eligible tops bottoms) :
    Grouping (fun t b => Eligible t b ∧ name (g.assignment t) = name b)
      tops bottoms := by
  refine ⟨g.assignment, (pendingConstruction_iff _ _ _ _).mpr ?_⟩
  intro t present
  have h := (pendingConstruction_iff _ _ _ _).mp g.construction t present
  exact ⟨h.1, h.2, rfl⟩

@[simp] theorem annotateGrouping_assignment (Eligible : Top → Bottom → Prop)
    (tops : List Top) (bottoms : List Bottom) (name : Bottom → Nat)
    (g : Grouping Eligible tops bottoms) :
    (annotateGrouping Eligible tops bottoms name g).assignment = g.assignment := rfl

/-- An injective naming of all declarations recovers the chosen physical
grouping uniquely.  This is a closed-inventory statement, not permission to
rename an open fragment while fixing arbitrary outside references. -/
theorem faithful_annotation (Eligible : Top → Bottom → Prop)
    (tops : List Top) (bottoms : List Bottom) (completeTops : ∀ t : Top, t ∈ tops)
    (name : Bottom → Nat) (injective : Function.Injective name)
    (g : Grouping Eligible tops bottoms)
    (named : Grouping (fun t b => Eligible t b ∧ name (g.assignment t) = name b)
      tops bottoms) :
    named.assignment = g.assignment := by
  funext t
  have h := (pendingConstruction_iff _ _ _ _).mp named.construction t (completeTops t)
  exact injective h.2.2.symm

/-- Any eligible ancestor may be chosen.  There is no nearest-bottom
convention and no requirement that a bottom discharge only one top. -/
noncomputable def reassignGrouping (Eligible : Top → Bottom → Prop)
    (tops : List Top) (bottoms : List Bottom) (g : Grouping Eligible tops bottoms)
    (t : Top) (b : Bottom) (present : b ∈ bottoms) (eligible : Eligible t b) :
    Grouping Eligible tops bottoms := by
  classical
  refine ⟨fun x => if x = t then b else g.assignment x,
    (pendingConstruction_iff _ _ _ _).mpr ?_⟩
  intro x hx
  by_cases same : x = t
  · subst x
    simpa using And.intro present eligible
  · simpa [same] using
      (pendingConstruction_iff _ _ _ _).mp g.construction x hx

/-- A raw tree with two eligible same-parameter ancestor bottoms need not
have a unique grouping.  The two witnesses differ in physical discharge
choice even when their displayed rules and sequents are identical. -/
theorem two_eligible_choices_distinct (Eligible : Top → Bottom → Prop)
    (tops : List Top) (bottoms : List Bottom) (g : Grouping Eligible tops bottoms)
    (t : Top) (_physical : t ∈ tops) (a b : Bottom) (ha : a ∈ bottoms) (hb : b ∈ bottoms)
    (ea : Eligible t a) (eb : Eligible t b) (different : a ≠ b) :
    reassignGrouping Eligible tops bottoms g t a ha ea ≠
      reassignGrouping Eligible tops bottoms g t b hb eb := by
  classical
  intro equal
  apply different
  have h := congrArg (fun (group : Grouping Eligible tops bottoms) => group.assignment t) equal
  simpa [reassignGrouping] using h

/-- Physical declaration identities remain separate from their names.
This theorem requires *all* bottoms to occur in the schedule. -/
theorem named_grouping_iff (Eligible : Top → Bottom → Prop)
    (tops : List Top) (bottoms : List Bottom)
    (completeTops : ∀ t : Top, t ∈ tops)
    (reference : Top → Nat) (name : Bottom → Nat) :
    Nonempty (Grouping
      (fun t b => Eligible t b ∧ reference t = name b) tops bottoms) ↔
      ∀ t ∈ tops, ∃ b ∈ bottoms, Eligible t b ∧ reference t = name b := by
  classical
  constructor
  · rintro ⟨g⟩ t present
    have h := (pendingConstruction_iff _ _ _ _).mp g.construction t present
    exact ⟨g.assignment t, h.1, h.2⟩
  · intro h
    let assignment : Top → Bottom := fun t => Classical.choose (h t (completeTops t))
    refine ⟨⟨assignment, (pendingConstruction_iff _ _ _ _).mpr ?_⟩⟩
    intro t present
    exact Classical.choose_spec (h t (completeTops t))

#check @pendingConstruction_iff
#check @groupingAssignmentEquiv
#check @named_grouping_iff
#print axioms pendingConstruction_iff
#print axioms groupingAssignmentEquiv
#print axioms process_pending_outside
#print axioms faithful_annotation
#print axioms two_eligible_choices_distinct
#print axioms named_grouping_iff

end Potkin.Research.D3DischargeGrouping

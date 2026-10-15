import Potkin.Research.D3SourceAdequacy

/-!
# A genuinely prepared, nested Sys(com) source

This is the native source `Diagram`, not a second proof carrier.  The outer
instance X has two physical role-zero applications and one role-one
application.  The inner instance Y joins the two former branches.  Both use
the genuine shared parameters Phi={A}, Psi={B}; neither bottom is dummy.
Ordinary donors contain only identity and internal weakening.  Their source
correctness and preparation are proved independently of target translation.
-/
namespace Potkin.Research.PreparedSysComSource
open D3SourceEncoding D3SourceAdequacy

abbrev Formula := D3SourceEncoding.Formula
abbrev Context := D3SourceEncoding.Context
abbrev Sequent := D3SourceEncoding.Sequent
abbrev Parameters := D3SourceEncoding.Parameters

def parameters (A B : Formula) : Parameters := ⟨{A}, {B}⟩
def gammaA (A C : Formula) : Context := {A} + {A} + {A} + {C}
def gammaB (A B C : Formula) : Context := {A} + {B} + {B} + {C}
def gammaY (A B C : Formula) : Context := {A} + {A} + {B} + {C}

def donorBoundary (A B C : Formula) (i : Fin 3) : Sequent :=
  if i.val = 0 then topInput 0 (parameters A B) (gammaA A C) {A}
  else if i.val = 1 then topInput 0 (parameters A B) (gammaB A B C) {A}
  else topInput 1 (parameters A B) (gammaB A B C) {A}

def common (A B C : Formula) : Sequent :=
  topOutput 1 (parameters A B) (gammaB A B C) {A}
def leftIntermediate (A B C : Formula) : Sequent :=
  topOutput 0 (parameters A B) (gammaA A C) {A}
def rightIntermediate (A B C : Formula) : Sequent :=
  topOutput 0 (parameters A B) (gammaB A B C) {A}

def transport {S T : Sequent} (equal : S = T) (D : Diagram S) : Diagram T :=
  equal ▸ D

@[simp] theorem transport_complete {S T : Sequent} (equal : S = T) (D : Diagram S) :
    (transport equal D).Complete ↔ D.Complete := by cases equal; rfl
@[simp] theorem transport_correct {S T : Sequent} (equal : S = T) (D : Diagram S) :
    LocallyCorrect (transport equal D) ↔ LocallyCorrect D := by cases equal; rfl
@[simp] theorem transport_events {S T : Sequent} (equal : S = T) (D : Diagram S)
    (address : InternalAddress) :
    events (transport equal D) address = events D address := by cases equal; rfl

theorem left_seam (A B C : Formula) :
    leftIntermediate A B C = topInput 0 (parameters A B) (gammaY A B C) {A} := by
  simp [leftIntermediate, topOutput, topInput, parameters, gammaA, gammaY,
    add_assoc, add_comm, add_left_comm, Multiset.cons_swap]

theorem left_output (A B C : Formula) :
    topOutput 0 (parameters A B) (gammaY A B C) {A} = common A B C := by
  simp [common, topOutput, parameters, gammaB, gammaY,
    add_assoc, add_comm, add_left_comm, Multiset.cons_swap]

def topNode (key owner : Nat) (role : Fin 2) (A B : Formula)
    (gamma pi : Context) (D : Diagram (topInput role (parameters A B) gamma pi)) :
    Diagram (topOutput role (parameters A B) gamma pi) :=
  .rule key (.top role (parameters A B) owner gamma pi) (.cons D .nil)

def bottomNode (key owner : Nat) (A B : Formula) (S : Sequent)
    (D E : Diagram S) : Diagram S :=
  .rule key (.bottom (parameters A B) owner S) (.cons D (.cons E .nil))

/-- Actual branch skeleton.  X=0 is rooted at []; Y=1 is rooted at [0]. -/
def source (A B C : Formula)
    (da : Diagram (donorBoundary A B C 0))
    (db : Diagram (donorBoundary A B C 1))
    (dc : Diagram (donorBoundary A B C 2)) : Diagram (common A B C) :=
  bottomNode 100 0 A B (common A B C)
    (bottomNode 101 1 A B (common A B C)
      (transport (left_output A B C)
        (topNode 102 1 0 A B (gammaY A B C) {A}
          (transport (left_seam A B C)
            (topNode 103 0 0 A B (gammaA A C) {A} da))))
      (topNode 104 1 1 A B (gammaB A B C) {A}
        (topNode 105 0 0 A B (gammaB A B C) {A} db)))
    (topNode 106 0 1 A B (gammaB A B C) {A} dc)

/-- A predicate over existing diagrams, with actual single-succedent IW
admission.  It is not a new syntax or proof representation. -/
inductive Ordinary : {S : Sequent} → Diagram S → Prop where
  | identity (key : Nat) (A : Formula) :
      Ordinary (.rule key (.identity A) .nil)
  | weakening (key : Nat) (A : Formula) (gamma pi : Context)
      (single : pi.card ≤ 1) (D : Diagram ⟨gamma, pi⟩) (ordinary : Ordinary D) :
      Ordinary (.rule key (.weakening A gamma pi) (.cons D .nil))

theorem Ordinary.complete {S : Sequent} {D : Diagram S} (ordinary : Ordinary D) :
    D.Complete := by
  induction ordinary with
  | identity => trivial
  | weakening key A gamma pi single D ordinary ih => exact ⟨ih, trivial⟩

theorem Ordinary.correct {S : Sequent} {D : Diagram S} (ordinary : Ordinary D) :
    LocallyCorrect D := by
  induction ordinary with
  | identity => exact ⟨trivial, trivial⟩
  | weakening key A gamma pi single D ordinary ih => exact ⟨single, ih, trivial⟩

def SystemFree {S : Sequent} (D : Diagram S) : Prop :=
  ∀ address, events D address = ⟨[], []⟩

theorem Ordinary.systemFree {S : Sequent} {D : Diagram S} (ordinary : Ordinary D) :
    SystemFree D := by
  induction ordinary with
  | identity => intro address; rfl
  | weakening key A gamma pi single D ordinary ih =>
      intro address
      simp only [events, childEvents, rootEvents, append]
      rw [ih (address ++ [0])]
      rfl

theorem ordinary_transport {S T : Sequent} (equal : S = T)
    (D : Diagram S) (ordinary : Ordinary D) : Ordinary (transport equal D) := by
  cases equal
  exact ordinary

theorem source_complete (A B C : Formula)
    (da : Diagram (donorBoundary A B C 0))
    (db : Diagram (donorBoundary A B C 1))
    (dc : Diagram (donorBoundary A B C 2))
    (ha : da.Complete) (hb : db.Complete) (hc : dc.Complete) :
    (source A B C da db dc).Complete := by
  simp only [source, topNode, bottomNode, Diagram.Complete, Children.Complete,
    transport_complete]
  tauto

theorem source_locallyCorrect (A B C : Formula)
    (da : Diagram (donorBoundary A B C 0))
    (db : Diagram (donorBoundary A B C 1))
    (dc : Diagram (donorBoundary A B C 2))
    (ha : LocallyCorrect da) (hb : LocallyCorrect db) (hc : LocallyCorrect dc) :
    LocallyCorrect (source A B C da db dc) := by
  simp only [source, topNode, bottomNode, LocallyCorrect, ChildrenCorrect,
    transport_correct, Rule.Valid, common, topOutput]
  simp
  exact ⟨⟨ha, hb⟩, hc⟩

def xBottom (A B : Formula) : Bottom := ⟨0, [], 100, parameters A B⟩
def yBottom (A B : Formula) : Bottom := ⟨1, [0], 101, parameters A B⟩
def xTopA (A B : Formula) : Top := ⟨0, [0, 0, 0], 103, 0, parameters A B⟩
def xTopB (A B : Formula) : Top := ⟨0, [0, 1, 0], 105, 0, parameters A B⟩
def xTopC (A B : Formula) : Top := ⟨0, [1], 106, 1, parameters A B⟩
def yTopA (A B : Formula) : Top := ⟨1, [0, 0], 102, 0, parameters A B⟩
def yTopB (A B : Formula) : Top := ⟨1, [0, 1], 104, 1, parameters A B⟩

def sourceEvents (A B : Formula) : Events :=
  ⟨[yTopA A B, xTopA A B, yTopB A B, xTopB A B, xTopC A B],
    [xBottom A B, yBottom A B]⟩

private def topPacket (t : Top) (e : Events) : Events :=
  append ⟨[t], []⟩ (append e ⟨[], []⟩)
private def bottomPacket (b : Bottom) (e f : Events) : Events :=
  append ⟨[], [b]⟩ (append e (append f ⟨[], []⟩))

theorem source_events (A B C : Formula)
    (da : Diagram (donorBoundary A B C 0))
    (db : Diagram (donorBoundary A B C 1))
    (dc : Diagram (donorBoundary A B C 2))
    (ha : SystemFree da) (hb : SystemFree db) (hc : SystemFree dc) :
    events (source A B C da db dc) [] = sourceEvents A B := by
  let assemble (a b c : Events) :=
    bottomPacket (xBottom A B)
      (bottomPacket (yBottom A B)
        (topPacket (yTopA A B) (topPacket (xTopA A B) a))
        (topPacket (yTopB A B) (topPacket (xTopB A B) b)))
      (topPacket (xTopC A B) c)
  have replaced :
      assemble (events da [0, 0, 0, 0]) (events db [0, 1, 0, 0]) (events dc [1, 0]) =
        assemble ⟨[], []⟩ ⟨[], []⟩ ⟨[], []⟩ :=
    (congrArg (fun e => assemble e (events db [0, 1, 0, 0]) (events dc [1, 0]))
      (ha [0, 0, 0, 0])).trans
      ((congrArg (fun e => assemble ⟨[], []⟩ e (events dc [1, 0]))
        (hb [0, 1, 0, 0])).trans
        (congrArg (fun e => assemble ⟨[], []⟩ ⟨[], []⟩ e) (hc [1, 0])))
  simp only [source, bottomNode, topNode, events, childEvents, rootEvents,
    transport_events, append, sourceEvents,
    xBottom, yBottom, xTopA, xTopB, xTopC, yTopA, yTopB]
  exact replaced

theorem sourceEvents_resolved (A B : Formula) : Resolved (sourceEvents A B) := by
  intro t ht
  simp only [sourceEvents, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ⟨yBottom A B, by simp [sourceEvents], ⟨rfl, [], rfl⟩, rfl⟩
  · exact ⟨xBottom A B, by simp [sourceEvents], ⟨rfl, [0, 0], rfl⟩, rfl⟩
  · exact ⟨yBottom A B, by simp [sourceEvents], ⟨rfl, [], rfl⟩, rfl⟩
  · exact ⟨xBottom A B, by simp [sourceEvents], ⟨rfl, [1, 0], rfl⟩, rfl⟩
  · exact ⟨xBottom A B, by simp [sourceEvents], ⟨rfl, [], rfl⟩, rfl⟩

/-- Generic source validity is established from independent local correctness,
completeness and absence of donor discharge events, not target checking. -/
theorem source_correct (A B C : Formula)
    (da : Diagram (donorBoundary A B C 0))
    (db : Diagram (donorBoundary A B C 1))
    (dc : Diagram (donorBoundary A B C 2))
    (ca : da.Complete) (cb : db.Complete) (cc : dc.Complete)
    (la : LocallyCorrect da) (lb : LocallyCorrect db) (lc : LocallyCorrect dc)
    (fa : SystemFree da) (fb : SystemFree db) (fc : SystemFree dc) :
    CompleteSourceCorrect (source A B C da db dc) := by
  refine ⟨source_complete A B C da db dc ca cb cc,
    source_locallyCorrect A B C da db dc la lb lc, ?_, ?_⟩
  · rw [source_events A B C da db dc fa fb fc]
    change ([0, 1] : List Nat).Nodup
    decide
  · apply (grouping_iff_resolved _).mpr
    rw [source_events A B C da db dc fa fb fc]
    exact sourceEvents_resolved A B

/-- Root-first physical ancestry, hence *below* in the paper's leaf-to-root
proof orientation.  Internal premise addresses are zero-based. -/
def StrictAncestor (a b : InternalAddress) : Prop := a ≠ b ∧ a.IsPrefix b

/-- The paper's preparation conditions, stated independently of translation:
same-instance tops are an antichain; two instances have no crossings in both
directions.  Fixed owner IDs are system-instance identities, not rule keys. -/
def Prepared (e : Events) : Prop :=
  (∀ t ∈ e.tops, ∀ u ∈ e.tops, t.owner = u.owner →
    ¬ StrictAncestor t.address u.address) ∧
  ¬ ∃ t ∈ e.tops, ∃ u ∈ e.tops, ∃ v ∈ e.tops, ∃ w ∈ e.tops,
    t.owner = v.owner ∧ u.owner = w.owner ∧ t.owner ≠ u.owner ∧
      StrictAncestor t.address u.address ∧ StrictAncestor w.address v.address

private theorem sourceEvents_ancestry (A B : Formula)
    (t : Top) (ht : t ∈ (sourceEvents A B).tops)
    (u : Top) (hu : u ∈ (sourceEvents A B).tops)
    (ancestor : StrictAncestor t.address u.address) : t.owner = 1 ∧ u.owner = 0 := by
  simp only [sourceEvents, List.mem_cons, List.not_mem_nil, or_false] at ht hu
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    rcases hu with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact absurd ancestor (by
        dsimp only [xTopA, xTopB, xTopC, yTopA, yTopB, StrictAncestor]
        decide)

theorem sourceEvents_prepared (A B : Formula) : Prepared (sourceEvents A B) := by
  constructor
  · intro t ht u hu same ancestor
    obtain ⟨ht', hu'⟩ := sourceEvents_ancestry A B t ht u hu ancestor
    omega
  · rintro ⟨t, ht, u, hu, v, hv, w, hw, tv, uw, different, tu, wv⟩
    obtain ⟨ht', hu'⟩ := sourceEvents_ancestry A B t ht u hu tu
    obtain ⟨hw', hv'⟩ := sourceEvents_ancestry A B w hw v hv wv
    omega

theorem source_prepared (A B C : Formula)
    (da : Diagram (donorBoundary A B C 0))
    (db : Diagram (donorBoundary A B C 1))
    (dc : Diagram (donorBoundary A B C 2))
    (ha : SystemFree da) (hb : SystemFree db) (hc : SystemFree dc) :
    Prepared (events (source A B C da db dc) []) := by
  rw [source_events A B C da db dc ha hb hc]
  exact sourceEvents_prepared A B

def wordContext (A : Formula) : List Formula → Context
  | [] => {A}
  | x :: xs => {x} + wordContext A xs

def wordTree (key : Nat) (A : Formula) : (xs : List Formula) →
    Diagram ⟨wordContext A xs, {A}⟩
  | [] => .rule key (.identity A) .nil
  | x :: xs => .rule key (.weakening x (wordContext A xs) {A})
      (.cons (wordTree (key + 1) A xs) .nil)

theorem wordTree_ordinary (key : Nat) (A : Formula) (xs : List Formula) :
    Ordinary (wordTree key A xs) := by
  induction xs generalizing key with
  | nil => exact .identity _ _
  | cons x xs ih => exact .weakening _ _ _ _ (by simp) _ (ih _)

theorem boundaryA (A B C : Formula) :
    (⟨wordContext A [C, A, A, A], {A}⟩ : Sequent) = donorBoundary A B C 0 := by
  simp [donorBoundary, topInput, parameters, wordContext, gammaA,
    add_assoc, add_comm, add_left_comm, Multiset.cons_swap]
theorem boundaryB (A B C : Formula) :
    (⟨wordContext A [C, B, B, A], {A}⟩ : Sequent) = donorBoundary A B C 1 := by
  simp [donorBoundary, topInput, parameters, wordContext, gammaB,
    add_assoc, add_comm, add_left_comm, Multiset.cons_swap]
theorem boundaryC (A B C : Formula) :
    (⟨wordContext A [C, B, B, B], {A}⟩ : Sequent) = donorBoundary A B C 2 := by
  simp [donorBoundary, topInput, parameters, wordContext, gammaB,
    add_assoc, add_comm, add_left_comm, Multiset.cons_swap]
theorem boundaryCReordered (A B C : Formula) :
    (⟨wordContext A [B, B, B, C], {A}⟩ : Sequent) = donorBoundary A B C 2 := by
  simp [donorBoundary, topInput, parameters, wordContext, gammaB,
    add_assoc, add_comm, add_left_comm, Multiset.cons_swap]

def donorA (A B C : Formula) : Diagram (donorBoundary A B C 0) :=
  transport (boundaryA A B C) (wordTree 10 A [C, A, A, A])
def donorB (A B C : Formula) : Diagram (donorBoundary A B C 1) :=
  transport (boundaryB A B C) (wordTree 20 A [C, B, B, A])
def donorC (A B C : Formula) : Diagram (donorBoundary A B C 2) :=
  transport (boundaryC A B C) (wordTree 30 A [C, B, B, B])
def donorCReordered (A B C : Formula) : Diagram (donorBoundary A B C 2) :=
  transport (boundaryCReordered A B C) (wordTree 40 A [B, B, B, C])

theorem donorA_ordinary (A B C : Formula) : Ordinary (donorA A B C) :=
  ordinary_transport _ _ (wordTree_ordinary _ _ _)
theorem donorB_ordinary (A B C : Formula) : Ordinary (donorB A B C) :=
  ordinary_transport _ _ (wordTree_ordinary _ _ _)
theorem donorC_ordinary (A B C : Formula) : Ordinary (donorC A B C) :=
  ordinary_transport _ _ (wordTree_ordinary _ _ _)
theorem donorCReordered_ordinary (A B C : Formula) : Ordinary (donorCReordered A B C) :=
  ordinary_transport _ _ (wordTree_ordinary _ _ _)

theorem ordinary_source_correct (A B C : Formula)
    (da : Diagram (donorBoundary A B C 0))
    (db : Diagram (donorBoundary A B C 1))
    (dc : Diagram (donorBoundary A B C 2))
    (ha : Ordinary da) (hb : Ordinary db) (hc : Ordinary dc) :
    CompleteSourceCorrect (source A B C da db dc) :=
  source_correct A B C da db dc ha.complete hb.complete hc.complete
    ha.correct hb.correct hc.correct ha.systemFree hb.systemFree hc.systemFree

theorem original_correct (A B C : Formula) :
    CompleteSourceCorrect (source A B C (donorA A B C) (donorB A B C) (donorC A B C)) :=
  ordinary_source_correct A B C _ _ _
    (donorA_ordinary A B C) (donorB_ordinary A B C) (donorC_ordinary A B C)

theorem replaced_correct (A B C : Formula) :
    CompleteSourceCorrect
      (source A B C (donorA A B C) (donorB A B C) (donorCReordered A B C)) :=
  ordinary_source_correct A B C _ _ _
    (donorA_ordinary A B C) (donorB_ordinary A B C) (donorCReordered_ordinary A B C)

theorem original_prepared (A B C : Formula) :
    Prepared (events (source A B C (donorA A B C) (donorB A B C) (donorC A B C)) []) :=
  source_prepared A B C _ _ _
    (donorA_ordinary A B C).systemFree (donorB_ordinary A B C).systemFree
    (donorC_ordinary A B C).systemFree

theorem replaced_prepared (A B C : Formula) :
    Prepared (events
      (source A B C (donorA A B C) (donorB A B C) (donorCReordered A B C)) []) :=
  source_prepared A B C _ _ _
    (donorA_ordinary A B C).systemFree (donorB_ordinary A B C).systemFree
    (donorCReordered_ordinary A B C).systemFree

#print axioms source_correct
#print axioms source_prepared
#print axioms original_correct
#print axioms replaced_correct
#check source
#check source_events
#check source_prepared

end Potkin.Research.PreparedSysComSource

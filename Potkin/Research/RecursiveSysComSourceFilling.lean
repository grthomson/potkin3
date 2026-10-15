import Potkin.Research.RecursiveSysComSourcePreparation

/-!
# Closing native recursively prepared sources with ordinary donors

Fillings use the existing native source `Diagram.Assignment`. Physical origin
indices are converted by the proved hole equivalence and exact boundaries.
Only identity/IW donors are used here; no closedness is inferred from a Box.
-/
namespace Potkin.Research.RecursiveSysComSource
open D3SourceEncoding D3SourceAdequacy
open PreparedSysComSource (Ordinary SystemFree)

mutual
theorem fill_localCorrect : {S : Sequent} → (D : Diagram S) → (F : D.Assignment) →
    LocallyCorrect D → (∀ h, LocallyCorrect (F h)) → LocallyCorrect (D.fill F)
  | _, .hole _, F, _, admitted => admitted PUnit.unit
  | _, .rule _ _ children, F, correct, admitted =>
      ⟨correct.1, fill_childrenCorrect children F correct.2 admitted⟩
theorem fill_childrenCorrect : {Ss : List Sequent} → (Ds : Children Ss) →
    (F : Ds.Assignment) → ChildrenCorrect Ds →
    (∀ h, LocallyCorrect (F h)) → ChildrenCorrect (Ds.fill F)
  | _, .nil, _, _, _ => trivial
  | _, .cons head tail, F, correct, admitted =>
      ⟨fill_localCorrect head (fun h => F (.inl h)) correct.1 (fun h => admitted (.inl h)),
       fill_childrenCorrect tail (fun h => F (.inr h)) correct.2 (fun h => admitted (.inr h))⟩
end

mutual
theorem fill_complete : {S : Sequent} → (D : Diagram S) → (F : D.Assignment) →
    (∀ h, (F h).Complete) → (D.fill F).Complete
  | _, .hole _, F, closed => closed PUnit.unit
  | _, .rule _ _ children, F, closed => fill_children_complete children F closed
theorem fill_children_complete : {Ss : List Sequent} → (Ds : Children Ss) →
    (F : Ds.Assignment) → (∀ h, (F h).Complete) → (Ds.fill F).Complete
  | _, .nil, _, _ => trivial
  | _, .cons head tail, F, closed =>
      ⟨fill_complete head (fun h => F (.inl h)) (fun h => closed (.inl h)),
       fill_children_complete tail (fun h => F (.inr h)) (fun h => closed (.inr h))⟩
end

mutual
theorem fill_events_systemFree : {S : Sequent} → (D : Diagram S) → (F : D.Assignment) →
    (∀ h, SystemFree (F h)) → (address : InternalAddress) →
    events (D.fill F) address = events D address
  | _, .hole _, F, free, address => free PUnit.unit address
  | _, .rule key r children, F, free, address =>
      congrArg (append (rootEvents address key r))
        (fill_children_events_systemFree children F free address 0)
theorem fill_children_events_systemFree : {Ss : List Sequent} → (Ds : Children Ss) →
    (F : Ds.Assignment) → (∀ h, SystemFree (F h)) →
    (address : InternalAddress) → (slot : Nat) →
    childEvents (Ds.fill F) address slot = childEvents Ds address slot
  | _, .nil, _, _, _, _ => rfl
  | _, .cons head tail, F, free, address, slot => congrArg₂ append
      (fill_events_systemFree head (fun h => F (.inl h)) (fun h => free (.inl h)) (address ++ [slot]))
      (fill_children_events_systemFree tail (fun h => F (.inr h))
        (fun h => free (.inr h)) address (slot + 1))
end

def Source.assignment {S O bounds} (source : Source S O bounds)
    (donors : ∀ o, Diagram (bounds o)) : source.erase.Assignment := fun h =>
  PreparedSysComSource.transport
    ((source.holeBoundary (source.holeEquiv.symm h)).symm.trans
      (congrArg source.erase.holeBoundary (source.holeEquiv.apply_symm_apply h)))
    (donors (source.holeEquiv.symm h))

def Source.filled {S O bounds} (source : Source S O bounds)
    (donors : ∀ o, Diagram (bounds o)) : Diagram S := source.erase.fill (source.assignment donors)

theorem Source.assignment_ordinary {S O bounds} (source : Source S O bounds)
    (donors : ∀ o, Diagram (bounds o)) (ordinary : ∀ o, Ordinary (donors o)) (h : source.erase.Hole) :
    Ordinary (source.assignment donors h) :=
  PreparedSysComSource.ordinary_transport _ _ (ordinary _)

theorem Source.filled_events {S O bounds} (source : Source S O bounds)
    (donors : ∀ o, Diagram (bounds o)) (ordinary : ∀ o, Ordinary (donors o))
    (address : InternalAddress) : events (source.filled donors) address = events source.erase address :=
  fill_events_systemFree source.erase (source.assignment donors)
    (fun h => (source.assignment_ordinary donors ordinary h).systemFree) address

theorem Source.filled_correct {S O bounds} (source : Source S O bounds)
    (hscope : WellScoped source) (donors : ∀ o, Diagram (bounds o))
    (ordinary : ∀ o, Ordinary (donors o)) : CompleteSourceCorrect (source.filled donors) := by
  refine ⟨fill_complete source.erase (source.assignment donors)
    (fun h => (source.assignment_ordinary donors ordinary h).complete), ?_⟩
  have original := source.correct hscope
  refine ⟨fill_localCorrect source.erase (source.assignment donors) source.localCorrect
    (fun h => (source.assignment_ordinary donors ordinary h).correct), ?_, ?_⟩
  · rw [source.filled_events donors ordinary []]
    exact original.2.1
  · rw [source.filled_events donors ordinary []]
    exact original.2.2

theorem Source.filled_prepared {S O bounds} (source : Source S O bounds)
    (hscope : WellScoped source) (donors : ∀ o, Diagram (bounds o))
    (ordinary : ∀ o, Ordinary (donors o)) (address : InternalAddress := []) :
    PreparedSysComSource.Prepared (events (source.filled donors) address) := by
  rw [source.filled_events donors ordinary address]
  exact source.prepared hscope address

#print axioms Source.filled_correct
#print axioms Source.filled_prepared
end Potkin.Research.RecursiveSysComSource

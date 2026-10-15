import Potkin.Research.RecursiveSysComTranslation
import Potkin.Research.HLJDonorIntegration

/-!
# Coordinated replacement at the recursive translation's physical frontier

The cache is the existing address-aligned native detached assignment. Logical
origins decide which physical copies change; they never identify those copies
with each other. Registry checking is separate from this exact filling law.
-/
namespace Potkin.Research.RecursiveSysComReuse
open RecursiveSysComSource RecursiveSysComTranslation StructuralLemmaCuts
  ContractionPostponement

variable {S : Seq} {O : Type} {bounds : O → Seq}
  (key : Key) (p : Source S O bounds) (K : Multiset (Potkin.Sequent Sig))

noncomputable def locations : List (O × InternalAddress) :=
  (scaffold key p K).leafOrder.map
    (fun h => ((origins key p K h).1, (scaffold key p K).leafAddress h))

theorem location_origins : (locations key p K).map Prod.fst = RecursiveSysComCopy.uses p := by
  simp only [locations, List.map_map]
  exact native_copy_word key p K

noncomputable def dirtyHoles (changed : O → Bool) : List (scaffold key p K).LeafOccurrence :=
  (scaffold key p K).leafOrder.filter (fun h => changed (origins key p K h).1)

private theorem filtered_length {A B : Type} (xs : List A) (f : A → B) (c : B → Bool) :
    (xs.filter (fun a => c (f a))).length = ((xs.map f).filter c).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : c (f a) <;> simp [h, ih]

theorem dirty_count (changed : O → Bool) :
    (dirtyHoles key p K changed).length = (RecursiveSysComCopy.affected p changed).length := by
  unfold dirtyHoles RecursiveSysComCopy.affected
  rw [filtered_length, native_copy_word]

theorem dirty_bound (changed : O → Bool) :
    (dirtyHoles key p K changed).length ≤ 2 ^ RecursiveSysComCopy.phases p := by
  rw [dirty_count]
  exact RecursiveSysComCopy.affected_le p changed

def patched (old new : (o : O) → CKTree Sig Data (framed K (bounds o)))
    (changed : O → Bool) : (o : O) → CKTree Sig Data (framed K (bounds o)) :=
  fun o => if changed o then new o else old o

variable (old new : (o : O) → CKTree Sig Data (framed K (bounds o)))
  (ordinary : (scaffold key p K).IsOrdinary)
  (complete : ∀ o, (old o).IsComplete)

include complete in
theorem supply_complete : ∀ h, (supply _ (origins key p K) old h).IsComplete := by
  intro h
  exact (complete_transport _ _).mpr (complete _)

noncomputable def cached : (scaffold key p K).LeafAssignment :=
  alignedDetached (scaffold key p K) ordinary (supply _ (origins key p K) old)
    (supply_complete key p K old complete)

noncomputable def refresh (changed : O → Bool) : (scaffold key p K).LeafAssignment :=
  fun h => if changed (origins key p K h).1 then supply _ (origins key p K) new h
    else cached key p K old ordinary complete h

theorem refresh_supply (changed : O → Bool) :
    refresh key p K old new ordinary complete changed =
      supply _ (origins key p K) (patched K old new changed) := by
  unfold refresh cached
  rw [alignedDetached_eq]
  funext h
  unfold supply patched
  split <;> simp_all

theorem refresh_retranslation (changed : O → Bool) :
    (scaffold key p K).fillAssignment (refresh key p K old new ordinary complete changed) =
      translate key p K (patched K old new changed) := by
  rw [refresh_supply]
  exact scaffold_fill key p K _

theorem unchanged_cached (changed : O → Bool) (h : (scaffold key p K).LeafOccurrence)
    (unchanged : changed (origins key p K h).1 = false) :
    refresh key p K old new ordinary complete changed h =
      cached key p K old ordinary complete h := by simp [refresh, unchanged]

/-- Root interfaces have no proper frontier cut. Their replacement is the
literal provider replacement, not a fabricated proper root selection. -/
theorem leaf_replacement (S : Seq) (K : Multiset (Potkin.Sequent Sig))
    (F : (o : PUnit) → CKTree Sig Data (framed K S)) :
    translate key (.leaf S) K F = F PUnit.unit := rfl

section Checked
variable [DecidableEq (Hypersequent Sig)]
  (P : EquippedPresentation Theory)
  (admitted : LocallyAdmittedTree P (scaffold key p K))
  (oldChecked newChecked : (o : O) → CheckedDerivation P (framed K (bounds o)))

noncomputable def checkedSupply
    (F : (o : O) → CheckedDerivation P (framed K (bounds o)))
    (h : (scaffold key p K).LeafOccurrence) :
    CheckedDerivation P ((scaffold key p K).leafBoundary h) :=
  (origins key p K h).2 ▸ F (origins key p K h).1

theorem checkedSupply_realize
    (F : (o : O) → CheckedDerivation P (framed K (bounds o))) :
    (fun h => (checkedSupply key p K P F h).realize) =
      supply _ (origins key p K) (fun o => (F o).realize) := by
  funext h
  exact HLJDonorIntegration.realize_cast (origins key p K h).2 (F _)

noncomputable def checkedRefresh (changed : O → Bool) : CheckedDerivation P (framed K S) :=
  checkedFill P (scaffold key p K) admitted (fun h =>
    if changed (origins key p K h).1 then checkedSupply key p K P newChecked h
    else checkedSupply key p K P oldChecked h)

theorem checkedRefresh_realize (changed : O → Bool) :
    (checkedRefresh key p K P admitted oldChecked newChecked changed).realize =
      translate key p K (patched K (fun o => (oldChecked o).realize)
        (fun o => (newChecked o).realize) changed) := by
  rw [checkedRefresh, checkedFill_realize]
  rw [← scaffold_fill]
  apply congrArg (scaffold key p K).fillAssignment
  funext h
  have ho := congrFun (checkedSupply_realize key p K P oldChecked) h
  have hn := congrFun (checkedSupply_realize key p K P newChecked) h
  split <;> simp_all [patched, supply]
end Checked

#print axioms refresh_retranslation
#print axioms dirty_count
#print axioms unchanged_cached
#print axioms checkedRefresh_realize
end Potkin.Research.RecursiveSysComReuse

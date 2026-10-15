import Potkin.Research.RecursiveSysComExamples
import Potkin.Research.RecursiveSysComReached
import Potkin.Research.RecursiveSysComReuse
import Potkin.Research.RecursiveSysComCutApplication
import Potkin.Research.PreparedSysComGround

/-!
# A checked recursive translation with a two-layer coordinated update

Four genuine identity/IW donors fill the balanced three-phase source. Changing
one mixed donor's IW order changes both its physical target uses. A source-
computed finite assembly stock and one donor stock check both outputs in the
same presentation. The proper native CK certificate is for that same output.
-/
namespace Potkin.Research.RecursiveSysComApplication
open RecursiveSysComSource RecursiveSysComTranslation ContractionPostponement
open RecursiveSysComExamples RecursiveSysComAdmission RecursiveSysComReached

abbrev Sig := RecursiveSysComTranslation.Sig
abbrev Data := RecursiveSysComTranslation.Data
abbrev Theory := RecursiveSysComTranslation.Theory
abbrev Key := RecursiveSysComTranslation.Key
abbrev Seq := RecursiveSysComTranslation.Seq

def A : D3SourceEncoding.Formula := .atom 0
def B : D3SourceEncoding.Formula := .atom 1
def C : D3SourceEncoding.Formula := .atom 2
abbrev Origin := BalancedOrigins
abbrev Bounds := balancedBounds A B C
abbrev source := balanced A B C

def originNumber : Origin → Nat
  | .inl (.inl _) => 0 | .inl (.inr _) => 1
  | .inr (.inl _) => 2 | .inr (.inr _) => 3

def donorKey (o : Origin) : Nat := 200 + 10 * originNumber o

noncomputable def donorStock : List (LocalOccurrence Sig Data) :=
  PreparedSysComGround.wordStock 200 C [A,A,A,A] ++
  PreparedSysComGround.wordStock 210 C [A,A,B,B] ++
  PreparedSysComGround.wordStock 220 C [A,A,B,B] ++
  PreparedSysComGround.wordStock 230 C [B,B,B,B] ++
  PreparedSysComGround.wordStock 240 C [B,B,A,A] ++
  [PreparedSysComGround.identityOccurrence C]

theorem donorStock_ids : donorStock.map LocalOccurrence.id =
    [200,201,202,203,210,211,212,213,220,221,222,223,230,231,232,233,
      240,241,242,243,50] := rfl

theorem donorStock_consistent : D3RegistryAdmission.ConsistentKeys donorStock := by
  have unique : (donorStock.map LocalOccurrence.id).Nodup := by rw [donorStock_ids]; decide
  exact List.inj_on_of_nodup_map unique

theorem donorStock_below : ∀ o ∈ donorStock, o.id < 10000 := by
  intro o member
  have hid : o.id ∈ donorStock.map LocalOccurrence.id := List.mem_map.mpr ⟨o, member, rfl⟩
  rw [donorStock_ids] at hid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
  omega

theorem donorStock_valid : ∀ o ∈ donorStock, Theory.Admits o := by
  intro o member
  simp only [donorStock, List.mem_append, List.mem_singleton] at member
  rcases member with ((((h | h) | h) | h) | h) | h
  · exact PreparedSysComGround.wordStock_admitted 200 C [A,A,A,A] o h
  · exact PreparedSysComGround.wordStock_admitted 210 C [A,A,B,B] o h
  · exact PreparedSysComGround.wordStock_admitted 220 C [A,A,B,B] o h
  · exact PreparedSysComGround.wordStock_admitted 230 C [B,B,B,B] o h
  · exact PreparedSysComGround.wordStock_admitted 240 C [B,B,A,A] o h
  · subst o
    exact PreparedSysComGround.identity_admitted C

theorem zero_boundary (S : Seq) : D3SourceEncoding.boundary S = framed 0 S := by
  unfold framed RecursiveSysComNative.frame
  rw [ContractionBoundaries.extend_zero]
  rfl

theorem donor_boundary (o : Origin) :
    PreparedSysComGround.wordBoundary C (balancedWord A B C o) = framed 0 (Bounds o) :=
  (congrArg D3SourceEncoding.boundary (balanced_donor_boundary A B C o)).trans (zero_boundary _)

noncomputable def old (o : Origin) : CKTree Sig Data (framed 0 (Bounds o)) :=
  donor_boundary o ▸ PreparedSysComGround.wordTree (donorKey o) C (balancedWord A B C o)

private theorem all_transport {G H : Hypersequent Sig} (e : G = H)
    (R : LocalOccurrence Sig Data → Prop) (t : CKTree Sig Data G) :
    AllNodes R (e ▸ t) ↔ AllNodes R t := by cases e; rfl

theorem old_nodes (o : Origin) : AllNodes (fun d => d ∈ donorStock) (old o) := by
  rw [old, all_transport]
  apply PreparedSysComGround.wordTree_all
  · simp only [donorStock, List.mem_append, List.mem_singleton]; tauto
  · intro d member
    cases o with
    | inl o => cases o <;>
        simp_all [donorKey, originNumber, balancedWord, donorStock, List.mem_append]
    | inr o => cases o <;>
        simp_all [donorKey, originNumber, balancedWord, donorStock, List.mem_append]

theorem old_complete (o : Origin) : (old o).IsComplete := by
  rw [old, ContractionPostponement.complete_transport]
  exact PreparedSysComGround.wordTree_complete _ _ _

def changed : Origin → Bool
  | .inl (.inr _) => true | _ => false

theorem new_boundary : PreparedSysComGround.wordBoundary C [B,B,A,A] =
    framed 0 (Bounds (.inl (.inr PUnit.unit))) := by
  have equal : PreparedSysComGround.wordBoundary C [B,B,A,A] =
      PreparedSysComGround.wordBoundary C [A,A,B,B] := by
    simp [PreparedSysComGround.wordBoundary, PreparedSysComSource.wordContext,
      add_assoc, add_comm, add_left_comm, Multiset.cons_swap]
  exact equal.trans (donor_boundary (.inl (.inr PUnit.unit)))

noncomputable def new : (o : Origin) → CKTree Sig Data (framed 0 (Bounds o))
  | .inl (.inr .unit) => new_boundary ▸ PreparedSysComGround.wordTree 240 C [B,B,A,A]
  | .inl (.inl .unit) => old (.inl (.inl .unit))
  | .inr (.inl .unit) => old (.inr (.inl .unit))
  | .inr (.inr .unit) => old (.inr (.inr .unit))

theorem new_nodes (o : Origin) : AllNodes (fun d => d ∈ donorStock) (new o) := by
  cases o with
  | inl o =>
    cases o with
    | inl u => cases u; exact old_nodes (.inl (.inl PUnit.unit))
    | inr u =>
      cases u
      rw [new, all_transport]
      apply PreparedSysComGround.wordTree_all
      · simp only [donorStock, List.mem_append, List.mem_singleton]; tauto
      · intro d member
        simp only [donorStock, List.mem_append, List.mem_singleton]
        tauto
  | inr o => cases o with
    | inl u => cases u; exact old_nodes (.inr (.inl PUnit.unit))
    | inr u => cases u; exact old_nodes (.inr (.inr PUnit.unit))

theorem new_complete (o : Origin) : (new o).IsComplete := by
  cases o with
  | inl o =>
    cases o with
    | inl u => cases u; exact old_complete (.inl (.inl PUnit.unit))
    | inr u => cases u; rw [new, ContractionPostponement.complete_transport]
                 ; exact PreparedSysComGround.wordTree_complete _ _ _
  | inr o => cases o with
    | inl u => cases u; exact old_complete (.inr (.inl PUnit.unit))
    | inr u => cases u; exact old_complete (.inr (.inr PUnit.unit))

theorem patched_new : RecursiveSysComReuse.patched 0 old new changed = new := by
  funext o
  cases o with
  | inl o => cases o with
    | inl u => cases u; rfl
    | inr u => cases u; rfl
  | inr o => cases o with
    | inl u => cases u; rfl
    | inr u => cases u; rfl

/-- Unlike the separate source-only example, these source IW keys coincide
with the exact target word translation's keys at each origin. -/
def sourceOld (o : Origin) : D3SourceEncoding.Diagram (Bounds o) :=
  PreparedSysComSource.transport (balanced_donor_boundary A B C o)
    (PreparedSysComSource.wordTree (donorKey o) C (balancedWord A B C o))

theorem sourceOld_ordinary (o : Origin) : PreparedSysComSource.Ordinary (sourceOld o) :=
  PreparedSysComSource.ordinary_transport _ _ (PreparedSysComSource.wordTree_ordinary _ _ _)

theorem source_new_boundary :
    (⟨PreparedSysComSource.wordContext C [B,B,A,A], {C}⟩ : D3SourceEncoding.Sequent) =
      Bounds (.inl (.inr PUnit.unit)) := by
  have equal : (⟨PreparedSysComSource.wordContext C [B,B,A,A], {C}⟩ : D3SourceEncoding.Sequent) =
      ⟨PreparedSysComSource.wordContext C [A,A,B,B], {C}⟩ := by
    simp [PreparedSysComSource.wordContext, Multiset.cons_swap,
      add_assoc, add_comm, add_left_comm]
  exact equal.trans (balanced_donor_boundary A B C (.inl (.inr PUnit.unit)))

def sourceNew : (o : Origin) → D3SourceEncoding.Diagram (Bounds o)
  | .inl (.inr .unit) => PreparedSysComSource.transport source_new_boundary
      (PreparedSysComSource.wordTree 240 C [B,B,A,A])
  | .inl (.inl .unit) => sourceOld (.inl (.inl .unit))
  | .inr (.inl .unit) => sourceOld (.inr (.inl .unit))
  | .inr (.inr .unit) => sourceOld (.inr (.inr .unit))

theorem sourceNew_ordinary (o : Origin) : PreparedSysComSource.Ordinary (sourceNew o) := by
  cases o with
  | inl o =>
    cases o with
    | inl u => cases u; exact sourceOld_ordinary (.inl (.inl PUnit.unit))
    | inr u =>
      cases u
      change PreparedSysComSource.Ordinary (PreparedSysComSource.transport source_new_boundary
        (PreparedSysComSource.wordTree 240 C [B,B,A,A]))
      exact PreparedSysComSource.ordinary_transport _ _ (PreparedSysComSource.wordTree_ordinary _ _ _)
  | inr o =>
    cases o with
    | inl u => cases u; exact sourceOld_ordinary (.inr (.inl PUnit.unit))
    | inr u => cases u; exact sourceOld_ordinary (.inr (.inr PUnit.unit))

/-- The existing constructor relation is used, not boundary coincidence. Both
the native source and target donors above are precisely these words transported
along their displayed boundary equalities. -/
theorem old_word_translation (o : Origin) :
    PreparedSysComGround.WordTranslation C
      (PreparedSysComSource.wordTree (donorKey o) C (balancedWord A B C o))
      (PreparedSysComGround.wordTree (donorKey o) C (balancedWord A B C o)) :=
  PreparedSysComGround.wordTree_translation _ _ _
theorem new_word_translation :
    PreparedSysComGround.WordTranslation C (PreparedSysComSource.wordTree 240 C [B,B,A,A])
      (PreparedSysComGround.wordTree 240 C [B,B,A,A]) :=
  PreparedSysComGround.wordTree_translation _ _ _

theorem source_before_correct : D3SourceAdequacy.CompleteSourceCorrect (source.filled sourceOld) :=
  source.filled_correct (balanced_scoped A B C) _ sourceOld_ordinary
theorem source_after_correct : D3SourceAdequacy.CompleteSourceCorrect (source.filled sourceNew) :=
  source.filled_correct (balanced_scoped A B C) _ sourceNew_ordinary
theorem source_before_prepared :
    PreparedSysComSource.Prepared (D3SourceAdequacy.events (source.filled sourceOld) []) :=
  source.filled_prepared (balanced_scoped A B C) _ sourceOld_ordinary
theorem source_after_prepared :
    PreparedSysComSource.Prepared (D3SourceAdequacy.events (source.filled sourceNew) []) :=
  source.filled_prepared (balanced_scoped A B C) _ sourceNew_ordinary

noncomputable def key : Key := allocatedKey 10000 (stock source 0)
noncomputable def registry : EquippedPresentation Theory :=
  presentation 10000 (stock source 0) donorStock donorStock_consistent donorStock_below
    donorStock_valid (stock_admitted key source 0 (by simp [HLJStructural.ValidComponents]))

noncomputable def checkedOld : CheckedDerivation registry (framed 0 (common A B C {C})) :=
  checkedTranslation 10000 source 0 (by simp [HLJStructural.ValidComponents]) donorStock
    donorStock_consistent donorStock_below donorStock_valid old old_nodes old_complete

noncomputable def checkedNew : CheckedDerivation registry (framed 0 (common A B C {C})) :=
  checkedTranslation 10000 source 0 (by simp [HLJStructural.ValidComponents]) donorStock
    donorStock_consistent donorStock_below donorStock_valid new new_nodes new_complete

theorem checkedOld_realize : checkedOld.realize = translate key source 0 old :=
  checkedTranslation_realize _ _ _ _ _ _ _ _ _ _ _
theorem checkedNew_realize : checkedNew.realize = translate key source 0 new :=
  checkedTranslation_realize _ _ _ _ _ _ _ _ _ _ _

private theorem node_ordinary {Gs G} (o : LocalOccurrence Sig Data)
    (hp : o.shape.premises = Gs) (hc : o.shape.conclusion = G)
    (cs : CKChildren Sig Data Gs) : (node o hp hc cs).IsOrdinary := by
  subst Gs; subst G
  trivial

theorem scaffold_ordinary : (scaffold key source 0).IsOrdinary := by
  change (close key 1000 0 _ _).IsOrdinary
  unfold close
  exact node_ordinary _ _ _ _

theorem coordinated_checked_reconstruction :
    (scaffold key source 0).fillAssignment
      (RecursiveSysComReuse.refresh key source 0 old new scaffold_ordinary old_complete changed) =
      checkedNew.realize := by
  rw [RecursiveSysComReuse.refresh_retranslation, patched_new, checkedNew_realize]

theorem balanced_word : (RecursiveSysComCopy.uses source).map originNumber =
    [0,2,1,2,0,3,1,3] := rfl
theorem nested_word :
    (RecursiveSysComCopy.uses (nested A B C)).map
      (fun o => match o with | .inl (.inl _) => 0 | .inl (.inr _) => 1 | .inr _ => 2) =
      [0,2,1,2] := rfl
theorem affected_indices : RecursiveSysComCopy.affectedIndices source changed = [2,6] := rfl

/-- A native addressed proper cut on the SAME checked updated output. Its
ordered detached tuple and typed remainder are the public native ones. -/
theorem checked_native_certificate : ∃ cut : CKCut checkedNew.realize,
    cut.plan.remainder = scaffold key source 0 ∧ cut.plan.siteOrder.length = 8 ∧
      cut.fill cut.plan.detached = checkedNew.realize := by
  rw [checkedNew_realize, ← scaffold_fill]
  let cut := RecursiveSysComCutApplication.actualProperFrontier key source 0 new
    scaffold_ordinary (fun o => StructuralLemmaCuts.complete_ordinary _ (new_complete o))
  refine ⟨cut, ?_, ?_, cut.fill_detached_reconstructs⟩
  · exact StructuralLemmaCuts.proper_remainder _ _ _ _
  · exact RecursiveSysComCutApplication.actual_proper_factor_count key source 0 new
      scaffold_ordinary (fun o => StructuralLemmaCuts.complete_ordinary _ (new_complete o))

#eval (RecursiveSysComCopy.uses source).map originNumber
#eval RecursiveSysComCopy.affectedIndices source changed
#print axioms coordinated_checked_reconstruction
#print axioms checked_native_certificate
#print axioms source_after_correct
#print axioms source_after_prepared
end Potkin.Research.RecursiveSysComApplication

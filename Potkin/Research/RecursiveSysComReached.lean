import Potkin.Research.RecursiveSysComTranslation
import Potkin.Research.RecursiveSysComAdmission

/-!
# Source-computed reached stock and checked recursive translation

The finite stock is calculated by the source constructors and their actual
Cartesian top-occurrence choices.  It is not obtained by traversing a completed
target or assuming that the whole target is registered.  Exact canonical
descriptors retain passive contexts, ordered premises and component incidence.
-/
namespace Potkin.Research.RecursiveSysComReached

open RecursiveSysComSource RecursiveSysComTranslation RecursiveSysComAdmission
open ContractionPostponement

abbrev Sig := RecursiveSysComTranslation.Sig
abbrev Data := RecursiveSysComTranslation.Data
abbrev Key := RecursiveSysComTranslation.Key
abbrev Seq := RecursiveSysComTranslation.Seq
abbrev Ctx := RecursiveSysComTranslation.Ctx
abbrev Parameters := RecursiveSysComTranslation.Parameters
abbrev Tag := Nat × Data

private def zeroKey : Key := fun _ _ => 0

noncomputable def iwTag (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (a : D3SourceEncoding.Formula) (gamma pi : Ctx) : Tag :=
  (hint, (iwInstance zeroKey hint K a gamma pi).instanceData)

noncomputable def closeTag (hint : Nat) (K : Multiset (Potkin.Sequent Sig)) (S : Seq) : Tag :=
  (hint, (closeInstance zeroKey hint K S).instanceData)

noncomputable def comTag (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (p : Parameters) {U V : Seq} (l : TopSpec 0 p U) (r : TopSpec 1 p V) : Tag :=
  (hint, (comInstance zeroKey hint K p l r).instanceData)

noncomputable def evalTag (key : Key) (tag : Tag) : LocalOccurrence Sig Data :=
  canonicalOccurrence (key tag.1 tag.2) tag.2

@[simp] theorem eval_iwTag (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (a : D3SourceEncoding.Formula) (gamma pi : Ctx) :
    evalTag key (iwTag hint K a gamma pi) = iwInstance key hint K a gamma pi := rfl

@[simp] theorem eval_closeTag (key : Key) (hint : Nat)
    (K : Multiset (Potkin.Sequent Sig)) (S : Seq) :
    evalTag key (closeTag hint K S) = closeInstance key hint K S := rfl

@[simp] theorem eval_comTag (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (p : Parameters) {U V : Seq} (l : TopSpec 0 p U) (r : TopSpec 1 p V) :
    evalTag key (comTag hint K p l r) = comInstance key hint K p l r := rfl

/-- The stock follows the actual right-then-left marked-premise staging.
Every legal ordered source top pair is included, even if descriptors coincide. -/
noncomputable def stock : {S : Seq} → {O : Type} → {bounds : O → Seq} →
    Source S O bounds → Multiset (Potkin.Sequent Sig) → List Tag
  | _, _, _, .leaf _, _ => []
  | _, _, _, .iw hint a gamma pi _ body, K => iwTag hint K a gamma pi :: stock body K
  | _, _, _, .phase hint _ p S _ left right topKey sl sr, K =>
      closeTag hint K S ::
        (stock right (K + {enc S}) ++
          (right.origins.flatMap (fun v => stock left (K + {enc (right.leafBoundary v)})) ++
            right.origins.flatMap (fun v => left.origins.map (fun u =>
              comTag (pairHint (topKey (.inl u)) (topKey (.inr v))) K p (sl u) (sr v)))))

/-- All reached target nodes are justified by source stock or actual donor
nodes. This theorem is independent of any chosen registry. -/
theorem translate_all (key : Key) (R : LocalOccurrence Sig Data → Prop) :
    {S : Seq} → {O : Type} → {bounds : O → Seq} → (p : Source S O bounds) →
    (K : Multiset (Potkin.Sequent Sig)) →
    (F : (o : O) → CKTree Sig Data (framed K (bounds o))) →
    (∀ a ∈ stock p K, R (evalTag key a)) → (∀ o, AllNodes R (F o)) →
      AllNodes R (translate key p K F)
  | _, _, _, .leaf _, _, F, _, donors => donors PUnit.unit
  | _, _, _, .iw hint a gamma pi single body, K, F, reached, donors => by
      simp only [translate, iw, node_all, AllChildren, and_true]
      constructor
      · simpa only [eval_iwTag] using reached (iwTag hint K a gamma pi) List.mem_cons_self
      · exact translate_all key R body K F
          (fun tag h => reached tag (List.mem_cons_of_mem _ h)) donors
  | _, _, _, .phase hint uid params S single left right topKey sl sr, K, F, reached, donors => by
      simp only [translate, close, node_all, AllChildren, and_true]
      constructor
      · simpa only [eval_closeTag] using reached (closeTag hint K S) List.mem_cons_self
      · apply translate_all key R right (K + {enc S})
        · intro tag member
          exact reached tag (List.mem_cons_of_mem _ (List.mem_append_left _ member))
        · intro v
          simp only [castTree, all_transport]
          apply translate_all key R left (K + {enc (right.leafBoundary v)})
          · intro tag member
            exact reached tag (List.mem_cons_of_mem _ (List.mem_append_right _
              (List.mem_append_left _ (List.mem_flatMap.mpr
                ⟨v, right.origin_mem v, member⟩))))
          · intro u
            unfold com
            refine (node_all _ _ _ _ R).mpr ⟨?_, donors (.inl u), donors (.inr v), trivial⟩
            have member : comTag (pairHint (topKey (.inl u)) (topKey (.inr v))) K params
                (sl u) (sr v) ∈ stock (.phase hint uid params S single left right topKey sl sr) K :=
              List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨v, right.origin_mem v,
                  List.mem_map.mpr ⟨u, left.origin_mem u, rfl⟩⟩)))
            simpa only [eval_comTag] using reached _ member

theorem encoded_single (S : Seq) (single : S.rhs.card ≤ 1) :
    HLJStructural.Single (enc S) := by
  simpa [HLJStructural.Single, enc, D3SourceEncoding.encodeSequent] using single

theorem top_output_single {role : Fin 2} {params : Parameters} {S : Seq}
    (spec : TopSpec role params S) : HLJStructural.Single (enc S) := by
  apply encoded_single
  rw [← spec.output]
  exact spec.single

theorem passive_add (K : Multiset (Potkin.Sequent Sig)) (S : Seq)
    (valid : HLJStructural.ValidComponents K) (single : HLJStructural.Single (enc S)) :
    HLJStructural.ValidComponents (K + {enc S}) :=
  (HLJStructural.valid_add _ _).mpr ⟨valid, (HLJStructural.valid_singleton _).mpr single⟩

/-- Strict schema admission for every source-reached instance, including every
passive context created by the recursive staging. -/
theorem stock_admitted (key : Key) :
    {S : Seq} → {O : Type} → {bounds : O → Seq} → (p : Source S O bounds) →
    (K : Multiset (Potkin.Sequent Sig)) → HLJStructural.ValidComponents K →
    ∀ tag ∈ stock p K, Theory.Admits (evalTag key tag)
  | _, _, _, .leaf _, _, _, _, member => nomatch member
  | _, _, _, .iw hint a gamma pi single body, K, valid, tag, member => by
      rcases List.mem_cons.mp member with equal | member
      · subst tag
        rw [eval_iwTag]
        exact RecursiveSysComNative.iw_admitted _ _ _ _ _ valid (by simpa using single)
      · exact stock_admitted key body K valid tag member
  | _, _, _, .phase hint uid params S single left right topKey sl sr, K, valid, tag, member => by
      rcases List.mem_cons.mp member with equal | member
      · subst tag
        rw [eval_closeTag]
        exact RecursiveSysComNative.ec_admitted _ _ _ valid (encoded_single S single)
      · rcases List.mem_append.mp member with member | member
        · exact stock_admitted key right (K + {enc S})
            (passive_add K S valid (encoded_single S single)) tag member
        · rcases List.mem_append.mp member with member | member
          · obtain ⟨v, _, member⟩ := List.mem_flatMap.mp member
            exact stock_admitted key left (K + {enc (right.leafBoundary v)})
              (passive_add K _ valid (top_output_single (sr v))) tag member
          · obtain ⟨v, _, member⟩ := List.mem_flatMap.mp member
            obtain ⟨u, _, equal⟩ := List.mem_map.mp member
            subst tag
            rw [eval_comTag]
            exact RecursiveSysComNative.com_admitted _ _ _ _ _ _ _ _ valid
              (by simpa using (sl u).single) (by simpa using (sr v).single)

theorem translate_complete (key : Key) :
    {S : Seq} → {O : Type} → {bounds : O → Seq} → (p : Source S O bounds) →
    (K : Multiset (Potkin.Sequent Sig)) →
    (F : (o : O) → CKTree Sig Data (framed K (bounds o))) →
    (∀ o, (F o).IsComplete) → (translate key p K F).IsComplete
  | _, _, _, .leaf _, _, _, complete => complete PUnit.unit
  | _, _, _, .iw _ _ _ _ _ body, K, F, complete => by
      simpa only [translate, iw, node_complete, CKChildren.IsComplete, and_true] using
        translate_complete key body K F complete
  | _, _, _, .phase _ _ _ _ _ left right _ _ _, K, F, complete => by
      simp only [translate, close, node_complete, CKChildren.IsComplete, and_true]
      apply translate_complete key right
      intro v
      simp only [castTree, complete_transport]
      apply translate_complete key left
      intro u
      simpa only [com, node_complete, CKChildren.IsComplete, and_true] using
        And.intro (complete (.inl u)) (complete (.inr v))

mutual
theorem all_mono {R Q : LocalOccurrence Sig Data → Prop}
    (implication : ∀ o, R o → Q o) : {G : Hypersequent Sig} →
    (tree : CKTree Sig Data G) → AllNodes R tree → AllNodes Q tree
  | _, .interface _, _ => trivial
  | _, .ordinary _ children, nodes => ⟨implication _ nodes.1, children_all_mono implication children nodes.2⟩

theorem children_all_mono {R Q : LocalOccurrence Sig Data → Prop}
    (implication : ∀ o, R o → Q o) : {Gs : List (Hypersequent Sig)} →
    (trees : CKChildren Sig Data Gs) → AllChildren R trees → AllChildren Q trees
  | _, .nil, _ => trivial
  | _, .cons head tail, nodes => ⟨all_mono implication head nodes.1,
      children_all_mono implication tail nodes.2⟩
end

theorem scaffold_admitted
    (offset : Nat) {S O bounds} (p : Source S O bounds)
    (K : Multiset (Potkin.Sequent Sig)) (valid : HLJStructural.ValidComponents K)
    (donors : List (LocalOccurrence Sig Data))
    (consistent : D3RegistryAdmission.ConsistentKeys donors)
    (below : ∀ o ∈ donors, o.id < offset)
    (donorsValid : ∀ o ∈ donors, Theory.Admits o) :
    LocallyAdmittedTree
      (presentation offset (stock p K) donors consistent below donorsValid
        (stock_admitted (allocatedKey offset (stock p K)) p K valid))
      (scaffold (allocatedKey offset (stock p K)) p K) := by
  apply admitted_of_reached offset (stock p K) donors consistent below donorsValid
    (stock_admitted (allocatedKey offset (stock p K)) p K valid)
  apply translate_all (allocatedKey offset (stock p K))
  · intro tag member
    exact .inr ⟨tag, member, rfl⟩
  · intro o
    trivial

noncomputable def checkedTranslation
    (offset : Nat) {S O bounds} (p : Source S O bounds)
    (K : Multiset (Potkin.Sequent Sig)) (valid : HLJStructural.ValidComponents K)
    (donors : List (LocalOccurrence Sig Data))
    (consistent : D3RegistryAdmission.ConsistentKeys donors)
    (below : ∀ o ∈ donors, o.id < offset)
    (donorsValid : ∀ o ∈ donors, Theory.Admits o)
    (F : (o : O) → CKTree Sig Data (framed K (bounds o)))
    (donorNodes : ∀ o, AllNodes (fun occurrence => occurrence ∈ donors) (F o))
    (complete : ∀ o, (F o).IsComplete) :
    CheckedDerivation
      (presentation offset (stock p K) donors consistent below donorsValid
        (stock_admitted (allocatedKey offset (stock p K)) p K valid)) (framed K S) := by
  classical
  let key := allocatedKey offset (stock p K)
  let P := presentation offset (stock p K) donors consistent below donorsValid
    (stock_admitted key p K valid)
  apply CompleteQuotation.checkedOfComplete P (translate key p K F)
  · apply admitted_of_reached offset (stock p K) donors consistent below donorsValid
      (stock_admitted key p K valid)
    apply translate_all key
    · intro tag member
      exact .inr ⟨tag, member, rfl⟩
    · intro o
      exact all_mono (fun _ h => Or.inl h) (F o) (donorNodes o)
  · exact translate_complete key p K F complete

theorem checkedTranslation_realize
    (offset : Nat) {S O bounds} (p : Source S O bounds)
    (K : Multiset (Potkin.Sequent Sig)) (valid : HLJStructural.ValidComponents K)
    (donors : List (LocalOccurrence Sig Data))
    (consistent : D3RegistryAdmission.ConsistentKeys donors)
    (below : ∀ o ∈ donors, o.id < offset)
    (donorsValid : ∀ o ∈ donors, Theory.Admits o)
    (F : (o : O) → CKTree Sig Data (framed K (bounds o)))
    (donorNodes : ∀ o, AllNodes (fun occurrence => occurrence ∈ donors) (F o))
    (complete : ∀ o, (F o).IsComplete) :
    (checkedTranslation offset p K valid donors consistent below donorsValid F donorNodes complete).realize =
      translate (allocatedKey offset (stock p K)) p K F := by
  classical
  unfold checkedTranslation
  apply CompleteQuotation.quote_realize

#check @checkedTranslation
#print axioms translate_all
#print axioms stock_admitted
#print axioms translate_complete
#print axioms scaffold_admitted
#print axioms checkedTranslation_realize

end Potkin.Research.RecursiveSysComReached

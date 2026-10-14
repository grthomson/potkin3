import Potkin.OriginCuts
import Potkin.Examples.MaterialRecordObstruction

/-!
# The same collected obstruction with persistent physical origins

Only the existing swapped-ground regression is revisited. These are native
checked sources in one presentation; the forests are still commutative.
Names 1 and 2 denote physical uses, not registered rule IDs.
-/

namespace Potkin.Examples.OriginCuts

open Potkin MaterialRecordObstruction

def namesAB : treeAB.OriginNames Nat :=
  (0, ((1, PUnit.unit), ((2, PUnit.unit), PUnit.unit)))

def namesBA : treeBA.OriginNames Nat :=
  (0, ((1, PUnit.unit), ((2, PUnit.unit), PUnit.unit)))

theorem freshAB : (treeAB.originList namesAB).Nodup := by decide
theorem freshBA : (treeBA.originList namesBA).Nodup := by decide

theorem forgotten_greatest_terms_equal :
    cutAB.detachedForest = cutBA.detachedForest ∧
      cutAB.remainder = cutBA.remainder :=
  ⟨maximal_forests_equal, maximal_remainders_equal⟩

theorem enriched_remainders_equal :
    cutAB.enrichedRemainder namesAB = cutBA.enrichedRemainder namesBA := rfl

/-- No decidable equality on annotated proofs, or reconstructed order of a
multiset, is needed to distinguish the two collected coefficient payloads. -/
theorem enriched_forests_differ :
    cutAB.originForest namesAB ≠ cutBA.originForest namesBA := by
  intro equal
  have sources := cutAB.collected_injective cutBA namesAB namesBA freshAB freshBA
    enriched_remainders_equal equal
  exact native_sources_differ (congrArg OriginTree.native sources)

theorem decodeAB :
    OriginTree.decode (cutAB.originForest namesAB)
      (cutAB.enrichedRemainder namesAB).native
      (cutAB.enrichedRemainder namesAB).names =
        (⟨treeAB, namesAB⟩ : OriginTree FixtureSignature FixtureData Nat Anonymous.GST) :=
  cutAB.decode_collected namesAB freshAB

theorem decodeBA :
    OriginTree.decode (cutBA.originForest namesBA)
      (cutBA.enrichedRemainder namesBA).native
      (cutBA.enrichedRemainder namesBA).names =
        (⟨treeBA, namesBA⟩ : OriginTree FixtureSignature FixtureData Nat Anonymous.GST) :=
  cutBA.decode_collected namesBA freshBA

/-- Equal registered occurrences at different physical uses retain two names
and two factors even after commutative collection. -/
def duplicateNames : RecursiveCut.duplicateTree.OriginNames Nat :=
  (0, ((1, PUnit.unit), ((2, PUnit.unit), PUnit.unit)))

theorem duplicate_uses_distinct :
    (RecursiveCut.duplicateBothCut.originForest duplicateNames).map
      OriginComponent.rootOrigin = ({1, 2} : Multiset Nat) := rfl

theorem duplicate_multiplicity_retained :
    (RecursiveCut.duplicateBothCut.originForest duplicateNames).card = 2 :=
  (RecursiveCut.duplicateBothCut.originForest_card duplicateNames).trans
    RecursiveCut.duplicate_detached_forest_card

end Potkin.Examples.OriginCuts

#print axioms Potkin.Examples.OriginCuts.enriched_forests_differ
#print axioms Potkin.Examples.OriginCuts.decodeAB
#print axioms Potkin.Examples.OriginCuts.decodeBA

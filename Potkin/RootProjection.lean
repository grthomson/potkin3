import Mathlib.Data.Multiset.Bind
import Potkin.RootCut

namespace Potkin

universe u v w

namespace CKForest

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-- Keep one whole hypersequent block for every connected factor. -/
def blockRoots (forest : CKForest sigma InstanceData) :
    Multiset (Hypersequent sigma) :=
  forest.map CKComponent.boundary

/-- Forget connected blocks; a nonempty forest yields one nonempty whole boundary. -/
def flattenedRoots (forest : CKForest sigma InstanceData) :
    Option (Hypersequent sigma) :=
  if hcard : forest.card = 0 then none
  else
    some {
      components := forest.bind (fun component => component.boundary.components)
      nonempty := by
        have hforest : forest ≠ 0 := by
          intro hzero
          exact hcard (Multiset.card_eq_zero.mpr hzero)
        obtain ⟨component, hcomponent⟩ := Multiset.exists_mem_of_ne_zero hforest
        obtain ⟨sequent, hsequent⟩ :=
          Multiset.exists_mem_of_ne_zero component.boundary.nonempty
        intro hzero
        have hmem : sequent ∈
            forest.bind (fun factor => factor.boundary.components) :=
          Multiset.mem_bind.mpr ⟨component, hcomponent, hsequent⟩
        simp [hzero] at hmem }

theorem flattened_connected_pair_eq_separate
    (S T : Sequent sigma)
    (connected : CKComponent sigma InstanceData)
    (left right : CKComponent sigma InstanceData)
    (hc : connected.boundary = Hypersequent.pair S T)
    (hl : left.boundary = Hypersequent.singleton S)
    (hr : right.boundary = Hypersequent.singleton T) :
    flattenedRoots ({connected} : CKForest sigma InstanceData) =
      flattenedRoots ({left} + {right}) := by
  simp [flattenedRoots, hc, hl, hr, Hypersequent.pair, Hypersequent.singleton]

theorem block_connected_pair_ne_separate
    (connected left right : CKComponent sigma InstanceData) :
    blockRoots ({connected} : CKForest sigma InstanceData) ≠
      blockRoots ({left} + {right}) := by
  intro h
  have cards := congrArg Multiset.card h
  simp [blockRoots] at cards

/-- Flattening can agree while the block-root projection still detects connectedness. -/
theorem connected_pair_root_projection_distinction
    (S T : Sequent sigma)
    (connected left right : CKComponent sigma InstanceData)
    (hc : connected.boundary = Hypersequent.pair S T)
    (hl : left.boundary = Hypersequent.singleton S)
    (hr : right.boundary = Hypersequent.singleton T) :
    flattenedRoots ({connected} : CKForest sigma InstanceData) =
        flattenedRoots ({left} + {right}) ∧
      blockRoots ({connected} : CKForest sigma InstanceData) ≠
        blockRoots ({left} + {right}) :=
  ⟨flattened_connected_pair_eq_separate S T connected left right hc hl hr,
    block_connected_pair_ne_separate connected left right⟩

end CKForest

end Potkin

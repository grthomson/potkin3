import Potkin.NestedCoherence

/-!
# Realised packaging of exact two-stage coherence

`BaseHom` transports admission evidence while leaving every occurrence,
address, boundary, and decorated `CKTree` unchanged.  These wrappers state
that fact at the realised-package level without asking dependent checked
proof terms from different presentations to be `HEq`.
-/

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

namespace RealizedOpenComponent

variable {G : Hypersequent sigma} (source : RealizedOpenComponent P)
variable {first second : ValidAddressCut source.component.tree}

/-- Realised final twice-punctured root package. -/
def canonicalTwoStageRoot
    (witness : CanonicalTwoStageWitness first second) :
    RealizedOpenComponent P :=
  source.remainderOfCut witness.finalCut.toCut

/-- Realised canonical punctured middle occurrence. -/
def canonicalTwoStageMiddle
    (witness : CanonicalTwoStageWitness first second)
    (outer : witness.finalCut.toCut.Site) : RealizedOpenComponent P :=
  (source.detachedOfCut witness.finalCut.toCut outer).remainderOfCut
    (witness.canonicalDecomposition.innerCut outer).toCut

/-- Realised canonical lower detached occurrence. -/
def canonicalTwoStageLower
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : witness.canonicalDecomposition.LowerOccurrence) :
    RealizedOpenComponent P :=
  (source.detachedOfCut witness.finalCut.toCut occurrence.1).detachedOfCut
    (witness.canonicalDecomposition.innerCut occurrence.1).toCut occurrence.2

/-- Base inclusion commutes definitionally with the canonical final package. -/
@[simp]
theorem canonicalTwoStageRoot_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C)
    (witness : CanonicalTwoStageWitness first second) :
    (source.canonicalTwoStageRoot witness).mapBase f =
      (source.mapBase f).canonicalTwoStageRoot witness := by
  rfl

/-- Base inclusion commutes definitionally with every canonical middle
package. -/
@[simp]
theorem canonicalTwoStageMiddle_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C)
    (witness : CanonicalTwoStageWitness first second)
    (outer : witness.finalCut.toCut.Site) :
    (source.canonicalTwoStageMiddle witness outer).mapBase f =
      (source.mapBase f).canonicalTwoStageMiddle witness outer := by
  rfl

/-- Base inclusion commutes definitionally with every canonical lower
package. -/
@[simp]
theorem canonicalTwoStageLower_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C)
    (witness : CanonicalTwoStageWitness first second)
    (occurrence : witness.canonicalDecomposition.LowerOccurrence) :
    (source.canonicalTwoStageLower witness occurrence).mapBase f =
      (source.mapBase f).canonicalTwoStageLower witness occurrence := by
  rfl

/-- The genuine composed two-stage filling reconstructs the realised source
after any occurrence-preserving base inclusion. -/
theorem canonicalTwoStageComposedFilling_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C)
    (witness : CanonicalTwoStageWitness first second) :
    witness.canonicalDecomposition.composedFilling =
      (source.mapBase f).component.tree := by
  simpa using witness.canonicalDecomposition.composedFilling_reconstructs

end RealizedOpenComponent

end Potkin

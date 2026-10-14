import Potkin.Research.RemainderExtractionFlags

/-!
# Finite native extraction sums, before and after explicit forest projection

This is the universal linearization of the physical flag bijection. It is not
declared to be a coalgebra coaction: no forest coproduct/product compatibility
is supplied by merely defining these sums. The coefficient carrier remains
the existing commutative CKForest; the addressed lists are witness records.
-/

namespace Potkin.Research.IteratedExtractionSums

open ContextCutPackets ContextCutAction RemainderExtractionFlags
open scoped BigOperators

universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

noncomputable section

instance remainderFintype {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    Fintype (BranchRemainder tree) := by
  classical
  exact ⟨Finset.univ.sigma (fun _ => Finset.univ), by intro flag; simp⟩

instance insideFintype {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    Fintype (BranchInside tree) :=
  Fintype.ofEquiv (BranchRemainder tree) (branchFlagEquiv tree).symm

abbrev PacketBasis (G : Hypersequent sigma) :=
  List (CKCutEntry sigma InstanceData) × List (CKCutEntry sigma InstanceData) ×
    CKTree sigma InstanceData G

def insideOutput {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (flag : BranchInside tree) : PacketBasis (InstanceData := InstanceData) G :=
  (insideLowerPacket flag.1 flag.2, insideMiddlePacket flag.1 flag.2, flag.1.remainder)

def remainderOutput {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (flag : BranchRemainder tree) : PacketBasis (InstanceData := InstanceData) G :=
  (orderedPacket flag.1, orderedPacket flag.2, flag.2.remainder)

/-- Arbitrary additive weights on the FULL three-output addressed data.
This is not a scalar counting identity or a finite-enumeration conjecture. -/
theorem extraction_sum {R : Type*} [AddCommMonoid R]
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (weight : PacketBasis (InstanceData := InstanceData) G → R) :
    (∑ flag : BranchInside tree, weight (insideOutput flag)) =
      ∑ flag : BranchRemainder tree, weight (remainderOutput flag) := by
  apply Fintype.sum_equiv (branchFlagEquiv tree)
  intro flag
  exact congrArg weight (branchFlag_outputs tree flag).symm

/-- Signed extraction records retain ordered packets until an explicit map. -/
def addressedInside {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    FreeAbelianGroup (PacketBasis (InstanceData := InstanceData) G) :=
  ∑ flag : BranchInside tree, FreeAbelianGroup.of (insideOutput flag)

def addressedRemainder {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    FreeAbelianGroup (PacketBasis (InstanceData := InstanceData) G) :=
  ∑ flag : BranchRemainder tree, FreeAbelianGroup.of (remainderOutput flag)

theorem addressed_coherence {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) : addressedInside tree = addressedRemainder tree :=
  extraction_sum tree FreeAbelianGroup.of

/-- Forget only packet addresses and order, preserving each actual typed
ordinary factor and its multiplicity. No Box becomes a forest component. -/
def collectPacket (packet : List (CKCutEntry sigma InstanceData)) :
    CKForest sigma InstanceData :=
  ↑(packet.map fun entry =>
    ({ boundary := entry.boundary, tree := entry.tree, ordinary := entry.ordinary } :
      CKComponent sigma InstanceData))

theorem collectPacket_append (left right : List (CKCutEntry sigma InstanceData)) :
    collectPacket (left ++ right) = collectPacket left + collectPacket right := by
  simp [collectPacket]

def collectOutput {G : Hypersequent sigma}
    (output : PacketBasis (InstanceData := InstanceData) G) :
    CKForest sigma InstanceData × CKForest sigma InstanceData × CKTree sigma InstanceData G :=
  (collectPacket output.1, collectPacket output.2.1, output.2.2)

/-- Actual three-factor equality after the declared commutative projection;
the literal final typed remainder is not projected or erased. -/
theorem collected_coherence {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) :
    (∑ flag : BranchInside tree,
      FreeAbelianGroup.of (collectOutput (insideOutput flag))) =
      ∑ flag : BranchRemainder tree,
        FreeAbelianGroup.of (collectOutput (remainderOutput flag)) :=
  extraction_sum tree (fun output => FreeAbelianGroup.of (collectOutput output))

#check @extraction_sum
#check @addressed_coherence
#check @collected_coherence
#print axioms extraction_sum
#print axioms addressed_coherence
#print axioms collectPacket_append
#print axioms collected_coherence

end
end Potkin.Research.IteratedExtractionSums

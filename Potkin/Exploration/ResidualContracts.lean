import Potkin.RealizedCut
import Potkin.MaterialInstallation
import Potkin.Examples.InverseCut
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.FixedPoints

/-!
# Native cut residuals, not coefficient convolution

The relation below is independently defined from an actual native proper/empty
`CKCut`, its commutative coefficient forest, and literal typed remainder equality.
It is guarded by admission in ONE fixed equipped presentation. Open admitted
trees are allowed; admission is not a claim of complete logical derivability.

The forest predicate intentionally observes the existing commutative projection.
The existential cut still retains addresses, premise order, multiplicities and
the exact detached-to-puncture matching. No order is reconstructed from a forest.

Whole extraction and interface identity are NOT cases of `NativeResidual`.
They remain native pointed observations, with distinct endpoint behavior.

The Galois connection packages this relation, not an unproved CK cut-flag law.
Sequential relational Box composition is proved separately below. It is NOT
the staged coefficient-convolution WP equation: that still needs the full
native addressed flag bijection, including endpoints.
-/

namespace Potkin.Exploration
universe u v w x
variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData} {G : Hypersequent sigma}

/-- Exact chosen-base support, not occurrence-kind purity. `B` is intentionally
an arbitrary exact occurrence predicate. Admission remains guarded by the fixed
`P` in `NativeResidual`; no cast from `B` to that theory's base is asserted. -/
def ExactMaterialCoefficient {pi : PrimitiveFragment sigma}
    (B : MaterialBase sigma InstanceData pi) (forest : CKForest sigma InstanceData) : Prop :=
  ∀ factor ∈ forest, factor.tree.AllVerticesInBase B

/-- Proper/empty native cuts at one exact root boundary in one fixed registry. -/
def NativeResidual (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop)
    (source remainder : CKTree sigma InstanceData G) : Prop :=
  LocallyAdmittedTree P source ∧
    ∃ cut : CKCut source, A cut.detachedForest ∧ cut.remainder = remainder

/-- An allowed residual carries hereditary registry admission and native refill. -/
theorem nativeResidual_witness {P : EquippedPresentation T}
    {A : CKForest sigma InstanceData → Prop}
    {source remainder : CKTree sigma InstanceData G}
    (h : NativeResidual P A source remainder) :
    LocallyAdmittedTree P remainder ∧
      ∃ cut : CKCut source, A cut.detachedForest ∧ cut.remainder = remainder ∧
        (∀ site, LocallyAdmittedTree P (cut.plan.detached site)) ∧
        cut.fill cut.plan.detached = source := by
  rcases h with ⟨admitted, cut, coefficient, equal⟩
  refine ⟨equal ▸ cut.remainder_locallyAdmitted admitted,
    cut, coefficient, equal, ?_, cut.fill_detached_reconstructs⟩
  exact cut.detached_locallyAdmitted admitted

section RelationalInfrastructure
variable {α : Type u} {β : Type v} {γ : Type w}

def RelPost (R : α → β → Prop) (X : Set α) : Set β :=
  {target | ∃ source ∈ X, R source target}

def RelBox (R : α → β → Prop) (Y : Set β) : Set α :=
  {source | ∀ target, R source target → target ∈ Y}

/-- Generic infrastructure; the native adapter is `nativeResidual_galois`. -/
theorem relPost_relBox_galois (R : α → β → Prop) :
    GaloisConnection (RelPost R) (RelBox R) := by
  intro X Y
  constructor
  · intro h source member target related
    exact h ⟨source, member, related⟩
  · intro h target witness
    rcases witness with ⟨source, member, related⟩
    exact h member target related

def RelCompose (R : α → β → Prop) (S : β → γ → Prop) : α → γ → Prop :=
  fun source target => ∃ middle, R source middle ∧ S middle target

/-- Relational composition reverses operator composition. No CK flag claim. -/
theorem relBox_compose (R : α → β → Prop) (S : β → γ → Prop) (Y : Set γ) :
    RelBox (RelCompose R S) Y = RelBox R (RelBox S Y) := by
  apply Set.ext
  intro source
  constructor
  · intro h middle first target second
    exact h target ⟨middle, first, second⟩
  · intro h target witness
    rcases witness with ⟨middle, first, second⟩
    exact h middle first target second
end RelationalInfrastructure

def NativePost (P : EquippedPresentation T) (A : CKForest sigma InstanceData → Prop)
    (X : Set (CKTree sigma InstanceData G)) : Set (CKTree sigma InstanceData G) :=
  RelPost (NativeResidual P A) X

def NativeBox (P : EquippedPresentation T) (A : CKForest sigma InstanceData → Prop)
    (Y : Set (CKTree sigma InstanceData G)) : Set (CKTree sigma InstanceData G) :=
  RelBox (NativeResidual P A) Y

/-- Native contract adjunction, derived from the independently defined relation. -/
theorem nativeResidual_galois (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) :
    GaloisConnection (NativePost (G := G) P A) (NativeBox P A) :=
  relPost_relBox_galois (NativeResidual P A)

/-- A pinned library consequence: native universal contracts preserve conjunction. -/
theorem nativeBox_inter (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop)
    (left right : Set (CKTree sigma InstanceData G)) :
    NativeBox P A (left ∩ right) = NativeBox P A left ∩ NativeBox P A right :=
  (nativeResidual_galois P A).u_inf

/-- Universal native residual contracts preserve arbitrarily many observations.
This direct structural extension does not require the missing complete-Set
instance dependency. The finite meet case above uses the library adjunction. -/
theorem nativeBox_iInter (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) {ι : Sort x}
    (contracts : ι → Set (CKTree sigma InstanceData G)) :
    NativeBox P A (⋂ i, contracts i) = ⋂ i, NativeBox P A (contracts i) := by
  apply Set.ext
  intro source
  simp only [NativeBox, RelBox, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro h i remainder related
    exact h remainder related i
  · intro h remainder related i
    exact h i remainder related

/-- Inverse-source residuals use the CONVERSE native relation. -/
def NativeInverseResidual (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop)
    (remainder source : CKTree sigma InstanceData G) : Prop :=
  NativeResidual P A source remainder

def NativeInversePost (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) :=
  RelPost (NativeInverseResidual (G := G) P A)

def NativeInverseBox (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) :=
  RelBox (NativeInverseResidual (G := G) P A)

theorem nativeInverseResidual_galois (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) :
    GaloisConnection (NativeInversePost (G := G) P A) (NativeInverseBox P A) :=
  relPost_relBox_galois (NativeInverseResidual P A)

/-- Explicit orientation: a remainder contract quantifies over allowed SOURCES. -/
theorem nativeInverseBox_iff (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop)
    (X : Set (CKTree sigma InstanceData G)) (remainder : CKTree sigma InstanceData G) :
    remainder ∈ NativeInverseBox P A X ↔
      ∀ source, NativeResidual P A source remainder → source ∈ X := Iff.rfl

def NativeFeasible (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) (source : CKTree sigma InstanceData G) : Prop :=
  ∃ remainder, NativeResidual P A source remainder

/-- Box alone is vacuous exactly when its feasible successor set is empty. -/
theorem nativeBox_empty_iff (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) (source : CKTree sigma InstanceData G) :
    source ∈ NativeBox P A ∅ ↔ ¬ NativeFeasible P A source := by
  constructor
  · intro h witness
    rcases witness with ⟨remainder, related⟩
    exact h remainder related
  · intro h remainder related
    exact (h ⟨remainder, related⟩).elim

/-- Interfaces have no ordinary CK cuts, independent of any finite fixture. -/
theorem nativeResidual_interface_source (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) (remainder : CKTree sigma InstanceData G) :
    ¬ NativeResidual P A (.interface G) remainder := by
  rintro ⟨_, cut, _, _⟩
  exact cut.sourceOrdinary

/-- Proper/empty CK cuts retain an ordinary root: typed whole extraction differs. -/
theorem nativeResidual_interface_target (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) (source : CKTree sigma InstanceData G) :
    ¬ NativeResidual P A source (.interface G) := by
  rintro ⟨_, cut, _, equal⟩
  have ordinary := cut.remainder_isOrdinary
  rw [equal] at ordinary
  exact ordinary

theorem nativeBox_interface (P : EquippedPresentation T)
    (A : CKForest sigma InstanceData → Prop) (Y : Set (CKTree sigma InstanceData G)) :
    (.interface G : CKTree sigma InstanceData G) ∈ NativeBox P A Y := by
  intro remainder related
  exact (nativeResidual_interface_source P A remainder related).elim

/-- Broadening allowed coefficients strengthens the universal source contract. -/
theorem nativeBox_antitone_coefficient (P : EquippedPresentation T)
    {A B : CKForest sigma InstanceData → Prop} (hAB : ∀ forest, A forest → B forest)
    (Y : Set (CKTree sigma InstanceData G)) : NativeBox P B Y ⊆ NativeBox P A Y := by
  intro source h remainder related
  rcases related with ⟨admitted, cut, coefficient, equal⟩
  exact h remainder ⟨admitted, cut, hAB _ coefficient, equal⟩

/-! Fixed-point triage, NOT a completed finite recognizer bridge.
`OrderHom.lfp` and `map_lfp` are checked below. Applying them to Set(native
trees) needs the complete Set lattice import, whose cached dependency
`Mathlib.Data.Nat.Set.olean` is unavailable in this checkout. A general least
fixed point would still be semantic existence, NOT executable terminating
saturation. For simultaneous provider/observer reachability the substantive
missing primitive is a finite JOINT native observation quotient with exact
constructor transitions, source guards and reconstructible witnesses.
Finite concrete registry boundaries alone do not provide that quotient for
arbitrary trees/coefficient predicates. No finite-height checking is used. -/

section NativeExamples
open Potkin.Examples

/-- Nonvacuous admitted example: the actual nullary generator's empty cut. -/
theorem admitted_ground_feasible :
    NativeFeasible RecursiveCut.duplicatePresentation (fun _ => True) InverseCut.ground :=
  ⟨InverseCut.ground, InverseCut.ground_admitted, InverseCut.groundEmpty, trivial, rfl⟩

theorem ground_is_checked : InverseCut.ground = Anonymous.checkedS.realize := rfl

/-- A native pointed whole witness exists, but is not an ordinary residual. -/
theorem whole_extraction_endpoint_failure :
    InverseCut.groundWhole.remainder = InverseCut.hole ∧
      ¬ NativeResidual RecursiveCut.duplicatePresentation (fun _ => True)
        InverseCut.ground InverseCut.hole :=
  ⟨rfl, nativeResidual_interface_target _ _ _⟩
end NativeExamples

/-! Tactic laboratory on actual obligations. The central proofs above have
explicit stable dependencies; these examples record routine search suggestions. -/
example (P : EquippedPresentation T) (A : CKForest sigma InstanceData → Prop)
    (Y : Set (CKTree sigma InstanceData G)) :
    (.interface G : CKTree sigma InstanceData G) ∈ NativeBox P A Y := by
  simp? only [nativeBox_interface]

example (P : EquippedPresentation T) (A : CKForest sigma InstanceData → Prop)
    {ι : Sort x} (contracts : ι → Set (CKTree sigma InstanceData G)) :
    NativeBox P A (⋂ i, contracts i) = ⋂ i, NativeBox P A (contracts i) := by
  exact?

#check GaloisConnection.u_inf
#check GaloisConnection.u_iInf
#check GaloisConnection.monotone_l
#check OrderHom.lfp
#check OrderHom.map_lfp
#synth SemilatticeInf (Set (CKTree sigma InstanceData G))
#print axioms nativeResidual_witness
#print axioms nativeResidual_galois
#print axioms nativeBox_inter
#print axioms nativeBox_iInter
#print axioms nativeInverseResidual_galois
#print axioms nativeBox_empty_iff
#print axioms whole_extraction_endpoint_failure

end Potkin.Exploration

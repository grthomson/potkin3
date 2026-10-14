import Potkin.CutExpansionSums
import Potkin.InverseCut
import Potkin.Examples.InverseCut

/-!
# Native finite cut coefficients: the available part of the linearization probe

This additive exploration leaves `CKForest` unchanged. The right coordinate is
the literal typed open remainder, not a forest unit or a quotient of interfaces.
Only native nonroot cuts (including the empty cut) are summed here. The global
whole endpoint is not represented by a fabricated cut and is not added here.

The installed-cut identity below uses the actual existing native bijection;
it is NOT a proof of the missing full ordered cut-flag law or coassociativity.
-/

namespace Potkin.Exploration

universe u v w z
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

noncomputable section

/-- Exact finite counts, without coefficient deduplication. This is a scalar
observation function on the native multiset, NOT an asserted free-module or
tensor comparison. Installed Finsupp/tensor imports are currently blocked by
missing transitive bytecode; the corresponding library bridge remains OPEN. -/
def linearize {Basis : Type z} (bag : Multiset Basis) : Basis → ℕ := by
  classical
  exact fun basis => bag.count basis

theorem linearize_add {Basis : Type z} (left right : Multiset Basis) :
    linearize (left + right) = linearize left + linearize right := by
  classical
  funext basis
  exact Multiset.count_add _ _ _

/-- The scalar observation has an actual finite support, witnessed by the
native bag's toFinset. This does not identify a nonexistent tensor carrier. -/
theorem linearize_support_finite {Basis : Type z} (bag : Multiset Basis) :
    ∃ support : Finset Basis, ∀ basis, basis ∈ support ↔ linearize bag basis ≠ 0 := by
  classical
  refine ⟨bag.toFinset, ?_⟩
  intro basis
  simp only [Multiset.mem_toFinset, linearize, Multiset.count_ne_zero]

/-- Existing native carriers, paired only at the coefficient layer. -/
abbrev CutBasis (G : Hypersequent sigma) :=
  CKForest sigma InstanceData × CKTree sigma InstanceData G

def cutBasis {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : ExtensionalCKCut tree) : CutBasis (InstanceData := InstanceData) G :=
  (cut.compiled.detachedForest, cut.compiled.remainder)

/-- Important limitation on possible collisions: fixed SOURCE plus literal
remainder already determines the public cut. Forest equality is not needed. -/
theorem cutBasis_injective {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} :
    Function.Injective (cutBasis : ExtensionalCKCut tree → _) := by
  intro left right equal
  have sameRemainder : left.compiled.remainder = right.compiled.remainder :=
    congrArg Prod.snd equal
  have sameCut := CKCut.eq_of_remainder_eq left.compiled right.compiled sameRemainder
  have samePublic := congrArg ExtensionalCKCut.ofCKCut sameCut
  simpa only [ExtensionalCKCut.ofCKCut_compiled] using samePublic

def cutBag {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) : Multiset (CutBasis (InstanceData := InstanceData) G) :=
  (↑(ExtensionalCKCut.enumerate tree ordinary) : Multiset (ExtensionalCKCut tree)).map
    (cutBasis (tree := tree))

def cutCoefficients {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) : CutBasis (InstanceData := InstanceData) G → ℕ :=
  linearize (cutBag tree ordinary)

/-- A universal coefficient statement, not a bounded enumeration experiment. -/
theorem coefficient_at_native_cut {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : ExtensionalCKCut tree) :
    cutCoefficients tree cut.sourceOrdinary (cutBasis cut) = 1 := by
  classical
  letI : DecidableEq (CutBasis (InstanceData := InstanceData) G) :=
    fun left right => Classical.propDecidable (left = right)
  change ((↑(ExtensionalCKCut.enumerate tree cut.sourceOrdinary) :
    Multiset (ExtensionalCKCut tree)).map (cutBasis (tree := tree))).count (cutBasis cut) = 1
  rw [Multiset.count_map_eq_count' _ _ cutBasis_injective cut, Multiset.coe_count]
  exact ExtensionalCKCut.count_enumerate_eq_one cut

/-- Equal factors INSIDE a forest remain multiplicities; this repeated-family
example separately shows that the linear adapter does not deduplicate outputs.
It does not invent two different cuts with an identical literal remainder. -/
theorem duplicate_native_family_coefficient {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : ExtensionalCKCut tree) :
    (cutCoefficients tree cut.sourceOrdinary + cutCoefficients tree cut.sourceOrdinary)
      (cutBasis cut) = 2 := by
  change cutCoefficients tree cut.sourceOrdinary (cutBasis cut) +
    cutCoefficients tree cut.sourceOrdinary (cutBasis cut) = 2
  rw [coefficient_at_native_cut]

/-- The independent installation choices are native constructor data: an old
ancestor selection masks every swallowed payload choice. -/
def installedChoiceCoefficients {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (installation : CKCut tree)
    (fillers : (site : installation.Site) →
      CKTree sigma InstanceData (installation.plan.siteBoundary site)) :
    CutBasis (InstanceData := InstanceData) G → ℕ :=
  linearize ((↑(installation.plan.enumerateExpansionChoices fillers) : Multiset _).map
    (fun choice => cutBasis ((installation.installedPublicCutEquiv fillers).symm choice)))

/-- Actual native installed-cut reindexing promoted to coefficient equality.
No enumeration of completed proofs is used to CONSTRUCT the right side. -/
theorem installed_coefficients {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (installation : CKCut tree)
    (fillers : (site : installation.Site) →
      CKTree sigma InstanceData (installation.plan.siteBoundary site)) :
    cutCoefficients (installation.fill fillers) (installation.fill_isOrdinary fillers) =
      installedChoiceCoefficients installation fillers := by
  unfold cutCoefficients cutBag installedChoiceCoefficients
  rw [installation.publicEnumerate_eq_expandedChoices fillers, Multiset.map_map]
  rfl

/-- Eligibility and further native coefficient continuations are also valid.
The weight may retain ordered addresses, origins, or native iterated factors. -/
theorem installed_filtered_continuation {Basis : Type z}
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (installation : CKCut tree)
    (fillers : (site : installation.Site) →
      CKTree sigma InstanceData (installation.plan.siteBoundary site))
    (eligible : ExtensionalCKCut (installation.fill fillers) → Prop)
    [DecidablePred eligible]
    (weight : ExtensionalCKCut (installation.fill fillers) → Multiset Basis) :
    linearize (((↑(ExtensionalCKCut.enumerate (installation.fill fillers)
      (installation.fill_isOrdinary fillers)) : Multiset _).filter eligible).bind weight) =
    linearize (((↑(installation.plan.enumerateExpansionChoices fillers) : Multiset _).filter
      (fun choice => eligible ((installation.installedPublicCutEquiv fillers).symm choice))).bind
      (fun choice => weight ((installation.installedPublicCutEquiv fillers).symm choice))) :=
  congrArg linearize (installation.publicEnumerate_filter_bind_expandedChoices
    fillers eligible weight)

/-- Changing natural coefficients needs only an additive map, but support
reflection additionally needs that this map reflects zero. -/
def changeCoefficients {Basis : Type z} {R : Type*} [AddMonoid R]
    (map : ℕ →+ R) (coefficients : Basis → ℕ) : Basis → R :=
  fun basis => map (coefficients basis)

theorem changeCoefficients_support {Basis : Type z} {R : Type*} [AddMonoid R]
    (map : ℕ →+ R) (reflectsZero : ∀ n, map n = 0 ↔ n = 0)
    (coefficients : Basis → ℕ) :
    {basis | changeCoefficients map coefficients basis ≠ 0} =
      {basis | coefficients basis ≠ 0} := by
  classical
  ext basis
  change (map (coefficients basis) ≠ 0) ↔ (coefficients basis ≠ 0)
  exact not_congr (reflectsZero (coefficients basis))

/-- Without zero reflection an additive post-map can erase an actual native
coefficient two. This ZERO additive map is not a unital semiring map. The
stronger ZMod 2 unital-ring probe remains blocked by library imports. -/
theorem duplicate_native_family_erased_zero_map {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : ExtensionalCKCut tree) :
    changeCoefficients (0 : ℕ →+ ℕ)
      (cutCoefficients tree cut.sourceOrdinary + cutCoefficients tree cut.sourceOrdinary)
        (cutBasis cut) = 0 := rfl

/- Tactic lab: the actual native reindexing obligation and finite-count
extensionality. A definitional proof cannot supply the native bijection; search
may find the named central theorem, but does not invent the missing bridge. -/
example {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (installation : CKCut tree)
    (fillers : (site : installation.Site) →
      CKTree sigma InstanceData (installation.plan.siteBoundary site)) :
    cutCoefficients (installation.fill fillers) (installation.fill_isOrdinary fillers) =
      installedChoiceCoefficients installation fillers := by
  fail_if_success rfl
  exact?

example {Basis : Type z} (left right : Multiset Basis) :
    linearize (left + right) = linearize left + linearize right := by
  classical
  ext basis
  simp? [linearize, Multiset.count_add]

/-- The actual registered binary fixture contains two physical uses of an
equal positive factor. Linearizing its native forest retains coefficient two. -/
theorem equal_detached_factor_multiplicity :
    linearize Examples.InverseCut.bothCut.detachedForest
      (⟨Examples.Anonymous.GS, Examples.InverseCut.ground, trivial⟩ :
        CKComponent Examples.Anonymous.signature Examples.Anonymous.InstanceData) = 2 := by
  classical
  change Examples.InverseCut.bothCut.detachedForest.count _ = 2
  simp [CKCut.detachedForest, Examples.InverseCut.equal_provider_uses.1]

#check Multiset.count_add
#check CKCut.installedPublicCutEquiv

end
end Potkin.Exploration

#print axioms Potkin.Exploration.cutBasis_injective
#print axioms Potkin.Exploration.coefficient_at_native_cut
#print axioms Potkin.Exploration.installed_coefficients
#print axioms Potkin.Exploration.installed_filtered_continuation
#print axioms Potkin.Exploration.changeCoefficients_support
#print axioms Potkin.Exploration.linearize_support_finite
#print axioms Potkin.Exploration.duplicate_native_family_erased_zero_map
#print axioms Potkin.Exploration.equal_detached_factor_multiplicity

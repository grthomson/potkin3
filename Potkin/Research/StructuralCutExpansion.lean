import Potkin.Research.StructuralReduction
import Potkin.MaterialComposition

/-!
# Physical CK expansion of one genuine contraction/Cut reduction

The logical rules and boundaries are those of `StructuralReduction`, not a
binary node labelled contraction.  Here the reduct has TWO physical uses of
the same arbitrary payload.  The cut expansion precedes commutative collection.
This is a finite witness/sum theorem; no full Hopf or quotient law is claimed.
-/

namespace Potkin.Research.StructuralCutExpansion
open StructuralReduction MaterialObservations

abbrev PTree := CKTree sigma Data PBoundary
abbrev QTree := CKTree sigma Data QBoundary

/-- Closed seed witnesses avoid postponed tactic metavariables in dependent
installation indices. They add no assumption to the typed filling bridge. -/
def groundPOrdinary : groundP.IsOrdinary := True.intro
def groundQOrdinary : groundQ.IsOrdinary := True.intro

/-- The two input positions are independent even when the installed proofs
are equal.  The actual reduct is its diagonal specialization. -/
def independentTarget (left right : PTree) (body : QTree) :=
  contractD (outerCut left (innerCut right body))

theorem diagonal_is_logical_target (proof : PTree) (body : QTree) :
    independentTarget proof proof body = target proof body := rfl

/-- A native installation in an actual reduct.  Its three sites are precisely
the two physical P roots and the Q root; no root cut or surrogate is used. -/
def targetInstallation (seedP : PTree) (seedQ : QTree)
    (pOrdinary : seedP.IsOrdinary) (qOrdinary : seedQ.IsOrdinary) :
    CKCut (target seedP seedQ) :=
  ⟨by trivial, .ordinary contractDOccurrence _
    (.cons _ _ (.descend (.ordinary cutDuplicatedOccurrence _
      (.cons _ _ (.detach pOrdinary)
        (.cons _ _ (.descend (.ordinary cutRemainingOccurrence _
          (.cons _ _ (.detach pOrdinary)
            (.cons _ _ (.detach qOrdinary) .nil)))) .nil)))) .nil)⟩

def targetFillers (seedP : PTree) (seedQ : QTree)
    (pOrdinary : seedP.IsOrdinary) (qOrdinary : seedQ.IsOrdinary)
    (left right : PTree) (body : QTree) :
    (site : (targetInstallation seedP seedQ pOrdinary qOrdinary).Site) →
      CKTree sigma Data
        ((targetInstallation seedP seedQ pOrdinary qOrdinary).plan.siteBoundary site)
  | .inl (.inl _) => left
  | .inl (.inr (.inl (.inl _))) => right
  | .inl (.inr (.inl (.inr (.inl _)))) => body
  | .inl (.inr (.inl (.inr (.inr impossible)))) => nomatch impossible
  | .inl (.inr (.inr impossible)) => nomatch impossible
  | .inr impossible => nomatch impossible

/-- New application bridge: native typed filling is literally the independently
specified logical reduct with independent physical payload positions. -/
theorem filling_is_independent_target (seedP : PTree) (seedQ : QTree)
    (pOrdinary : seedP.IsOrdinary) (qOrdinary : seedQ.IsOrdinary)
    (left right : PTree) (body : QTree) :
    (targetInstallation seedP seedQ pOrdinary qOrdinary).fill
      (targetFillers seedP seedQ pOrdinary qOrdinary left right body) =
        independentTarget left right body := rfl

theorem installation_has_three_physical_addresses (seedP : PTree) (seedQ : QTree)
    (pOrdinary : seedP.IsOrdinary) (qOrdinary : seedQ.IsOrdinary) :
    (targetInstallation seedP seedQ pOrdinary qOrdinary).orderedAddresses =
      [[0, 0], [0, 1, 0], [0, 1, 1]] := rfl

/-- Distinct logical ports are not needed: the two copies of the SAME port
have distinct incomparable physical addresses. -/
theorem copied_root_addresses_distinct :
    ([0, 0] : InternalAddress) ≠ [0, 1, 0] := by decide

/-- Native choices only, not another cut carrier. `inl` is an enclosing Cut
selection, never the witness-free whole-tree endpoint. -/
abbrev PhysicalChoices (left right : PTree) (body : QTree) :=
  PUnit.{1} ⊕ (CKBranchCut left × (PUnit.{1} ⊕ (CKBranchCut right × CKBranchCut body)))

def physicalCut (left right : PTree) (body : QTree) :
    PhysicalChoices left right body → CKCut (independentTarget left right body)
  | .inl _ =>
      ⟨by trivial, .ordinary contractDOccurrence _ (.cons _ _ (.detach (by trivial)) .nil)⟩
  | .inr (leftCut, .inl _) =>
      ⟨by trivial, .ordinary contractDOccurrence _
        (.cons _ _ (.descend (.ordinary cutDuplicatedOccurrence _
          (.cons _ _ leftCut (.cons _ _ (.detach (by trivial)) .nil)))) .nil)⟩
  | .inr (leftCut, .inr (rightCut, bodyCut)) =>
      ⟨by trivial, .ordinary contractDOccurrence _
        (.cons _ _ (.descend (.ordinary cutDuplicatedOccurrence _
          (.cons _ _ leftCut (.cons _ _ (.descend (.ordinary cutRemainingOccurrence _
            (.cons _ _ rightCut (.cons _ _ bodyCut .nil)))) .nil)))) .nil)⟩

/-- Merely remove the terminal units of the EXISTING installation choice
index; the recursive payload cuts themselves are unchanged. -/
abbrev InstallationChoices (left right : PTree) (body : QTree) :=
  (targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).plan.ExpansionChoices
    (targetFillers groundP groundQ groundPOrdinary groundQOrdinary left right body)

def packInstallationChoices (left right : PTree) (body : QTree) :
    PhysicalChoices left right body → InstallationChoices left right body
  | .inl _ => (.inl PUnit.unit, PUnit.unit)
  | .inr (leftCut, .inl _) =>
      (.inr (leftCut, (.inl PUnit.unit, PUnit.unit)), PUnit.unit)
  | .inr (leftCut, .inr (rightCut, bodyCut)) =>
      (.inr (leftCut, (.inr (rightCut, (bodyCut, PUnit.unit)), PUnit.unit)), PUnit.unit)

def unpackInstallationChoices (left right : PTree) (body : QTree) :
    InstallationChoices left right body → PhysicalChoices left right body
  | (.inl _, _) => .inl PUnit.unit
  | (.inr (leftCut, (.inl _, _)), _) => .inr (leftCut, .inl PUnit.unit)
  | (.inr (leftCut, (.inr (rightCut, (bodyCut, _)), _)), _) =>
      .inr (leftCut, .inr (rightCut, bodyCut))

theorem pack_unpackInstallationChoices (left right : PTree) (body : QTree)
    (choice : InstallationChoices left right body) :
    packInstallationChoices left right body (unpackInstallationChoices left right body choice) =
      choice := by
  rcases choice with ⟨outer, tailUnit⟩
  cases tailUnit
  cases outer with
  | inl outerUnit => cases outerUnit; rfl
  | inr pair =>
      rcases pair with ⟨leftCut, inner, tailUnit⟩
      cases tailUnit
      cases inner with
      | inl innerUnit => cases innerUnit; rfl
      | inr pair =>
          rcases pair with ⟨rightCut, bodyCut, tailUnit⟩
          cases tailUnit
          rfl

theorem physicalCut_eq_installed (left right : PTree) (body : QTree)
    (choice : PhysicalChoices left right body) :
    (targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).expandedCut
      (targetFillers groundP groundQ groundPOrdinary groundQOrdinary left right body)
      (packInstallationChoices left right body choice) = physicalCut left right body choice := by
  cases choice with
  | inl outerUnit => cases outerUnit; rfl
  | inr pair =>
      rcases pair with ⟨leftCut, inner⟩
      cases inner with
      | inl innerUnit => cases innerUnit; rfl
      | inr pair => rcases pair with ⟨rightCut, bodyCut⟩; rfl

def physicalChoices (left right : PTree) (body : QTree)
    (cut : CKCut (independentTarget left right body)) : PhysicalChoices left right body :=
  unpackInstallationChoices left right body
    ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).plan.decomposeCut
      (targetFillers groundP groundQ groundPOrdinary groundQOrdinary left right body) cut.plan)

theorem physicalChoices_physicalCut (left right : PTree) (body : QTree)
    (choice : PhysicalChoices left right body) :
    physicalChoices left right body (physicalCut left right body choice) = choice := by
  cases choice with
  | inl unit => cases unit; rfl
  | inr pair =>
      rcases pair with ⟨leftCut, inner⟩
      cases inner with
      | inl unit => cases unit; rfl
      | inr pair => rcases pair with ⟨rightCut, bodyCut⟩; rfl

theorem physicalCut_physicalChoices (left right : PTree) (body : QTree)
    (cut : CKCut (independentTarget left right body)) :
    physicalCut left right body (physicalChoices left right body cut) = cut := by
  rw [← physicalCut_eq_installed, physicalChoices, pack_unpackInstallationChoices]
  exact ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).installedCutEquiv
    (targetFillers groundP groundQ groundPOrdinary groundQOrdinary left right body)).left_inv cut

/-- Exhaustive constructor classification: arbitrary internal choices in the
two copies are independent, except when an enclosing ancestor suppresses them. -/
def physicalCutEquiv (left right : PTree) (body : QTree) :
    CKCut (independentTarget left right body) ≃ PhysicalChoices left right body where
  toFun := physicalChoices left right body
  invFun := physicalCut left right body
  left_inv := physicalCut_physicalChoices left right body
  right_inv := physicalChoices_physicalCut left right body

theorem independent_choices_injective (left right : PTree) (body : QTree) :
    Function.Injective (fun choices : CKBranchCut left × CKBranchCut right × CKBranchCut body =>
      physicalCut left right body (.inr (choices.1, .inr choices.2))) := by
  intro first second equal
  have choices := congrArg (physicalChoices left right body) equal
  change (Sum.inr (first.1, Sum.inr first.2) : PhysicalChoices left right body) =
    Sum.inr (second.1, Sum.inr second.2) at choices
  have pair :
      (first.1, (Sum.inr first.2 : PUnit.{1} ⊕ (CKBranchCut right × CKBranchCut body))) =
      (second.1, Sum.inr second.2) := Sum.inr.inj choices
  injection pair with leftEqual innerEqual
  exact Prod.ext leftEqual (Sum.inr.inj innerEqual)

/-- Every actual cut reconstructs with its own addressed detached family, not
with an address fabricated after multiset collection. -/
theorem physicalCut_native_refill (left right : PTree) (body : QTree)
    (choice : PhysicalChoices left right body) :
    (physicalCut left right body choice).fill
      (physicalCut left right body choice).plan.detached = independentTarget left right body :=
  (physicalCut left right body choice).fill_detached_reconstructs

/-- The source has two slots, while the reduct has three.  The source root
is not artificially retained across logical normalization. -/
def sourceInstallation (seedP : PTree) (seedQ : QTree)
    (pOrdinary : seedP.IsOrdinary) (qOrdinary : seedQ.IsOrdinary) :
    CKCut (source seedP seedQ) :=
  ⟨by trivial, .ordinary cutContractedOccurrence _
    (.cons _ _ (.detach pOrdinary)
      (.cons _ _ (.descend (.ordinary contractAOccurrence _
        (.cons _ _ (.detach qOrdinary) .nil))) .nil))⟩

def sourceFillers (seedP : PTree) (seedQ : QTree)
    (pOrdinary : seedP.IsOrdinary) (qOrdinary : seedQ.IsOrdinary)
    (proof : PTree) (body : QTree) :
    (site : (sourceInstallation seedP seedQ pOrdinary qOrdinary).Site) →
      CKTree sigma Data
        ((sourceInstallation seedP seedQ pOrdinary qOrdinary).plan.siteBoundary site)
  | .inl _ => proof
  | .inr (.inl (.inl _)) => body
  | .inr (.inl (.inr impossible)) => nomatch impossible
  | .inr (.inr impossible) => nomatch impossible

theorem filling_is_logical_source (seedP : PTree) (seedQ : QTree)
    (pOrdinary : seedP.IsOrdinary) (qOrdinary : seedQ.IsOrdinary)
    (proof : PTree) (body : QTree) :
    (sourceInstallation seedP seedQ pOrdinary qOrdinary).fill
      (sourceFillers seedP seedQ pOrdinary qOrdinary proof body) = source proof body := rfl

theorem source_installation_addresses (seedP : PTree) (seedQ : QTree)
    (pOrdinary : seedP.IsOrdinary) (qOrdinary : seedQ.IsOrdinary) :
    (sourceInstallation seedP seedQ pOrdinary qOrdinary).orderedAddresses =
      [[0], [1, 0]] := rfl

/-- Source and target are separate native templates, with exact typed filling
bridges.  Neither equality assumes a proof quotient or normalization law. -/
theorem source_target_native_fillings (proof : PTree) (body : QTree) :
    (sourceInstallation groundP groundQ groundPOrdinary groundQOrdinary).fill
      (sourceFillers groundP groundQ groundPOrdinary groundQOrdinary proof body) = source proof body ∧
    (targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).fill
      (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body) = target proof body :=
  ⟨rfl, rfl⟩

universe z z'
variable {Origin : Type z}

/-! These are annotations of the EXISTING native proof carrier.  The two P
uses have the same boundary definitionally: tagging never transports or
changes a formula, occurrence decoration, registry, or native tree. -/

mutual
def tagTreeNames {Name : Type z} {Tagged : Type z'} (tag : Name → Tagged) :
    {G : Hypersequent sigma} → (tree : CKTree sigma Data G) →
      tree.OriginNames Name → tree.OriginNames Tagged
  | _, .interface _, name => tag name
  | _, .ordinary _ children, names =>
      (tag names.1, tagChildNames tag children names.2)

def tagChildNames {Name : Type z} {Tagged : Type z'} (tag : Name → Tagged) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma Data Gs) →
      children.OriginNames Name → children.OriginNames Tagged
  | _, .nil, _ => PUnit.unit
  | _, .cons head tail, names =>
      (tagTreeNames tag head names.1, tagChildNames tag tail names.2)
end

mutual
theorem tagged_tree_origins {Name : Type z} {Tagged : Type z'} (tag : Name → Tagged) :
    {G : Hypersequent sigma} → (tree : CKTree sigma Data G) →
      (names : tree.OriginNames Name) →
      tree.originList (tagTreeNames tag tree names) = (tree.originList names).map tag
  | _, .interface _, _ => rfl
  | _, .ordinary _ children, names => by
      simp only [tagTreeNames, CKTree.originList, List.map_cons,
        tagged_child_origins tag children names.2]

theorem tagged_child_origins {Name : Type z} {Tagged : Type z'} (tag : Name → Tagged) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma Data Gs) →
      (names : children.OriginNames Name) →
      children.originList (tagChildNames tag children names) =
        (children.originList names).map tag
  | _, .nil, _ => rfl
  | _, .cons head tail, names => by
      simp only [tagChildNames, CKChildren.originList, List.map_append,
        tagged_tree_origins tag head names.1, tagged_child_origins tag tail names.2]
end

/-- Fixed redex births, physically separated P births, and Q births.  This is
an origin TYPE, not a new proof tree or a cut representation. -/
abbrev PhysicalOrigin (Name : Type z) := Fin 3 ⊕ ((Bool × Name) ⊕ Name)

def leftBirth (name : Origin) : PhysicalOrigin Origin := .inr (.inl (false, name))
def rightBirth (name : Origin) : PhysicalOrigin Origin := .inr (.inl (true, name))
def bodyBirth (name : Origin) : PhysicalOrigin Origin := .inr (.inr name)

def leftCopyNames (proof : PTree) (names : proof.OriginNames Origin) :
    proof.OriginNames (PhysicalOrigin Origin) := tagTreeNames leftBirth proof names
def rightCopyNames (proof : PTree) (names : proof.OriginNames Origin) :
    proof.OriginNames (PhysicalOrigin Origin) := tagTreeNames rightBirth proof names
def bodyCopyNames (body : QTree) (names : body.OriginNames Origin) :
    body.OriginNames (PhysicalOrigin Origin) := tagTreeNames bodyBirth body names

/-- EVERY birth in one physical copy is disjoint from EVERY birth in the
other, including old interfaces and arbitrary-depth internal vertices.  No
freshness within the supplied original naming is silently assumed. -/
theorem copied_origins_disjoint (proof : PTree) (names : proof.OriginNames Origin) :
    List.Disjoint (proof.originList (leftCopyNames proof names))
      (proof.originList (rightCopyNames proof names)) := by
  intro name leftMember rightMember
  rw [leftCopyNames, tagged_tree_origins] at leftMember
  rw [rightCopyNames, tagged_tree_origins] at rightMember
  obtain ⟨leftName, _, leftEqual⟩ := List.mem_map.mp leftMember
  obtain ⟨rightName, _, rightEqual⟩ := List.mem_map.mp rightMember
  have impossible := congrArg Prod.fst
    (Sum.inl.inj (Sum.inr.inj (leftEqual.trans rightEqual.symm)))
  cases impossible

def physicalTargetNames (left right : PTree) (body : QTree)
    (leftNames : left.OriginNames Origin) (rightNames : right.OriginNames Origin)
    (bodyNames : body.OriginNames Origin) :
    (independentTarget left right body).OriginNames (PhysicalOrigin Origin) :=
  (.inl ⟨0, by decide⟩,
    ((.inl ⟨1, by decide⟩, (leftCopyNames left leftNames,
      ((.inl ⟨2, by decide⟩, (rightCopyNames right rightNames,
        (bodyCopyNames body bodyNames, PUnit.unit))), PUnit.unit))), PUnit.unit))

def physicallyNamedTarget (proof : PTree) (body : QTree)
    (proofNames : proof.OriginNames Origin) (bodyNames : body.OriginNames Origin) :
    OriginTree sigma Data (PhysicalOrigin Origin) resultBoundary :=
  ⟨target proof body, physicalTargetNames proof proof body proofNames proofNames bodyNames⟩

/-- Seed payload names are discarded by installation; retained redex roots
keep these three distinct births. -/
def targetSeedNames : (target groundP groundQ).OriginNames (PhysicalOrigin Origin) :=
  (.inl ⟨0, by decide⟩,
    ((.inl ⟨1, by decide⟩, ((.inl ⟨0, by decide⟩, PUnit.unit),
      ((.inl ⟨2, by decide⟩, ((.inl ⟨0, by decide⟩, PUnit.unit),
        ((.inl ⟨0, by decide⟩, PUnit.unit), PUnit.unit))), PUnit.unit))), PUnit.unit))

def physicalFillerNames (proof : PTree) (body : QTree)
    (proofNames : proof.OriginNames Origin) (bodyNames : body.OriginNames Origin) :
    (site : (targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).Site) →
      ((targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body) site).OriginNames
        (PhysicalOrigin Origin)
  | .inl (.inl _) => leftCopyNames proof proofNames
  | .inl (.inr (.inl (.inl _))) => rightCopyNames proof proofNames
  | .inl (.inr (.inl (.inr (.inl _)))) => bodyCopyNames body bodyNames
  | .inl (.inr (.inl (.inr (.inr impossible)))) => nomatch impossible
  | .inl (.inr (.inr impossible)) => nomatch impossible
  | .inr impossible => nomatch impossible

theorem filling_preserves_physical_names (proof : PTree) (body : QTree)
    (proofNames : proof.OriginNames Origin) (bodyNames : body.OriginNames Origin) :
    (targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).plan.fillOriginNames
      (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body)
      targetSeedNames (physicalFillerNames proof body proofNames bodyNames) =
        (physicallyNamedTarget proof body proofNames bodyNames).names := rfl

/-- Explicit sharing observation, applied ONLY after the independent physical
cut formula above.  It forgets the copy bit, not boundaries or native proofs. -/
def forgetCopyBirth : PhysicalOrigin Origin → (Fin 3 ⊕ (Origin ⊕ Origin))
  | .inl root => .inl root
  | .inr (.inl (_, name)) => .inr (.inl name)
  | .inr (.inr name) => .inr (.inr name)

def sharingNameObservation {G : Hypersequent sigma} (tree : CKTree sigma Data G)
    (names : tree.OriginNames (PhysicalOrigin Origin)) : List (Fin 3 ⊕ (Origin ⊕ Origin)) :=
  (tree.originList names).map forgetCopyBirth

/-- The disjoint physical birth sets become the same ordered name observation
after explicitly forgetting the copy bit.  No adequacy for a structural query
and no CK-stable sharing quotient is asserted by this equality. -/
theorem sharing_identifies_copy_names (proof : PTree) (names : proof.OriginNames Origin) :
    sharingNameObservation proof (leftCopyNames proof names) =
      sharingNameObservation proof (rightCopyNames proof names) := by
  simp [sharingNameObservation, leftCopyNames, rightCopyNames,
    tagged_tree_origins, List.map_map, Function.comp_def, leftBirth, rightBirth,
    forgetCopyBirth]

/-- The exact full native material sum. This is explicitly an immediate
specialization of the existing composition theorem AFTER the new typed
logical-reduct filling bridge.  Origin annotations remain independent. -/
theorem reduct_material_expansion
    (B : MaterialBase sigma Data PrimitiveFragment.atoms)
    (proof : PTree) (body : QTree)
    (names : (target groundP groundQ).OriginNames Origin)
    (innerNames : (site : (targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).Site) →
      ((targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body) site).OriginNames Origin) :
    cutSum B
      ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).fill
        (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body))
      ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).fill_isOrdinary _)
      ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).plan.fillOriginNames
        (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body) names innerNames) =
    expansionSum B (targetInstallation groundP groundQ groundPOrdinary groundQOrdinary)
      (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body) names innerNames :=
  material_cutSum_composition B _ _ names innerNames

/-- The same exact finite sum directly on the independently specified logical
reduct, with the two uses labelled by disjoint physical birth namespaces. -/
theorem physically_named_reduct_material_expansion
    (B : MaterialBase sigma Data PrimitiveFragment.atoms)
    (proof : PTree) (body : QTree)
    (proofNames : proof.OriginNames Origin) (bodyNames : body.OriginNames Origin) :
    cutSum B (physicallyNamedTarget proof body proofNames bodyNames).native (by trivial)
      (physicallyNamedTarget proof body proofNames bodyNames).names =
    expansionSum B (targetInstallation groundP groundQ groundPOrdinary groundQOrdinary)
      (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body)
      targetSeedNames (physicalFillerNames proof body proofNames bodyNames) := by
  have expansion := reduct_material_expansion B proof body targetSeedNames
    (physicalFillerNames proof body proofNames bodyNames)
  rw [filling_preserves_physical_names] at expansion
  exact expansion

/-- Exact physical cuts BEFORE collection, including multiplicities under
any independently specified observation.  The RHS enumerates installation
choices, not completed reduct cuts. -/
theorem reduct_exact_observation_expansion
    {Basis : Type z} (proof : PTree) (body : QTree)
    (eligible : ExtensionalCKCut
      ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).fill
        (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body)) → Prop)
    [DecidablePred eligible]
    (observe : ExtensionalCKCut
      ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).fill
        (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body)) → Multiset Basis) :
    ((↑(ExtensionalCKCut.enumerate
      ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).fill
        (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body))
      ((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).fill_isOrdinary _)) :
      Multiset _).filter eligible).bind observe =
    ((↑((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).plan.enumerateExpansionChoices
      (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body)) :
      Multiset _).filter
        (fun choice => eligible
          (((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).installedPublicCutEquiv
            (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body)).symm choice))).bind
        (fun choice => observe
          (((targetInstallation groundP groundQ groundPOrdinary groundQOrdinary).installedPublicCutEquiv
            (targetFillers groundP groundQ groundPOrdinary groundQOrdinary proof proof body)).symm choice)) :=
  CKCut.publicEnumerate_filter_bind_expandedChoices _ _ eligible observe

/-- Scope correction: a Cut root is logical, never an exact material member.
Its ancestor cut exists natively, but cannot become a material spanning gain
merely because the installed payloads are pure. -/
theorem outer_enclosing_ineligible
    (B : MaterialBase sigma Data PrimitiveFragment.atoms)
    (left right : PTree) (body : QTree) :
    ¬ (physicalCut left right body (.inl PUnit.unit)).plan.DetachedInBase B := by
  intro pure
  have material := B.member_material (pure (.inl PUnit.unit)).1
  change OccurrenceKind.logical = OccurrenceKind.material at material
  cases material

theorem inner_enclosing_ineligible
    (B : MaterialBase sigma Data PrimitiveFragment.atoms)
    (left right : PTree) (body : QTree) (leftCut : CKBranchCut left) :
    ¬ (physicalCut left right body (.inr (leftCut, .inl PUnit.unit))).plan.DetachedInBase B := by
  intro pure
  have material := B.member_material (pure (.inl (.inr (.inl PUnit.unit)))).1
  change OccurrenceKind.logical = OccurrenceKind.material at material
  cases material

/-- All AND ONLY independent payload branch choices are materially eligible.
Each may select arbitrary internal roots, not just the whole payload. -/
theorem independent_material_iff
    (B : MaterialBase sigma Data PrimitiveFragment.atoms)
    (left right : PTree) (body : QTree)
    (leftCut : CKBranchCut left) (rightCut : CKBranchCut right) (bodyCut : CKBranchCut body) :
    (physicalCut left right body (.inr (leftCut, .inr (rightCut, bodyCut)))).plan.DetachedInBase B ↔
      leftCut.DetachedInBase B ∧ rightCut.DetachedInBase B ∧ bodyCut.DetachedInBase B := by
  constructor
  · intro pure
    exact ⟨fun site => pure (.inl (.inl site)),
      fun site => pure (.inl (.inr (.inl (.inl site)))),
      fun site => pure (.inl (.inr (.inl (.inr (.inl site)))))⟩
  · rintro ⟨leftPure, rightPure, bodyPure⟩ site
    cases site with
    | inr impossible => nomatch impossible
    | inl site =>
      cases site with
      | inl site => exact leftPure site
      | inr site =>
        cases site with
        | inr impossible => nomatch impossible
        | inl site =>
          cases site with
          | inl site => exact rightPure site
          | inr site =>
            cases site with
            | inl site => exact bodyPure site
            | inr impossible => nomatch impossible

/-- The full positive cut space is classified first, then material filtering
removes enclosing logical roots. This is not a lawful restriction of CK cuts
or an assertion that material cuts alone form a Hopf algebra. -/
theorem material_cut_coverage
    (B : MaterialBase sigma Data PrimitiveFragment.atoms)
    (left right : PTree) (body : QTree)
    (cut : CKCut (independentTarget left right body))
    (pure : cut.plan.DetachedInBase B) :
    ∃ leftCut : CKBranchCut left, ∃ rightCut : CKBranchCut right, ∃ bodyCut : CKBranchCut body,
      cut = physicalCut left right body (.inr (leftCut, .inr (rightCut, bodyCut))) ∧
        leftCut.DetachedInBase B ∧ rightCut.DetachedInBase B ∧ bodyCut.DetachedInBase B := by
  have reconstruct := physicalCut_physicalChoices left right body cut
  cases classified : physicalChoices left right body cut with
  | inl unit =>
      cases unit
      rw [classified] at reconstruct
      exact False.elim (outer_enclosing_ineligible B left right body (reconstruct.symm ▸ pure))
  | inr pair =>
      rcases pair with ⟨leftCut, inner⟩
      cases inner with
      | inl unit =>
          cases unit
          rw [classified] at reconstruct
          exact False.elim
            (inner_enclosing_ineligible B left right body leftCut (reconstruct.symm ▸ pure))
      | inr pair =>
          rcases pair with ⟨rightCut, bodyCut⟩
          rw [classified] at reconstruct
          exact ⟨leftCut, rightCut, bodyCut, reconstruct.symm,
            (independent_material_iff B left right body leftCut rightCut bodyCut).mp
              (reconstruct.symm ▸ pure)⟩

/-! Small kernel regressions use literal constructor plans, never cut
enumeration or a finite search.  The selected leaves are genuine INTERNAL
vertices of both physical copies of the same unary P module. -/

def regressionPayload : PTree := payloadUnaryP groundP

def regressionEmptyP : CKBranchCut regressionPayload :=
  .descend (.ordinary payloadUnaryPOccurrence _
    (.cons _ _ (.descend (.ordinary groundPOccurrence .nil .nil)) .nil))

def regressionInternalP : CKBranchCut regressionPayload :=
  .descend (.ordinary payloadUnaryPOccurrence _
    (.cons _ _ (.detach (by trivial)) .nil))

def regressionEmptyQ : CKBranchCut groundQ :=
  .descend (.ordinary groundQOccurrence .nil .nil)

def regressionLeft : CKCut (target regressionPayload groundQ) :=
  physicalCut regressionPayload regressionPayload groundQ
    (.inr (regressionInternalP, .inr (regressionEmptyP, regressionEmptyQ)))

def regressionRight : CKCut (target regressionPayload groundQ) :=
  physicalCut regressionPayload regressionPayload groundQ
    (.inr (regressionEmptyP, .inr (regressionInternalP, regressionEmptyQ)))

def regressionBoth : CKCut (target regressionPayload groundQ) :=
  physicalCut regressionPayload regressionPayload groundQ
    (.inr (regressionInternalP, .inr (regressionInternalP, regressionEmptyQ)))

def regressionOuterEnclosing : CKCut (target regressionPayload groundQ) :=
  physicalCut regressionPayload regressionPayload groundQ (.inl PUnit.unit)

def regressionInnerEnclosing : CKCut (target regressionPayload groundQ) :=
  physicalCut regressionPayload regressionPayload groundQ
    (.inr (regressionEmptyP, .inl PUnit.unit))

theorem regression_admitted :
    LocallyAdmittedTree presentation (target regressionPayload groundQ) := by
  apply target_admitted
  · exact ⟨by simp [presentation], ⟨by simp [presentation], trivial⟩, trivial⟩
  · exact ⟨by simp [presentation], trivial⟩

theorem regression_left_only :
    regressionLeft.orderedAddresses = [[0, 0, 0]] ∧
      regressionLeft.remainder =
        independentTarget (payloadUnaryP (.interface PBoundary)) regressionPayload groundQ :=
  ⟨rfl, rfl⟩

theorem regression_right_only :
    regressionRight.orderedAddresses = [[0, 1, 0, 0]] ∧
      regressionRight.remainder =
        independentTarget regressionPayload (payloadUnaryP (.interface PBoundary)) groundQ :=
  ⟨rfl, rfl⟩

theorem regression_both_copies :
    regressionBoth.orderedAddresses = [[0, 0, 0], [0, 1, 0, 0]] ∧
      regressionBoth.remainder = independentTarget
        (payloadUnaryP (.interface PBoundary)) (payloadUnaryP (.interface PBoundary)) groundQ ∧
      regressionBoth.detachedTuple.map (fun entry => (entry.address, entry.boundary)) =
        [([0, 0, 0], PBoundary), ([0, 1, 0, 0], PBoundary)] ∧
      regressionBoth.detachedForest.card = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Enclosing selection keeps the FULL installed outer subtree as its factor;
there are no left/right internal alternatives beneath this selected vertex. -/
theorem regression_outer_enclosing :
    regressionOuterEnclosing.orderedAddresses = [[0]] ∧
      regressionOuterEnclosing.remainder = contractD (.interface duplicatedBoundary) ∧
      regressionOuterEnclosing.plan.detached (.inl PUnit.unit) =
        outerCut regressionPayload (innerCut regressionPayload groundQ) :=
  ⟨rfl, rfl, rfl⟩

theorem regression_inner_enclosing :
    regressionInnerEnclosing.orderedAddresses = [[0, 1]] ∧
      regressionInnerEnclosing.remainder =
        contractD (outerCut regressionPayload (.interface middleBoundary)) ∧
      regressionInnerEnclosing.plan.detached (.inl (.inr (.inl PUnit.unit))) =
        innerCut regressionPayload groundQ :=
  ⟨rfl, rfl, rfl⟩

def regressionPayloadNames : regressionPayload.OriginNames Nat :=
  (7, ((8, PUnit.unit), PUnit.unit))
def regressionBodyNames : groundQ.OriginNames Nat := (9, PUnit.unit)

/-- Collection retains two factors with disjoint physical births although
their native decorated proof trees are structurally equal. -/
theorem regression_both_births :
    (regressionBoth.originForest
      (physicallyNamedTarget regressionPayload groundQ
        regressionPayloadNames regressionBodyNames).names).map OriginComponent.rootOrigin =
      ({leftBirth 8, rightBirth 8} : Multiset (PhysicalOrigin Nat)) := rfl

theorem regression_both_native_refill :
    regressionBoth.fill regressionBoth.plan.detached = target regressionPayload groundQ :=
  regressionBoth.fill_detached_reconstructs

end Potkin.Research.StructuralCutExpansion

#print axioms Potkin.Research.StructuralCutExpansion.physicalCutEquiv
#print axioms Potkin.Research.StructuralCutExpansion.filling_is_independent_target
#print axioms Potkin.Research.StructuralCutExpansion.physicalCut_native_refill
#print axioms Potkin.Research.StructuralCutExpansion.reduct_material_expansion
#print axioms Potkin.Research.StructuralCutExpansion.physically_named_reduct_material_expansion
#print axioms Potkin.Research.StructuralCutExpansion.reduct_exact_observation_expansion
#print axioms Potkin.Research.StructuralCutExpansion.material_cut_coverage
#print axioms Potkin.Research.StructuralCutExpansion.copied_origins_disjoint
#print axioms Potkin.Research.StructuralCutExpansion.filling_preserves_physical_names
#print axioms Potkin.Research.StructuralCutExpansion.sharing_identifies_copy_names
#print axioms Potkin.Research.StructuralCutExpansion.regression_left_only
#print axioms Potkin.Research.StructuralCutExpansion.regression_right_only
#print axioms Potkin.Research.StructuralCutExpansion.regression_both_copies
#print axioms Potkin.Research.StructuralCutExpansion.regression_outer_enclosing
#print axioms Potkin.Research.StructuralCutExpansion.regression_inner_enclosing
#print axioms Potkin.Research.StructuralCutExpansion.regression_both_births

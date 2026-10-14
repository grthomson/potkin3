import Potkin.OriginCutCoherence
import Potkin.Examples.Anonymous

/-!
# A genuine atomic identity/Cut fragment

This is an infinite fragment of the existing native `CKTree`, not a new
proof syntax.  Its only logical cell is atomic Gentzen Cut against atomic
identity.  The two closed providers are selected grounds; the selected
binary operation has two ordered closed atomic premise slots.  Every local
occurrence carries its exact whole boundary and supplied component incidence.

Logical equality is generated independently by the right identity-Cut
equation and typed context congruence.  It is intentionally not equality of
material observations: eliminating that cell beneath a material operation
can create a new composite material island.
-/

namespace Potkin.AtomicIdentityFragment

abbrev sigma := Examples.Anonymous.signature

inductive Data where
  | ground₀ | ground₁ | binary | identity | cut
deriving DecidableEq, Repr

abbrev atom : Formula sigma := Examples.Anonymous.formulaS
abbrev closedBoundary : Hypersequent sigma := Examples.Anonymous.GS
def identitySequent : Sequent sigma := ⟨{atom}, {atom}⟩
def identityBoundary : Hypersequent sigma := .singleton identitySequent

def closedShape : OccurrenceShape sigma := ⟨[], closedBoundary⟩
def binaryShape : OccurrenceShape sigma :=
  ⟨[closedBoundary, closedBoundary], closedBoundary⟩
def identityShape : OccurrenceShape sigma := ⟨[], identityBoundary⟩
def cutShape : OccurrenceShape sigma :=
  ⟨[closedBoundary, identityBoundary], closedBoundary⟩

private def singletonProfile (sequent : Sequent sigma) :
    ComponentProfile (Hypersequent.singleton sequent) :=
  ⟨[sequent], rfl⟩

def closedProfiles : OccurrenceProfiles closedShape where
  premise := fun i => Fin.elim0 i
  conclusion := singletonProfile Examples.Anonymous.S

def binaryProfiles : OccurrenceProfiles binaryShape where
  premise := fun i => Fin.cases (singletonProfile Examples.Anonymous.S)
    (fun j => Fin.cases (singletonProfile Examples.Anonymous.S)
      (fun impossible => Fin.elim0 impossible) j) i
  conclusion := singletonProfile Examples.Anonymous.S

def identityProfiles : OccurrenceProfiles identityShape where
  premise := fun i => Fin.elim0 i
  conclusion := singletonProfile identitySequent

def cutProfiles : OccurrenceProfiles cutShape where
  premise := fun i => Fin.cases (singletonProfile Examples.Anonymous.S)
    (fun j => Fin.cases (singletonProfile identitySequent)
      (fun impossible => Fin.elim0 impossible) j) i
  conclusion := singletonProfile Examples.Anonymous.S

def closedIncidence : ComponentIncidence closedShape := ⟨closedProfiles, ∅⟩
def identityIncidence : ComponentIncidence identityShape := ⟨identityProfiles, ∅⟩

def binaryIncidence : ComponentIncidence binaryShape where
  profiles := binaryProfiles
  edges := {⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩,
    ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩}

def cutIncidence : ComponentIncidence cutShape where
  profiles := cutProfiles
  edges := {⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩,
    ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩}

def ground₀ : LocalOccurrence sigma Data :=
  ⟨100, .material, closedShape, .ground₀, some closedIncidence⟩
def ground₁ : LocalOccurrence sigma Data :=
  ⟨101, .material, closedShape, .ground₁, some closedIncidence⟩
def materialBinary : LocalOccurrence sigma Data :=
  ⟨102, .material, binaryShape, .binary, some binaryIncidence⟩
def identityOccurrence : LocalOccurrence sigma Data :=
  ⟨103, .logical, identityShape, .identity, some identityIncidence⟩
def cutOccurrence : LocalOccurrence sigma Data :=
  ⟨104, .logical, cutShape, .cut, some cutIncidence⟩

/-- The logical cell has the literal atomic identity and Gentzen-Cut boundary,
not just the name or kind of one. Component edges are supplied separately. -/
theorem exact_logical_boundaries :
    identityOccurrence.shape.premises = [] ∧
    identityOccurrence.shape.conclusion =
      Hypersequent.singleton (⟨{atom}, {atom}⟩ : Sequent sigma) ∧
    cutOccurrence.shape.premises =
      [Hypersequent.singleton (⟨0, {atom}⟩ : Sequent sigma),
       Hypersequent.singleton (⟨{atom}, {atom}⟩ : Sequent sigma)] ∧
    cutOccurrence.shape.conclusion =
      Hypersequent.singleton (⟨0, {atom}⟩ : Sequent sigma) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem exact_logical_incidence :
    identityOccurrence.incidence = some identityIncidence ∧
    cutOccurrence.incidence = some cutIncidence ∧
    cutIncidence.edges.card = 2 := by
  exact ⟨rfl, rfl, by decide⟩

inductive MaterialMember : LocalOccurrence sigma Data → Prop where
  | ground₀ : MaterialMember ground₀
  | ground₁ : MaterialMember ground₁
  | binary : MaterialMember materialBinary

def base : MaterialBase sigma Data Examples.Anonymous.primitiveFragment where
  Member := MaterialMember
  member_material := by intro o h; cases h <;> rfl
  member_primitiveBoundary := by
    intro o h
    cases h with
    | ground₀ => exact ⟨fun i => Fin.elim0 i, Examples.Anonymous.GS_primitive⟩
    | ground₁ => exact ⟨fun i => Fin.elim0 i, Examples.Anonymous.GS_primitive⟩
    | binary =>
        exact ⟨fun i => Fin.cases Examples.Anonymous.GS_primitive
          (fun j => Fin.cases Examples.Anonymous.GS_primitive
            (fun impossible => Fin.elim0 impossible) j) i,
          Examples.Anonymous.GS_primitive⟩

def theory : ProofTheory sigma Data where
  primitive := Examples.Anonymous.primitiveFragment
  base := base
  rules := {
    logical := fun o => o = identityOccurrence ∨ o = cutOccurrence
    structural := fun _ => False }
  initial := fun _ => False

def presentation : EquippedPresentation theory where
  registry := [ground₀, ground₁, materialBinary, identityOccurrence, cutOccurrence]
  uniqueIds := by decide
  admitted := by
    intro o h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact .material .ground₀
    · exact .material .ground₁
    · exact .material .binary
    · exact .logical rfl (Or.inl rfl)
    · exact .logical rfl (Or.inr rfl)

abbrev Tree := CKTree sigma Data closedBoundary
abbrev NamedTree (Origin : Type) := OriginTree sigma Data Origin closedBoundary

def tree₀ : Tree := .ordinary ground₀ .nil
def tree₁ : Tree := .ordinary ground₁ .nil
def identityTree : CKTree sigma Data identityBoundary :=
  .ordinary identityOccurrence .nil
def binaryTree (left right : Tree) : Tree :=
  .ordinary materialBinary (.cons left (.cons right .nil))
def identityCut (tree : Tree) : Tree :=
  .ordinary cutOccurrence (.cons tree (.cons identityTree .nil))

def namedHole {Origin : Type} (name : Origin) : NamedTree Origin :=
  ⟨.interface closedBoundary, name⟩
def named₀ {Origin : Type} (name : Origin) : NamedTree Origin :=
  ⟨tree₀, (name, PUnit.unit)⟩
def named₁ {Origin : Type} (name : Origin) : NamedTree Origin :=
  ⟨tree₁, (name, PUnit.unit)⟩
def namedBinary {Origin : Type} (name : Origin)
    (left right : NamedTree Origin) : NamedTree Origin :=
  ⟨binaryTree left.native right.native,
    (name, (left.names, (right.names, PUnit.unit)))⟩
def namedIdentityCut {Origin : Type} (cutName axName : Origin)
    (tree : NamedTree Origin) : NamedTree Origin :=
  ⟨identityCut tree.native,
    (cutName, (tree.names, ((axName, PUnit.unit), PUnit.unit)))⟩

/-- Arbitrary depth and branching on the EXISTING native carrier. Inherited
holes have the same complete closed atomic interface. This excludes general
implication/tensor rules and nonidentity Cut continuations, not material arity. -/
inductive ClosedFragment : Tree → Prop where
  | hole : ClosedFragment (.interface closedBoundary)
  | ground₀ : ClosedFragment tree₀
  | ground₁ : ClosedFragment tree₁
  | binary {left right} : ClosedFragment left → ClosedFragment right →
      ClosedFragment (binaryTree left right)
  | identityCut {tree} : ClosedFragment tree → ClosedFragment (identityCut tree)

theorem ClosedFragment.locallyAdmitted {tree : Tree}
    (fragment : ClosedFragment tree) : LocallyAdmittedTree presentation tree := by
  induction fragment with
  | hole => trivial
  | ground₀ => exact ⟨by simp [presentation], trivial⟩
  | ground₁ => exact ⟨by simp [presentation], trivial⟩
  | binary _ _ hl hr => exact ⟨by simp [presentation], hl, hr, trivial⟩
  | identityCut _ ih =>
      exact ⟨by simp [presentation], ih,
        ⟨by simp [presentation], trivial⟩, trivial⟩

/-! ## Independent logical normalization -/

private def uncons {Origin : Type} {G : Hypersequent sigma}
    {Gs : List (Hypersequent sigma)} :
    OriginChildren sigma Data Origin (G :: Gs) →
      OriginTree sigma Data Origin G × OriginChildren sigma Data Origin Gs
  | ⟨.cons head tail, names⟩ => (⟨head, names.1⟩, ⟨tail, names.2⟩)

private theorem uncons_cons {Origin : Type} {G : Hypersequent sigma}
    {Gs : List (Hypersequent sigma)} (head : OriginTree sigma Data Origin G)
    (tail : OriginChildren sigma Data Origin Gs) :
    uncons (OriginChildren.cons head tail) = (head, tail) := by
  rcases head with ⟨head, headNames⟩
  rcases tail with ⟨tail, tailNames⟩
  rfl

private noncomputable def contractIdentityRoot {Origin : Type}
    (name : Origin) (children : CKChildren sigma Data
      [closedBoundary, identityBoundary]) (names : children.OriginNames Origin) :
      NamedTree Origin := by
  classical
  let namedChildren : OriginChildren sigma Data Origin
    [closedBoundary, identityBoundary] := ⟨children, names⟩
  exact if (uncons (uncons namedChildren).2).1.native = identityTree then
    (uncons namedChildren).1
  else ⟨.ordinary cutOccurrence children, (name, names)⟩

/-- A single exact identity-Cut contraction at the root. Unknown/nonidentity
continuations are not contracted. No origin, incidence or rule-name guess is
used to certify the cell. -/
noncomputable def normalizeRoot {Origin : Type}
    (o : LocalOccurrence sigma Data) (name : Origin)
    (children : OriginChildren sigma Data Origin o.shape.premises) :
    OriginTree sigma Data Origin o.shape.conclusion := by
  classical
  by_cases h : o = cutOccurrence
  · subst o
    exact contractIdentityRoot name children.native children.names
  · exact ⟨.ordinary o children.native, (name, children.names)⟩

mutual
noncomputable def normalizeTree {Origin : Type} : {G : Hypersequent sigma} →
    (tree : CKTree sigma Data G) → tree.OriginNames Origin →
    OriginTree sigma Data Origin G
  | _, .interface G, name => ⟨.interface G, name⟩
  | _, .ordinary o children, names =>
      normalizeRoot o names.1 (normalizeChildren children names.2)

noncomputable def normalizeChildren {Origin : Type} :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma Data Gs) →
    children.OriginNames Origin → OriginChildren sigma Data Origin Gs
  | _, .nil, _ => ⟨.nil, PUnit.unit⟩
  | _, .cons head tail, names =>
      OriginChildren.cons (normalizeTree head names.1)
        (normalizeChildren tail names.2)
end

noncomputable def observe {Origin : Type} {G : Hypersequent sigma}
    (tree : OriginTree sigma Data Origin G) : OriginTree sigma Data Origin G :=
  normalizeTree tree.native tree.names

private theorem binary_ne_cut : materialBinary ≠ cutOccurrence := by
  intro h
  have := congrArg LocalOccurrence.id h
  contradiction
private theorem ground₀_ne_cut : ground₀ ≠ cutOccurrence := by
  intro h
  have := congrArg LocalOccurrence.id h
  contradiction
private theorem ground₁_ne_cut : ground₁ ≠ cutOccurrence := by
  intro h
  have := congrArg LocalOccurrence.id h
  contradiction
private theorem identity_ne_cut : identityOccurrence ≠ cutOccurrence := by
  intro h
  have := congrArg LocalOccurrence.id h
  contradiction

private theorem normalize_identityTree {Origin : Type} (name : Origin) :
    normalizeTree identityTree (name, PUnit.unit) =
      (⟨identityTree, (name, PUnit.unit)⟩ :
        OriginTree sigma Data Origin identityBoundary) := by
  simp [identityTree, normalizeTree, normalizeChildren, normalizeRoot, identity_ne_cut]
  rfl

@[simp] theorem observe_hole {Origin : Type} (name : Origin) :
    observe (namedHole name) = namedHole name := rfl
@[simp] theorem observe_ground₀ {Origin : Type} (name : Origin) :
    observe (named₀ name) = named₀ name := by
  simp [observe, named₀, tree₀, normalizeTree, normalizeChildren,
    normalizeRoot, ground₀_ne_cut]
  rfl
@[simp] theorem observe_ground₁ {Origin : Type} (name : Origin) :
    observe (named₁ name) = named₁ name := by
  simp [observe, named₁, tree₁, normalizeTree, normalizeChildren,
    normalizeRoot, ground₁_ne_cut]
  rfl
@[simp] theorem observe_binary {Origin : Type} (name : Origin)
    (left right : NamedTree Origin) :
    observe (namedBinary name left right) =
      namedBinary name (observe left) (observe right) := by
  simp [observe, namedBinary, binaryTree, normalizeTree, normalizeChildren,
    normalizeRoot, binary_ne_cut, OriginChildren.cons]
  rfl
@[simp] theorem observe_identityCut {Origin : Type} (cutName axName : Origin)
    (tree : NamedTree Origin) :
    observe (namedIdentityCut cutName axName tree) = observe tree := by
  change normalizeRoot cutOccurrence cutName
    (OriginChildren.cons (normalizeTree tree.native tree.names)
      (OriginChildren.cons (normalizeTree identityTree (axName, PUnit.unit))
        ⟨.nil, PUnit.unit⟩)) = normalizeTree tree.native tree.names
  rw [normalize_identityTree]
  simp only [normalizeRoot, contractIdentityRoot]
  rw [uncons_cons]
  rw [uncons_cons]
  simp

/-- Ordinary equality generated by the actual identity-Cut equation and
ordered native material/context congruence. The rule list is independent of
all CK observations. Primitive origins and typed holes are rigid. -/
inductive LogicalEq {Origin : Type} : NamedTree Origin → NamedTree Origin → Prop where
  | refl (tree) : LogicalEq tree tree
  | symm {t u} : LogicalEq t u → LogicalEq u t
  | trans {t u v} : LogicalEq t u → LogicalEq u v → LogicalEq t v
  | identityCut (cutName axName : Origin) (tree) :
      LogicalEq (namedIdentityCut cutName axName tree) tree
  | binary {l l' r r'} (name : Origin) : LogicalEq l l' → LogicalEq r r' →
      LogicalEq (namedBinary name l r) (namedBinary name l' r')
  | underIdentity {t u} (cutName axName : Origin) : LogicalEq t u →
      LogicalEq (namedIdentityCut cutName axName t)
        (namedIdentityCut cutName axName u)

theorem LogicalEq.observe_eq {Origin : Type} {t u : NamedTree Origin}
    (equal : LogicalEq t u) : observe t = observe u := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | identityCut => simp
  | binary _ _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | underIdentity _ _ _ ih => simpa using ih

theorem generated_normalization {Origin : Type} {tree : Tree}
    (fragment : ClosedFragment tree) (names : tree.OriginNames Origin) :
    LogicalEq (⟨tree, names⟩ : NamedTree Origin)
      (observe (⟨tree, names⟩ : NamedTree Origin)) := by
  induction fragment with
  | hole => exact .refl _
  | ground₀ =>
      rcases names with ⟨name, nilEvidence⟩
      cases nilEvidence
      change LogicalEq (named₀ name) (observe (named₀ name))
      rw [observe_ground₀]
      exact .refl _
  | ground₁ =>
      rcases names with ⟨name, nilEvidence⟩
      cases nilEvidence
      change LogicalEq (named₁ name) (observe (named₁ name))
      rw [observe_ground₁]
      exact .refl _
  | binary hl hr ihl ihr =>
      rcases names with ⟨name, nl, nr, nilEvidence⟩
      cases nilEvidence
      change LogicalEq (namedBinary name ⟨_, nl⟩ ⟨_, nr⟩)
        (observe (namedBinary name ⟨_, nl⟩ ⟨_, nr⟩))
      rw [observe_binary]
      exact LogicalEq.binary name (ihl nl) (ihr nr)
  | identityCut h ih =>
      rcases names with ⟨cutName, nt, ⟨axName, axUnit⟩, nilEvidence⟩
      cases nilEvidence
      cases axUnit
      change LogicalEq (namedIdentityCut cutName axName ⟨_, nt⟩)
        (observe (namedIdentityCut cutName axName ⟨_, nt⟩))
      rw [observe_identityCut]
      exact LogicalEq.trans (LogicalEq.identityCut cutName axName ⟨_, nt⟩) (ih nt)

/-- A complete independently instantiated normalization/equality theorem for
the stated infinite identity-Cut fragment. -/
theorem logicalEq_iff_observe_eq {Origin : Type} {t u : NamedTree Origin}
    (ht : ClosedFragment t.native) (hu : ClosedFragment u.native) :
    LogicalEq t u ↔ observe t = observe u := by
  constructor
  · exact LogicalEq.observe_eq
  · intro h
    have left := generated_normalization ht t.names
    have right := generated_normalization hu u.names
    exact left.trans (by rw [h]; exact right.symm)

/-! ## Native typed filling and coherent origin renaming -/

/-- The existing native named-vacancy decoder serves as partial filling.
This operation itself is not arbitrary-input validation or private checked
node construction; admitted extraction/filling retains its existing gates. -/
noncomputable def fillNamed {Origin : Type}
    (forest : OriginForest sigma Data Origin) (tree : NamedTree Origin) :
    NamedTree Origin := OriginTree.decode forest tree.native tree.names

@[simp] theorem fillNamed_binary {Origin : Type}
    (forest : OriginForest sigma Data Origin) (name : Origin)
    (left right : NamedTree Origin) :
    fillNamed forest (namedBinary name left right) =
      namedBinary name (fillNamed forest left) (fillNamed forest right) := rfl

@[simp] theorem fillNamed_identityCut {Origin : Type}
    (forest : OriginForest sigma Data Origin) (cutName axName : Origin)
    (tree : NamedTree Origin) :
    fillNamed forest (namedIdentityCut cutName axName tree) =
      namedIdentityCut cutName axName (fillNamed forest tree) := rfl

theorem LogicalEq.fillNamed {Origin : Type} {t u : NamedTree Origin}
    (equal : LogicalEq t u) (forest : OriginForest sigma Data Origin) :
    LogicalEq (fillNamed forest t) (fillNamed forest u) := by
  induction equal with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | identityCut cutName axName tree =>
      simpa only [fillNamed_identityCut] using
        LogicalEq.identityCut cutName axName
          (AtomicIdentityFragment.fillNamed forest tree)
  | binary name _ _ ih₁ ih₂ =>
      simpa only [fillNamed_binary] using LogicalEq.binary name ih₁ ih₂
  | underIdentity cutName axName _ ih =>
      simpa only [fillNamed_identityCut] using
        LogicalEq.underIdentity cutName axName ih

mutual
def renameNames {Origin Origin' : Type} (f : Origin → Origin') :
    {G : Hypersequent sigma} → (tree : CKTree sigma Data G) →
    tree.OriginNames Origin → tree.OriginNames Origin'
  | _, .interface _, name => f name
  | _, .ordinary _ children, names =>
      (f names.1, renameChildNames f children names.2)

def renameChildNames {Origin Origin' : Type} (f : Origin → Origin') :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma Data Gs) →
    children.OriginNames Origin → children.OriginNames Origin'
  | _, .nil, _ => PUnit.unit
  | _, .cons head tail, names =>
      (renameNames f head names.1, renameChildNames f tail names.2)
end

def rename {Origin Origin' : Type} (f : Origin → Origin')
    (tree : NamedTree Origin) : NamedTree Origin' :=
  ⟨tree.native, renameNames f tree.native tree.names⟩

@[simp] theorem rename_native {Origin Origin' : Type} (f : Origin → Origin')
    (tree : NamedTree Origin) : (rename f tree).native = tree.native := rfl
@[simp] theorem rename_hole {Origin Origin' : Type} (f : Origin → Origin')
    (name : Origin) : rename f (namedHole name) = namedHole (f name) := rfl
@[simp] theorem rename_ground₀ {Origin Origin' : Type} (f : Origin → Origin')
    (name : Origin) : rename f (named₀ name) = named₀ (f name) := rfl
@[simp] theorem rename_ground₁ {Origin Origin' : Type} (f : Origin → Origin')
    (name : Origin) : rename f (named₁ name) = named₁ (f name) := rfl
@[simp] theorem rename_binary {Origin Origin' : Type} (f : Origin → Origin')
    (name : Origin) (left right : NamedTree Origin) :
    rename f (namedBinary name left right) =
      namedBinary (f name) (rename f left) (rename f right) := rfl
@[simp] theorem rename_identityCut {Origin Origin' : Type} (f : Origin → Origin')
    (cutName axName : Origin) (tree : NamedTree Origin) :
    rename f (namedIdentityCut cutName axName tree) =
      namedIdentityCut (f cutName) (f axName) (rename f tree) := rfl

theorem LogicalEq.rename {Origin Origin' : Type} {t u : NamedTree Origin}
    (equal : LogicalEq t u) (f : Origin → Origin') :
    LogicalEq (rename f t) (rename f u) := by
  induction equal with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | identityCut cutName axName tree =>
      simpa only [rename_identityCut] using
        LogicalEq.identityCut (f cutName) (f axName)
          (AtomicIdentityFragment.rename f tree)
  | binary name _ _ ih₁ ih₂ =>
      simpa only [rename_binary] using LogicalEq.binary (f name) ih₁ ih₂
  | underIdentity cutName axName _ ih =>
      simpa only [rename_identityCut] using
        LogicalEq.underIdentity (f cutName) (f axName) ih

theorem observe_rename {Origin Origin' : Type} (f : Origin → Origin')
    {tree : Tree} (fragment : ClosedFragment tree)
    (names : tree.OriginNames Origin) :
    observe (rename f (⟨tree, names⟩ : NamedTree Origin)) =
      rename f (observe (⟨tree, names⟩ : NamedTree Origin)) := by
  induction fragment with
  | hole => rfl
  | ground₀ =>
      rcases names with ⟨name, nilEvidence⟩
      cases nilEvidence
      change observe (rename f (named₀ name)) = rename f (observe (named₀ name))
      simp
  | ground₁ =>
      rcases names with ⟨name, nilEvidence⟩
      cases nilEvidence
      change observe (rename f (named₁ name)) = rename f (observe (named₁ name))
      simp
  | binary hl hr ihl ihr =>
      rcases names with ⟨name, nl, nr, nilEvidence⟩
      cases nilEvidence
      change observe (rename f (namedBinary name ⟨_, nl⟩ ⟨_, nr⟩)) =
        rename f (observe (namedBinary name ⟨_, nl⟩ ⟨_, nr⟩))
      simp only [rename_binary, observe_binary]
      rw [ihl nl, ihr nr]
  | identityCut h ih =>
      rcases names with ⟨cutName, nt, ⟨axName, axUnit⟩, nilEvidence⟩
      cases nilEvidence
      cases axUnit
      change observe (rename f (namedIdentityCut cutName axName ⟨_, nt⟩)) =
        rename f (observe (namedIdentityCut cutName axName ⟨_, nt⟩))
      simp only [rename_identityCut, observe_identityCut]
      exact ih nt

/-- Degree zero must not be used to infer raw purity from logical
normalization: a bare inherited vacancy and its identity detour observe
identically, although only the former is vacuously pure. -/
theorem inherited_hole_purity_obstruction {Origin : Type}
    (name cutName axName : Origin) :
    observe (namedIdentityCut cutName axName (namedHole name)) = namedHole name ∧
    (namedHole name).native.AllVerticesMaterial ∧
    ¬ (namedIdentityCut cutName axName (namedHole name)).native.AllVerticesMaterial := by
  refine ⟨by simp, trivial, ?_⟩
  intro pure
  have impossible : OccurrenceKind.logical = .material := pure.1
  cases impossible

/-! ## Exact checked unsafe fusion -/

def raw₀ : RawDerivation sigma := .node ground₀.id .nil
def raw₁ : RawDerivation sigma := .node ground₁.id .nil
def rawIdentity : RawDerivation sigma := .node identityOccurrence.id .nil
def rawIdentityCut (raw : RawDerivation sigma) : RawDerivation sigma :=
  .node cutOccurrence.id (.cons raw (.cons rawIdentity .nil))
def rawBinary (left right : RawDerivation sigma) : RawDerivation sigma :=
  .node materialBinary.id (.cons left (.cons right .nil))

def rawFused : RawDerivation sigma := rawBinary raw₀ raw₁
def rawSeparated : RawDerivation sigma := rawBinary (rawIdentityCut raw₀) raw₁

theorem rawFused_succeeds : CheckResult.Succeeded
    (presentation.checkAt closedBoundary rawFused) := by decide
theorem rawSeparated_succeeds : CheckResult.Succeeded
    (presentation.checkAt closedBoundary rawSeparated) := by decide
def checkedFused : CheckedDerivation presentation closedBoundary :=
  CheckResult.get rawFused_succeeds
def checkedSeparated : CheckedDerivation presentation closedBoundary :=
  CheckResult.get rawSeparated_succeeds

theorem checkedFused_literal : checkedFused.realize = binaryTree tree₀ tree₁ := rfl
theorem checkedSeparated_literal :
    checkedSeparated.realize = binaryTree (identityCut tree₀) tree₁ := rfl

def fused : NamedTree Nat := namedBinary 0 (named₀ 1) (named₁ 2)
def separated : NamedTree Nat :=
  namedBinary 0 (namedIdentityCut 3 4 (named₀ 1)) (named₁ 2)

theorem fused_checked : fused.native = checkedFused.realize := rfl
theorem separated_checked : separated.native = checkedSeparated.realize := rfl
theorem fused_fresh : fused.Fresh := by
  change ([0, 1, 2] : List Nat).Nodup
  decide
theorem separated_fresh : separated.Fresh := by
  change ([0, 3, 1, 4, 2] : List Nat).Nodup
  decide

theorem actual_logical_fusion : LogicalEq separated fused :=
  .binary 0 (.identityCut 3 4 (named₀ 1)) (.refl (named₁ 2))
theorem ordinary_observer_fusion : observe separated = observe fused :=
  actual_logical_fusion.observe_eq

/-- Full ordinary identity-Cut normalization can create a composite material
coefficient. It is therefore not an equality of the sparse material records. -/
theorem unsafe_fusion_maximal_islands :
    fused.native.AllVerticesMaterial ∧
    ¬ separated.native.AllVerticesMaterial ∧
    fused.native.maximalMaterialAddresses = [[]] ∧
    separated.native.maximalMaterialAddresses = [[0, 0], [1]] := by
  decide

def separatedMaximalCut : CKCut separated.native :=
  separated.native.maximalMaterialCut (by trivial)
    unsafe_fusion_maximal_islands.2.1

theorem unsafe_fusion_material_degrees :
    fused.native.degree = 3 ∧ separatedMaximalCut.detachedDegreeSum = 2 := by
  decide

theorem no_fabricated_root_cut :
    ¬ ∃ cut : ValidAddressCut fused.native, cut.addresses = {[]} :=
  fused.native.root_singleton_not_validAddressCut

end Potkin.AtomicIdentityFragment

#print axioms Potkin.AtomicIdentityFragment.logicalEq_iff_observe_eq
#print axioms Potkin.AtomicIdentityFragment.LogicalEq.fillNamed
#print axioms Potkin.AtomicIdentityFragment.LogicalEq.rename
#print axioms Potkin.AtomicIdentityFragment.observe_rename
#print axioms Potkin.AtomicIdentityFragment.inherited_hole_purity_obstruction
#print axioms Potkin.AtomicIdentityFragment.actual_logical_fusion
#print axioms Potkin.AtomicIdentityFragment.unsafe_fusion_maximal_islands

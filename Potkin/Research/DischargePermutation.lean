import Potkin.Research.OpenDischargeSummary
import Potkin.Research.NativeDischargeReplacement
import Potkin.AllHoleFilling
import Potkin.CompleteQuotation

/-!
# The open implication-right / `Sys(com)` bottom permutation

The system instance keeps its stable bottom UID while its exact registered
occurrence (including its common sequent) changes.  Thus both future fillings
refer to the same bottom, without holewise renaming or an implicit snapshot
cast.  The only formula operation in the concrete signature is implication.
All proof objects below are the existing boundary-indexed native `CKTree`.

The permutation itself and its subject-reduction antecedent are established
mathematics (Aschieri--Ciabattoni--Genco, arXiv:1607.05120, Figure 1).  This
module supplies the native, unfinished-derivation instantiation; it does not
claim a translation to that paper's term calculus.
-/

namespace Potkin.Research.DischargePermutation

open OpenDischarge

inductive Atom where | p | q deriving DecidableEq, Repr
inductive Op : Nat → Type where | imp : Op 2
def sigma : Signature := ⟨Atom, Op⟩

/-- Decidable equality directly on the native formula constructor. -/
def formulaDecidableEq (A B : Formula sigma) : Decidable (A = B) :=
  match A, B with
  | .atom a, .atom b =>
      if h : (show Atom from a) = (show Atom from b) then
        isTrue (by cases h; rfl)
      else isFalse (by intro hEq; cases hEq; exact h rfl)
  | .atom _, .app _ _ => isFalse (by intro h; cases h)
  | .app _ _, .atom _ => isFalse (by intro h; cases h)
  | .app .imp args, .app .imp otherArgs =>
      match formulaDecidableEq (args 0) (otherArgs 0) with
      | isFalse h => isFalse (by
          intro hEq
          have hargs : args = otherArgs := by cases hEq; rfl
          exact h (congrFun hargs 0))
      | isTrue h0 =>
          match formulaDecidableEq (args 1) (otherArgs 1) with
          | isFalse h => isFalse (by
              intro hEq
              have hargs : args = otherArgs := by cases hEq; rfl
              exact h (congrFun hargs 1))
          | isTrue h1 => isTrue (by
              have hargs : args = otherArgs := by
                funext i
                rcases i with ⟨i, hi⟩
                cases i with
                | zero => exact h0
                | succ i =>
                    cases i with
                    | zero => exact h1
                    | succ i => omega
              cases hargs
              rfl)

instance : DecidableEq (Formula sigma) := formulaDecidableEq

def p : Formula sigma := .atom .p
def q : Formula sigma := .atom .q
def implies (A B : Formula sigma) : Formula sigma := .app2 .imp A B
def Imp (A B C : Formula sigma) : Prop := C = implies A B

def parameters : DependencyInterface.Parameters sigma := ⟨{p}, {q}⟩
def bottomUID : Nat := 42
def identityS : Sequent sigma := ⟨{p}, {p}⟩
def doubledS : Sequent sigma := ⟨{p} + {p}, {p}⟩
def commonS : Sequent sigma := ⟨{p} + {q}, {p}⟩
def twiceQS : Sequent sigma := ⟨{q} + ({q} + {p}), {p}⟩
def beforeContractS : Sequent sigma := ⟨{p} + {p} + {q}, {p}⟩
def targetS : Sequent sigma := ⟨{p}, {implies q p}⟩
def GI := Hypersequent.singleton identityS
def GD := Hypersequent.singleton doubledS
def GS := Hypersequent.singleton commonS
def GQQ := Hypersequent.singleton twiceQS
def GPPQ := Hypersequent.singleton beforeContractS
def GT := Hypersequent.singleton targetS

inductive Label where
  | identity | weakenP | weakenQ | weakenQAgain | topLeft | topRight
  | contractP | bottomSource | implication | bottomTarget
  deriving DecidableEq, Repr

def labels : List Label :=
  [.identity, .weakenP, .weakenQ, .weakenQAgain, .topLeft, .topRight,
   .contractP, .bottomSource, .implication, .bottomTarget]
def id : Label → Nat
  | .identity => 700 | .weakenP => 701 | .weakenQ => 702
  | .weakenQAgain => 703 | .topLeft => 704 | .topRight => 705
  | .contractP => 706 | .bottomSource => 707 | .implication => 708
  | .bottomTarget => 709

private def profile (S : Sequent sigma) : ComponentProfile (.singleton S) := ⟨[S], rfl⟩
private def nullaryIncidence (S : Sequent sigma) :
    ComponentIncidence (⟨[], .singleton S⟩ : OccurrenceShape sigma) :=
  ⟨⟨fun i => Fin.elim0 i, profile S⟩, ∅⟩
private def unaryIncidence (I O : Sequent sigma) :
    ComponentIncidence (⟨[.singleton I], .singleton O⟩ : OccurrenceShape sigma) where
  profiles := ⟨fun i => Fin.cases (profile I) (fun j => Fin.elim0 j) i, profile O⟩
  edges := {⟨⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩,
    ⟨0, by change 0 < 1; decide⟩⟩}
private def binaryIncidence (S : Sequent sigma) :
    ComponentIncidence (⟨[.singleton S, .singleton S], .singleton S⟩ : OccurrenceShape sigma) where
  profiles := ⟨fun i => Fin.cases (profile S)
    (fun j => Fin.cases (profile S) (fun k => Fin.elim0 k) j) i, profile S⟩
  edges := {⟨⟨0, by change 0 < 2; decide⟩, ⟨0, by change 0 < 1; decide⟩,
      ⟨0, by change 0 < 1; decide⟩⟩,
    ⟨⟨1, by change 1 < 2; decide⟩, ⟨0, by change 0 < 1; decide⟩,
      ⟨0, by change 0 < 1; decide⟩⟩}

def unary (label : Label) (kind : OccurrenceKind) (tag : Data sigma)
    (I O : Sequent sigma) : LocalOccurrence sigma (Data sigma) :=
  ⟨id label, kind, ⟨[.singleton I], .singleton O⟩, tag, some (unaryIncidence I O)⟩
def occurrence : Label → LocalOccurrence sigma (Data sigma)
  | .identity => ⟨id .identity, .logical, ⟨[], GI⟩, .identity p,
      some (nullaryIncidence identityS)⟩
  | .weakenP => unary .weakenP .structural (.weakening p {p} {p}) identityS doubledS
  | .weakenQ => unary .weakenQ .structural (.weakening q {p} {p}) identityS commonS
  | .weakenQAgain => unary .weakenQAgain .structural
      (.weakening q ({q} + {p}) {p}) commonS twiceQS
  | .topLeft => unary .topLeft .structural
      (.top ⟨0, by decide⟩ parameters bottomUID {p} {p}) doubledS commonS
  | .topRight => unary .topRight .structural
      (.top ⟨1, by decide⟩ parameters bottomUID ({q} + {p}) {p}) twiceQS beforeContractS
  | .contractP => unary .contractP .structural
      (.contraction p {q} {p}) beforeContractS commonS
  | .bottomSource => ⟨id .bottomSource, .structural, ⟨[GS, GS], GS⟩,
      .bottom parameters bottomUID commonS, some (binaryIncidence commonS)⟩
  | .implication => unary .implication .logical
      (.implicationRight {p} q p (implies q p)) commonS targetS
  | .bottomTarget => ⟨id .bottomTarget, .structural, ⟨[GT, GT], GT⟩,
      .bottom parameters bottomUID targetS, some (binaryIncidence targetS)⟩

theorem exact_occurrence (label : Label) : ExactInstance Imp (occurrence label) := by
  cases label <;> simp [occurrence, unary, ExactInstance, Imp, identityS,
    doubledS, commonS, twiceQS, beforeContractS, targetS, GI, GS, GT,
    DependencyInterface.topInput, DependencyInterface.topOutput, parameters,
    Multiset.add_comm]
  all_goals
    apply congrArg Hypersequent.singleton
    apply Sequent.ext
    · exact (congrArg (Multiset.cons q) (Multiset.pair_comm q p)).trans
        (Multiset.cons_swap q p {q})
    · rfl

def registry := labels.map occurrence
def base : MaterialBase sigma (Data sigma) PrimitiveFragment.full where
  Member := fun _ => False
  member_material := fun h => False.elim h
  member_primitiveBoundary := fun h => False.elim h
def theory : ProofTheory sigma (Data sigma) where
  primitive := .full
  base := base
  rules := { logical := fun o => ExactInstance Imp o ∧ o.kind = .logical
             structural := fun o => ExactInstance Imp o ∧ o.kind = .structural }
  initial := fun _ => False
def presentation : EquippedPresentation theory where
  registry := registry
  uniqueIds := by decide
  admitted := by
    intro o h
    rcases List.mem_map.mp h with ⟨label, _, rfl⟩
    cases label <;>
      first | exact .logical rfl ⟨exact_occurrence _, rfl⟩
            | exact .structural rfl ⟨exact_occurrence _, rfl⟩

theorem registered (label : Label) : occurrence label ∈ registry := by
  apply List.mem_map.mpr
  refine ⟨label, ?_, rfl⟩
  cases label <;> simp [labels]

abbrev Tree := CKTree sigma (Data sigma)
def impTree (P : Tree GS) : Tree GT :=
  .ordinary (occurrence .implication) (.cons P .nil)
def bottomS (P Q : Tree GS) : Tree GS :=
  .ordinary (occurrence .bottomSource) (.cons P (.cons Q .nil))
def bottomT (P Q : Tree GT) : Tree GT :=
  .ordinary (occurrence .bottomTarget) (.cons P (.cons Q .nil))

/-- Forward literature orientation: one ordinary unary inference is duplicated,
but no premise/filling or system bottom is copied. -/
def source (P Q : Tree GS) : Tree GT := impTree (bottomS P Q)
def target (P Q : Tree GS) : Tree GT := bottomT (impTree P) (impTree Q)
def sourceShell : Tree GT := source (.interface GS) (.interface GS)
def targetShell : Tree GT := target (.interface GS) (.interface GS)

def sourceLeft : sourceShell.LeafOccurrence := .inl (.inl PUnit.unit)
def sourceRight : sourceShell.LeafOccurrence := .inl (.inr (.inl PUnit.unit))
def targetLeft : targetShell.LeafOccurrence := .inl (.inl PUnit.unit)
def targetRight : targetShell.LeafOccurrence := .inr (.inl (.inl PUnit.unit))

/-- A bijection of physical vacancies, not an identification by equal boundary. -/
def holeEquiv : sourceShell.LeafOccurrence ≃ targetShell.LeafOccurrence where
  toFun
    | .inl (.inl h) => .inl (.inl h)
    | .inl (.inr (.inl h)) => .inr (.inl (.inl h))
    | .inl (.inr (.inr h)) => nomatch h
    | .inr h => nomatch h
  invFun
    | .inl (.inl h) => .inl (.inl h)
    | .inl (.inr h) => nomatch h
    | .inr (.inl (.inl h)) => .inl (.inr (.inl h))
    | .inr (.inl (.inr h)) => nomatch h
    | .inr (.inr h) => nomatch h
  left_inv h := by
    rcases h with (h | h)
    · rcases h with (h | h)
      · rfl
      · rcases h with (h | h)
        · rfl
        · exact nomatch h
    · exact nomatch h
  right_inv h := by
    rcases h with (h | h)
    · rcases h with (h | h)
      · rfl
      · exact nomatch h
    · rcases h with (h | h)
      · rcases h with (h | h)
        · rfl
        · exact nomatch h
      · exact nomatch h

theorem hole_boundary (h : sourceShell.LeafOccurrence) :
    sourceShell.leafBoundary h = targetShell.leafBoundary (holeEquiv h) := by
  rcases h with (h | h)
  · rcases h with (h | h)
    · rfl
    · rcases h with (h | h)
      · rfl
      · exact nomatch h
  · exact nomatch h

theorem source_left_address : sourceShell.leafAddress sourceLeft = [0, 0] := rfl
theorem source_right_address : sourceShell.leafAddress sourceRight = [0, 1] := rfl
theorem target_left_address : targetShell.leafAddress targetLeft = [0, 0] := rfl
theorem target_right_address : targetShell.leafAddress targetRight = [1, 0] := rfl

def sourceAssignment (P Q : Tree GS) : sourceShell.LeafAssignment
  | .inl (.inl _) => P
  | .inl (.inr (.inl _)) => Q
  | .inl (.inr (.inr h)) => nomatch h
  | .inr h => nomatch h
def targetAssignment (P Q : Tree GS) : targetShell.LeafAssignment
  | .inl (.inl _) => P
  | .inl (.inr h) => nomatch h
  | .inr (.inl (.inl _)) => Q
  | .inr (.inl (.inr h)) => nomatch h
  | .inr (.inr h) => nomatch h

theorem source_fill (P Q : Tree GS) :
    sourceShell.fillAssignment (sourceAssignment P Q) = source P Q := rfl
theorem target_fill (P Q : Tree GS) :
    targetShell.fillAssignment (targetAssignment P Q) = target P Q := rfl

/-- Every arbitrary future filling of the two physical source holes is included. -/
theorem every_source_filling (F : sourceShell.LeafAssignment) :
    sourceShell.fillAssignment F = source (F sourceLeft) (F sourceRight) := rfl
theorem every_target_filling (F : targetShell.LeafAssignment) :
    targetShell.fillAssignment F = target (F targetLeft) (F targetRight) := rfl

/-- The actual address transport inside either payload.  The suffix is retained
literally, including repeated equal-looking occurrences. -/
def sourcePayloadAddress (i : Fin 2) (suffix : InternalAddress) : InternalAddress :=
  [0, i.val] ++ suffix
def targetPayloadAddress (i : Fin 2) (suffix : InternalAddress) : InternalAddress :=
  [i.val, 0] ++ suffix

theorem shell_branch_transport (i : Fin 2) (suffix : InternalAddress) :
    (∃ a, sourcePayloadAddress i suffix = [0] ++ [i.val] ++ a) ∧
    (∃ a, targetPayloadAddress i suffix = [] ++ [i.val] ++ a) := by
  exact ⟨⟨suffix, rfl⟩, ⟨0 :: suffix, rfl⟩⟩

/-- Exact correspondence of the available shell owner at every physical hole.
The common bottom sequent and the placement/copies of implication-right do
not enter this independent discharge condition. -/
theorem shell_exposure_transport (h : sourceShell.LeafOccurrence) (role : Fin 2) :
    (∃ suffix, sourceShell.leafAddress h = [0] ++ [role.val] ++ suffix) ↔
    (∃ suffix, targetShell.leafAddress (holeEquiv h) = [] ++ [role.val] ++ suffix) := by
  rcases h with (h | h)
  · rcases h with (h | h)
    · simp [sourceShell, source, impTree, bottomS, targetShell, target,
        bottomT, holeEquiv, CKTree.leafAddress, CKChildren.leafAddress,
        List.cons.injEq]
    · rcases h with (h | h)
      · simp [sourceShell, source, impTree, bottomS, targetShell, target,
          bottomT, holeEquiv, CKTree.leafAddress, CKChildren.leafAddress,
          InternalAddress.shiftHead, List.cons.injEq]
      · exact nomatch h
  · exact nomatch h

theorem source_exact_iff (P Q : Tree GS) :
    ExactTree Imp (source P Q) ↔ ExactTree Imp P ∧ ExactTree Imp Q := by
  simp [source, impTree, bottomS, ExactTree, ExactChildren, exact_occurrence]
theorem target_exact_iff (P Q : Tree GS) :
    ExactTree Imp (target P Q) ↔ ExactTree Imp P ∧ ExactTree Imp Q := by
  simp [target, impTree, bottomT, ExactTree, ExactChildren, exact_occurrence]
  rfl
theorem local_permutation (P Q : Tree GS) :
    ExactTree Imp (source P Q) ↔ ExactTree Imp (target P Q) :=
  (source_exact_iff P Q).trans (target_exact_iff P Q).symm

def shellGrant (address : InternalAddress) (rule : Nat) : Grant sigma :=
  ⟨bottomUID, address, rule, parameters⟩

/-- Resolution at the actual shell bottom, retaining its prescribed branch. -/
def ShellDemand (branch : Nat) (r : Requirement sigma) : Prop :=
  r.owner = bottomUID ∧ r.parameters = parameters ∧ r.role.val = branch

def PayloadLegal (branch : Nat) (e : Events sigma) : Prop :=
  ∀ r ∈ e.requirements,
    (∃ g ∈ e.grants, Compatible r g) ∨ ShellDemand branch r

def assembled (left right : Events sigma) (lp rp : InternalAddress)
    (root : Grant sigma) : Events sigma :=
  ⟨left.requirements.map (prefixRequirement lp) ++
      right.requirements.map (prefixRequirement rp),
   root :: (left.grants.map (prefixGrant lp) ++ right.grants.map (prefixGrant rp))⟩

theorem prefix_compatible (a : InternalAddress) (r : Requirement sigma)
    (g : Grant sigma) :
    Compatible (prefixRequirement a r) (prefixGrant a g) ↔ Compatible r g := by
  exact compatible_prefix a r g

/-- This is a semantic resolution lemma, not a polynomial/tree-shape observer.
The two payloads may be invalid, have nested bottoms, or name one another's
owners: the false cross-branch test detects those demands. -/
theorem assembled_legal_iff (left right : Events sigma) (lp rp : InternalAddress)
    (root : Grant sigma)
    (leftRoot : ∀ r, Compatible (prefixRequirement lp r) root ↔ ShellDemand 0 r)
    (rightRoot : ∀ r, Compatible (prefixRequirement rp r) root ↔ ShellDemand 1 r)
    (leftCross : ∀ (r : Requirement sigma) (g : Grant sigma),
      ¬ Compatible (prefixRequirement lp r) (prefixGrant rp g))
    (rightCross : ∀ (r : Requirement sigma) (g : Grant sigma),
      ¬ Compatible (prefixRequirement rp r) (prefixGrant lp g)) :
    LegalEvents (assembled left right lp rp root) [] ↔
      PayloadLegal 0 left ∧ PayloadLegal 1 right := by
  constructor
  · intro h
    constructor
    · intro r hr
      have present : prefixRequirement lp r ∈
          (assembled left right lp rp root).requirements := by
        exact List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
      rcases h _ present with ⟨g, hg, hc⟩
      have member : g = root ∨ g ∈ left.grants.map (prefixGrant lp) ∨
          g ∈ right.grants.map (prefixGrant rp) := by
        simpa [assembled, List.mem_cons, List.mem_append] using hg
      rcases member with rfl | hl | hr
      · exact Or.inr ((leftRoot r).mp hc)
      · rcases List.mem_map.mp hl with ⟨g, originalMember, rfl⟩
        exact Or.inl ⟨g, originalMember, (prefix_compatible lp r g).mp hc⟩
      · rcases List.mem_map.mp hr with ⟨g, _, rfl⟩
        exact False.elim (leftCross r g hc)
    · intro r hr
      have present : prefixRequirement rp r ∈
          (assembled left right lp rp root).requirements := by
        exact List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
      rcases h _ present with ⟨g, hg, hc⟩
      have member : g = root ∨ g ∈ left.grants.map (prefixGrant lp) ∨
          g ∈ right.grants.map (prefixGrant rp) := by
        simpa [assembled, List.mem_cons, List.mem_append] using hg
      rcases member with rfl | hl | hr
      · exact Or.inr ((rightRoot r).mp hc)
      · rcases List.mem_map.mp hl with ⟨g, _, rfl⟩
        exact False.elim (rightCross r g hc)
      · rcases List.mem_map.mp hr with ⟨g, originalMember, rfl⟩
        exact Or.inl ⟨g, originalMember, (prefix_compatible rp r g).mp hc⟩
  · rintro ⟨hl, hr⟩ r present
    rcases List.mem_append.mp present with present | present
    · rcases List.mem_map.mp present with ⟨r, originalPresent, rfl⟩
      rcases hl r originalPresent with own | shell
      · rcases own with ⟨g, hg, hc⟩
        refine ⟨prefixGrant lp g, ?_, (prefix_compatible lp r g).mpr hc⟩
        simp only [assembled, List.append_nil, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (List.mem_map.mpr ⟨g, hg, rfl⟩))
      · exact ⟨root, by simp [assembled], (leftRoot r).mpr shell⟩
    · rcases List.mem_map.mp present with ⟨r, originalPresent, rfl⟩
      rcases hr r originalPresent with own | shell
      · rcases own with ⟨g, hg, hc⟩
        refine ⟨prefixGrant rp g, ?_, (prefix_compatible rp r g).mpr hc⟩
        simp only [assembled, List.append_nil, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (List.mem_map.mpr ⟨g, hg, rfl⟩))
      · exact ⟨root, by simp [assembled], (rightRoot r).mpr shell⟩

theorem source_events (P Q : Tree GS) :
    events (source P Q) [] = assembled (events P []) (events Q [])
      [0, 0] [0, 1] (shellGrant [0] (id .bottomSource)) := by
  have hp := events_prefix P [0, 0] []
  have hq := events_prefix Q [0, 1] []
  simp only [List.append_nil] at hp hq
  simp [source, impTree, bottomS, events, childEvents, rootEvents,
    occurrence, unary, Events.append, assembled, shellGrant, hp, hq, prefixEvents]

theorem target_events (P Q : Tree GS) :
    events (target P Q) [] = assembled (events P []) (events Q [])
      [0, 0] [1, 0] (shellGrant [] (id .bottomTarget)) := by
  have hp := events_prefix P [0, 0] []
  have hq := events_prefix Q [1, 0] []
  simp only [List.append_nil] at hp hq
  simp [target, impTree, bottomT, events, childEvents, rootEvents,
    occurrence, unary, Events.append, assembled, shellGrant]
  constructor
  · exact congrArg₂ (fun (a b : List (Requirement sigma)) => a ++ b)
      (congrArg Events.requirements hp) (congrArg Events.requirements hq)
  · exact congrArg₂ (fun (a b : List (Grant sigma)) => a ++ b)
      (congrArg Events.grants hp) (congrArg Events.grants hq)

theorem source_discharge_iff (P Q : Tree GS) :
    LegalEvents (events (source P Q) []) [] ↔
      PayloadLegal 0 (events P []) ∧ PayloadLegal 1 (events Q []) := by
  rw [source_events]
  apply assembled_legal_iff
  · intro r
    simp [Compatible, prefixRequirement, shellGrant, ShellDemand, List.cons.injEq, eq_comm]
  · intro r
    simp [Compatible, prefixRequirement, shellGrant, ShellDemand, List.cons.injEq, eq_comm]
  · intro r g
    simp [Compatible, prefixRequirement, prefixGrant, List.cons.injEq]
  · intro r g
    simp [Compatible, prefixRequirement, prefixGrant, List.cons.injEq]

theorem target_discharge_iff (P Q : Tree GS) :
    LegalEvents (events (target P Q) []) [] ↔
      PayloadLegal 0 (events P []) ∧ PayloadLegal 1 (events Q []) := by
  rw [target_events]
  apply assembled_legal_iff
  · intro r
    simp [Compatible, prefixRequirement, shellGrant, ShellDemand, List.cons.injEq, eq_comm]
  · intro r
    simp [Compatible, prefixRequirement, shellGrant, ShellDemand, List.cons.injEq, eq_comm]
  · intro r g
    simp [Compatible, prefixRequirement, prefixGrant, List.cons.injEq]
  · intro r g
    simp [Compatible, prefixRequirement, prefixGrant, List.cons.injEq]

theorem same_owner_inventory (P Q : Tree GS) :
    (events (source P Q) []).grants.map Grant.uid =
      (events (target P Q) []).grants.map Grant.uid := by
  rw [source_events, target_events]
  simp [assembled, shellGrant, List.map_map, Function.comp_def, prefixGrant]

/-- Finite, fixed-owner interface agreement of the actual registered shells.
This is the hypothesis of the general reuse theorem, not a proof about a
particular future filler. The two physical holes move as recorded above. -/
private theorem source_shell_exposure :
    (directSummary Imp sourceShell []).exposure =
      (exposureRows [⟨[0, 0], GS⟩, ⟨[0, 1], GS⟩]
        [shellGrant [0] (id .bottomSource)] : Multiset (Exposure sigma)) := rfl

private theorem target_shell_exposure :
    (directSummary Imp targetShell []).exposure =
      (exposureRows [⟨[0, 0], GS⟩, ⟨[1, 0], GS⟩]
        [shellGrant [] (id .bottomTarget)] : Multiset (Exposure sigma)) := rfl

def implication_interface : FixedOwnerInterface Imp sourceShell targetShell := by
  refine ⟨holeEquiv, hole_boundary, rfl, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    have exactSource : ExactTree Imp sourceShell :=
      (source_exact_iff (.interface GS) (.interface GS)).mpr ⟨trivial, trivial⟩
    have exactTarget : ExactTree Imp targetShell :=
      (target_exact_iff (.interface GS) (.interface GS)).mpr ⟨trivial, trivial⟩
    change (ExactTree Imp sourceShell ∧ UniqueOwners (events sourceShell []) ∧
      InteriorLegal (events sourceShell [])) ↔
      (ExactTree Imp targetShell ∧ UniqueOwners (events targetShell []) ∧
        InteriorLegal (events targetShell []))
    simp only [exactSource, exactTarget, true_and]
    simp [sourceShell, targetShell, source, target, impTree, bottomS, bottomT,
      events, childEvents, rootEvents, occurrence, unary, Events.append,
      UniqueOwners, InteriorLegal]
  · intro hole
    rcases hole with (hole | hole)
    · rcases hole with (hole | hole)
      · cases hole
        change exposureAt (directSummary Imp sourceShell []) [0, 0] =
          exposureAt (directSummary Imp targetShell []) [0, 0]
        simp [exposureAt, source_shell_exposure, target_shell_exposure, eraseExposure,
          exposureRows, shellGrant, List.flatMap, List.map, List.filterMap, List.filter,
          List.cons.injEq]
      · rcases hole with (hole | hole)
        · cases hole
          change exposureAt (directSummary Imp sourceShell []) [0, 1] =
            exposureAt (directSummary Imp targetShell []) [1, 0]
          simp [exposureAt, source_shell_exposure, target_shell_exposure, eraseExposure,
            exposureRows, shellGrant, List.flatMap, List.map, List.filterMap, List.filter,
            List.cons.injEq]
        · exact nomatch hole
    · exact nomatch hole

/-- The normalization instance is now an application of generic finite-summary
replacement, including every native typed exterior and arbitrary future P,Q.
Both validity and every scope/owner-collision failure are reflected. -/
theorem implication_permutation_exterior (P Q : Tree GS)
    {G : Hypersequent sigma} {tree : Tree G} {address : InternalAddress}
    (context : CKTree.PunctureAt GT tree address) :
    Legal Imp (context.insert (source P Q)) [] [] ↔
      Legal Imp (context.insert (target P Q)) [] [] := by
  have matching (hole : sourceShell.LeafOccurrence) :
      HEq (sourceAssignment P Q hole) (targetAssignment P Q (holeEquiv hole)) := by
    rcases hole with (hole | hole)
    · rcases hole with (hole | hole)
      · rfl
      · rcases hole with (hole | hole)
        · rfl
        · exact nomatch hole
    · exact nomatch hole
  exact fixedOwner_replacement Imp implication_interface
    (sourceAssignment P Q) (targetAssignment P Q) matching context

theorem open_implication_permutation (P Q : Tree GS) :
    Legal Imp (source P Q) [] [] ↔ Legal Imp (target P Q) [] [] :=
  implication_permutation_exterior P Q
    (CKTree.PunctureAt.root : CKTree.PunctureAt GT (.interface GT) [])

mutual
/-- Preservation of any node-local forbidden-rule policy, in particular the
absence of logical Cut in an ambient registry where the shell rules are not
Cut.  This does not identify CK extraction with logical Cut. -/
def NodesSatisfy (allowed : LocalOccurrence sigma (Data sigma) → Prop) :
    {G : Hypersequent sigma} → Tree G → Prop
  | _, .interface _ => True
  | _, .ordinary o children => allowed o ∧ ChildrenSatisfy allowed children
def ChildrenSatisfy (allowed : LocalOccurrence sigma (Data sigma) → Prop) :
    {Gs : List (Hypersequent sigma)} → CKChildren sigma (Data sigma) Gs → Prop
  | _, .nil => True
  | _, .cons head tail => NodesSatisfy allowed head ∧ ChildrenSatisfy allowed tail
end

theorem forbidden_rule_preservation
    (allowed : LocalOccurrence sigma (Data sigma) → Prop)
    (hImp : allowed (occurrence .implication))
    (hSource : allowed (occurrence .bottomSource))
    (hTarget : allowed (occurrence .bottomTarget)) (P Q : Tree GS) :
    NodesSatisfy allowed (source P Q) ↔ NodesSatisfy allowed (target P Q) := by
  simp [source, target, impTree, bottomS, bottomT, NodesSatisfy,
    ChildrenSatisfy, hImp, hSource, hTarget]
  rfl

def identity : Tree GI := .ordinary (occurrence .identity) .nil
def leftFilling : Tree GS := .ordinary (occurrence .topLeft)
  (.cons (.ordinary (occurrence .weakenP) (.cons identity .nil)) .nil)
def rightFilling : Tree GS := .ordinary (occurrence .contractP)
  (.cons (.ordinary (occurrence .topRight)
    (.cons (.ordinary (occurrence .weakenQAgain)
      (.cons (.ordinary (occurrence .weakenQ) (.cons identity .nil)) .nil)) .nil)) .nil)

theorem left_registered : LocallyAdmittedTree presentation leftFilling := by
  simp [leftFilling, identity, LocallyAdmittedTree, LocallyAdmittedChildren,
    presentation, registered]
theorem right_registered : LocallyAdmittedTree presentation rightFilling := by
  simp [rightFilling, identity, LocallyAdmittedTree, LocallyAdmittedChildren,
    presentation, registered]

theorem source_registered (P Q : Tree GS)
    (hP : LocallyAdmittedTree presentation P)
    (hQ : LocallyAdmittedTree presentation Q) :
    LocallyAdmittedTree presentation (source P Q) := by
  exact ⟨registered .implication, ⟨registered .bottomSource, hP, hQ, trivial⟩, trivial⟩
theorem target_registered (P Q : Tree GS)
    (hP : LocallyAdmittedTree presentation P)
    (hQ : LocallyAdmittedTree presentation Q) :
    LocallyAdmittedTree presentation (target P Q) := by
  exact ⟨registered .bottomTarget, ⟨registered .implication, hP, trivial⟩,
    ⟨registered .implication, hQ, trivial⟩, trivial⟩
theorem source_complete (P Q : Tree GS) (hP : P.IsComplete) (hQ : Q.IsComplete) :
    (source P Q).IsComplete := by
  exact ⟨⟨hP, hQ, trivial⟩, trivial⟩
theorem target_complete (P Q : Tree GS) (hP : P.IsComplete) (hQ : Q.IsComplete) :
    (target P Q).IsComplete := by
  exact ⟨⟨hP, trivial⟩, ⟨hQ, trivial⟩, trivial⟩

def checkedSource := CompleteQuotation.checkedOfComplete presentation
  (source leftFilling rightFilling)
  (source_registered _ _ left_registered right_registered)
  (source_complete _ _ (by trivial) (by trivial))
def checkedTarget := CompleteQuotation.checkedOfComplete presentation
  (target leftFilling rightFilling)
  (target_registered _ _ left_registered right_registered)
  (target_complete _ _ (by trivial) (by trivial))

/-- Both compiler outputs are rechecked in the one immutable equipped stock;
the imported quotation theorem preserves their literal native realization. -/
def checkedSourceFor (P Q : CheckedDerivation presentation GS) :=
  CompleteQuotation.checkedOfComplete presentation (source P.realize Q.realize)
    (source_registered _ _ P.realizeLocallyAdmitted Q.realizeLocallyAdmitted)
    (source_complete _ _ P.realizeIsComplete Q.realizeIsComplete)
def checkedTargetFor (P Q : CheckedDerivation presentation GS) :=
  CompleteQuotation.checkedOfComplete presentation (target P.realize Q.realize)
    (target_registered _ _ P.realizeLocallyAdmitted Q.realizeLocallyAdmitted)
    (target_complete _ _ P.realizeIsComplete Q.realizeIsComplete)

theorem checked_future_filling_permutation (P Q : CheckedDerivation presentation GS) :
    Legal Imp (checkedSourceFor P Q).realize [] [] ↔
      Legal Imp (checkedTargetFor P Q).realize [] [] := by
  rw [show (checkedSourceFor P Q).realize = source P.realize Q.realize from
    CompleteQuotation.quote_realize _ _ _ _]
  rw [show (checkedTargetFor P Q).realize = target P.realize Q.realize from
    CompleteQuotation.quote_realize _ _ _ _]
  exact open_implication_permutation P.realize Q.realize

/-- The same registered native quotations can be reused in every typed
exterior. Admission of an exterior in this exact registry remains a native
checker obligation; the legality equivalence does not invent rule instances. -/
theorem checked_exterior_filling_permutation (P Q : CheckedDerivation presentation GS)
    {G : Hypersequent sigma} {tree : Tree G} {address : InternalAddress}
    (context : CKTree.PunctureAt GT tree address) :
    Legal Imp (context.insert (checkedSourceFor P Q).realize) [] [] ↔
      Legal Imp (context.insert (checkedTargetFor P Q).realize) [] [] := by
  rw [show (checkedSourceFor P Q).realize = source P.realize Q.realize from
    CompleteQuotation.quote_realize _ _ _ _]
  rw [show (checkedTargetFor P Q).realize = target P.realize Q.realize from
    CompleteQuotation.quote_realize _ _ _ _]
  exact implication_permutation_exterior P.realize Q.realize context

theorem checked_source_realize : checkedSource.realize = source leftFilling rightFilling :=
  CompleteQuotation.quote_realize _ _ _ _
theorem checked_target_realize : checkedTarget.realize = target leftFilling rightFilling :=
  CompleteQuotation.quote_realize _ _ _ _

theorem fixture_source_legal : Legal Imp (source leftFilling rightFilling) [] [] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [source_exact_iff]
    simp [leftFilling, rightFilling, identity, ExactTree, ExactChildren, exact_occurrence]
  · simp [UniqueOwners, source, impTree, bottomS, leftFilling, rightFilling,
      identity, events, childEvents, rootEvents, Events.append, occurrence, unary]
  · rw [source_discharge_iff]
    simp [PayloadLegal, ShellDemand, leftFilling, rightFilling, identity,
      events, childEvents, rootEvents, Events.append, occurrence, unary]

theorem fixture_target_legal : Legal Imp (target leftFilling rightFilling) [] [] :=
  (open_implication_permutation leftFilling rightFilling).mp fixture_source_legal

/-- Both top occurrences depend on the shared shell bottom, rather than
being independently closed-grounded pieces. -/
theorem left_not_closed : ¬ LegalEvents (events leftFilling []) [] := by
  simp [LegalEvents, leftFilling, identity, events, childEvents, rootEvents,
    Events.append, occurrence, unary]
theorem right_not_closed : ¬ LegalEvents (events rightFilling []) [] := by
  simp [LegalEvents, rightFilling, identity, events, childEvents, rootEvents,
    Events.append, occurrence, unary]

#check open_implication_permutation
#check forbidden_rule_preservation
#check holeEquiv
#check every_source_filling
#check checked_source_realize
#check fixture_source_legal
#check checked_future_filling_permutation
#print axioms open_implication_permutation
#print axioms implication_interface
#print axioms implication_permutation_exterior
#print axioms forbidden_rule_preservation
#print axioms holeEquiv
#print axioms fixture_source_legal
#print axioms fixture_target_legal
#print axioms checked_source_realize
#print axioms checked_target_realize
#print axioms checked_future_filling_permutation
#print axioms checked_exterior_filling_permutation

end Potkin.Research.DischargePermutation

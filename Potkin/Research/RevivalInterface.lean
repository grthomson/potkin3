import Potkin.GeneralFilling

/-!
# A literal LQ ghost fragment and its scoped certificate observer

The signature and the finite stock below are genuine instances of ordinary
single-succedent identity, left weakening, negation-left and disjunction-left,
plus Lang's repeated-boundary ghost disjunction and ghost initials. Ghost
owner occurrences are identified by their *physical paths*, not stock IDs.

Certificate metadata is not proof evidence. Local admission and quotation use
the existing POTKIN equipped registry and checker. No revival compiler, Cut
elimination, or equality of CK tensors is asserted by this module.
-/

namespace Potkin.Research.RevivalInterface

inductive Atom where | p | q deriving DecidableEq, Repr
inductive Op : Nat → Type where
  | neg : Op 1
  | disj : Op 2

def sigma : Signature := ⟨Atom, Op⟩

/-- Structural recursion on the *native* formula, with recursive calls only
at its actual finite argument slots. No secondary formula representation or
noncomputable equality oracle is used by the public checker. -/
def formulaDecidableEq (A B : Formula sigma) : Decidable (A = B) :=
  match A, B with
  | .atom a, .atom b =>
      if h : (show Atom from a) = (show Atom from b) then
        isTrue (by cases h; rfl)
      else isFalse (by intro hEq; cases hEq; exact h rfl)
  | .atom _, .app _ _ => isFalse (by intro h; cases h)
  | .app _ _, .atom _ => isFalse (by intro h; cases h)
  | .app .neg _, .app .disj _ => isFalse (by intro h; cases h)
  | .app .disj _, .app .neg _ => isFalse (by intro h; cases h)
  | .app .neg args, .app .neg otherArgs =>
      match formulaDecidableEq (args 0) (otherArgs 0) with
      | isTrue h => isTrue (by
          have hargs : args = otherArgs := by
            funext i
            have hi : i = 0 := Subsingleton.elim _ _
            simpa only [hi] using h
          cases hargs
          rfl)
      | isFalse h => isFalse (by
          intro hEq
          have hargs : args = otherArgs := by cases hEq; rfl
          exact h (congrFun hargs 0))
  | .app .disj args, .app .disj otherArgs =>
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
                exact Fin.cases h0
                  (fun j => Fin.cases h1 (fun k => Fin.elim0 k) j) i
              cases hargs
              rfl)
termination_by structural A

instance : DecidableEq (Formula sigma) := formulaDecidableEq

def p : Formula sigma := .atom .p
def q : Formula sigma := .atom .q
def neg (a : Formula sigma) : Formula sigma := .app1 .neg a
def disj (a b : Formula sigma) : Formula sigma := .app2 .disj a b
def np := neg p
def nq := neg q

inductive Data where
  | identity | ghostP | ghostQ | negIdentity | negP | negQ
  | weakQ | weakNotQ | weakP | weakQp | weakQnotP | weakQq
  | disjLower | owner | disjUpper
deriving DecidableEq, Repr

def identityS : Sequent sigma := ⟨{p}, {p}⟩
def ghostPS : Sequent sigma := ⟨0, {p}⟩
def ghostQS : Sequent sigma := ⟨0, {q}⟩
def negIdentityS : Sequent sigma := ⟨{p,np}, 0⟩
def negPS : Sequent sigma := ⟨{np}, 0⟩
def negQS : Sequent sigma := ⟨{nq}, 0⟩
def pStepS : Sequent sigma := ⟨{p,np,q}, 0⟩
def qStepOneS : Sequent sigma := ⟨{p,nq}, 0⟩
def qStepTwoS : Sequent sigma := ⟨{p,np,nq}, 0⟩
def S : Sequent sigma := ⟨{p,np,q,nq}, 0⟩
def R : Sequent sigma := ⟨{np,q,nq,disj p p}, 0⟩
def U : Sequent sigma := ⟨{np,q,nq,disj (disj p p) (disj p p)}, 0⟩
def GS := Hypersequent.singleton S
def GR := Hypersequent.singleton R
def GU := Hypersequent.singleton U

def nullaryShape (out : Sequent sigma) : OccurrenceShape sigma :=
  ⟨[], .singleton out⟩
def unaryShape (input out : Sequent sigma) : OccurrenceShape sigma :=
  ⟨[.singleton input], .singleton out⟩
def binaryShape (left right out : Sequent sigma) : OccurrenceShape sigma :=
  ⟨[.singleton left, .singleton right], .singleton out⟩

private def singletonProfile (s : Sequent sigma) :
    ComponentProfile (.singleton s) := ⟨[s], rfl⟩
private def nullaryIncidence (out : Sequent sigma) :
    ComponentIncidence (nullaryShape out) where
  profiles := { premise := fun i => Fin.elim0 i
                conclusion := singletonProfile out }
  edges := ∅
private def unaryProfiles (input out : Sequent sigma) :
    OccurrenceProfiles (unaryShape input out) where
  premise := fun i => Fin.cases (singletonProfile input) (fun j => Fin.elim0 j) i
  conclusion := singletonProfile out
private def unaryIncidence (input out : Sequent sigma) :
    ComponentIncidence (unaryShape input out) where
  profiles := unaryProfiles input out
  edges := {⟨⟨0, by change 0 < 1; decide⟩,
    ⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩⟩}
private def binaryProfiles (left right out : Sequent sigma) :
    OccurrenceProfiles (binaryShape left right out) where
  premise := fun i => Fin.cases (singletonProfile left)
    (fun j => Fin.cases (singletonProfile right) (fun k => Fin.elim0 k) j) i
  conclusion := singletonProfile out
private def binaryIncidence (left right out : Sequent sigma) :
    ComponentIncidence (binaryShape left right out) where
  profiles := binaryProfiles left right out
  edges := {⟨⟨0, by change 0 < 2; decide⟩,
    ⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩⟩,
    ⟨⟨1, by change 1 < 2; decide⟩,
      ⟨0, by change 0 < 1; decide⟩, ⟨0, by change 0 < 1; decide⟩⟩}

def dataId : Data → Nat
  | .identity => 300 | .ghostP => 301 | .ghostQ => 302
  | .negIdentity => 303 | .negP => 304 | .negQ => 305
  | .weakQ => 306 | .weakNotQ => 307 | .weakP => 308
  | .weakQp => 309 | .weakQnotP => 310 | .weakQq => 311
  | .disjLower => 312 | .owner => 313 | .disjUpper => 314

def leafOccurrence (label : Data) (out : Sequent sigma) : LocalOccurrence sigma Data :=
  ⟨dataId label, .logical, nullaryShape out, label, some (nullaryIncidence out)⟩
def unaryOccurrence (label : Data) (kind : OccurrenceKind) (input out : Sequent sigma) :
    LocalOccurrence sigma Data :=
  ⟨dataId label, kind, unaryShape input out, label, some (unaryIncidence input out)⟩
def binaryOccurrence (label : Data) (left right out : Sequent sigma) :
    LocalOccurrence sigma Data :=
  ⟨dataId label, .logical, binaryShape left right out, label,
    some (binaryIncidence left right out)⟩

def occurrence : Data → LocalOccurrence sigma Data
  | .identity => leafOccurrence .identity identityS
  | .ghostP => leafOccurrence .ghostP ghostPS
  | .ghostQ => leafOccurrence .ghostQ ghostQS
  | .negIdentity => unaryOccurrence .negIdentity .logical identityS negIdentityS
  | .negP => unaryOccurrence .negP .logical ghostPS negPS
  | .negQ => unaryOccurrence .negQ .logical ghostQS negQS
  | .weakQ => unaryOccurrence .weakQ .structural negIdentityS pStepS
  | .weakNotQ => unaryOccurrence .weakNotQ .structural pStepS S
  | .weakP => unaryOccurrence .weakP .structural negPS negIdentityS
  | .weakQp => unaryOccurrence .weakQp .structural negQS qStepOneS
  | .weakQnotP => unaryOccurrence .weakQnotP .structural qStepOneS qStepTwoS
  | .weakQq => unaryOccurrence .weakQq .structural qStepTwoS S
  | .disjLower => binaryOccurrence .disjLower S S R
  | .owner => binaryOccurrence .owner R R R
  | .disjUpper => binaryOccurrence .disjUpper R R U

def labels : List Data :=
  [.identity,.ghostP,.ghostQ,.negIdentity,.negP,.negQ,
    .weakQ,.weakNotQ,.weakP,.weakQp,.weakQnotP,.weakQq,
    .disjLower,.owner,.disjUpper]
def registry := labels.map occurrence

def base : MaterialBase sigma Data PrimitiveFragment.full where
  Member := fun _ => False
  member_material := fun h => False.elim h
  member_primitiveBoundary := fun h => False.elim h
def theory : ProofTheory sigma Data where
  primitive := .full
  base := base
  rules := { logical := fun o => o ∈ registry ∧ o.kind = .logical
             structural := fun o => o ∈ registry ∧ o.kind = .structural }
  initial := fun _ => False
def presentation : EquippedPresentation theory where
  registry := registry
  uniqueIds := by decide
  admitted := by
    intro o h
    rcases List.mem_map.mp h with ⟨label, _, rfl⟩
    cases label <;>
      first
      | exact .logical rfl ⟨h, rfl⟩
      | exact .structural rfl ⟨h, rfl⟩

theorem occurrence_registered (label : Data) : occurrence label ∈ registry := by
  apply List.mem_map.mpr
  refine ⟨label, ?_, rfl⟩
  cases label <;> simp [labels]

def weakeningShape (Gamma : Context sigma) (a : Formula sigma) : OccurrenceShape sigma :=
  unaryShape ⟨Gamma,0⟩ ⟨Gamma + {a},0⟩
def negationLeftShape (Gamma : Context sigma) (a : Formula sigma) : OccurrenceShape sigma :=
  unaryShape ⟨Gamma,{a}⟩ ⟨Gamma + {neg a},0⟩
def disjunctionLeftShape (Gamma : Context sigma) (a b : Formula sigma) :
    OccurrenceShape sigma :=
  binaryShape ⟨Gamma + {a},0⟩ ⟨Gamma + {b},0⟩ ⟨Gamma + {disj a b},0⟩

/-- The complete ordinary boundaries are actual LJ schemas. Multiset exchange
is used, not an arbitrary succedent swap or invented component movement. -/
theorem exact_ordinary_instances :
    (occurrence .identity).shape = nullaryShape ⟨{p},{p}⟩ ∧
    (occurrence .negIdentity).shape = negationLeftShape {p} p ∧
    (occurrence .negP).shape = negationLeftShape 0 p ∧
    (occurrence .negQ).shape = negationLeftShape 0 q ∧
    (occurrence .weakQ).shape = weakeningShape {p,np} q ∧
    (occurrence .weakNotQ).shape = weakeningShape {p,np,q} nq ∧
    (occurrence .weakP).shape = weakeningShape {np} p ∧
    (occurrence .weakQp).shape = weakeningShape {nq} p ∧
    (occurrence .weakQnotP).shape = weakeningShape {p,nq} np ∧
    (occurrence .weakQq).shape = weakeningShape {p,np,nq} q ∧
    (occurrence .disjLower).shape = disjunctionLeftShape {np,q,nq} p p ∧
    (occurrence .disjUpper).shape =
      disjunctionLeftShape {np,q,nq} (disj p p) (disj p p) := by
  simp only [occurrence, leafOccurrence, unaryOccurrence, binaryOccurrence,
    weakeningShape, negationLeftShape, disjunctionLeftShape, identityS,
    negIdentityS, ghostPS, ghostQS, negPS, negQS, pStepS, qStepOneS,
    qStepTwoS, S, R, U, np, nq, nullaryShape, unaryShape, binaryShape,
    OccurrenceShape.mk.injEq]
  decide

theorem exact_ghost_instances :
    (occurrence .ghostP).shape = nullaryShape ⟨0,{p}⟩ ∧
    (occurrence .ghostQ).shape = nullaryShape ⟨0,{q}⟩ ∧
    (occurrence .owner).shape = binaryShape R R R := ⟨rfl,rfl,rfl⟩

def ordinaryS : CKTree sigma Data GS :=
  .ordinary (occurrence .weakNotQ) (.cons
    (.ordinary (occurrence .weakQ) (.cons
      (.ordinary (occurrence .negIdentity) (.cons
        (.ordinary (occurrence .identity) .nil) .nil)) .nil)) .nil)
def moduleP : CKTree sigma Data GS :=
  .ordinary (occurrence .weakNotQ) (.cons
    (.ordinary (occurrence .weakQ) (.cons
      (.ordinary (occurrence .weakP) (.cons
        (.ordinary (occurrence .negP) (.cons
          (.ordinary (occurrence .ghostP) .nil) .nil)) .nil)) .nil)) .nil)
def moduleQ : CKTree sigma Data GS :=
  .ordinary (occurrence .weakQq) (.cons
    (.ordinary (occurrence .weakQnotP) (.cons
      (.ordinary (occurrence .weakQp) (.cons
        (.ordinary (occurrence .negQ) (.cons
          (.ordinary (occurrence .ghostQ) .nil) .nil)) .nil)) .nil)) .nil)
def chooseModule : Atom → CKTree sigma Data GS | .p => moduleP | .q => moduleQ
def lower (left right : CKTree sigma Data GS) : CKTree sigma Data GR :=
  .ordinary (occurrence .disjLower) (.cons left (.cons right .nil))
def fixture (a b : Atom) : CKTree sigma Data GR :=
  .ordinary (occurrence .owner) (.cons (lower ordinaryS ordinaryS)
    (.cons (lower (chooseModule a) (chooseModule b)) .nil))
def upper (left right : CKTree sigma Data GR) : CKTree sigma Data GU :=
  .ordinary (occurrence .disjUpper) (.cons left (.cons right .nil))
def good := upper (fixture .p .p) (fixture .q .q)
def bad := upper (fixture .p .q) (fixture .p .q)

def rawOrdinaryS : RawDerivation sigma :=
  .node 307 (.cons (.node 306 (.cons (.node 303 (.cons
    (.node 300 .nil) .nil)) .nil)) .nil)
def rawModule : Atom → RawDerivation sigma
  | .p => .node 307 (.cons (.node 306 (.cons (.node 308 (.cons
    (.node 304 (.cons (.node 301 .nil) .nil)) .nil)) .nil)) .nil)
  | .q => .node 311 (.cons (.node 310 (.cons (.node 309 (.cons
    (.node 305 (.cons (.node 302 .nil) .nil)) .nil)) .nil)) .nil)
def rawLower (left right : RawDerivation sigma) : RawDerivation sigma :=
  .node 312 (.cons left (.cons right .nil))
def rawFixture (a b : Atom) : RawDerivation sigma :=
  .node 313 (.cons (rawLower rawOrdinaryS rawOrdinaryS)
    (.cons (rawLower (rawModule a) (rawModule b)) .nil))
def rawGood : RawDerivation sigma :=
  .node 314 (.cons (rawFixture .p .p) (.cons (rawFixture .q .q) .nil))
def rawBad : RawDerivation sigma :=
  .node 314 (.cons (rawFixture .p .q) (.cons (rawFixture .p .q) .nil))

/-- The finite lookup fact is independent of any quoted children. -/
private def registeredEntry (label : Data) :
    EquippedPresentation.LookupResult presentation (dataId label) :=
  ⟨occurrence label, occurrence_registered label, by cases label <;> rfl⟩
private theorem lookup_registered (label : Data) :
    presentation.lookup (dataId label) = some (registeredEntry label) := by
  cases label <;> rfl

private theorem check_of_checkAt {G : Hypersequent sigma} {raw : RawDerivation sigma}
    (d : CheckedDerivation presentation G)
    (hd : presentation.checkAt G raw = .ok d) :
    presentation.check raw = .ok ⟨G,d⟩ := by
  cases hc : presentation.check raw with
  | error error => simp [EquippedPresentation.checkAt, hc] at hd
  | ok result =>
    rcases result with ⟨actual, derivation⟩
    by_cases ha : actual = G
    · subst actual
      simp only [EquippedPresentation.checkAt, hc, dif_pos rfl, Except.ok.injEq] at hd
      cases hd
      rfl
    · simp [EquippedPresentation.checkAt, hc, ha] at hd

/-- Reduce only one binary stock node, using already checked ordered children.
No checked constructor is exposed or fabricated: `checkAt` constructs the node. -/
private theorem binary_succeeds (label : Data) (L R O : Sequent sigma)
    (ho : occurrence label = binaryOccurrence label L R O)
    (left right : RawDerivation sigma)
    (dl : CheckedDerivation presentation (Hypersequent.singleton L))
    (dr : CheckedDerivation presentation (Hypersequent.singleton R))
    (hl : presentation.check left = .ok ⟨Hypersequent.singleton L,dl⟩)
    (hr : presentation.check right = .ok ⟨Hypersequent.singleton R,dr⟩) :
    CheckResult.Succeeded (presentation.checkAt (Hypersequent.singleton O)
      (.node (dataId label) (.cons left (.cons right .nil)))) := by
  simp [EquippedPresentation.checkAt, EquippedPresentation.check,
    lookup_registered, registeredEntry, ho, binaryOccurrence, binaryShape,
    RawChildren.length, EquippedPresentation.checkChildren, hl, hr,
    CheckResult.Succeeded]

private theorem binary_realizes (label : Data) (L R O : Sequent sigma)
    (ho : occurrence label = binaryOccurrence label L R O)
    (left right : RawDerivation sigma)
    (dl : CheckedDerivation presentation (Hypersequent.singleton L))
    (dr : CheckedDerivation presentation (Hypersequent.singleton R))
    (hl : presentation.check left = .ok ⟨Hypersequent.singleton L,dl⟩)
    (hr : presentation.check right = .ok ⟨Hypersequent.singleton R,dr⟩)
    (d : CheckedDerivation presentation (Hypersequent.singleton O))
    (hd : presentation.checkAt (Hypersequent.singleton O)
      (.node (dataId label) (.cons left (.cons right .nil))) = .ok d) :
    d.realize = .ordinary (binaryOccurrence label L R O)
      (.cons dl.realize (.cons dr.realize .nil)) := by
  simp [EquippedPresentation.checkAt, EquippedPresentation.check,
    lookup_registered, registeredEntry, ho, binaryOccurrence, binaryShape,
    RawChildren.length, EquippedPresentation.checkChildren, hl, hr,
    Except.ok.injEq] at hd
  cases hd
  rfl

private theorem raw_ordinary_succeeds :
    CheckResult.Succeeded (presentation.checkAt GS rawOrdinaryS) := by decide
private theorem raw_module_succeeds (a : Atom) :
    CheckResult.Succeeded (presentation.checkAt GS (rawModule a)) := by
  cases a <;> decide
private def checkedOrdinaryS : CheckedDerivation presentation GS :=
  CheckResult.get raw_ordinary_succeeds
private def checkedModule (a : Atom) : CheckedDerivation presentation GS :=
  CheckResult.get (raw_module_succeeds a)
private theorem checked_ordinary_realizes : checkedOrdinaryS.realize = ordinaryS := rfl
private theorem checked_module_realizes (a : Atom) :
    (checkedModule a).realize = chooseModule a := by cases a <;> rfl
private theorem check_ordinary :
    presentation.check rawOrdinaryS = .ok ⟨GS,checkedOrdinaryS⟩ :=
  check_of_checkAt checkedOrdinaryS (CheckResult.eq_ok_get raw_ordinary_succeeds)
private theorem check_module (a : Atom) :
    presentation.check (rawModule a) = .ok ⟨GS,checkedModule a⟩ :=
  check_of_checkAt (checkedModule a) (CheckResult.eq_ok_get (raw_module_succeeds a))

private theorem raw_lower_succeeds (left right : RawDerivation sigma)
    (dl dr : CheckedDerivation presentation GS)
    (hl : presentation.check left = .ok ⟨GS,dl⟩)
    (hr : presentation.check right = .ok ⟨GS,dr⟩) :
    CheckResult.Succeeded (presentation.checkAt GR (rawLower left right)) :=
  binary_succeeds .disjLower S S R rfl left right dl dr hl hr
private def checkedLower (left right : RawDerivation sigma)
    (dl dr : CheckedDerivation presentation GS)
    (hl : presentation.check left = .ok ⟨GS,dl⟩)
    (hr : presentation.check right = .ok ⟨GS,dr⟩) :
    CheckedDerivation presentation GR :=
  CheckResult.get (raw_lower_succeeds left right dl dr hl hr)
private theorem check_lower (left right : RawDerivation sigma)
    (dl dr : CheckedDerivation presentation GS)
    (hl : presentation.check left = .ok ⟨GS,dl⟩)
    (hr : presentation.check right = .ok ⟨GS,dr⟩) :
    presentation.check (rawLower left right) =
      .ok ⟨GR,checkedLower left right dl dr hl hr⟩ :=
  check_of_checkAt _ (CheckResult.eq_ok_get (raw_lower_succeeds left right dl dr hl hr))
private theorem checked_lower_realizes (left right : RawDerivation sigma)
    (dl dr : CheckedDerivation presentation GS)
    (hl : presentation.check left = .ok ⟨GS,dl⟩)
    (hr : presentation.check right = .ok ⟨GS,dr⟩) :
    (checkedLower left right dl dr hl hr).realize = lower dl.realize dr.realize :=
  binary_realizes .disjLower S S R rfl left right dl dr hl hr _
    (CheckResult.eq_ok_get (raw_lower_succeeds left right dl dr hl hr))

private def checkedLeftLower := checkedLower rawOrdinaryS rawOrdinaryS
  checkedOrdinaryS checkedOrdinaryS check_ordinary check_ordinary
private def checkedRightLower (a b : Atom) := checkedLower (rawModule a) (rawModule b)
  (checkedModule a) (checkedModule b) (check_module a) (check_module b)
private theorem check_left_lower :
    presentation.check (rawLower rawOrdinaryS rawOrdinaryS) = .ok ⟨GR,checkedLeftLower⟩ :=
  check_lower _ _ _ _ check_ordinary check_ordinary
private theorem check_right_lower (a b : Atom) :
    presentation.check (rawLower (rawModule a) (rawModule b)) =
      .ok ⟨GR,checkedRightLower a b⟩ := check_lower _ _ _ _ (check_module a) (check_module b)

theorem raw_fixture_succeeds (a b : Atom) :
    CheckResult.Succeeded (presentation.checkAt GR (rawFixture a b)) :=
  binary_succeeds .owner R R R rfl
    (rawLower rawOrdinaryS rawOrdinaryS) (rawLower (rawModule a) (rawModule b))
    checkedLeftLower (checkedRightLower a b)
    check_left_lower (check_right_lower a b)
#print axioms raw_fixture_succeeds

def checkedFixture (a b : Atom) : CheckedDerivation presentation GR :=
  CheckResult.get (raw_fixture_succeeds a b)
private theorem check_fixture (a b : Atom) :
    presentation.check (rawFixture a b) = .ok ⟨GR,checkedFixture a b⟩ :=
  check_of_checkAt _ (CheckResult.eq_ok_get (raw_fixture_succeeds a b))
theorem raw_good_succeeds :
    CheckResult.Succeeded (presentation.checkAt GU rawGood) :=
  binary_succeeds .disjUpper R R U rfl (rawFixture .p .p) (rawFixture .q .q)
    (checkedFixture .p .p) (checkedFixture .q .q)
    (check_fixture .p .p) (check_fixture .q .q)
theorem raw_bad_succeeds :
    CheckResult.Succeeded (presentation.checkAt GU rawBad) :=
  binary_succeeds .disjUpper R R U rfl (rawFixture .p .q) (rawFixture .p .q)
    (checkedFixture .p .q) (checkedFixture .p .q)
    (check_fixture .p .q) (check_fixture .p .q)
def checkedGood : CheckedDerivation presentation GU := CheckResult.get raw_good_succeeds
def checkedBad : CheckedDerivation presentation GU := CheckResult.get raw_bad_succeeds

theorem checked_fixture_realizes (a b : Atom) :
    (checkedFixture a b).realize = fixture a b := by
  have hl0 : checkedLeftLower.realize = lower checkedOrdinaryS.realize checkedOrdinaryS.realize :=
    checked_lower_realizes rawOrdinaryS rawOrdinaryS
      checkedOrdinaryS checkedOrdinaryS check_ordinary check_ordinary
  have hl : checkedLeftLower.realize = lower ordinaryS ordinaryS :=
    hl0.trans (congrArg (fun x => lower x x) checked_ordinary_realizes)
  have hr0 : (checkedRightLower a b).realize =
      lower (checkedModule a).realize (checkedModule b).realize :=
    checked_lower_realizes (rawModule a) (rawModule b)
      (checkedModule a) (checkedModule b) (check_module a) (check_module b)
  have hr : (checkedRightLower a b).realize = lower (chooseModule a) (chooseModule b) :=
    hr0.trans (congrArg₂ lower (checked_module_realizes a) (checked_module_realizes b))
  have h : (checkedFixture a b).realize =
      .ordinary (binaryOccurrence .owner R R R)
        (.cons checkedLeftLower.realize (.cons (checkedRightLower a b).realize .nil)) :=
    binary_realizes .owner R R R rfl
    (rawLower rawOrdinaryS rawOrdinaryS) (rawLower (rawModule a) (rawModule b))
    checkedLeftLower (checkedRightLower a b)
    check_left_lower (check_right_lower a b) (checkedFixture a b)
    (CheckResult.eq_ok_get (raw_fixture_succeeds a b))
  exact h.trans (congrArg₂ (fun (left right : CKTree sigma Data GR) =>
    CKTree.ordinary (binaryOccurrence .owner R R R) (.cons left (.cons right .nil))) hl hr)
#print axioms checked_fixture_realizes

theorem checked_separator_realizes :
    checkedGood.realize = good ∧ checkedBad.realize = bad := by
  constructor
  · have hd : presentation.checkAt GU rawGood = .ok checkedGood :=
      CheckResult.eq_ok_get raw_good_succeeds
    have h : checkedGood.realize = .ordinary (binaryOccurrence .disjUpper R R U)
        (.cons (checkedFixture .p .p).realize (.cons (checkedFixture .q .q).realize .nil)) :=
      binary_realizes .disjUpper R R U rfl (rawFixture .p .p) (rawFixture .q .q)
      (checkedFixture .p .p) (checkedFixture .q .q)
      (check_fixture .p .p) (check_fixture .q .q) checkedGood hd
    exact h.trans (congrArg₂ (fun (left right : CKTree sigma Data GR) =>
      CKTree.ordinary (binaryOccurrence .disjUpper R R U) (.cons left (.cons right .nil)))
      (checked_fixture_realizes .p .p) (checked_fixture_realizes .q .q))
  · have hd : presentation.checkAt GU rawBad = .ok checkedBad :=
      CheckResult.eq_ok_get raw_bad_succeeds
    have h : checkedBad.realize = .ordinary (binaryOccurrence .disjUpper R R U)
        (.cons (checkedFixture .p .q).realize (.cons (checkedFixture .p .q).realize .nil)) :=
      binary_realizes .disjUpper R R U rfl (rawFixture .p .q) (rawFixture .p .q)
      (checkedFixture .p .q) (checkedFixture .p .q)
      (check_fixture .p .q) (check_fixture .p .q) checkedBad hd
    exact h.trans (congrArg₂ (fun (left right : CKTree sigma Data GR) =>
      CKTree.ordinary (binaryOccurrence .disjUpper R R U) (.cons left (.cons right .nil)))
      (checked_fixture_realizes .p .q) (checked_fixture_realizes .p .q))

theorem modules_admitted :
    LocallyAdmittedTree presentation ordinaryS ∧
    LocallyAdmittedTree presentation moduleP ∧
    LocallyAdmittedTree presentation moduleQ := by
  simp [ordinaryS, moduleP, moduleQ, LocallyAdmittedTree,
    LocallyAdmittedChildren, presentation, occurrence_registered]

theorem fixture_admitted (a b : Atom) :
    LocallyAdmittedTree presentation (fixture a b) := by
  rw [← checked_fixture_realizes a b]
  exact (checkedFixture a b).realizeLocallyAdmitted

theorem separator_admitted :
    LocallyAdmittedTree presentation good ∧ LocallyAdmittedTree presentation bad := by
  constructor
  · rw [← checked_separator_realizes.1]
    exact checkedGood.realizeLocallyAdmitted
  · rw [← checked_separator_realizes.2]
    exact checkedBad.realizeLocallyAdmitted

theorem fixture_complete (a b : Atom) : (fixture a b).IsComplete := by
  cases a <;> cases b <;>
    simp [fixture, lower, chooseModule, ordinaryS, moduleP, moduleQ,
      CKTree.IsComplete, CKChildren.IsComplete]

theorem literal_node_counts :
    moduleP.degree = 5 ∧ moduleQ.degree = 5 ∧
    (fixture .p .p).degree = 21 ∧ good.degree = 43 ∧ bad.degree = 43 := by decide

mutual
def inventory : {G : Hypersequent sigma} → CKTree sigma Data G →
    Multiset (LocalOccurrence sigma Data)
  | _, .interface _ => 0
  | _, .ordinary o children => {o} + childInventory children
def childInventory : {Gs : List (Hypersequent sigma)} → CKChildren sigma Data Gs →
    Multiset (LocalOccurrence sigma Data)
  | _, .nil => 0
  | _, .cons head tail => inventory head + childInventory tail
end

/-- Full local occurrence values, including all literal boundaries, supplied
incidence and stock IDs; only their physical placements are forgotten. -/
theorem equal_exact_inventory : inventory good = inventory bad := by
  have swap (x y z : Multiset (LocalOccurrence sigma Data)) :
      x + (y + z) = y + (x + z) := by
    rw [← Multiset.add_assoc, Multiset.add_comm x y, Multiset.add_assoc]
  simp [inventory, childInventory, good, bad, upper, fixture, lower,
    chooseModule, Multiset.add_assoc, swap, Multiset.add_comm]

/-! ## Physical owner scope and checkpoints

This presentation has only right one-sided ghost initials. The observer below
implements exactly that *stated fragment* of Definition 5, not all of LQ.
Both colours are distinct atoms throughout; the two-element palette is not a
formal q=1 specialization. All physical owner choices remain distinct entries.
-/

structure OwnerSlot where
  address : List Nat
  colour : Atom
  right : Bool
  seenCheckpoint : Bool
deriving DecidableEq

def emptyConclusion : Data → Bool
  | .identity | .ghostP | .ghostQ => false
  | _ => true

theorem emptyConclusion_exact (label : Data) :
    emptyConclusion label = true ↔
      ∀ s ∈ (occurrence label).shape.conclusion.components, s.rhs = 0 := by
  cases label <;>
    simp [emptyConclusion, occurrence, leafOccurrence, unaryOccurrence,
      binaryOccurrence, nullaryShape, unaryShape, binaryShape,
      identityS, ghostPS, ghostQS, negIdentityS, negPS, negQS,
      pStepS, qStepOneS, qStepTwoS, S, R, U, Hypersequent.singleton]

def advance (empty : Bool) (env : List OwnerSlot) : List OwnerSlot :=
  env.map (fun slot => { slot with seenCheckpoint := slot.seenCheckpoint || empty })
def enterOwner (address : List Nat) (colour : Atom) (right : Bool)
    (env : List OwnerSlot) : List OwnerSlot :=
  env ++ [⟨address, colour, right, false⟩]
def compatibleRight (a : Atom) (slot : OwnerSlot) : Bool :=
  slot.right && slot.seenCheckpoint && decide (slot.colour = a)

mutual
/-- Exact scoped count on native source trees. An open typed Box is NOT a
closed certificate provider; it receives zero, not a fabricated proof. -/
def certificateCount : {G : Hypersequent sigma} → CKTree sigma Data G →
    List Nat → List OwnerSlot → Nat
  | _, .interface _, _, _ => 0
  | _, .ordinary o children, address, env =>
    let inherited := advance (emptyConclusion o.instanceData) env
    match o.instanceData with
    | .ghostP => (inherited.filter (compatibleRight .p)).length
    | .ghostQ => (inherited.filter (compatibleRight .q)).length
    | .owner => ownerCount children address inherited
    | _ => childrenCount children address 0 inherited
def childrenCount : {Gs : List (Hypersequent sigma)} → CKChildren sigma Data Gs →
    List Nat → Nat → List OwnerSlot → Nat
  | _, .nil, _, _, _ => 1
  | _, .cons head tail, address, slot, env =>
    certificateCount head (address ++ [slot]) env *
      childrenCount tail address (slot + 1) env
def ownerCount : {Gs : List (Hypersequent sigma)} → CKChildren sigma Data Gs →
    List Nat → List OwnerSlot → Nat
  | _, .nil, _, _ => 0
  | _, .cons _ .nil, _, _ => 0
  | _, .cons left (.cons right .nil), address, env =>
    certificateCount left (address ++ [0]) (enterOwner address .p false env) *
      certificateCount right (address ++ [1]) (enterOwner address .p true env) +
    certificateCount left (address ++ [0]) (enterOwner address .q false env) *
      certificateCount right (address ++ [1]) (enterOwner address .q true env)
  | _, .cons _ (.cons _ (.cons _ _)), _, _ => 0
end

mutual
/-- Constructive Definition-5 choices in the represented right-ghost fragment:
ordinary premises all receive certificates; a physical owner selects one
colour shared by its left/right children; a ghost leaf chooses a genuine
eligible right ancestor already carrying a permitted checkpoint. -/
def HasScopedCertificate : {G : Hypersequent sigma} → CKTree sigma Data G →
    List Nat → List OwnerSlot → Prop
  | _, .interface _, _, _ => False
  | _, .ordinary o children, address, env =>
    let inherited := advance (emptyConclusion o.instanceData) env
    match o.instanceData with
    | .ghostP => ∃ slot ∈ inherited, compatibleRight .p slot = true
    | .ghostQ => ∃ slot ∈ inherited, compatibleRight .q slot = true
    | .owner => OwnerCertificate children address inherited
    | _ => ChildrenCertificate children address 0 inherited
def ChildrenCertificate : {Gs : List (Hypersequent sigma)} → CKChildren sigma Data Gs →
    List Nat → Nat → List OwnerSlot → Prop
  | _, .nil, _, _, _ => True
  | _, .cons head tail, address, slot, env =>
    HasScopedCertificate head (address ++ [slot]) env ∧
      ChildrenCertificate tail address (slot + 1) env
def OwnerCertificate : {Gs : List (Hypersequent sigma)} → CKChildren sigma Data Gs →
    List Nat → List OwnerSlot → Prop
  | _, .nil, _, _ => False
  | _, .cons _ .nil, _, _ => False
  | _, .cons left (.cons right .nil), address, env =>
    ∃ colour : Atom,
      HasScopedCertificate left (address ++ [0]) (enterOwner address colour false env) ∧
        HasScopedCertificate right (address ++ [1]) (enterOwner address colour true env)
  | _, .cons _ (.cons _ (.cons _ _)), _, _ => False
end

private theorem filter_length_pos {a : Type} (xs : List a) (test : a → Bool) :
    0 < (xs.filter test).length ↔ ∃ x ∈ xs, test x = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : test x = true
      · simp [hx]
      · simp [hx, ih]

private theorem mul_positive (a b : Nat) : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  ⟨fun h => ⟨Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩,
    fun h => Nat.mul_pos h.1 h.2⟩

mutual
/-- A constructor proof for arbitrary native trees, not an enumeration check.
Interpretation as this LQ fragment additionally requires exact local admission;
the theorem does not classify foreign occurrences from their labels alone. -/
theorem count_positive_iff : {G : Hypersequent sigma} →
    (tree : CKTree sigma Data G) → (address : List Nat) → (env : List OwnerSlot) →
    (0 < certificateCount tree address env ↔ HasScopedCertificate tree address env)
  | _, .interface _, _, _ => by simp [certificateCount, HasScopedCertificate]
  | _, .ordinary o children, address, env => by
    cases h : o.instanceData <;>
      simp only [certificateCount, HasScopedCertificate, h]
    all_goals first
      | exact filter_length_pos _ _
      | exact ownerCount_positive_iff children address _
      | exact childrenCount_positive_iff children address 0 _
theorem childrenCount_positive_iff : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (address : List Nat) →
    (slot : Nat) → (env : List OwnerSlot) →
    (0 < childrenCount children address slot env ↔
      ChildrenCertificate children address slot env)
  | _, .nil, _, _, _ => by simp [childrenCount, ChildrenCertificate]
  | _, .cons head tail, address, slot, env => by
      simp only [childrenCount, ChildrenCertificate, mul_positive,
        count_positive_iff head, childrenCount_positive_iff tail]
theorem ownerCount_positive_iff : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma Data Gs) → (address : List Nat) →
    (env : List OwnerSlot) →
    (0 < ownerCount children address env ↔ OwnerCertificate children address env)
  | _, .nil, _, _ => by simp [ownerCount, OwnerCertificate]
  | _, .cons _ .nil, _, _ => by simp [ownerCount, OwnerCertificate]
  | _, .cons left (.cons right .nil), address, env => by
      simp only [ownerCount, OwnerCertificate, Nat.add_pos_iff_pos_or_pos,
        mul_positive, count_positive_iff]
      constructor
      · intro h
        rcases h with hp | hq
        · exact ⟨.p, hp⟩
        · exact ⟨.q, hq⟩
      · rintro ⟨colour, h⟩
        cases colour with
        | p => exact Or.inl h
        | q => exact Or.inr h
  | _, .cons _ (.cons _ (.cons _ _)), _, _ => by simp [ownerCount, OwnerCertificate]
end

theorem cooperative_counts :
    certificateCount (fixture .p .p) [] [] = 1 ∧
    certificateCount (fixture .p .q) [] [] = 0 ∧
    certificateCount (fixture .q .p) [] [] = 0 ∧
    certificateCount (fixture .q .q) [] [] = 1 := by decide

theorem separator_counts :
    certificateCount good [] [] = 1 ∧ certificateCount bad [] [] = 0 := by decide

/-- Equal complete local inference inventory cannot decide the new observer.
This is not the earlier rule-permission observer or a claim about provability
of the common LJ-provable endsequent. -/
theorem certificate_separator :
    inventory good = inventory bad ∧
      HasScopedCertificate good [] [] ∧ ¬ HasScopedCertificate bad [] [] := by
  have hc := separator_counts
  refine ⟨equal_exact_inventory, ?_, ?_⟩
  · apply (count_positive_iff good [] []).mp
    simp [hc.1]
  · intro h
    have hp := (count_positive_iff bad [] []).mpr h
    simp [hc.2] at hp

#print axioms exact_ordinary_instances
#print axioms exact_ghost_instances
#print axioms checked_separator_realizes
#print axioms equal_exact_inventory
#print axioms count_positive_iff
#print axioms certificate_separator

end Potkin.Research.RevivalInterface

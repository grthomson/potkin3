import Potkin.Research.D3SchemaPermutation
import Potkin.Research.D3SourceEncoding

/-!
# Implication permutation on the independently specified source fragment

The implication interpretation is the actual source constructor, not an
arbitrary predicate.  The stronger source-shell result below encodes source
inferences directly, retaining their supplied component incidence.  It uses
the verified generic fixed-owner replacement theorem; it does not reprove
global discharge correctness by a bespoke permutation induction.
-/

namespace Potkin.Research.D3SourcePermutation

open OpenDischarge

structure Application where
  gamma : D3SourceEncoding.Context
  antecedent : D3SourceEncoding.Formula
  consequent : D3SourceEncoding.Formula
  parameters : D3SourceEncoding.Parameters
  owner : Nat
  sourceKey : Nat
  implicationKey : Nat
  targetKey : Nat

namespace Application

variable (a : Application)

def asSchema : D3SchemaPermutation.Schema D3SourceEncoding.signature where
  gamma := D3SourceEncoding.encodeContext a.gamma
  antecedent := D3SourceEncoding.encodeFormula a.antecedent
  consequent := D3SourceEncoding.encodeFormula a.consequent
  result := D3SourceEncoding.encodeFormula (.implication a.antecedent a.consequent)
  parameters := D3SourceEncoding.encodeParameters a.parameters
  owner := a.owner
  sourceKey := a.sourceKey
  implicationKey := a.implicationKey
  targetKey := a.targetKey

theorem actual_implication : D3SourceEncoding.Imp a.asSchema.antecedent a.asSchema.consequent
    a.asSchema.result := rfl

/-- Actual constructor instantiation of the any-formula native schema theorem. -/
theorem actual_schema_exterior
    (P Q : CKTree D3SourceEncoding.signature (Data D3SourceEncoding.signature) a.asSchema.sourceBoundary)
    {G : Hypersequent D3SourceEncoding.signature}
    {tree : CKTree D3SourceEncoding.signature (Data D3SourceEncoding.signature) G}
    {address : InternalAddress}
    (context : CKTree.PunctureAt a.asSchema.targetBoundary tree address) :
    Legal D3SourceEncoding.Imp (context.insert (a.asSchema.source P Q)) [] [] ↔
      Legal D3SourceEncoding.Imp (context.insert (a.asSchema.target P Q)) [] [] :=
  a.asSchema.implication_permutation_schema_exterior D3SourceEncoding.Imp a.actual_implication
    P Q context

def input : D3SourceEncoding.Sequent := ⟨{a.antecedent} + a.gamma, {a.consequent}⟩
def output : D3SourceEncoding.Sequent :=
  ⟨a.gamma, {.implication a.antecedent a.consequent}⟩

def source (P Q : D3SourceEncoding.Diagram a.input) : D3SourceEncoding.Diagram a.output :=
  .rule a.implicationKey (.implicationRight a.gamma a.antecedent a.consequent)
    (.cons (.rule a.sourceKey (.bottom a.parameters a.owner a.input)
      (.cons P (.cons Q .nil))) .nil)

def target (P Q : D3SourceEncoding.Diagram a.input) : D3SourceEncoding.Diagram a.output :=
  .rule a.targetKey (.bottom a.parameters a.owner a.output)
    (.cons (.rule a.implicationKey (.implicationRight a.gamma a.antecedent a.consequent)
      (.cons P .nil))
      (.cons (.rule a.implicationKey (.implicationRight a.gamma a.antecedent a.consequent)
        (.cons Q .nil)) .nil))

def sourceShell := D3SourceEncoding.encode (a.source (.hole a.input) (.hole a.input))
def targetShell := D3SourceEncoding.encode (a.target (.hole a.input) (.hole a.input))

def holeEquiv : a.sourceShell.LeafOccurrence ≃ a.targetShell.LeafOccurrence where
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

theorem hole_boundary (h : a.sourceShell.LeafOccurrence) :
    a.sourceShell.leafBoundary h = a.targetShell.leafBoundary (a.holeEquiv h) := by
  rcases h with (h | h)
  · rcases h with (h | h)
    · rfl
    · rcases h with (h | h)
      · rfl
      · exact nomatch h
  · exact nomatch h

def shellGrant (address : InternalAddress) (key : Nat) : Grant D3SourceEncoding.signature :=
  ⟨a.owner, address, key, D3SourceEncoding.encodeParameters a.parameters⟩

private theorem source_shell_exposure :
    (directSummary D3SourceEncoding.Imp a.sourceShell []).exposure =
      (exposureRows [⟨[0, 0], D3SourceEncoding.boundary a.input⟩,
          ⟨[0, 1], D3SourceEncoding.boundary a.input⟩]
        [a.shellGrant [0] a.sourceKey] : Multiset (Exposure D3SourceEncoding.signature)) := rfl
private theorem target_shell_exposure :
    (directSummary D3SourceEncoding.Imp a.targetShell []).exposure =
      (exposureRows [⟨[0, 0], D3SourceEncoding.boundary a.input⟩,
          ⟨[1, 0], D3SourceEncoding.boundary a.input⟩]
        [a.shellGrant [] a.targetKey] : Multiset (Exposure D3SourceEncoding.signature)) := rfl

/-- This interface is for the encodings of actual SOURCE rule applications,
not merely for equal displayed native sequents or canonical edge surrogates. -/
def source_interface : FixedOwnerInterface D3SourceEncoding.Imp a.sourceShell a.targetShell := by
  refine ⟨a.holeEquiv, a.hole_boundary, rfl, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    have sourceLocal : D3SourceEncoding.LocallyCorrect (a.source (.hole a.input) (.hole a.input)) := by
      simp [source, D3SourceEncoding.LocallyCorrect, D3SourceEncoding.ChildrenCorrect, D3SourceEncoding.Rule.Valid,
        input]
    have targetLocal : D3SourceEncoding.LocallyCorrect (a.target (.hole a.input) (.hole a.input)) := by
      simp [target, D3SourceEncoding.LocallyCorrect, D3SourceEncoding.ChildrenCorrect, D3SourceEncoding.Rule.Valid,
        output]
    have exactSource : ExactTree D3SourceEncoding.Imp a.sourceShell :=
      (D3SourceEncoding.exact_tree_iff _).mpr sourceLocal
    have exactTarget : ExactTree D3SourceEncoding.Imp a.targetShell :=
      (D3SourceEncoding.exact_tree_iff _).mpr targetLocal
    change (ExactTree D3SourceEncoding.Imp a.sourceShell ∧ UniqueOwners (events a.sourceShell []) ∧
      InteriorLegal (events a.sourceShell [])) ↔
      (ExactTree D3SourceEncoding.Imp a.targetShell ∧ UniqueOwners (events a.targetShell []) ∧
        InteriorLegal (events a.targetShell []))
    simp only [exactSource, exactTarget, true_and]
    simp [sourceShell, targetShell, source, target, D3SourceEncoding.encode, D3SourceEncoding.encodeChildren,
      D3SourceEncoding.occurrence, D3SourceEncoding.ruleData, events, childEvents, rootEvents, Events.append,
      UniqueOwners, InteriorLegal]
  · intro hole
    rcases hole with (hole | hole)
    · rcases hole with (hole | hole)
      · cases hole
        change exposureAt (directSummary D3SourceEncoding.Imp a.sourceShell []) [0, 0] =
          exposureAt (directSummary D3SourceEncoding.Imp a.targetShell []) [0, 0]
        simp [exposureAt, a.source_shell_exposure, a.target_shell_exposure,
          eraseExposure, exposureRows, shellGrant, List.flatMap, List.map,
          List.filterMap, List.filter, List.cons.injEq]
      · rcases hole with (hole | hole)
        · cases hole
          change exposureAt (directSummary D3SourceEncoding.Imp a.sourceShell []) [0, 1] =
            exposureAt (directSummary D3SourceEncoding.Imp a.targetShell []) [1, 0]
          simp [exposureAt, a.source_shell_exposure, a.target_shell_exposure,
            eraseExposure, exposureRows, shellGrant, List.flatMap, List.map,
            List.filterMap, List.filter, List.cons.injEq]
        · exact nomatch hole
    · exact nomatch hole

def sourceAssignment (P Q : D3SourceEncoding.Diagram a.input) : a.sourceShell.LeafAssignment
  | .inl (.inl _) => D3SourceEncoding.encode P
  | .inl (.inr (.inl _)) => D3SourceEncoding.encode Q
  | .inl (.inr (.inr h)) => nomatch h
  | .inr h => nomatch h
def targetAssignment (P Q : D3SourceEncoding.Diagram a.input) : a.targetShell.LeafAssignment
  | .inl (.inl _) => D3SourceEncoding.encode P
  | .inl (.inr h) => nomatch h
  | .inr (.inl (.inl _)) => D3SourceEncoding.encode Q
  | .inr (.inl (.inr h)) => nomatch h
  | .inr (.inr h) => nomatch h

/-- Arbitrary source donors, with their stable tokens unchanged, in every
native exterior. Source correctness is connected separately by adequacy. -/
theorem encoded_source_permutation_exterior (P Q : D3SourceEncoding.Diagram a.input)
    {G : Hypersequent D3SourceEncoding.signature}
    {tree : CKTree D3SourceEncoding.signature (Data D3SourceEncoding.signature) G}
    {address : InternalAddress}
    (context : CKTree.PunctureAt (D3SourceEncoding.boundary a.output) tree address) :
    Legal D3SourceEncoding.Imp (context.insert (D3SourceEncoding.encode (a.source P Q))) [] [] ↔
      Legal D3SourceEncoding.Imp (context.insert (D3SourceEncoding.encode (a.target P Q))) [] [] := by
  have matching (hole : a.sourceShell.LeafOccurrence) :
      HEq (a.sourceAssignment P Q hole)
        (a.targetAssignment P Q (a.holeEquiv hole)) := by
    rcases hole with (hole | hole)
    · rcases hole with (hole | hole)
      · rfl
      · rcases hole with (hole | hole)
        · rfl
        · exact nomatch hole
    · exact nomatch hole
  exact fixedOwner_replacement D3SourceEncoding.Imp a.source_interface
    (a.sourceAssignment P Q) (a.targetAssignment P Q) matching context

end Application

#check @Application.actual_schema_exterior
#check @Application.encoded_source_permutation_exterior
#print axioms Application.actual_schema_exterior
#print axioms Application.source_interface
#print axioms Application.encoded_source_permutation_exterior

end Potkin.Research.D3SourcePermutation

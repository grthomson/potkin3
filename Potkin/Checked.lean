import Potkin.CKTree
import Potkin.Presentation

namespace Potkin

universe u v w

mutual

/-- Anonymous raw candidates make no boundary or admission claims. -/
inductive RawDerivation (sigma : Signature.{u, v}) : Type (max u v) where
  | puncture
  | node (id : Nat) (children : RawChildren sigma)

/-- Ordered raw children. -/
inductive RawChildren (sigma : Signature.{u, v}) : Type (max u v) where
  | nil
  | cons (head : RawDerivation sigma) (tail : RawChildren sigma)

end

namespace RawChildren

variable {sigma : Signature.{u, v}}

def length : RawChildren sigma -> Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

end RawChildren

mutual

/-- Rich checked derivations retain exact registry provenance and occurrence data. -/
inductive CheckedDerivation {sigma : Signature.{u, v}} {InstanceData : Type w}
    {T : ProofTheory sigma InstanceData} (P : EquippedPresentation T) :
    Hypersequent sigma -> Type (max (max u v) w) where
  | private node (o : LocalOccurrence sigma InstanceData)
      (registered : o ∈ P.registry)
      (children : CheckedChildren P o.shape.premises) :
      CheckedDerivation P o.shape.conclusion

/-- Ordered checked children indexed by the entire premise boundary list. -/
inductive CheckedChildren {sigma : Signature.{u, v}} {InstanceData : Type w}
    {T : ProofTheory sigma InstanceData} (P : EquippedPresentation T) :
    List (Hypersequent sigma) -> Type (max (max u v) w) where
  | private nil : CheckedChildren P []
  | private cons {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
      (head : CheckedDerivation P G) (tail : CheckedChildren P Gs) :
      CheckedChildren P (G :: Gs)

end

/-- Complete checking failures.  Raw punctures are rejected on this route. -/
inductive CheckError where
  | unknownId (id : Nat)
  | unexpectedPuncture
  | wrongArity (id expected actual : Nat)
  | wrongBoundary (id slot : Nat)
  | wrongRootBoundary
deriving DecidableEq, Repr

namespace EquippedPresentation

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData}

mutual

/-- Resolve every raw node through the unique finite registry. -/
def check [DecidableEq (Hypersequent sigma)] (P : EquippedPresentation T) :
    RawDerivation sigma ->
      Except CheckError (Sigma (CheckedDerivation P))
  | .puncture => .error .unexpectedPuncture
  | .node id rawChildren =>
      match P.lookup id with
      | none => .error (.unknownId id)
      | some entry =>
          if rawChildren.length = entry.occurrence.shape.premises.length then
            match checkChildren P id 0 entry.occurrence.shape.premises rawChildren with
            | .error error => .error error
            | .ok children =>
                .ok ⟨entry.occurrence.shape.conclusion,
                  .node entry.occurrence entry.registered children⟩
          else
            .error (.wrongArity id entry.occurrence.shape.premises.length rawChildren.length)

def checkChildren [DecidableEq (Hypersequent sigma)]
    (P : EquippedPresentation T) (parentId slot : Nat) :
    (boundaries : List (Hypersequent sigma)) -> RawChildren sigma ->
      Except CheckError (CheckedChildren P boundaries)
  | [], .nil => .ok .nil
  | [], .cons _ _ => .error (.wrongArity parentId slot (slot + 1))
  | _ :: _, .nil => .error (.wrongArity parentId (slot + 1) slot)
  | G :: Gs, .cons raw rest =>
      match check P raw with
      | .error error => .error error
      | .ok ⟨H, child⟩ =>
          if h : H = G then
            match checkChildren P parentId (slot + 1) Gs rest with
            | .error error => .error error
            | .ok tail => .ok (.cons (h ▸ child) tail)
          else
            .error (.wrongBoundary parentId slot)

end

/-- Check a complete candidate against one exact whole root boundary. -/
def checkAt [DecidableEq (Hypersequent sigma)] (P : EquippedPresentation T)
    (expected : Hypersequent sigma) (raw : RawDerivation sigma) :
    Except CheckError (CheckedDerivation P expected) :=
  match P.check raw with
  | .error error => .error error
  | .ok ⟨actual, derivation⟩ =>
      if h : actual = expected then .ok (h ▸ derivation)
      else .error .wrongRootBoundary

end EquippedPresentation

namespace CheckResult

/-- Proposition that an executable check returned a value. -/
def Succeeded {alpha : Type _} : Except CheckError alpha -> Prop
  | .ok _ => True
  | .error _ => False

instance {alpha : Type _} (result : Except CheckError alpha) :
    Decidable (Succeeded result) :=
  match result with
  | .ok _ => isTrue trivial
  | .error _ => isFalse (fun h => h)

/-- Extract a value only from a proved-successful executable check. -/
def get {alpha : Type _} {result : Except CheckError alpha}
    (success : Succeeded result) : alpha :=
  match result with
  | .ok value => value
  | .error _ => False.elim success

theorem eq_ok_get {alpha : Type _} {result : Except CheckError alpha}
    (success : Succeeded result) : result = .ok (get success) := by
  cases result with
  | ok value => rfl
  | error error => exact False.elim success

end CheckResult

namespace CheckedDerivation

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

/-- The exact registered occurrence retained at the root. -/
def rootOccurrence {G : Hypersequent sigma} :
    CheckedDerivation P G -> LocalOccurrence sigma InstanceData
  | .node o _ _ => o

/-- Checked construction makes the retained conclusion exactly the type index. -/
theorem boundaryCorrect {G : Hypersequent sigma} (d : CheckedDerivation P G) :
    d.rootOccurrence.shape.conclusion = G := by
  cases d
  rfl

mutual

/-- Reindex a checked derivation through transported registry admissions. -/
def mapBase {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) :
    {G : Hypersequent sigma} -> CheckedDerivation P G ->
      CheckedDerivation (P.mapBase f) G
  | _, .node o registered children =>
      .node o (by simpa using registered) (CheckedChildren.mapBase f children)

def CheckedChildren.mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) :
    {boundaries : List (Hypersequent sigma)} -> CheckedChildren P boundaries ->
      CheckedChildren (P.mapBase f) boundaries
  | _, .nil => .nil
  | _, .cons head tail => .cons (mapBase f head) (CheckedChildren.mapBase f tail)

end

mutual

/-- Explicit realization into the open occurrence-decorated CK carrier. -/
def realize : {G : Hypersequent sigma} -> CheckedDerivation P G ->
    CKTree sigma InstanceData G
  | _, .node o _ children => .ordinary o (CheckedChildren.realize children)

def CheckedChildren.realize :
    {boundaries : List (Hypersequent sigma)} -> CheckedChildren P boundaries ->
      CKChildren sigma InstanceData boundaries
  | _, .nil => .nil
  | _, .cons head tail => .cons (realize head) (CheckedChildren.realize tail)

end

/-- Every realized complete checked derivation has a positive ordinary root. -/
theorem realize_isOrdinary {G : Hypersequent sigma} (d : CheckedDerivation P G) :
    (realize d).IsOrdinary := by
  cases d
  trivial

mutual

@[simp]
theorem realize_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C)
    {G : Hypersequent sigma} (d : CheckedDerivation P G) :
    realize (mapBase f d) = realize d := by
  cases d
  simp only [mapBase, realize]
  congr 1
  apply CheckedChildren.realize_mapBase

@[simp]
theorem CheckedChildren.realize_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) {boundaries : List (Hypersequent sigma)}
    (children : CheckedChildren P boundaries) :
    CheckedChildren.realize (CheckedChildren.mapBase f children) =
      CheckedChildren.realize children := by
  cases children
  · rfl
  · simp only [CheckedChildren.mapBase, CheckedChildren.realize]
    rw [realize_mapBase, CheckedChildren.realize_mapBase]

end

/-- Identity base transport has literally unchanged occurrence-decorated action. -/
@[simp]
theorem realize_mapBase_id {G : Hypersequent sigma}
    (d : CheckedDerivation P G) :
    realize (mapBase (BaseHom.id T.base) d) = realize d :=
  realize_mapBase (BaseHom.id T.base) d

/-- Composite base transport has the same decorated action as staged transport. -/
@[simp]
theorem realize_mapBase_comp
    {C D : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (g : BaseHom C D)
    {G : Hypersequent sigma} (d : CheckedDerivation P G) :
    realize (mapBase g (mapBase f d)) =
      realize (mapBase (g.comp f) d) := by
  simp only [realize_mapBase]

@[simp]
theorem erase_realize_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C)
    {G : Hypersequent sigma} (d : CheckedDerivation P G) :
    CKTree.erase (realize (mapBase f d)) = CKTree.erase (realize d) := by
  rw [realize_mapBase]

end CheckedDerivation

end Potkin

import Potkin.Research.DischargePermutation
import Potkin.Research.OpenDischargeCertificates

/-!
# Scoped occurrence-resolved certificates for the unary permutation

The correspondence below keeps the physical ancestor *position*, UID,
parameters and ordered branch.  Its two lists still contain their actual
addresses; an address is never recovered from a collected coefficient.
Readdressing is an explicit map between witness types, not a definition of
CK flag coherence or an erasure of certificate scope.
-/

namespace Potkin.Research.DischargeCertificatePermutation

open OpenDischarge OpenDischargeCertificates DischargePermutation

universe u v
variable {s : Signature.{u, v}}

/-- Exact indexed scope correspondence.  Addresses remain in each native
scope and may differ only as supplied by the actual source/target traversal. -/
structure ScopeCorrespondence (left right : List (OwnerSlot s)) where
  positions : Fin left.length ≃ Fin right.length
  samePosition : ∀ i, (positions i).val = i.val
  uid : ∀ i, (right.get (positions i)).uid = (left.get i).uid
  parameters : ∀ i, (right.get (positions i)).parameters = (left.get i).parameters
  role : ∀ i, (right.get (positions i)).role = (left.get i).role

def ScopeCorrespondence.refl (scope : List (OwnerSlot s)) :
    ScopeCorrespondence scope scope :=
  ⟨Equiv.refl _, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def ScopeCorrespondence.enter {left right : List (OwnerSlot s)}
    (matchScope : ScopeCorrespondence left right) (uid : Nat)
    (pack : Parameters s) (leftAddress rightAddress : InternalAddress) (role : Fin 2) :
    ScopeCorrespondence
      (enterOwner uid pack leftAddress role left)
      (enterOwner uid pack rightAddress role right) where
  positions :=
    { toFun := Fin.cases 0 (fun i => (matchScope.positions i).succ)
      invFun := Fin.cases 0 (fun i => (matchScope.positions.symm i).succ)
      left_inv := by
        intro i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => simp
      right_inv := by
        intro i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => simp }
  samePosition := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simp [matchScope.samePosition i]
  uid := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact matchScope.uid i
  parameters := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact matchScope.parameters i
  role := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact matchScope.role i

def eligibleOwnerEquiv {left right : List (OwnerSlot s)}
    (matchScope : ScopeCorrespondence left right) (uid : Nat)
    (pack : Parameters s) (role : Fin 2) :
    EligibleOwner uid pack role left ≃ EligibleOwner uid pack role right where
  toFun chosen := ⟨matchScope.positions chosen.val, by
    rw [matchScope.uid, matchScope.parameters, matchScope.role]
    exact chosen.property⟩
  invFun chosen := ⟨matchScope.positions.symm chosen.val, by
    have h := chosen.property
    have hu := matchScope.uid (matchScope.positions.symm chosen.val)
    have hp := matchScope.parameters (matchScope.positions.symm chosen.val)
    have hr := matchScope.role (matchScope.positions.symm chosen.val)
    simp only [Equiv.apply_symm_apply] at hu hp hr
    rw [← hu, ← hp, ← hr]
    exact h⟩
  left_inv chosen := by
    apply Subtype.ext
    exact matchScope.positions.symm_apply_apply chosen.val
  right_inv chosen := by
    apply Subtype.ext
    exact matchScope.positions.apply_symm_apply chosen.val

theorem eligible_position_preserved {left right : List (OwnerSlot s)}
    (matchScope : ScopeCorrespondence left right) (uid : Nat)
    (pack : Parameters s) (role : Fin 2) (chosen : EligibleOwner uid pack role left) :
    ((eligibleOwnerEquiv matchScope uid pack role chosen).val).val = chosen.val.val :=
  matchScope.samePosition chosen.val

mutual

/-- Uniform readdressing of closed certificate types.  Interfaces remain
uninhabited; nested owners carry their new actual traversal addresses. -/
def readdressEquiv : {G : Hypersequent s} → (tree : CKTree s (Data s) G) →
    (leftAddress rightAddress : InternalAddress) →
    {left right : List (OwnerSlot s)} → ScopeCorrespondence left right →
    ClosedKernel tree leftAddress left ≃ ClosedKernel tree rightAddress right
  | _, .interface _, _, _, _, _, _ => Equiv.refl _
  | _, .ordinary o children, la, ra, _, _, matchScope => by
      cases label : o.instanceData <;> simp only [ClosedKernel, Kernel, label]
      all_goals first
        | exact Equiv.prodCongr (eligibleOwnerEquiv matchScope _ _ _)
            (readdressChildrenEquiv children la ra 0 matchScope)
        | exact readdressBottomEquiv children _ _ la ra matchScope
        | exact readdressChildrenEquiv children la ra 0 matchScope

def readdressChildrenEquiv : {Gs : List (Hypersequent s)} →
    (children : CKChildren s (Data s) Gs) → (leftAddress rightAddress : InternalAddress) →
    (slot : Nat) → {left right : List (OwnerSlot s)} → ScopeCorrespondence left right →
    ChildrenKernel children (fun _ _ _ => PEmpty) leftAddress slot left ≃
      ChildrenKernel children (fun _ _ _ => PEmpty) rightAddress slot right
  | _, .nil, _, _, _, _, _, _ => Equiv.refl _
  | _, .cons head tail, la, ra, slot, _, _, matchScope =>
      Equiv.prodCongr
        (readdressEquiv head (la ++ [slot]) (ra ++ [slot]) matchScope)
        (readdressChildrenEquiv tail la ra (slot + 1) matchScope)

def readdressBottomEquiv : {Gs : List (Hypersequent s)} →
    (children : CKChildren s (Data s) Gs) → (uid : Nat) → (pack : Parameters s) →
    (leftAddress rightAddress : InternalAddress) →
    {left right : List (OwnerSlot s)} → ScopeCorrespondence left right →
    BottomKernel children (fun _ _ _ => PEmpty) uid pack leftAddress left ≃
      BottomKernel children (fun _ _ _ => PEmpty) uid pack rightAddress right
  | _, .nil, _, _, _, _, _, _, _ => Equiv.refl _
  | _, .cons _ .nil, _, _, _, _, _, _, _ => Equiv.refl _
  | _, .cons P (.cons Q .nil), uid, pack, la, ra, _, _, matchScope =>
      Equiv.prodCongr
        (readdressEquiv P (la ++ [0]) (ra ++ [0])
          (matchScope.enter uid pack la ra 0))
        (readdressEquiv Q (la ++ [1]) (ra ++ [1])
          (matchScope.enter uid pack la ra 1))
  | _, .cons _ (.cons _ (.cons _ _)), _, _, _, _, _, _, _ => Equiv.refl _

end

/-- Actual certificate transport for arbitrary inherited owners and arbitrary
future premises.  The shared system bottom changes its absolute address,
not its UID/pack or its two branch positions. -/
def scoped_permutation_equiv (P Q : Tree GS) (address : InternalAddress)
    (scope : List (OwnerSlot sigma)) :
    ClosedKernel (source P Q) address scope ≃ ClosedKernel (target P Q) address scope := by
  let eP := readdressEquiv P ((address ++ [0]) ++ [0]) ((address ++ [0]) ++ [0])
    ((ScopeCorrespondence.refl scope).enter bottomUID parameters
      (address ++ [0]) address 0)
  let eQ := readdressEquiv Q ((address ++ [0]) ++ [1]) ((address ++ [1]) ++ [0])
    ((ScopeCorrespondence.refl scope).enter bottomUID parameters
      (address ++ [0]) address 1)
  refine
    { toFun := fun c => ⟨⟨eP c.1.1, PUnit.unit⟩, ⟨eQ c.1.2, PUnit.unit⟩⟩
      invFun := fun c => ⟨⟨eP.symm c.1.1, eQ.symm c.2.1⟩, PUnit.unit⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨p, q⟩, unit⟩
    cases unit
    simp
  · rintro ⟨⟨p, unitP⟩, ⟨q, unitQ⟩⟩
    cases unitP
    cases unitQ
    simp

def headOwner (address : InternalAddress) (role : Fin 2) :
    EligibleOwner bottomUID parameters role
      (enterOwner bottomUID parameters address role []) :=
  ⟨0, rfl, rfl, rfl⟩

def left_certificate (address ownerAddress : InternalAddress) :
    ClosedKernel leftFilling address
      (enterOwner bottomUID parameters ownerAddress 0 []) :=
  ⟨headOwner ownerAddress 0, ⟨⟨PUnit.unit, PUnit.unit⟩, PUnit.unit⟩⟩

def right_certificate (address ownerAddress : InternalAddress) :
    ClosedKernel rightFilling address
      (enterOwner bottomUID parameters ownerAddress 1 []) :=
  ⟨⟨headOwner ownerAddress 1,
      ⟨⟨⟨PUnit.unit, PUnit.unit⟩, PUnit.unit⟩, PUnit.unit⟩⟩, PUnit.unit⟩

/-- Both designated tops choose physical scope index zero, shared owner 42,
with different ordered branch roles. -/
def fixture_source_certificate :
    ClosedKernel (source leftFilling rightFilling) [] [] :=
  ⟨⟨left_certificate [0, 0] [0], right_certificate [0, 1] [0]⟩, PUnit.unit⟩
def fixture_target_certificate :
    ClosedKernel (target leftFilling rightFilling) [] [] :=
  scoped_permutation_equiv leftFilling rightFilling [] [] fixture_source_certificate

theorem left_requires_inherited_owner : ClosedKernel leftFilling [] [] → False := by
  intro certificate
  exact Fin.elim0 certificate.1.val
theorem right_requires_inherited_owner : ClosedKernel rightFilling [] [] → False := by
  intro certificate
  exact Fin.elim0 certificate.1.1.val

/-- A genuine proper native cut detaching the two actual payloads below the
source bottom.  The ordinary root is never selected. -/
def sourcePayloadCut (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    CKCut (source P Q) :=
  ⟨trivial, .ordinary _ _
    (.cons (bottomS P Q) .nil
      (.descend (.ordinary _ _
        (.cons P (.cons Q .nil) (.detach hP) (.cons Q .nil (.detach hQ) .nil))))
      .nil)⟩
def targetPayloadCut (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    CKCut (target P Q) :=
  ⟨trivial, .ordinary _ _
    (.cons (impTree P) (.cons (impTree Q) .nil)
      (.descend (.ordinary _ _ (.cons P .nil (.detach hP) .nil)))
      (.cons (impTree Q) .nil
        (.descend (.ordinary _ _ (.cons Q .nil (.detach hQ) .nil))) .nil))⟩

theorem source_payload_addresses (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    (sourcePayloadCut P Q hP hQ).orderedAddresses = [[0, 0], [0, 1]] := rfl
theorem target_payload_addresses (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    (targetPayloadCut P Q hP hQ).orderedAddresses = [[0, 0], [1, 0]] := rfl
theorem source_payload_tuple (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    (sourcePayloadCut P Q hP hQ).detachedTuple =
      [⟨[0, 0], GS, P, hP⟩, ⟨[0, 1], GS, Q, hQ⟩] := rfl
theorem target_payload_tuple (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    (targetPayloadCut P Q hP hQ).detachedTuple =
      [⟨[0, 0], GS, P, hP⟩, ⟨[1, 0], GS, Q, hQ⟩] := rfl
theorem source_payload_remainder (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    (sourcePayloadCut P Q hP hQ).remainder = sourceShell := rfl
theorem target_payload_remainder (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    (targetPayloadCut P Q hP hQ).remainder = targetShell := rfl
theorem source_payload_refill (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    let cut := sourcePayloadCut P Q hP hQ
    cut.fill cut.plan.detached = source P Q :=
  (sourcePayloadCut P Q hP hQ).fill_detached_reconstructs
theorem target_payload_refill (P Q : Tree GS) (hP : P.IsOrdinary) (hQ : Q.IsOrdinary) :
    let cut := targetPayloadCut P Q hP hQ
    cut.fill cut.plan.detached = target P Q :=
  (targetPayloadCut P Q hP hQ).fill_detached_reconstructs

def fixture_source_cut := sourcePayloadCut leftFilling rightFilling (by trivial) (by trivial)
def fixture_target_cut := targetPayloadCut leftFilling rightFilling (by trivial) (by trivial)

/-- The vacant slots ask their detached factors for certificates under the
scope supplied by this SAME remainder certificate.  Independent closure
would fail, as the two theorems immediately above establish. -/
def fixture_source_pieces :=
  branchEquiv (.descend fixture_source_cut.plan)
    (emptyProvider (source leftFilling rightFilling)) [] [] fixture_source_certificate
def fixture_target_pieces :=
  branchEquiv (.descend fixture_target_cut.plan)
    (emptyProvider (target leftFilling rightFilling)) [] [] fixture_target_certificate

theorem fixture_source_glue :
    (branchEquiv (.descend fixture_source_cut.plan)
      (emptyProvider (source leftFilling rightFilling)) [] []).symm fixture_source_pieces =
        fixture_source_certificate :=
  (branchEquiv (.descend fixture_source_cut.plan)
    (emptyProvider (source leftFilling rightFilling)) [] []).symm_apply_apply _
theorem fixture_target_glue :
    (branchEquiv (.descend fixture_target_cut.plan)
      (emptyProvider (target leftFilling rightFilling)) [] []).symm fixture_target_pieces =
        fixture_target_certificate :=
  (branchEquiv (.descend fixture_target_cut.plan)
    (emptyProvider (target leftFilling rightFilling)) [] []).symm_apply_apply _

#check scoped_permutation_equiv
#print axioms eligible_position_preserved
#print axioms readdressEquiv
#print axioms scoped_permutation_equiv
#check sourcePayloadCut
#print axioms source_payload_refill
#print axioms target_payload_refill
#print axioms fixture_source_glue
#print axioms fixture_target_glue

end Potkin.Research.DischargeCertificatePermutation

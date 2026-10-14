import Potkin.Research.D3SourceEncoding
import Potkin.Research.D3DischargeGrouping
import Potkin.Research.NativeDischargeReplacement

/-!
# Source discharge and native legality on the encoding image

Source events are computed from the independent source rule constructors.
Correctness requires an independent pending-discharge grouping, with stable
reference/declaration tokens. It is not defined as native legality or summary
success. The finite pending schedule equivalence is reused explicitly; a full
constructor-by-constructor erasure/decoration equivalence of unannotated source
derivations remains a stronger obligation.
-/

namespace Potkin.Research.D3SourceAdequacy
open D3SourceEncoding

structure Top where
  owner : Nat
  address : InternalAddress
  key : Nat
  role : Fin 2
  parameters : Parameters
  deriving DecidableEq

structure Bottom where
  uid : Nat
  address : InternalAddress
  key : Nat
  parameters : Parameters
  deriving DecidableEq

structure Events where
  tops : List Top
  bottoms : List Bottom

def append (a b : Events) : Events := ⟨a.tops ++ b.tops, a.bottoms ++ b.bottoms⟩

def rootEvents (address : InternalAddress) (key : Nat) : Rule → Events
  | .top role p owner _ _ => ⟨[⟨owner, address, key, role, p⟩], []⟩
  | .bottom p uid _ => ⟨[], [⟨uid, address, key, p⟩]⟩
  | _ => ⟨[], []⟩

mutual
def events : {S : D3SourceEncoding.Sequent} → Diagram S → InternalAddress → Events
  | _, .hole _, _ => ⟨[], []⟩
  | _, .rule key r children, address =>
      append (rootEvents address key r) (childEvents children address 0)
def childEvents : {Ss : List D3SourceEncoding.Sequent} → Children Ss → InternalAddress → Nat → Events
  | _, .nil, _, _ => ⟨[], []⟩
  | _, .cons head tail, address, slot =>
      append (events head (address ++ [slot])) (childEvents tail address (slot + 1))
end

def Eligible (t : Top) (b : Bottom) : Prop :=
  t.parameters = b.parameters ∧
    ∃ suffix, t.address = b.address ++ [t.role.val] ++ suffix

def Resolved (e : Events) : Prop :=
  ∀ t ∈ e.tops, ∃ b ∈ e.bottoms, Eligible t b ∧ t.owner = b.uid

/-- Ordinal physical indices retain multiplicity even if every visible field
is equal. Reverse preorder processes descendants before their ancestors. -/
def DischargeGrouping (e : Events) :=
  D3DischargeGrouping.Grouping
    (fun (t : Fin e.tops.length) (b : Fin e.bottoms.length) =>
      Eligible (e.tops.get t) (e.bottoms.get b) ∧
        (e.tops.get t).owner = (e.bottoms.get b).uid)
    (List.finRange e.tops.length) (List.finRange e.bottoms.length).reverse

theorem grouping_iff_resolved (e : Events) :
    Nonempty (DischargeGrouping e) ↔ Resolved e := by
  classical
  have h := D3DischargeGrouping.named_grouping_iff
    (fun (t : Fin e.tops.length) (b : Fin e.bottoms.length) =>
      Eligible (e.tops.get t) (e.bottoms.get b))
    (List.finRange e.tops.length) (List.finRange e.bottoms.length).reverse
    (fun t => by simp) (fun t => (e.tops.get t).owner) (fun b => (e.bottoms.get b).uid)
  constructor
  · intro grouped t ht
    rcases List.mem_iff_get.mp ht with ⟨i, hi⟩
    rcases h.mp grouped i (by simp) with ⟨b, _, hb⟩
    exact ⟨e.bottoms.get b, List.get_mem _ _, hi ▸ hb⟩
  · intro resolved
    apply h.mpr
    intro t _
    rcases resolved (e.tops.get t) (List.get_mem _ _) with ⟨b, hb, compatible⟩
    rcases List.mem_iff_get.mp hb with ⟨i, hi⟩
    exact ⟨i, by simp, hi.symm ▸ compatible⟩

/-- No implicit freshening: declaration collisions and invalid references are
inputs which fail this predicate. Closed-proof interpretation also needs completeness. -/
def SourceCorrect {S : D3SourceEncoding.Sequent} (D : Diagram S) : Prop :=
  LocallyCorrect D ∧ ((events D []).bottoms.map Bottom.uid).Nodup ∧
    Nonempty (DischargeGrouping (events D []))

/-- A closed source derivation, unlike a partially annotated typed diagram. -/
def CompleteSourceCorrect {S : D3SourceEncoding.Sequent} (D : Diagram S) : Prop :=
  D.Complete ∧ SourceCorrect D

def encodeTop (t : Top) : OpenDischarge.Requirement signature :=
  ⟨t.owner, t.address, t.key, t.role, encodeParameters t.parameters⟩
def encodeBottom (b : Bottom) : OpenDischarge.Grant signature :=
  ⟨b.uid, b.address, b.key, encodeParameters b.parameters⟩
def encodeEvents (e : Events) : OpenDischarge.Events signature :=
  ⟨e.tops.map encodeTop, e.bottoms.map encodeBottom⟩

@[simp] theorem encodeEvents_append (a b : Events) :
    encodeEvents (append a b) = (encodeEvents a).append (encodeEvents b) := by
  simp [encodeEvents, append, OpenDischarge.Events.append]

theorem encode_rootEvents (address : InternalAddress) (key : Nat) (r : Rule) :
    OpenDischarge.rootEvents address (occurrence key r) = encodeEvents (rootEvents address key r) := by
  cases r <;> rfl

mutual
theorem encode_events : {S : D3SourceEncoding.Sequent} → (D : Diagram S) → (address : InternalAddress) →
    OpenDischarge.events (encode D) address = encodeEvents (events D address)
  | _, .hole _, _ => rfl
  | _, .rule key r children, address => by
      change (OpenDischarge.rootEvents address (occurrence key r)).append
        (OpenDischarge.childEvents (encodeChildren children) address 0) = _
      rw [encode_rootEvents, encode_childEvents]
      exact (encodeEvents_append _ _).symm
theorem encode_childEvents : {Ss : List D3SourceEncoding.Sequent} → (Ds : Children Ss) →
    (address : InternalAddress) → (slot : Nat) →
    OpenDischarge.childEvents (encodeChildren Ds) address slot = encodeEvents (childEvents Ds address slot)
  | _, .nil, _, _ => rfl
  | _, .cons head tail, address, slot => by
      change (OpenDischarge.events (encode head) (address ++ [slot])).append
        (OpenDischarge.childEvents (encodeChildren tail) address (slot + 1)) = _
      rw [encode_events, encode_childEvents]
      exact (encodeEvents_append _ _).symm
end

theorem compatible_iff (t : Top) (b : Bottom) :
    OpenDischarge.Compatible (encodeTop t) (encodeBottom b) ↔ Eligible t b ∧ t.owner = b.uid := by
  change (t.owner = b.uid ∧ encodeParameters t.parameters = encodeParameters b.parameters ∧
    (∃ suffix, t.address = b.address ++ [t.role.val] ++ suffix)) ↔ _
  constructor
  · rintro ⟨owner, pack, branch⟩
    exact ⟨⟨encodeParameters_injective pack, branch⟩, owner⟩
  · rintro ⟨⟨pack, branch⟩, owner⟩
    exact ⟨owner, congrArg encodeParameters pack, branch⟩

theorem encoded_resolved_iff (e : Events) :
    OpenDischarge.LegalEvents (encodeEvents e) [] ↔ Resolved e := by
  constructor
  · intro legal t ht
    rcases legal (encodeTop t) (List.mem_map.mpr ⟨t, ht, rfl⟩) with ⟨g, hg, compatible⟩
    have member : g ∈ e.bottoms.map encodeBottom := by simpa [encodeEvents] using hg
    rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
    exact ⟨b, hb, (compatible_iff t b).mp compatible⟩
  · intro resolved r hr
    rcases List.mem_map.mp hr with ⟨t, ht, rfl⟩
    rcases resolved t ht with ⟨b, hb, compatible⟩
    refine ⟨encodeBottom b, ?_, (compatible_iff t b).mpr compatible⟩
    simpa [encodeEvents] using (List.mem_map.mpr ⟨b, hb, rfl⟩ : encodeBottom b ∈ e.bottoms.map encodeBottom)

/-- Universal source adequacy for the independently specified fragment on its
encoding image. No registry membership is smuggled into source correctness. -/
theorem source_correct_iff_native {S : D3SourceEncoding.Sequent} (D : Diagram S) :
    SourceCorrect D ↔ OpenDischarge.Legal Imp (encode D) [] [] := by
  unfold SourceCorrect OpenDischarge.Legal
  rw [exact_tree_iff, encode_events]
  change (_ ∧ ((events D []).bottoms.map Bottom.uid).Nodup ∧
    Nonempty (DischargeGrouping (events D []))) ↔
    (_ ∧ OpenDischarge.UniqueOwners (encodeEvents (events D [])) ∧
      OpenDischarge.LegalEvents (encodeEvents (events D [])) [])
  rw [grouping_iff_resolved, encoded_resolved_iff]
  simp only [OpenDischarge.UniqueOwners, encodeEvents, List.map_map]
  rfl

/-- Source completion transfer, with native physical hole transport and a
genuine typed exterior. The two source assemblies must be the actual encodings,
not merely have equal displayed boundaries. No validity/freshness premise. -/
theorem source_contextual_replacement
    {S : D3SourceEncoding.Sequent} (P P' : Diagram S)
    (interface : OpenDischarge.FixedOwnerInterface Imp (encode P) (encode P'))
    (F : P.Assignment) (F' : P'.Assignment)
    (matching : ∀ h, HEq (encodeAssignment P F h)
      (encodeAssignment P' F' (interface.holes h)))
    {O : D3SourceEncoding.Sequent} {E : Diagram O} {address : InternalAddress}
    (exterior : CKTree.PunctureAt (boundary S) (encode E) address)
    (left right : Diagram O)
    (left_encoding : encode left = exterior.insert (encode (P.fill F)))
    (right_encoding : encode right = exterior.insert (encode (P'.fill F'))) :
    SourceCorrect left ↔ SourceCorrect right := by
  rw [source_correct_iff_native, source_correct_iff_native,
    left_encoding, right_encoding, encode_fill, encode_fill]
  exact OpenDischarge.fixedOwner_replacement Imp interface
    (encodeAssignment P F) (encodeAssignment P' F') matching exterior

/-- Concrete source exterior and simultaneous source completions, using the
proved naturality maps rather than assuming their encoding equalities. -/
theorem source_completion_replacement
    {S : D3SourceEncoding.Sequent} (P P' : Diagram S)
    (interface : OpenDischarge.FixedOwnerInterface Imp (encode P) (encode P'))
    (F : P.Assignment) (F' : P'.Assignment)
    (matching : ∀ h, HEq (encodeAssignment P F h)
      (encodeAssignment P' F' (interface.holes h)))
    {O : D3SourceEncoding.Sequent} {E : Diagram O} {address : InternalAddress}
    (exterior : Diagram.PunctureAt S E address) :
    SourceCorrect (exterior.insert (P.fill F)) ↔
      SourceCorrect (exterior.insert (P'.fill F')) := by
  rw [source_correct_iff_native, source_correct_iff_native,
    encode_insert, encode_insert, encode_fill, encode_fill]
  exact OpenDischarge.fixedOwner_replacement Imp interface
    (encodeAssignment P F) (encodeAssignment P' F') matching (encodePuncture exterior)

theorem complete_source_replacement
    {S : D3SourceEncoding.Sequent} (P P' : Diagram S)
    (interface : OpenDischarge.FixedOwnerInterface Imp (encode P) (encode P'))
    (F : P.Assignment) (F' : P'.Assignment)
    (matching : ∀ h, HEq (encodeAssignment P F h)
      (encodeAssignment P' F' (interface.holes h)))
    {O : D3SourceEncoding.Sequent} {E : Diagram O} {address : InternalAddress}
    (exterior : Diagram.PunctureAt S E address)
    (completeLeft : (exterior.insert (P.fill F)).Complete)
    (completeRight : (exterior.insert (P'.fill F')).Complete) :
    CompleteSourceCorrect (exterior.insert (P.fill F)) ↔
      CompleteSourceCorrect (exterior.insert (P'.fill F')) := by
  simp only [CompleteSourceCorrect, completeLeft, completeRight, true_and]
  exact source_completion_replacement P P' interface F F' matching exterior

#check @source_correct_iff_native
#check @source_contextual_replacement
#check @source_completion_replacement
#print axioms grouping_iff_resolved
#print axioms encode_events
#print axioms source_correct_iff_native
#print axioms source_contextual_replacement
#print axioms source_completion_replacement
end Potkin.Research.D3SourceAdequacy

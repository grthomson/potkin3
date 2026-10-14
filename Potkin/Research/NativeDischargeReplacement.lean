import Potkin.Research.DischargeSummaryCongruence

/-!
# Fixed-owner replacement under native fillings and exterior contexts

Only boundary-facing metadata are projected: native proofs, physical vacancies,
typed assignments, and puncture insertion are unchanged. Owner UIDs and every
future reference are fixed. Actual top addresses remain in the source summary
and native certificates; an exterior ancestor cannot observe their local suffix.
-/

namespace Potkin.Research.OpenDischarge

universe u v
variable {sigma : Signature.{u, v}}

theorem rootAgreement_trans {a b c : Summary sigma}
    (first : RootAgreement a b) (second : RootAgreement b c) : RootAgreement a c :=
  ⟨first.conclusion.trans second.conclusion, first.inventory.trans second.inventory,
    first.requirements.trans second.requirements, first.ok.trans second.ok⟩

theorem forall₂_map_same {α β γ : Type*} (items : List α) (f : α → β) (g : α → γ)
    (relation : β → γ → Prop) (paired : ∀ item, relation (f item) (g item)) :
    List.Forall₂ relation (items.map f) (items.map g) := by
  induction items with
  | nil => exact .nil
  | cons head tail ih => exact .cons (paired head) ih

theorem rootAgreement_at
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (left right : InternalAddress) :
    RootAgreement (directSummary Imp tree left) (directSummary Imp tree right) := by
  constructor
  · rfl
  · exact (inventory_at Imp tree left).trans (inventory_at Imp tree right).symm
  · have normalized (address : InternalAddress) :
        (directSummary Imp tree address).requirements.map eraseRequirement =
          (directSummary Imp tree []).requirements.map eraseRequirement := by
      rw [requirements_at Imp tree address, Multiset.map_map]
      rfl
    exact (normalized left).trans (normalized right).symm
  · exact (ok_at_iff Imp tree left).trans (ok_at_iff Imp tree right).symm

theorem rootAgreement_of_heq
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G H : Hypersequent sigma} (left : CKTree sigma (Data sigma) G)
    (right : CKTree sigma (Data sigma) H) (boundary : G = H) (same : HEq left right)
    (leftAddress rightAddress : InternalAddress) :
    RootAgreement (directSummary Imp left leftAddress)
      (directSummary Imp right rightAddress) := by
  cases boundary
  cases same
  exact rootAgreement_at Imp left leftAddress rightAddress

/-- The rooted refinement used for native exterior congruence. This uses
checked field laws, not an assumption of composition or successful inputs.
The stronger all-field law additionally retains open-hole exposures. -/
theorem rootAgreement_fill
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (tree : CKTree sigma (Data sigma) G)
    (assignment : tree.LeafAssignment) :
    RootAgreement (directSummary Imp (tree.fillAssignment assignment) [])
      (composeSummary (directSummary Imp tree []) (attachedSummaries Imp tree assignment [])) := by
  refine ⟨conclusion_fill Imp tree assignment [], inventory_fill Imp tree assignment [],
    ?_, ok_fill_root Imp tree assignment⟩
  exact congrArg (Multiset.map eraseRequirement) (requirements_fill Imp tree assignment [])

/-- Equality of finite boundary-facing summaries.  The hole map is physical;
its order and exact typed boundary are explicit. No owner renaming occurs. -/
structure FixedOwnerInterface
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (source target : CKTree sigma (Data sigma) G) where
  holes : source.LeafOccurrence ≃ target.LeafOccurrence
  boundary : ∀ hole, source.leafBoundary hole = target.leafBoundary (holes hole)
  order : source.leafOrder.map holes = target.leafOrder
  root : RootAgreement (directSummary Imp source []) (directSummary Imp target [])
  exposure : ∀ hole,
    exposureAt (directSummary Imp source []) (source.leafAddress hole) =
      exposureAt (directSummary Imp target []) (target.leafAddress (holes hole))

/-- Literal equality of the full existing finite summaries is sufficient.
The declared physical-hole correspondence follows native premise order; its
exact boundary and address preservation are derived, not assumed. -/
noncomputable def fixedOwnerInterface_of_summaryEquality
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {source target : CKTree sigma (Data sigma) G}
    (equal : directSummary Imp source [] = directSummary Imp target []) :
    FixedOwnerInterface Imp source target := by
  refine ⟨fullSummary_holeEquiv Imp equal, fullSummary_holeEquiv_boundary Imp equal,
    fullSummary_holeEquiv_order Imp equal, ?_, ?_⟩
  · exact rootAgreement_of_eq equal
  · intro hole
    calc
      _ = exposureAt (directSummary Imp target []) (source.leafAddress hole) :=
        congrArg (fun summary => exposureAt summary (source.leafAddress hole)) equal
      _ = _ := congrArg (exposureAt (directSummary Imp target []))
        (fullSummary_holeEquiv_address Imp equal hole)

/-- All future assignments are allowed, including ones causing ownership
collisions or discharge failures. Only native typed matching is required. -/
theorem fixedOwner_fill_rootAgreement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} {source target : CKTree sigma (Data sigma) G}
    (interface : FixedOwnerInterface Imp source target)
    (left : source.LeafAssignment) (right : target.LeafAssignment)
    (matching : ∀ hole, HEq (left hole) (right (interface.holes hole))) :
    RootAgreement (directSummary Imp (source.fillAssignment left) [])
      (directSummary Imp (target.fillAssignment right) []) := by
  apply rootAgreement_trans (rootAgreement_fill Imp source left)
  apply rootAgreement_trans ?_ (rootAgreement_symm (rootAgreement_fill Imp target right))
  apply compose_rootAgreement interface.root ?_
    (attachment_holes Imp source left []) (attachment_holes Imp target right [])
  rw [attachedSummaries_eq_map, attachedSummaries_eq_map,
    ← interface.order, List.map_map]
  apply forall₂_map_same
  intro hole
  constructor
  · exact interface.boundary hole
  · exact rootAgreement_of_heq Imp (left hole) (right (interface.holes hole))
      (interface.boundary hole) (matching hole) _ _
  · simpa using interface.exposure hole

/-- A native thin shell, not another context representation. -/
def vacantChildren : (boundaries : List (Hypersequent sigma)) →
    CKChildren sigma (Data sigma) boundaries
  | [] => .nil
  | G :: rest => .cons (.interface G) (vacantChildren rest)

def premiseAssignment : {boundaries : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) boundaries) →
    (vacantChildren boundaries).LeafAssignment
  | _, .nil, hole => nomatch hole
  | _, .cons head tail, hole =>
      match hole with
      | Sum.inl _ => head
      | Sum.inr hole => premiseAssignment tail hole

theorem fill_vacantChildren : {boundaries : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) boundaries) →
    (vacantChildren boundaries).fillAssignment (premiseAssignment children) = children
  | _, .nil => rfl
  | _, .cons head tail => by
      change CKChildren.cons head
        ((vacantChildren _).fillAssignment (premiseAssignment tail)) = _
      rw [fill_vacantChildren tail]

def ChildrenRootAgreement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {boundaries : List (Hypersequent sigma)} →
    CKChildren sigma (Data sigma) boundaries → CKChildren sigma (Data sigma) boundaries → Prop
  | _, .nil, .nil => True
  | _, .cons left restLeft, .cons right restRight =>
      RootAgreement (directSummary Imp left []) (directSummary Imp right []) ∧
        ChildrenRootAgreement Imp restLeft restRight

theorem childrenRootAgreement_refl
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop) :
    {boundaries : List (Hypersequent sigma)} →
    (children : CKChildren sigma (Data sigma) boundaries) →
    ChildrenRootAgreement Imp children children
  | _, .nil => trivial
  | _, .cons head tail =>
      ⟨rootAgreement_refl _, childrenRootAgreement_refl Imp tail⟩

theorem thinAttachments_agree
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (parent : Summary sigma) : {boundaries : List (Hypersequent sigma)} →
    (left right : CKChildren sigma (Data sigma) boundaries) →
    ChildrenRootAgreement Imp left right →
    (address : InternalAddress) → (slot : Nat) →
    List.Forall₂ (AttachmentAgreement parent parent)
      (attachedChildSummaries Imp (vacantChildren boundaries) (premiseAssignment left)
        address slot)
      (attachedChildSummaries Imp (vacantChildren boundaries) (premiseAssignment right)
        address slot)
  | _, .nil, .nil, _, _, _ => .nil
  | _, .cons left restLeft, .cons right restRight, agree, address, slot => by
      change List.Forall₂ (AttachmentAgreement parent parent)
        ((⟨address ++ [slot], _⟩, directSummary Imp left (address ++ [slot])) :: _)
        ((⟨address ++ [slot], _⟩, directSummary Imp right (address ++ [slot])) :: _)
      apply List.Forall₂.cons
      · refine ⟨rfl, ?_, rfl⟩
        exact rootAgreement_trans (rootAgreement_at Imp left _ [])
          (rootAgreement_trans agree.1 (rootAgreement_at Imp right [] _))
      · exact thinAttachments_agree Imp parent restLeft restRight agree.2 address (slot + 1)

/-- Native ordinary-node congruence follows from the already checked compact
composition operation on its thin typed shell. Siblings stay ordered. -/
theorem ordinary_rootAgreement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    (o : LocalOccurrence sigma (Data sigma))
    (left right : CKChildren sigma (Data sigma) o.shape.premises)
    (agree : ChildrenRootAgreement Imp left right) :
    RootAgreement (directSummary Imp (.ordinary o left) [])
      (directSummary Imp (.ordinary o right) []) := by
  let shell : CKTree sigma (Data sigma) o.shape.conclusion :=
    .ordinary o (vacantChildren o.shape.premises)
  have filledLeft : shell.fillAssignment (premiseAssignment left) = .ordinary o left :=
    congrArg (CKTree.ordinary o) (fill_vacantChildren left)
  have filledRight : shell.fillAssignment (premiseAssignment right) = .ordinary o right :=
    congrArg (CKTree.ordinary o) (fill_vacantChildren right)
  rw [← filledLeft, ← filledRight]
  apply rootAgreement_trans (rootAgreement_fill Imp shell (premiseAssignment left))
  apply rootAgreement_trans ?_
    (rootAgreement_symm (rootAgreement_fill Imp shell (premiseAssignment right)))
  apply compose_rootAgreement (rootAgreement_refl _) ?_
    (attachment_holes Imp shell (premiseAssignment left) [])
    (attachment_holes Imp shell (premiseAssignment right) [])
  exact thinAttachments_agree Imp _ left right agree [] 0

mutual

/-- Every native typed exterior, including arbitrary unchanged siblings and
inherited vacancies. No successful-exterior assumption hides failures. -/
theorem exterior_rootAgreement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {H : Hypersequent sigma} (left right : CKTree sigma (Data sigma) H)
    (agree : RootAgreement (directSummary Imp left []) (directSummary Imp right [])) :
    {G : Hypersequent sigma} → {tree : CKTree sigma (Data sigma) G} →
    {address : InternalAddress} → (context : CKTree.PunctureAt H tree address) →
    RootAgreement (directSummary Imp (context.insert left) [])
      (directSummary Imp (context.insert right) [])
  | _, _, _, .root => agree
  | _, _, _, .child o children slot address below =>
      ordinary_rootAgreement Imp o _ _ (exterior_childrenRootAgreement Imp left right agree below)

theorem exterior_childrenRootAgreement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {H : Hypersequent sigma} (left right : CKTree sigma (Data sigma) H)
    (agree : RootAgreement (directSummary Imp left []) (directSummary Imp right [])) :
    {boundaries : List (Hypersequent sigma)} →
    {children : CKChildren sigma (Data sigma) boundaries} →
    {slot : Nat} → {address : InternalAddress} →
    (context : CKChildren.PunctureAt H children slot address) →
    ChildrenRootAgreement Imp (context.insert left) (context.insert right)
  | _, _, _, _, .head head tail address below =>
      ⟨exterior_rootAgreement Imp left right agree below, childrenRootAgreement_refl Imp tail⟩
  | _, _, _, _, .tail head tail slot address below =>
      ⟨rootAgreement_refl _, exterior_childrenRootAgreement Imp left right agree below⟩

end

theorem rootAgreement_legality
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {G : Hypersequent sigma} (left right : CKTree sigma (Data sigma) G)
    (agree : RootAgreement (directSummary Imp left []) (directSummary Imp right [])) :
    Legal Imp left [] [] ↔ Legal Imp right [] [] := by
  rw [closed_summary_agreement, closed_summary_agreement]
  have empty : (directSummary Imp left []).requirements = 0 ↔
      (directSummary Imp right []).requirements = 0 := by
    constructor
    · intro zero
      have mapped := agree.requirements
      rw [zero, Multiset.map_zero] at mapped
      simpa using mapped.symm
    · intro zero
      have mapped := agree.requirements
      rw [zero, Multiset.map_zero] at mapped
      simpa using mapped
  exact and_congr agree.ok empty

/-- The reusable contract: finite fixed-owner interface equality implies
replacement correctness under arbitrary matching future fillings AND every
native exterior. Ill-scoped inputs and declaration collisions reflect too. -/
theorem fixedOwner_replacement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {H : Hypersequent sigma} {source target : CKTree sigma (Data sigma) H}
    (interface : FixedOwnerInterface Imp source target)
    (left : source.LeafAssignment) (right : target.LeafAssignment)
    (matching : ∀ hole, HEq (left hole) (right (interface.holes hole)))
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    {address : InternalAddress} (context : CKTree.PunctureAt H tree address) :
    Legal Imp (context.insert (source.fillAssignment left)) [] [] ↔
      Legal Imp (context.insert (target.fillAssignment right)) [] [] := by
  apply rootAgreement_legality
  exact exterior_rootAgreement Imp _ _
    (fixedOwner_fill_rootAgreement Imp interface left right matching) context

/-- Full finite-summary equality alone supplies the physical matching map.
The donor at each matched hole is the same native typed tree, not a renamed
reference or a substituted registry snapshot. -/
theorem summaryEquality_replacement
    (Imp : Formula sigma → Formula sigma → Formula sigma → Prop)
    {H : Hypersequent sigma} {source target : CKTree sigma (Data sigma) H}
    (equal : directSummary Imp source [] = directSummary Imp target [])
    (left : source.LeafAssignment) (right : target.LeafAssignment)
    (matching : ∀ hole,
      HEq (left hole) (right (fullSummary_holeEquiv Imp equal hole)))
    {G : Hypersequent sigma} {tree : CKTree sigma (Data sigma) G}
    {address : InternalAddress} (context : CKTree.PunctureAt H tree address) :
    Legal Imp (context.insert (source.fillAssignment left)) [] [] ↔
      Legal Imp (context.insert (target.fillAssignment right)) [] [] :=
  fixedOwner_replacement Imp (fixedOwnerInterface_of_summaryEquality Imp equal)
    left right matching context

#check @fixedOwner_replacement
#print axioms fixedOwner_fill_rootAgreement
#print axioms exterior_rootAgreement
#print axioms fixedOwner_replacement
#print axioms summaryEquality_replacement

end Potkin.Research.OpenDischarge

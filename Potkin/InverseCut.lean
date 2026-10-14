import Potkin.InverseCutGeometry
import Potkin.IntrinsicCutIdentity
import Potkin.CKCutPuncture
import Potkin.CompositeCutExpansion
import Potkin.MaterialInstallation

/-!
# Native typed inverse cuts

The pointed observation is the EXISTING native `CKBranchCut`: descent is
an ordinary proper/empty cut; detachment is positive whole extraction to a
typed root interface; an interface has only the identity observation. Whole
extraction is not a fabricated CK root cut and is not the tensor-unit endpoint.

Assignments are indexed by every physical interface of the literal remainder.
The reverse map leaves inherited interfaces unchanged and supplies the FULL
detached tree at a new interface, including interfaces inside that provider.
-/

namespace Potkin
universe u v w
variable {sigma : Signature.{u, v}} {InstanceData : Type w}

def CKTree.rootObservation : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → CKBranchCut tree
  | _, .interface G => .descend (.interface G)
  | _, .ordinary _ _ => .detach trivial

theorem CKTree.rootObservation_remainder {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) : tree.rootObservation.remainder = .interface G := by
  cases tree <;> rfl

mutual
def CKTree.assignmentObservation : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
      CKBranchCut (tree.fillAssignment assignment)
  | _, .interface _, assignment => (assignment PUnit.unit).rootObservation
  | _, .ordinary o children, assignment =>
      .descend (.ordinary o (children.fillAssignment assignment)
        (children.assignmentCuts assignment))

def CKChildren.assignmentCuts : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) →
      (assignment : children.LeafAssignment) → CKChildCuts (children.fillAssignment assignment)
  | _, .nil, _ => .nil
  | _, .cons head tail, assignment =>
      .cons _ _ (head.assignmentObservation (fun h => assignment (.inl h)))
        (tail.assignmentCuts (fun h => assignment (.inr h)))
end

mutual
theorem CKTree.assignmentObservation_remainder : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
      (tree.assignmentObservation assignment).remainder = tree
  | _, .interface _, assignment => (assignment PUnit.unit).rootObservation_remainder
  | _, .ordinary o children, assignment =>
      congrArg (CKTree.ordinary o) (children.assignmentCuts_remainder assignment)

theorem CKChildren.assignmentCuts_remainder : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (assignment : children.LeafAssignment) →
      (children.assignmentCuts assignment).remainder = children
  | _, .nil, _ => rfl
  | _, .cons head tail, assignment =>
      congrArg₂ CKChildren.cons
        (head.assignmentObservation_remainder (fun h => assignment (.inl h)))
        (tail.assignmentCuts_remainder (fun h => assignment (.inr h)))
end

mutual
def CKCutPlan.leafAssignment : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) → cut.remainder.LeafAssignment
  | _, _, .interface G => fun _ => .interface G
  | _, _, .ordinary _ _ cuts => cuts.leafAssignment

def CKChildCuts.leafAssignment : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} →
      (cuts : CKChildCuts children) → cuts.remainder.LeafAssignment
  | _, _, .nil => fun hole => nomatch hole
  | _, _, .cons _ _ head tail => fun hole =>
      match hole with
      | Sum.inl hole => head.leafAssignment hole
      | Sum.inr hole => tail.leafAssignment hole

def CKBranchCut.leafAssignment : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) → cut.remainder.LeafAssignment
  | _, tree, .detach _ => fun _ => tree
  | _, _, .descend cut => cut.leafAssignment
end

mutual
theorem CKCutPlan.allHole_reconstruction : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKCutPlan tree) →
      cut.remainder.fillAssignment cut.leafAssignment = tree
  | _, _, .interface _ => rfl
  | _, _, .ordinary o _ cuts => congrArg (CKTree.ordinary o) cuts.allHole_reconstruction

theorem CKChildCuts.allHole_reconstruction : {Gs : List (Hypersequent sigma)} →
    {children : CKChildren sigma InstanceData Gs} → (cuts : CKChildCuts children) →
      cuts.remainder.fillAssignment cuts.leafAssignment = children
  | _, _, .nil => rfl
  | _, _, .cons _ _ head tail =>
      congrArg₂ CKChildren.cons head.allHole_reconstruction tail.allHole_reconstruction

theorem CKBranchCut.allHole_reconstruction : {G : Hypersequent sigma} →
    {tree : CKTree sigma InstanceData G} → (cut : CKBranchCut tree) →
      cut.remainder.fillAssignment cut.leafAssignment = tree
  | _, _, .detach _ => rfl
  | _, _, .descend cut => cut.allHole_reconstruction
end

/-- Fixed source and literal remainder determine the PUBLIC address cut.
This does not assert uniqueness from factor VALUES plus remainder. -/
theorem CKCut.eq_of_remainder_eq {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (left right : CKCut tree)
    (equal : left.remainder = right.remainder) : left = right := by
  apply CKCut.eq_of_addressFinset_eq
  apply Finset.ext
  intro address
  rw [CKCutPlan.mem_addressFinset_iff, CKCutPlan.mem_addressFinset_iff,
    ← left.vertexAndInterface_iff_selectedSite, ← right.vertexAndInterface_iff_selectedSite,
    equal]

theorem CKCutPlan.eq_of_remainder_eq {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (left right : CKCutPlan tree)
    (equal : left.remainder = right.remainder) : left = right := by
  cases tree with
  | interface G => cases left; cases right; rfl
  | ordinary o children =>
      have cuts : (⟨trivial, left⟩ : CKCut (.ordinary o children)) = ⟨trivial, right⟩ :=
        CKCut.eq_of_remainder_eq _ _ equal
      exact congrArg (fun c : CKCut (.ordinary o children) => c.plan) cuts

theorem CKBranchCut.eq_of_remainder_eq {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (left right : CKBranchCut tree)
    (equal : left.remainder = right.remainder) : left = right := by
  cases left with
  | detach ordinary =>
      cases right with
      | detach _ => rfl
      | descend plan =>
          cases plan with
          | interface _ => exact ordinary.elim
          | ordinary _ _ _ => contradiction
  | descend left =>
      cases right with
      | detach ordinary =>
          cases left with
          | interface _ => exact ordinary.elim
          | ordinary _ _ _ => contradiction
      | descend right => exact congrArg CKBranchCut.descend (left.eq_of_remainder_eq right equal)

/-- Only a sigma of existing native trees and observations, with a fixed
literal remainder predicate. No additional proof or cut syntax. -/
abbrev CKTree.CutAssembly {G : Hypersequent sigma} (remainder : CKTree sigma InstanceData G) :=
  (tree : CKTree sigma InstanceData G) ×
    {cut : CKBranchCut tree // cut.remainder = remainder}

def CKTree.CutAssembly.assignment {G : Hypersequent sigma}
    {remainder : CKTree sigma InstanceData G} (assembly : remainder.CutAssembly) :
    remainder.LeafAssignment := assembly.2.property ▸ assembly.2.val.leafAssignment

theorem CKTree.CutAssembly.reconstruction {G : Hypersequent sigma}
    {remainder : CKTree sigma InstanceData G} (assembly : remainder.CutAssembly) :
    remainder.fillAssignment assembly.assignment = assembly.1 := by
  rcases assembly with ⟨tree, cut, equal⟩
  cases equal
  exact cut.allHole_reconstruction

theorem CKTree.CutAssembly.ext_source {G : Hypersequent sigma}
    {remainder : CKTree sigma InstanceData G} (left right : remainder.CutAssembly)
    (equal : left.1 = right.1) : left = right := by
  rcases left with ⟨tree, left, leftR⟩
  rcases right with ⟨tree', right, rightR⟩
  cases equal
  have cuts := left.eq_of_remainder_eq right (leftR.trans rightR.symm)
  cases cuts
  rfl

/-- The witness-level inverse-cut theorem for arbitrary native typed open
trees, with both inverse laws. It includes all three pointed endpoint cases. -/
def CKTree.leafAssignmentCutEquiv {G : Hypersequent sigma}
    (remainder : CKTree sigma InstanceData G) : remainder.LeafAssignment ≃ remainder.CutAssembly where
  toFun assignment := ⟨remainder.fillAssignment assignment,
    remainder.assignmentObservation assignment, remainder.assignmentObservation_remainder assignment⟩
  invFun := CKTree.CutAssembly.assignment
  left_inv assignment := remainder.fillAssignment_injective
    (CKTree.CutAssembly.reconstruction _)
  right_inv assembly := CKTree.CutAssembly.ext_source _ _ assembly.reconstruction

/-- Ordinary remainders give actual native CK cuts, never a root cut. -/
def CKTree.assignmentProperCut {G : Hypersequent sigma}
    (remainder : CKTree sigma InstanceData G) (ordinary : remainder.IsOrdinary)
    (assignment : remainder.LeafAssignment) : CKCut (remainder.fillAssignment assignment) := by
  cases remainder with
  | interface _ => exact ordinary.elim
  | ordinary o children =>
      exact ⟨trivial, .ordinary o (children.fillAssignment assignment)
        (children.assignmentCuts assignment)⟩

def CKTree.assignmentPublicCut {G : Hypersequent sigma}
    (remainder : CKTree sigma InstanceData G) (ordinary : remainder.IsOrdinary)
    (assignment : remainder.LeafAssignment) :
    ExtensionalCKCut (remainder.fillAssignment assignment) :=
  ExtensionalCKCut.ofCKCut (remainder.assignmentProperCut ordinary assignment)

theorem CKTree.assignmentProperCut_remainder {G : Hypersequent sigma}
    (remainder : CKTree sigma InstanceData G) (ordinary : remainder.IsOrdinary)
    (assignment : remainder.LeafAssignment) :
    (remainder.assignmentProperCut ordinary assignment).remainder = remainder := by
  cases remainder with
  | interface _ => exact ordinary.elim
  | ordinary o children => exact congrArg (CKTree.ordinary o) (children.assignmentCuts_remainder assignment)

theorem CKTree.assignmentProperCut_native_refill {G : Hypersequent sigma}
    (remainder : CKTree sigma InstanceData G) (ordinary : remainder.IsOrdinary)
    (assignment : remainder.LeafAssignment) :
    let cut := remainder.assignmentProperCut ordinary assignment
    cut.fill cut.plan.detached = remainder.fillAssignment assignment :=
  (remainder.assignmentProperCut ordinary assignment).plan.fill_detached_reconstructs

mutual
theorem CKCutPlan.leafAssignment_locallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (cut : CKCutPlan tree) → LocallyAdmittedTree P tree →
      ∀ hole, LocallyAdmittedTree P (cut.leafAssignment hole)
  | _, _, .interface _, _, _ => trivial
  | _, _, .ordinary _ _ children, admitted, hole =>
      children.leafAssignment_locallyAdmitted admitted.2 hole

theorem CKChildCuts.leafAssignment_locallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {Gs : List (Hypersequent sigma)} → {children : CKChildren sigma InstanceData Gs} →
    (cuts : CKChildCuts children) → LocallyAdmittedChildren P children →
      ∀ hole, LocallyAdmittedTree P (cuts.leafAssignment hole)
  | _, _, .nil, _, hole => nomatch hole
  | _, _, .cons _ _ head tail, admitted, hole =>
      match hole with
      | Sum.inl hole => head.leafAssignment_locallyAdmitted admitted.1 hole
      | Sum.inr hole => tail.leafAssignment_locallyAdmitted admitted.2 hole

theorem CKBranchCut.leafAssignment_locallyAdmitted
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} → {tree : CKTree sigma InstanceData G} →
    (cut : CKBranchCut tree) → LocallyAdmittedTree P tree →
      ∀ hole, LocallyAdmittedTree P (cut.leafAssignment hole)
  | _, _, .detach _, admitted, _ => admitted
  | _, _, .descend cut, admitted, hole => cut.leafAssignment_locallyAdmitted admitted hole
end

variable {pi : PrimitiveFragment sigma}

theorem CKTree.rootObservation_material_iff (B : MaterialBase sigma InstanceData pi)
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    tree.rootObservation.DetachedInBase B ↔ tree.AllVerticesInBase B := by
  cases tree with
  | interface G =>
      constructor
      · intro _; trivial
      · intro _ site; exact nomatch site
  | ordinary o children =>
      constructor
      · intro pure; exact pure PUnit.unit
      · intro pure site; cases site; exact pure

mutual
theorem CKTree.assignmentObservation_material_iff (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} → (tree : CKTree sigma InstanceData G) →
    (assignment : tree.LeafAssignment) →
      (tree.assignmentObservation assignment).DetachedInBase B ↔
        ∀ hole, (assignment hole).AllVerticesInBase B
  | _, .interface _, assignment => by
      constructor
      · intro pure hole
        cases hole
        exact ((assignment PUnit.unit).rootObservation_material_iff B).mp pure
      · intro pure
        exact ((assignment PUnit.unit).rootObservation_material_iff B).mpr (pure PUnit.unit)
  | _, .ordinary _ children, assignment => children.assignmentCuts_material_iff B assignment

theorem CKChildren.assignmentCuts_material_iff (B : MaterialBase sigma InstanceData pi) :
    {Gs : List (Hypersequent sigma)} → (children : CKChildren sigma InstanceData Gs) →
    (assignment : children.LeafAssignment) →
      (children.assignmentCuts assignment).DetachedInBase B ↔
        ∀ hole, (assignment hole).AllVerticesInBase B
  | _, .nil, _ => by constructor <;> intro _ hole <;> exact nomatch hole
  | _, .cons head tail, assignment => by
      constructor
      · intro pure hole
        cases hole with
        | inl hole =>
            exact (head.assignmentObservation_material_iff B _).mp
              (fun site => pure (.inl site)) hole
        | inr hole =>
            exact (tail.assignmentCuts_material_iff B _).mp
              (fun site => pure (.inr site)) hole
      · intro pure site
        cases site with
        | inl site =>
            exact (head.assignmentObservation_material_iff B _).mpr
              (fun hole => pure (.inl hole)) site
        | inr site =>
            exact (tail.assignmentCuts_material_iff B _).mpr
              (fun hole => pure (.inr hole)) site
end


def CKCutEntry.mapAddress (f : InternalAddress → InternalAddress)
    (entry : CKCutEntry sigma InstanceData) : CKCutEntry sigma InstanceData :=
  {entry with address := f entry.address}

def CKTree.positiveEntry (address : InternalAddress) : {G : Hypersequent sigma} →
    CKTree sigma InstanceData G → Option (CKCutEntry sigma InstanceData)
  | _, .interface _ => none
  | _, .ordinary o children => some ⟨address, o.shape.conclusion, .ordinary o children, trivial⟩

theorem CKTree.positiveEntry_mapAddress (f : InternalAddress → InternalAddress)
    (address : InternalAddress) {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    (tree.positiveEntry address).map (CKCutEntry.mapAddress f) = tree.positiveEntry (f address) := by
  cases tree <;> rfl

def CKCutPlan.addressedTuple {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCutPlan tree) : List (CKCutEntry sigma InstanceData) :=
  cut.siteOrder.map (fun site => ⟨cut.address site, cut.siteBoundary site,
    cut.detached site, cut.detachedOrdinary site⟩)

def CKChildCuts.addressedTuple {Gs : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData Gs} (cut : CKChildCuts children) :
    List (CKCutEntry sigma InstanceData) :=
  cut.siteOrder.map (fun site => ⟨cut.address site, cut.siteBoundary site,
    cut.detached site, cut.detachedOrdinary site⟩)

def CKBranchCut.addressedTuple {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKBranchCut tree) : List (CKCutEntry sigma InstanceData) :=
  cut.siteOrder.map (fun site => ⟨cut.relativeAddress site, cut.siteBoundary site,
    cut.detached site, cut.detachedOrdinary site⟩)

theorem CKChildCuts.addressedTuple_cons {G : Hypersequent sigma}
    {Gs : List (Hypersequent sigma)} (head : CKTree sigma InstanceData G)
    (tail : CKChildren sigma InstanceData Gs) (hc : CKBranchCut head) (tc : CKChildCuts tail) :
    (CKChildCuts.cons head tail hc tc).addressedTuple =
      hc.addressedTuple.map (CKCutEntry.mapAddress (List.cons 0)) ++
        tc.addressedTuple.map (CKCutEntry.mapAddress InternalAddress.shiftHead) := by
  change (hc.siteOrder.map (Sum.inl : hc.Site → hc.Site ⊕ tc.Site) ++
    tc.siteOrder.map Sum.inr).map (fun site : hc.Site ⊕ tc.Site =>
      (⟨(CKChildCuts.cons head tail hc tc).address site,
        (CKChildCuts.cons head tail hc tc).siteBoundary site,
        (CKChildCuts.cons head tail hc tc).detached site,
        (CKChildCuts.cons head tail hc tc).detachedOrdinary site⟩ : CKCutEntry sigma InstanceData)) = _
  rw [List.map_append, List.map_map, List.map_map]
  simp only [CKBranchCut.addressedTuple, CKChildCuts.addressedTuple, List.map_map]
  rfl

theorem CKTree.rootObservation_tuple {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) :
    tree.rootObservation.addressedTuple = (tree.positiveEntry []).toList := by
  cases tree <;> rfl

mutual
/-- Exact boundaries, FULL positive providers, physical addresses, canonical
premise order and repeated equal provider occurrences all survive. -/
theorem CKTree.assignmentObservation_tuple : {G : Hypersequent sigma} →
    (tree : CKTree sigma InstanceData G) → (assignment : tree.LeafAssignment) →
      (tree.assignmentObservation assignment).addressedTuple =
        tree.leafOrder.filterMap (fun hole =>
          (assignment hole).positiveEntry (tree.leafAddress hole))
  | _, .interface _, assignment => by
      change (assignment PUnit.unit).rootObservation.addressedTuple =
        ((assignment PUnit.unit).positiveEntry []).toList
      exact (assignment PUnit.unit).rootObservation_tuple
  | _, .ordinary _ children, assignment => children.assignmentCuts_tuple assignment

theorem CKChildren.assignmentCuts_tuple : {Gs : List (Hypersequent sigma)} →
    (children : CKChildren sigma InstanceData Gs) → (assignment : children.LeafAssignment) →
      (children.assignmentCuts assignment).addressedTuple =
        children.leafOrder.filterMap (fun hole =>
          (assignment hole).positiveEntry (children.leafAddress hole))
  | _, .nil, _ => rfl
  | _, .cons head tail, assignment => by
      change (CKChildCuts.cons _ _ (head.assignmentObservation (fun h => assignment (.inl h)))
        (tail.assignmentCuts (fun h => assignment (.inr h)))).addressedTuple = _
      rw [CKChildCuts.addressedTuple_cons, head.assignmentObservation_tuple, tail.assignmentCuts_tuple]
      change (head.leafOrder.filterMap (fun h =>
          (assignment (.inl h)).positiveEntry (head.leafAddress h))).map
            (CKCutEntry.mapAddress (List.cons 0)) ++
        (tail.leafOrder.filterMap (fun h =>
          (assignment (.inr h)).positiveEntry (tail.leafAddress h))).map
            (CKCutEntry.mapAddress InternalAddress.shiftHead) =
        (head.leafOrder.map (Sum.inl : head.LeafOccurrence →
          head.LeafOccurrence ⊕ tail.LeafOccurrence) ++ tail.leafOrder.map Sum.inr).filterMap
          (fun h : head.LeafOccurrence ⊕ tail.LeafOccurrence =>
            (assignment h).positiveEntry ((CKChildren.cons head tail).leafAddress h))
      simp only [List.filterMap_append, List.filterMap_map,
        List.map_filterMap, Function.comp_def, CKChildren.leafAddress]
      congr 1 <;> apply List.filterMap_congr <;> intro hole _ <;>
        exact CKTree.positiveEntry_mapAddress _ _ _
end

theorem CKTree.assignmentProperCut_detachedTuple {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) (ordinary : tree.IsOrdinary)
    (assignment : tree.LeafAssignment) :
    (tree.assignmentProperCut ordinary assignment).detachedTuple =
      tree.leafOrder.filterMap (fun hole => (assignment hole).positiveEntry (tree.leafAddress hole)) := by
  cases tree with
  | interface _ => exact ordinary.elim
  | ordinary _ children => exact children.assignmentCuts_tuple assignment

/-- Reverse classification is addressed, not guessed from collected factors:
the positive reverse providers are exactly the native selected entries.
Every other physical remainder interface receives its unchanged interface. -/
theorem CKBranchCut.inverse_assignment_tuple {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKBranchCut tree) :
    cut.addressedTuple = cut.remainder.leafOrder.filterMap (fun hole =>
      (cut.leafAssignment hole).positiveEntry (cut.remainder.leafAddress hole)) := by
  let assembly : cut.remainder.CutAssembly := ⟨tree, cut, rfl⟩
  have inverse := cut.remainder.leafAssignmentCutEquiv.right_inv assembly
  have tuples := congrArg (fun a : cut.remainder.CutAssembly => a.2.val.addressedTuple) inverse
  exact tuples.symm.trans (cut.remainder.assignmentObservation_tuple cut.leafAssignment)

/-- An all-interface assignment gives the empty positive coefficient. -/
theorem CKTree.assignment_no_positive_tuple {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) (assignment : tree.LeafAssignment)
    (unchanged : ∀ hole, assignment hole = .interface (tree.leafBoundary hole)) :
    (tree.assignmentObservation assignment).addressedTuple = [] := by
  rw [tree.assignmentObservation_tuple]
  have noPositive : (fun hole => (assignment hole).positiveEntry (tree.leafAddress hole)) =
      (fun _ => none) := by
    funext hole
    rw [unchanged hole]
    rfl
  rw [noPositive]
  simp

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

theorem CKTree.CutAssembly.assignment_locallyAdmitted {G : Hypersequent sigma}
    {remainder : CKTree sigma InstanceData G} (assembly : remainder.CutAssembly)
    (admitted : LocallyAdmittedTree P assembly.1) :
    ∀ hole, LocallyAdmittedTree P (assembly.assignment hole) := by
  rcases assembly with ⟨tree, cut, equal⟩
  cases equal
  exact cut.leafAssignment_locallyAdmitted admitted

/-- Admission is in ONE fixed equipped registry, for all retained exact
occurrences and all providers; it is not a rule-kind/name approximation. -/
def CKTree.admittedLeafAssignmentCutEquiv {G : Hypersequent sigma}
    (remainder : CKTree sigma InstanceData G) (admitted : LocallyAdmittedTree P remainder) :
    {assignment : remainder.LeafAssignment // ∀ hole, LocallyAdmittedTree P (assignment hole)} ≃
      {assembly : remainder.CutAssembly // LocallyAdmittedTree P assembly.1} where
  toFun assignment := ⟨remainder.leafAssignmentCutEquiv assignment.val,
    remainder.fillAssignment_locallyAdmitted assignment.val admitted assignment.property⟩
  invFun assembly := ⟨assembly.val.assignment, assembly.val.assignment_locallyAdmitted assembly.property⟩
  left_inv assignment := Subtype.ext (remainder.leafAssignmentCutEquiv.left_inv assignment.val)
  right_inv assembly := Subtype.ext (remainder.leafAssignmentCutEquiv.right_inv assembly.val)


theorem CKTree.CutAssembly.assignment_material_iff {G : Hypersequent sigma}
    {remainder : CKTree sigma InstanceData G} (B : MaterialBase sigma InstanceData pi)
    (assembly : remainder.CutAssembly) :
    (∀ hole, (assembly.assignment hole).AllVerticesInBase B) ↔
      assembly.2.val.DetachedInBase B := by
  have same := remainder.leafAssignmentCutEquiv.right_inv assembly
  have pure := remainder.assignmentObservation_material_iff B assembly.assignment
  have predicate := congrArg (fun a : remainder.CutAssembly => a.2.val.DetachedInBase B) same
  change (remainder.assignmentObservation assembly.assignment).DetachedInBase B =
    assembly.2.val.DetachedInBase B at predicate
  exact pure.symm.trans ⟨Eq.mp predicate, Eq.mpr predicate⟩

/-- Exact selected-base restriction; positive OPEN providers are allowed.
The retained remainder need NOT be material. -/
def CKTree.materialLeafAssignmentCutEquiv {G : Hypersequent sigma}
    (remainder : CKTree sigma InstanceData G) (B : MaterialBase sigma InstanceData pi) :
    {assignment : remainder.LeafAssignment // ∀ hole, (assignment hole).AllVerticesInBase B} ≃
      {assembly : remainder.CutAssembly // assembly.2.val.DetachedInBase B} where
  toFun assignment := ⟨remainder.leafAssignmentCutEquiv assignment.val,
    (remainder.assignmentObservation_material_iff B assignment.val).mpr assignment.property⟩
  invFun assembly := ⟨assembly.val.assignment,
    (assembly.val.assignment_material_iff B).mpr assembly.property⟩
  left_inv assignment := Subtype.ext (remainder.leafAssignmentCutEquiv.left_inv assignment.val)
  right_inv assembly := Subtype.ext (remainder.leafAssignmentCutEquiv.right_inv assembly.val)


end Potkin

#print axioms Potkin.CKCut.eq_of_remainder_eq
#print axioms Potkin.CKBranchCut.allHole_reconstruction
#print axioms Potkin.CKTree.leafAssignmentCutEquiv
#print axioms Potkin.CKTree.assignmentProperCut_detachedTuple
#print axioms Potkin.CKBranchCut.inverse_assignment_tuple
#print axioms Potkin.CKTree.admittedLeafAssignmentCutEquiv
#print axioms Potkin.CKTree.materialLeafAssignmentCutEquiv

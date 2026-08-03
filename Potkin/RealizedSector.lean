import Potkin.Checked

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

mutual

/--
An ambient open CK tree is locally admitted by one exact equipped
presentation when every ordinary vertex is the exact occurrence of that
presentation and all of its ordered children are locally admitted.  Typed
interfaces are admitted vacancies and do not assert a proof constructor.
-/
def LocallyAdmittedTree (P : EquippedPresentation T) :
    {G : Hypersequent sigma} -> CKTree sigma InstanceData G -> Prop
  | _, .interface _ => True
  | _, .ordinary o children =>
      o ∈ P.registry ∧ LocallyAdmittedChildren P children

/-- Local admission of an exact ordered boundary-indexed child tuple. -/
def LocallyAdmittedChildren (P : EquippedPresentation T) :
    {boundaries : List (Hypersequent sigma)} ->
      CKChildren sigma InstanceData boundaries -> Prop
  | _, .nil => True
  | _, .cons head tail =>
      LocallyAdmittedTree P head ∧ LocallyAdmittedChildren P tail

end

namespace LocallyAdmittedChildren

/-- Every ordered child of a locally admitted child tuple is locally admitted. -/
theorem get {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (admitted : LocallyAdmittedChildren P children)
    (i : Fin boundaries.length) :
    LocallyAdmittedTree P (children.get i) := by
  induction boundaries with
  | nil => exact Fin.elim0 i
  | cons G Gs ih =>
      cases children with
      | cons head tail =>
          rcases admitted with ⟨headAdmitted, tailAdmitted⟩
          cases i using Fin.cases with
          | zero => exact headAdmitted
          | succ i => exact ih tailAdmitted i

end LocallyAdmittedChildren

namespace LocallyAdmittedTree

/-- Exact registry membership at every admitted ordinary root. -/
theorem registered {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (admitted : LocallyAdmittedTree P (.ordinary o children)) :
    o ∈ P.registry :=
  admitted.1

/-- The presentation therefore supplies proof-theory admission at the root. -/
theorem rootAdmitted {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (admitted : LocallyAdmittedTree P (.ordinary o children)) :
    T.Admits o :=
  P.admitted o admitted.registered

/-- The exact ordered children below an admitted ordinary root are admitted. -/
theorem children {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (admitted : LocallyAdmittedTree P (.ordinary o children)) :
    LocallyAdmittedChildren P children :=
  admitted.2

/-- Admission is hereditary to every immediate premise slot. -/
theorem child {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (admitted : LocallyAdmittedTree P (.ordinary o children))
    (i : Fin o.shape.premises.length) :
    LocallyAdmittedTree P (children.get i) :=
  admitted.children.get i

end LocallyAdmittedTree

namespace CKTree

/--
The reflexive descendant relation on the ambient CK carrier.  A constructor
step records one exact ordered premise slot, so induction over this relation
is suitable for arbitrary finite vertex paths without treating an interface
as a vertex.
-/
inductive IsDescendant :
    {G H : Hypersequent sigma} ->
      CKTree sigma InstanceData G -> CKTree sigma InstanceData H -> Prop where
  | refl (tree : CKTree sigma InstanceData G) : IsDescendant tree tree
  | child (o : LocalOccurrence sigma InstanceData)
      (children : CKChildren sigma InstanceData o.shape.premises)
      (i : Fin o.shape.premises.length)
      {H : Hypersequent sigma} {tree : CKTree sigma InstanceData H}
      (below : IsDescendant (children.get i) tree) :
      IsDescendant (.ordinary o children) tree

end CKTree

namespace LocallyAdmittedTree

/-- Local admission is hereditary along every finite descendant path. -/
theorem descendant {G H : Hypersequent sigma}
    {source : CKTree sigma InstanceData G}
    {tree : CKTree sigma InstanceData H}
    (sourceAdmitted : LocallyAdmittedTree P source)
    (below : CKTree.IsDescendant source tree) :
    LocallyAdmittedTree P tree := by
  induction below with
  | refl => exact sourceAdmitted
  | child o children i below ih =>
      exact ih (sourceAdmitted.child i)

end LocallyAdmittedTree

mutual

/-- Local admission is preserved when the presentation base is transported. -/
def LocallyAdmittedTree.mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
      LocallyAdmittedTree P tree ->
        LocallyAdmittedTree (P.mapBase f) tree
  | _, .interface _, _ => trivial
  | _, .ordinary _ children, admitted =>
      ⟨by simpa using admitted.1,
        LocallyAdmittedChildren.mapBase f admitted.2⟩

/-- Base transport preserves admission of every ordered child. -/
def LocallyAdmittedChildren.mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) :
    {boundaries : List (Hypersequent sigma)} ->
      {children : CKChildren sigma InstanceData boundaries} ->
      LocallyAdmittedChildren P children ->
        LocallyAdmittedChildren (P.mapBase f) children
  | _, .nil, _ => trivial
  | _, .cons _ _, admitted =>
      ⟨LocallyAdmittedTree.mapBase f admitted.1,
        LocallyAdmittedChildren.mapBase f admitted.2⟩

end

/-- Realization of a complete checked derivation is locally admitted. -/
def CheckedDerivation.realizeLocallyAdmitted
    {G : Hypersequent sigma} (derivation : CheckedDerivation P G) :
    LocallyAdmittedTree P derivation.realize :=
  CheckedDerivation.rec
    (motive_1 := fun _ derivation =>
      LocallyAdmittedTree P derivation.realize)
    (motive_2 := fun _ children =>
      LocallyAdmittedChildren P
        (CheckedDerivation.CheckedChildren.realize children))
    (fun _ registered _ childrenAdmitted => by
      simpa only [CheckedDerivation.realize, LocallyAdmittedTree] using
        And.intro registered childrenAdmitted)
    (by
      simp only [CheckedDerivation.CheckedChildren.realize,
        LocallyAdmittedChildren])
    (fun _ _ headAdmitted tailAdmitted => by
      simpa only [CheckedDerivation.CheckedChildren.realize,
        LocallyAdmittedChildren] using
        And.intro headAdmitted tailAdmitted)
    derivation

/-- The realized ordered children of a checked node are locally admitted. -/
def CheckedChildren.realizeLocallyAdmitted
    {boundaries : List (Hypersequent sigma)}
    (children : CheckedChildren P boundaries) :
    LocallyAdmittedChildren P
      (CheckedDerivation.CheckedChildren.realize children) :=
  CheckedChildren.rec
    (motive_1 := fun _ derivation =>
      LocallyAdmittedTree P derivation.realize)
    (motive_2 := fun _ children =>
      LocallyAdmittedChildren P
        (CheckedDerivation.CheckedChildren.realize children))
    (fun _ registered _ childrenAdmitted => by
      simpa only [CheckedDerivation.realize, LocallyAdmittedTree] using
        And.intro registered childrenAdmitted)
    (by
      simp only [CheckedDerivation.CheckedChildren.realize,
        LocallyAdmittedChildren])
    (fun _ _ headAdmitted tailAdmitted => by
      simpa only [CheckedDerivation.CheckedChildren.realize,
        LocallyAdmittedChildren] using
        And.intro headAdmitted tailAdmitted)
    children

/--
A realised open connected component is a positive ambient CK component whose
ordinary vertices are admitted by one exact equipped presentation.  It may
contain any number of typed interfaces below its ordinary root.
-/
structure RealizedOpenComponent (P : EquippedPresentation T) where
  component : CKComponent sigma InstanceData
  locallyAdmitted : LocallyAdmittedTree P component.tree

namespace RealizedOpenComponent

/-- Package any positive locally admitted tree as a realised open component. -/
def ofTree {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) (admitted : LocallyAdmittedTree P tree) :
    RealizedOpenComponent P where
  component := { boundary := G, tree := tree, ordinary := ordinary }
  locallyAdmitted := admitted

/-- Proof-preserving base transport leaves the ambient component unchanged. -/
def mapBase {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C)
    (component : RealizedOpenComponent P) :
    RealizedOpenComponent (P.mapBase f) where
  component := component.component
  locallyAdmitted := component.locallyAdmitted.mapBase f

/-- Identity material inclusion leaves a realised component unchanged. -/
theorem mapBase_id_heq (component : RealizedOpenComponent P) :
    HEq (component.mapBase (BaseHom.id T.base)) component := by
  cases component
  rfl

/-- Realised-component transport respects composition of inclusions. -/
theorem mapBase_comp_heq
    {C D : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (g : BaseHom C D)
    (component : RealizedOpenComponent P) :
    HEq ((component.mapBase f).mapBase g)
      (component.mapBase (g.comp f)) := by
  cases component
  rfl

/-- A positive ordinary descendant of a realised component is realised. -/
def ofDescendant (component : RealizedOpenComponent P)
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (below : CKTree.IsDescendant component.component.tree tree)
    (ordinary : tree.IsOrdinary) : RealizedOpenComponent P :=
  ofTree tree ordinary (component.locallyAdmitted.descendant below)

end RealizedOpenComponent

namespace CheckedDerivation

/-- Every complete checked proof determines a positive realised open component. -/
def realizedOpenComponent {G : Hypersequent sigma}
    (derivation : CheckedDerivation P G) : RealizedOpenComponent P :=
  RealizedOpenComponent.ofTree derivation.realize
    derivation.realize_isOrdinary derivation.realizeLocallyAdmitted

/-- The mapped complete proof remains in the transported realised open sector. -/
theorem realizeLocallyAdmitted_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) {G : Hypersequent sigma}
    (derivation : CheckedDerivation P G) :
    LocallyAdmittedTree (P.mapBase f) (derivation.mapBase f).realize :=
  (derivation.mapBase f).realizeLocallyAdmitted

end CheckedDerivation

/-- External forests of positive realised open components retain multiplicity. -/
abbrev RealizedOpenForest (P : EquippedPresentation T) :=
  Multiset (RealizedOpenComponent P)

end Potkin

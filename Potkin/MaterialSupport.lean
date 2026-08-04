import Potkin.RealizedCut

/-!
# Exact material-base occurrence support

Material dependence is recorded at every occurrence address in an admitted
decorated CK tree.  The primary carrier is proof-relevant and keeps the exact
`LocalOccurrence` together with its occurrence-indexed base membership.
Forgetting addresses produces a `Multiset`, so repeated uses remain repeated
without imposing decidable equality on instance or incidence data.
-/

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

namespace MaterialBase

/-- One exact occurrence-indexed member of a material base. -/
structure ExactOccurrence
    {pi : PrimitiveFragment sigma}
    (B : MaterialBase sigma InstanceData pi) where
  occurrence : LocalOccurrence sigma InstanceData
  member : B.Member occurrence

namespace ExactOccurrence

variable {pi : PrimitiveFragment sigma}
variable {B C : MaterialBase sigma InstanceData pi}

@[ext]
theorem ext {left right : ExactOccurrence B}
    (occurrence : left.occurrence = right.occurrence) : left = right := by
  cases left
  cases right
  cases occurrence
  rfl

/-- Persistent base inclusion changes only membership evidence. -/
def map (f : BaseHom B C) (occurrence : ExactOccurrence B) :
    ExactOccurrence C :=
  { occurrence := occurrence.occurrence
    member := f.map_member occurrence.member }

@[simp]
theorem map_occurrence (f : BaseHom B C) (occurrence : ExactOccurrence B) :
    (occurrence.map f).occurrence = occurrence.occurrence := rfl

theorem map_injective (f : BaseHom B C) :
    Function.Injective (map f) := by
  intro left right equal
  apply ext
  exact congrArg
    (fun occurrence : ExactOccurrence C => occurrence.occurrence) equal

end ExactOccurrence

end MaterialBase

mutual

/-- One proof-relevant use of an exact base occurrence in a decorated tree.
There is deliberately no constructor for an interface. -/
inductive CKTree.MaterialUse
    {pi : PrimitiveFragment sigma}
    (B : MaterialBase sigma InstanceData pi) :
    {G : Hypersequent sigma} -> CKTree sigma InstanceData G ->
      Type (max (max u v) w)
  | root {o : LocalOccurrence sigma InstanceData}
      {children : CKChildren sigma InstanceData o.shape.premises}
      (member : B.Member o) :
      CKTree.MaterialUse B (.ordinary o children)
  | descend {o : LocalOccurrence sigma InstanceData}
      {children : CKChildren sigma InstanceData o.shape.premises}
      (use : CKChildren.MaterialUse B children) :
      CKTree.MaterialUse B (.ordinary o children)

/-- One material use located in an exact ordered child position. -/
inductive CKChildren.MaterialUse
    {pi : PrimitiveFragment sigma}
    (B : MaterialBase sigma InstanceData pi) :
    {boundaries : List (Hypersequent sigma)} ->
      CKChildren sigma InstanceData boundaries -> Type (max (max u v) w)
  | head {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
      {head : CKTree sigma InstanceData G}
      {tail : CKChildren sigma InstanceData Gs}
      (use : CKTree.MaterialUse B head) :
      CKChildren.MaterialUse B (.cons head tail)
  | tail {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
      {head : CKTree sigma InstanceData G}
      {tail : CKChildren sigma InstanceData Gs}
      (use : CKChildren.MaterialUse B tail) :
      CKChildren.MaterialUse B (.cons head tail)

end

namespace CKTree.MaterialUse

variable {pi : PrimitiveFragment sigma}
variable {B C : MaterialBase sigma InstanceData pi}

mutual

/-- Exact zero-based source address of a material use. -/
def sourceAddress : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    CKTree.MaterialUse B tree -> InternalAddress
  | _, _, .root _ => []
  | _, _, .descend use => use.sourceAddress

/-- Exact address of a material use within an ordered child tuple. -/
def _root_.Potkin.CKChildren.MaterialUse.sourceAddress :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    CKChildren.MaterialUse B children -> InternalAddress
  | _, _, .head use => 0 :: use.sourceAddress
  | _, _, .tail use => InternalAddress.shiftHead use.sourceAddress

end

mutual

/-- Exact base member used at this proof-relevant path. -/
def exactOccurrence : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    CKTree.MaterialUse B tree -> MaterialBase.ExactOccurrence B
  | _, _, .root member => ⟨_, member⟩
  | _, _, .descend use => use.exactOccurrence

/-- Exact base member used below an ordered child tuple. -/
def _root_.Potkin.CKChildren.MaterialUse.exactOccurrence :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    CKChildren.MaterialUse B children -> MaterialBase.ExactOccurrence B
  | _, _, .head use => use.exactOccurrence
  | _, _, .tail use => use.exactOccurrence

end

/-- Registry ID retained by one exact material use. -/
def occurrenceId {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (use : CKTree.MaterialUse B tree) : Nat :=
  use.exactOccurrence.occurrence.id

/-- Whole boundary concluded at the material-use site. -/
def siteBoundary {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (use : CKTree.MaterialUse B tree) : Hypersequent sigma :=
  use.exactOccurrence.occurrence.shape.conclusion

mutual

/-- Occurrence-preserving transport of one proof-relevant use. -/
def mapBase (f : BaseHom B C) :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    CKTree.MaterialUse B tree -> CKTree.MaterialUse C tree
  | _, _, .root member => .root (f.map_member member)
  | _, _, .descend use => .descend (use.mapBase f)

/-- Occurrence-preserving transport below a child tuple. -/
def _root_.Potkin.CKChildren.MaterialUse.mapBase (f : BaseHom B C) :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    CKChildren.MaterialUse B children -> CKChildren.MaterialUse C children
  | _, _, .head use => .head (use.mapBase f)
  | _, _, .tail use => .tail (use.mapBase f)

end

mutual

@[simp]
theorem sourceAddress_mapBase {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (f : BaseHom B C)
    (use : CKTree.MaterialUse B tree) :
    (use.mapBase f).sourceAddress = use.sourceAddress := by
  cases use with
  | root => rfl
  | descend use =>
      simpa [mapBase, sourceAddress] using
        CKChildren.MaterialUse.sourceAddress_mapBase f use

@[simp]
theorem _root_.Potkin.CKChildren.MaterialUse.sourceAddress_mapBase
    {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (f : BaseHom B C) (use : CKChildren.MaterialUse B children) :
    (use.mapBase f).sourceAddress = use.sourceAddress := by
  cases use with
  | head use => simp [CKChildren.MaterialUse.mapBase,
      CKChildren.MaterialUse.sourceAddress, sourceAddress_mapBase]
  | tail use => simp [CKChildren.MaterialUse.mapBase,
      CKChildren.MaterialUse.sourceAddress,
      CKChildren.MaterialUse.sourceAddress_mapBase]

end


mutual

@[simp]
theorem exactOccurrence_mapBase {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (f : BaseHom B C)
    (use : CKTree.MaterialUse B tree) :
    (use.mapBase f).exactOccurrence = use.exactOccurrence.map f := by
  cases use with
  | root => rfl
  | descend use =>
      simpa [mapBase, exactOccurrence] using
        CKChildren.MaterialUse.exactOccurrence_mapBase f use

@[simp]
theorem _root_.Potkin.CKChildren.MaterialUse.exactOccurrence_mapBase
    {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (f : BaseHom B C) (use : CKChildren.MaterialUse B children) :
    (use.mapBase f).exactOccurrence = use.exactOccurrence.map f := by
  cases use with
  | head use => simp [CKChildren.MaterialUse.mapBase,
      CKChildren.MaterialUse.exactOccurrence, exactOccurrence_mapBase]
  | tail use => simp [CKChildren.MaterialUse.mapBase,
      CKChildren.MaterialUse.exactOccurrence,
      CKChildren.MaterialUse.exactOccurrence_mapBase]

end

end CKTree.MaterialUse

/-! ## Exact-once structural enumeration -/

mutual

/-- Deterministic preorder enumeration of every material-base use in a
locally admitted open tree.  Logical and structural nodes are traversed but
do not themselves contribute entries. -/
def CKTree.materialUseList
    {T : ProofTheory sigma InstanceData} (P : EquippedPresentation T) :
    {G : Hypersequent sigma} -> (tree : CKTree sigma InstanceData G) ->
    LocallyAdmittedTree P tree -> List (CKTree.MaterialUse T.base tree)
  | _, .interface _, _ => []
  | _, .ordinary o children, admitted =>
      let childUses :=
        (children.materialUseList P admitted.2).map CKTree.MaterialUse.descend
      if kind : o.kind = .material then
        CKTree.MaterialUse.root
          (ProofTheory.Admits.materialMembership_of_kind
            admitted.rootAdmitted kind) :: childUses
      else childUses

/-- Deterministic enumeration through every ordered premise position. -/
def CKChildren.materialUseList
    {T : ProofTheory sigma InstanceData} (P : EquippedPresentation T) :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    LocallyAdmittedChildren P children ->
      List (CKChildren.MaterialUse T.base children)
  | _, .nil, _ => []
  | _, .cons head tail, admitted =>
      (head.materialUseList P admitted.1).map CKChildren.MaterialUse.head ++
        (tail.materialUseList P admitted.2).map CKChildren.MaterialUse.tail

end

namespace CKTree

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

@[simp]
theorem materialUseList_interface (G : Hypersequent sigma) :
    materialUseList P (.interface G) trivial = [] := rfl

theorem materialUseList_ordinary_material
    (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (admitted : LocallyAdmittedTree P (.ordinary o children))
    (kind : o.kind = .material) :
    materialUseList P (.ordinary o children) admitted =
      CKTree.MaterialUse.root
          (ProofTheory.Admits.materialMembership_of_kind
            admitted.rootAdmitted kind) ::
        (children.materialUseList P admitted.2).map
          CKTree.MaterialUse.descend := by
  simp [materialUseList, kind]

theorem materialUseList_ordinary_nonmaterial
    (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (admitted : LocallyAdmittedTree P (.ordinary o children))
    (kind : o.kind ≠ .material) :
    materialUseList P (.ordinary o children) admitted =
      (children.materialUseList P admitted.2).map
        CKTree.MaterialUse.descend := by
  simp [materialUseList, kind]

mutual

/-- Exact preorder extraction commutes with occurrence-preserving base
inclusion.  Addresses and occurrences are unchanged; only membership
evidence is transported. -/
theorem materialUseList_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    (admitted : LocallyAdmittedTree P tree) ->
    materialUseList (P.mapBase f) tree (admitted.mapBase f) =
      (materialUseList P tree admitted).map
        (CKTree.MaterialUse.mapBase f)
  | _, .interface _, _ => rfl
  | _, .ordinary o children, admitted => by
      have childEq := CKChildren.materialUseList_mapBase f children admitted.2
      by_cases kind : o.kind = .material
      · simp only [materialUseList_ordinary_material o children
          (admitted.mapBase f) kind,
          materialUseList_ordinary_material o children admitted kind,
          List.map_cons, List.map_map]
        rw [childEq]
        apply congrArg₂ List.cons
        · rfl
        · have descendMap
              (uses : List (CKChildren.MaterialUse T.base children)) :
              (uses.map (CKChildren.MaterialUse.mapBase f)).map
                  (fun use => CKTree.MaterialUse.descend (o := o) use) =
                uses.map (fun use =>
                  (CKTree.MaterialUse.descend (o := o) use).mapBase f) := by
              induction uses with
              | nil => rfl
              | cons use uses ih =>
                  exact congrArg₂ List.cons rfl ih
          exact descendMap _
      · simp only [materialUseList_ordinary_nonmaterial o children
          (admitted.mapBase f) kind,
          materialUseList_ordinary_nonmaterial o children admitted kind,
          List.map_map]
        rw [childEq]
        have descendMap
            (uses : List (CKChildren.MaterialUse T.base children)) :
            (uses.map (CKChildren.MaterialUse.mapBase f)).map
                (fun use => CKTree.MaterialUse.descend (o := o) use) =
              uses.map (fun use =>
                (CKTree.MaterialUse.descend (o := o) use).mapBase f) := by
            induction uses with
            | nil => rfl
            | cons use uses ih =>
                exact congrArg₂ List.cons rfl ih
        exact descendMap _

/-- Ordered-child extraction commutes with base inclusion slot by slot. -/
theorem CKChildren.materialUseList_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    (admitted : LocallyAdmittedChildren P children) ->
    CKChildren.materialUseList (P.mapBase f) children
        (LocallyAdmittedChildren.mapBase f admitted) =
      (CKChildren.materialUseList P children admitted).map
        (CKChildren.MaterialUse.mapBase f)
  | _, .nil, _ => rfl
  | _, .cons head tail, admitted => by
      rw [CKChildren.materialUseList, CKChildren.materialUseList,
        List.map_append, List.map_map, List.map_map,
        materialUseList_mapBase f head admitted.1,
        CKChildren.materialUseList_mapBase f tail admitted.2]
      apply congrArg₂ List.append
      · have headMap
            (uses : List (CKTree.MaterialUse T.base head)) :
            (uses.map (CKTree.MaterialUse.mapBase f)).map
                (fun use => CKChildren.MaterialUse.head
                  (tail := tail) use) =
              uses.map (fun use =>
                (CKChildren.MaterialUse.head (tail := tail) use).mapBase f) := by
            induction uses with
            | nil => rfl
            | cons use uses ih =>
                exact congrArg₂ List.cons rfl ih
        exact headMap _
      · have tailMap
            (uses : List (CKChildren.MaterialUse T.base tail)) :
            (uses.map (CKChildren.MaterialUse.mapBase f)).map
                (fun use => CKChildren.MaterialUse.tail
                  (head := head) use) =
              uses.map (fun use =>
                (CKChildren.MaterialUse.tail (head := head) use).mapBase f) := by
            induction uses with
            | nil => rfl
            | cons use uses ih =>
                exact congrArg₂ List.cons rfl ih
        exact tailMap _

end

/-- Address-preserving summary used by small executable fixtures. -/
def materialUseSummary {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G)
    (admitted : LocallyAdmittedTree P tree) :
    List (InternalAddress × Nat) :=
  (tree.materialUseList P admitted).map fun use =>
    (use.sourceAddress, use.occurrenceId)

/-- Address-forgetting exact occurrence multiplicity profile. -/
def materialProfile {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G)
    (admitted : LocallyAdmittedTree P tree) :
    Multiset (MaterialBase.ExactOccurrence T.base) :=
  Multiset.ofList <| (tree.materialUseList P admitted).map
    (fun use => use.exactOccurrence)

/-- Multiplicity profiles are pushed forward along the identity-on-
occurrences base inclusion. -/
theorem materialProfile_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G)
    (admitted : LocallyAdmittedTree P tree) :
    tree.materialProfile (P := P.mapBase f) (admitted.mapBase f) =
      (tree.materialProfile admitted).map
        (MaterialBase.ExactOccurrence.map f) := by
  rw [materialProfile, materialProfile, materialUseList_mapBase]
  change Multiset.ofList
      (((tree.materialUseList P admitted).map
        (CKTree.MaterialUse.mapBase f)).map
          (fun use => use.exactOccurrence)) =
    Multiset.ofList
      (((tree.materialUseList P admitted).map
        (fun use => use.exactOccurrence)).map
          (MaterialBase.ExactOccurrence.map f))
  apply congrArg Multiset.ofList
  simp only [List.map_map]
  apply List.map_congr_left
  intro use _
  exact CKTree.MaterialUse.exactOccurrence_mapBase f use

end CKTree

namespace CheckedDerivation

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

/-- Material uses of a complete checked proof, read from its occurrence-
decorated realization with checker-supplied local admission. -/
def materialUseList {G : Hypersequent sigma} (derivation : CheckedDerivation P G) :=
  derivation.realize.materialUseList P derivation.realizeLocallyAdmitted

def materialUseSummary {G : Hypersequent sigma}
    (derivation : CheckedDerivation P G) : List (InternalAddress × Nat) :=
  derivation.realize.materialUseSummary derivation.realizeLocallyAdmitted

def materialProfile {G : Hypersequent sigma} (derivation : CheckedDerivation P G) :=
  derivation.realize.materialProfile derivation.realizeLocallyAdmitted

end CheckedDerivation

namespace RealizedOpenComponent

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

def materialUseList (source : RealizedOpenComponent P) :=
  source.component.tree.materialUseList P source.locallyAdmitted

def materialUseSummary (source : RealizedOpenComponent P) :
    List (InternalAddress × Nat) :=
  source.component.tree.materialUseSummary source.locallyAdmitted

def materialProfile (source : RealizedOpenComponent P) :=
  source.component.tree.materialProfile source.locallyAdmitted

end RealizedOpenComponent

/-! ## Wholly material regions -/

mutual

/-- Every ordinary vertex in a tree has stored material kind.  Interfaces are
vacuously pure vacancies and contribute no material occurrence. -/
def CKTree.AllVerticesMaterial : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> Prop
  | _, .interface _ => True
  | _, .ordinary o children =>
      o.kind = .material ∧ children.AllVerticesMaterial

def CKChildren.AllVerticesMaterial :
    {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries -> Prop
  | _, .nil => True
  | _, .cons head tail =>
      head.AllVerticesMaterial ∧ tail.AllVerticesMaterial

end

mutual

def CKTree.allVerticesMaterialDecidable : {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) -> Decidable tree.AllVerticesMaterial
  | _, .interface _ => isTrue trivial
  | _, .ordinary o children =>
      @instDecidableAnd (o.kind = .material) children.AllVerticesMaterial
        (inferInstance : Decidable (o.kind = .material))
        (CKChildren.allVerticesMaterialDecidable children)

def CKChildren.allVerticesMaterialDecidable :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
      Decidable children.AllVerticesMaterial
  | _, .nil => isTrue trivial
  | _, .cons head tail =>
      @instDecidableAnd head.AllVerticesMaterial tail.AllVerticesMaterial
        (CKTree.allVerticesMaterialDecidable head)
        (CKChildren.allVerticesMaterialDecidable tail)

end

instance CKTree.decidableAllVerticesMaterial {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) : Decidable tree.AllVerticesMaterial :=
  CKTree.allVerticesMaterialDecidable tree

instance CKChildren.decidableAllVerticesMaterial
    {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries) :
    Decidable children.AllVerticesMaterial :=
  CKChildren.allVerticesMaterialDecidable children

mutual

/-- Maximal wholly-material positive roots.  A whole pure proof legitimately
returns the root address `[]`; this is an address antichain, not a CK cut. -/
def CKTree.maximalMaterialAddresses : {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) -> List InternalAddress
  | _, .interface _ => []
  | _, tree@(.ordinary _ children) =>
      if tree.AllVerticesMaterial then [[]]
      else children.maximalMaterialAddresses

def CKChildren.maximalMaterialAddresses :
    {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries -> List InternalAddress
  | _, .nil => []
  | _, .cons head tail =>
      (head.maximalMaterialAddresses.map (0 :: ·)) ++
        (tail.maximalMaterialAddresses.map InternalAddress.shiftHead)

end

end Potkin

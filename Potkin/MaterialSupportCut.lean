import Potkin.MaterialSupport
import Potkin.GeneralFilling
import Potkin.SourceAddressPruning

/-!
# Material support under CK filling and cutting

This module exposes the recursive old-or-inserted classification of one exact
material use under CK filling.  The classifiers follow the cut constructors
and preserve the ordered site witness.  The constructor views themselves
rebuild exactly, but the cut classifiers below are forward-only.  No bijection
theorem is claimed here: the current `MaterialUse` indices require a
noncomputable recursor view, and Lean does not yet reduce that view robustly
inside the nested inverse-law proof.
-/

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {pi : PrimitiveFragment sigma}
variable {B : MaterialBase sigma InstanceData pi}

/-! ## Total constructor views -/

/-- Total root-or-descendant view of a material use. -/
noncomputable def CKTree.MaterialUse.split : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (use : CKTree.MaterialUse B tree) ->
      match G, tree with
      | _, .interface _ => ULift.{max (max u v) w, 0} Empty
      | _, .ordinary o children =>
          PSum (B.Member o) (CKChildren.MaterialUse B children) :=
  CKTree.MaterialUse.rec
    (motive_1 := fun {G}
      (tree : CKTree sigma InstanceData G)
      (_ : CKTree.MaterialUse B tree) =>
      match G, tree with
      | _, .interface _ => ULift.{max (max u v) w, 0} Empty
      | _, .ordinary o children =>
          PSum (B.Member o) (CKChildren.MaterialUse B children))
    (motive_2 := fun {boundaries}
      (children : CKChildren sigma InstanceData boundaries)
      (_ : CKChildren.MaterialUse B children) =>
        ULift.{max (max u v) w, 0} PUnit)
    (fun member => .inl member)
    (fun use _ => .inr use)
    (fun _ _ => ULift.up PUnit.unit)
    (fun _ _ => ULift.up PUnit.unit)

/-- Total head-or-tail view of a material use in an ordered child tuple. -/
noncomputable def CKChildren.MaterialUse.split :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (use : CKChildren.MaterialUse B children) ->
      match boundaries, children with
      | _, .nil => ULift.{max (max u v) w, 0} Empty
      | _, .cons first rest =>
          Sum (CKTree.MaterialUse B first) (CKChildren.MaterialUse B rest) :=
  CKChildren.MaterialUse.rec
    (motive_1 := fun {G}
      (tree : CKTree sigma InstanceData G)
      (_ : CKTree.MaterialUse B tree) =>
        ULift.{max (max u v) w, 0} PUnit)
    (motive_2 := fun {boundaries}
      (children : CKChildren sigma InstanceData boundaries)
      (_ : CKChildren.MaterialUse B children) =>
      match boundaries, children with
      | _, .nil => ULift.{max (max u v) w, 0} Empty
      | _, .cons first rest =>
          Sum (CKTree.MaterialUse B first) (CKChildren.MaterialUse B rest))
    (fun _ => ULift.up PUnit.unit)
    (fun _ _ => ULift.up PUnit.unit)
    (fun use _ => .inl use)
    (fun use _ => .inr use)

@[simp]
theorem CKTree.MaterialUse.split_root
    {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (member : B.Member o) :
    (CKTree.MaterialUse.root (children := children) member).split =
      PSum.inl member := rfl

@[simp]
theorem CKTree.MaterialUse.split_descend
    {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (use : CKChildren.MaterialUse B children) :
    (CKTree.MaterialUse.descend (o := o) use).split =
      PSum.inr use := rfl

@[simp]
theorem CKChildren.MaterialUse.split_head
    {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
    {first : CKTree sigma InstanceData G}
    {rest : CKChildren sigma InstanceData Gs}
    (use : CKTree.MaterialUse B first) :
    (CKChildren.MaterialUse.head (tail := rest) use).split =
      Sum.inl use := rfl

@[simp]
theorem CKChildren.MaterialUse.split_tail
    {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
    {first : CKTree sigma InstanceData G}
    {rest : CKChildren sigma InstanceData Gs}
    (use : CKChildren.MaterialUse B rest) :
    (CKChildren.MaterialUse.tail (head := first) use).split =
      Sum.inr use := rfl

/-- Rebuilding the constructor exposed by `split` returns the same use. -/
theorem CKTree.MaterialUse.rebuild_split :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (use : CKTree.MaterialUse B tree) ->
      match G, tree with
      | _, .interface _ => True
      | _, .ordinary _ _ =>
          (match use.split with
          | PSum.inl member => CKTree.MaterialUse.root member
          | PSum.inr childUse => CKTree.MaterialUse.descend childUse) = use :=
  CKTree.MaterialUse.rec
    (motive_1 := fun {G}
      (tree : CKTree sigma InstanceData G)
      (use : CKTree.MaterialUse B tree) =>
      match G, tree with
      | _, .interface _ => True
      | _, .ordinary _ _ =>
          (match use.split with
          | PSum.inl member => CKTree.MaterialUse.root member
          | PSum.inr childUse => CKTree.MaterialUse.descend childUse) = use)
    (motive_2 := fun {boundaries}
      (children : CKChildren sigma InstanceData boundaries)
      (_ : CKChildren.MaterialUse B children) => True)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => trivial)
    (fun _ _ => trivial)

/-- Rebuilding the ordered-child constructor exposed by `split` is exact. -/
theorem CKChildren.MaterialUse.rebuild_split :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (use : CKChildren.MaterialUse B children) ->
      match boundaries, children with
      | _, .nil => True
      | _, .cons _ _ =>
          (match use.split with
          | Sum.inl headUse => CKChildren.MaterialUse.head headUse
          | Sum.inr tailUse => CKChildren.MaterialUse.tail tailUse) = use :=
  CKChildren.MaterialUse.rec
    (motive_1 := fun {G}
      (tree : CKTree sigma InstanceData G)
      (_ : CKTree.MaterialUse B tree) => True)
    (motive_2 := fun {boundaries}
      (children : CKChildren sigma InstanceData boundaries)
      (use : CKChildren.MaterialUse B children) =>
      match boundaries, children with
      | _, .nil => True
      | _, .cons _ _ =>
          (match use.split with
          | Sum.inl headUse => CKChildren.MaterialUse.head headUse
          | Sum.inr tailUse => CKChildren.MaterialUse.tail tailUse) = use)
    (fun _ => trivial)
    (fun _ _ => trivial)
    (fun _ _ => rfl)
    (fun _ _ => rfl)

/-! ## Recursive filling classification -/

mutual

/-- Classify a use of a filled plan as retained or belonging to one filler. -/
noncomputable def CKCutPlan.partitionMaterialUse :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    CKTree.MaterialUse B (cut.fill fillers) ->
      Sum (CKTree.MaterialUse B cut.remainder)
        (Sigma fun site => CKTree.MaterialUse B (fillers site))
  | _, _, .interface _, _, use => nomatch use
  | _, _, .ordinary o _ cuts, fillers, use =>
      match use.split with
      | .inl member =>
          .inl (CKTree.MaterialUse.root (B := B) (o := o)
            (children := cuts.remainder) member)
      | .inr childUse =>
          match cuts.partitionMaterialUse fillers childUse with
          | .inl retained => .inl (CKTree.MaterialUse.descend
              (B := B) (o := o) retained)
          | .inr inserted => .inr inserted

/-- Ordered-child form of material-use classification. -/
noncomputable def CKChildCuts.partitionMaterialUse :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    CKChildren.MaterialUse B (cuts.fill fillers) ->
      Sum (CKChildren.MaterialUse B cuts.remainder)
        (Sigma fun site => CKTree.MaterialUse B (fillers site))
  | _, _, .nil, _, use => nomatch use
  | _, _, .cons _ _ headCut tailCuts, fillers, use =>
      match use.split with
      | .inl headUse =>
          match headCut.partitionMaterialUse
              (fun site => fillers (.inl site)) headUse with
          | .inl retained => .inl (CKChildren.MaterialUse.head
              (B := B) (tail := tailCuts.remainder) retained)
          | .inr inserted => .inr ⟨.inl inserted.1, inserted.2⟩
      | .inr tailUse =>
          match tailCuts.partitionMaterialUse
              (fun site => fillers (.inr site)) tailUse with
          | .inl retained => .inl (CKChildren.MaterialUse.tail
              (B := B) (head := headCut.remainder) retained)
          | .inr inserted => .inr ⟨.inr inserted.1, inserted.2⟩

/-- Branch form of material-use classification. -/
noncomputable def CKBranchCut.partitionMaterialUse :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    CKTree.MaterialUse B (cut.fill fillers) ->
      Sum (CKTree.MaterialUse B cut.remainder)
        (Sigma fun site => CKTree.MaterialUse B (fillers site))
  | _, _, .detach _, _, use => .inr ⟨PUnit.unit, use⟩
  | _, _, .descend cut, fillers, use =>
      cut.partitionMaterialUse fillers use

end

/-! ## Public cut APIs -/

namespace CKCut

/-- Public arbitrary-filling partition, retaining the exact recursive site. -/
noncomputable def partitionFilledMaterialUse {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G} (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (use : CKTree.MaterialUse B (cut.fill fillers)) :
    Sum (CKTree.MaterialUse B cut.remainder)
      (Sigma fun site => CKTree.MaterialUse B (fillers site)) :=
  cut.plan.partitionMaterialUse fillers use

end CKCut

namespace ValidAddressCut

/-- Extensional-cut wrapper for the same exact recursive partition. -/
noncomputable def partitionFilledMaterialUse
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : ValidAddressCut tree)
    (fillers : (site : cut.toCut.Site) ->
      CKTree sigma InstanceData (cut.toCut.plan.siteBoundary site))
    (use : CKTree.MaterialUse B (cut.toCut.fill fillers)) :
    Sum (CKTree.MaterialUse B cut.toCut.remainder)
      (Sigma fun site => CKTree.MaterialUse B (fillers site)) :=
  cut.toCut.partitionFilledMaterialUse fillers use

end ValidAddressCut

end Potkin

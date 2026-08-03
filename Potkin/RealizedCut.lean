import Potkin.CKCut
import Potkin.RealizedSector

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

mutual

/-- A recursive cut preserves local admission of its retained remainder. -/
def CKCutPlan.remainderLocallyAdmitted :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> LocallyAdmittedTree P tree ->
      LocallyAdmittedTree P cut.remainder
  | _, _, .interface _, _ => trivial
  | _, _, .ordinary _ _ cuts, admitted =>
      ⟨admitted.1, cuts.remainderLocallyAdmitted admitted.2⟩

/-- Child-tuple remainders preserve local admission slot by slot. -/
def CKChildCuts.remainderLocallyAdmitted :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> LocallyAdmittedChildren P children ->
      LocallyAdmittedChildren P cuts.remainder
  | _, _, .nil, _ => trivial
  | _, _, .cons _ _ headCut tailCuts, admitted =>
      ⟨headCut.remainderLocallyAdmitted admitted.1,
        tailCuts.remainderLocallyAdmitted admitted.2⟩

/-- A branch detachment creates an admitted interface; descent is recursive. -/
def CKBranchCut.remainderLocallyAdmitted :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> LocallyAdmittedTree P tree ->
      LocallyAdmittedTree P cut.remainder
  | _, _, .detach _, _ => trivial
  | _, _, .descend cut, admitted =>
      cut.remainderLocallyAdmitted admitted

end


mutual

/-- Every detached occurrence of an admitted cut plan is locally admitted. -/
def CKCutPlan.detachedLocallyAdmitted :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> LocallyAdmittedTree P tree ->
    (site : cut.Site) -> LocallyAdmittedTree P (cut.detached site)
  | _, _, .interface _, _, site => nomatch site
  | _, _, .ordinary _ _ cuts, admitted, site =>
      cuts.detachedLocallyAdmitted admitted.2 site

/-- Detached occurrences inherit admission from their exact ordered child. -/
def CKChildCuts.detachedLocallyAdmitted :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> LocallyAdmittedChildren P children ->
    (site : cuts.Site) -> LocallyAdmittedTree P (cuts.detached site)
  | _, _, .nil, _, site => nomatch site
  | _, _, .cons _ _ headCut tailCuts, admitted, site => by
      change Sum headCut.Site tailCuts.Site at site
      cases site with
      | inl headSite =>
          exact headCut.detachedLocallyAdmitted admitted.1 headSite
      | inr tailSite =>
          exact tailCuts.detachedLocallyAdmitted admitted.2 tailSite

/-- Root detachment keeps the admitted source; descent uses hereditary closure. -/
def CKBranchCut.detachedLocallyAdmitted :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> LocallyAdmittedTree P tree ->
    (site : cut.Site) -> LocallyAdmittedTree P (cut.detached site)
  | _, _, .detach _, admitted, _ => admitted
  | _, _, .descend cut, admitted, site =>
      cut.detachedLocallyAdmitted admitted site

end

/-- A cut plan on a positive source retains a positive ordinary root. -/
def CKCutPlan.remainderIsOrdinary :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> tree.IsOrdinary -> cut.remainder.IsOrdinary
  | _, _, .interface _, notOrdinary => False.elim notOrdinary
  | _, _, .ordinary _ _ _, _ => trivial

namespace CKCut

variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Public cut-heredity theorem for the retained punctured remainder. -/
theorem remainder_locallyAdmitted (cut : CKCut tree)
    (admitted : LocallyAdmittedTree P tree) :
    LocallyAdmittedTree P cut.remainder :=
  cut.plan.remainderLocallyAdmitted admitted

/-- Public cut-heredity theorem for every address-indexed detached factor. -/
theorem detached_locallyAdmitted (cut : CKCut tree)
    (admitted : LocallyAdmittedTree P tree) (site : cut.Site) :
    LocallyAdmittedTree P (cut.plan.detached site) :=
  cut.plan.detachedLocallyAdmitted admitted site

/-- The retained remainder of a public cut is still a positive component. -/
theorem remainder_isOrdinary (cut : CKCut tree) :
    cut.remainder.IsOrdinary :=
  cut.plan.remainderIsOrdinary cut.sourceOrdinary

end CKCut

namespace RealizedOpenComponent

/-- Package the retained remainder of a realised cut in the same sector. -/
def remainderOfCut (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) : RealizedOpenComponent P :=
  ofTree cut.remainder cut.remainder_isOrdinary
    (cut.remainder_locallyAdmitted source.locallyAdmitted)

/-- Package one exact address-indexed detached occurrence in the same sector. -/
def detachedOfCut (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) (site : cut.Site) :
    RealizedOpenComponent P :=
  ofTree (cut.plan.detached site) (cut.plan.detachedOrdinary site)
    (cut.detached_locallyAdmitted source.locallyAdmitted site)

/-- The realised addressed tuple, retaining one entry for every ordered site. -/
def detachedTupleOfCut (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) : List (RealizedOpenComponent P) :=
  cut.orderedSites.map (source.detachedOfCut cut)

/-- Filling the realised detached tuple reconstructs the exact source tree. -/
theorem fill_detachedOfCut_reconstructs (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    cut.fill (fun site => (source.detachedOfCut cut site).component.tree) =
      source.component.tree := by
  simpa [detachedOfCut, ofTree] using cut.fill_detached_reconstructs

/-- Base transport commutes with packaging the retained remainder. -/
@[simp]
theorem remainderOfCut_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    (source.remainderOfCut cut).mapBase f =
      (source.mapBase f).remainderOfCut cut := by
  rfl

/-- Base transport commutes with every address-indexed detached occurrence. -/
@[simp]
theorem detachedOfCut_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) (site : cut.Site) :
    (source.detachedOfCut cut site).mapBase f =
      (source.mapBase f).detachedOfCut cut site := by
  rfl

/-- Base transport commutes with the complete occurrence-level detached tuple. -/
@[simp]
theorem detachedTupleOfCut_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    (source.detachedTupleOfCut cut).map (mapBase f) =
      (source.mapBase f).detachedTupleOfCut cut := by
  simp only [detachedTupleOfCut, List.map_map]
  apply List.map_congr_left
  intro site _
  exact detachedOfCut_mapBase f source cut site

/-- Reconstruction is unchanged by proof-preserving base transport. -/
theorem fill_detachedOfCut_mapBase
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    cut.fill (fun site =>
        ((source.detachedOfCut cut site).mapBase f).component.tree) =
      (source.mapBase f).component.tree := by
  simpa using source.fill_detachedOfCut_reconstructs cut

/-! ## Identity and composition action on realised cut data -/

@[simp]
theorem remainderOfCut_mapBase_id_component
    (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    ((source.remainderOfCut cut).mapBase
      (BaseHom.id T.base)).component =
      (source.remainderOfCut cut).component := rfl

@[simp]
theorem remainderOfCut_mapBase_comp_component
    {C D : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (g : BaseHom C D)
    (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    (((source.remainderOfCut cut).mapBase f).mapBase g).component =
      ((source.remainderOfCut cut).mapBase (g.comp f)).component := rfl

@[simp]
theorem detachedOfCut_mapBase_id_component
    (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) (site : cut.Site) :
    ((source.detachedOfCut cut site).mapBase
      (BaseHom.id T.base)).component =
      (source.detachedOfCut cut site).component := rfl

@[simp]
theorem detachedOfCut_mapBase_comp_component
    {C D : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (g : BaseHom C D)
    (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) (site : cut.Site) :
    (((source.detachedOfCut cut site).mapBase f).mapBase g).component =
      ((source.detachedOfCut cut site).mapBase (g.comp f)).component := rfl

/-- The complete addressed tuple has identical underlying components under identity. -/
@[simp]
theorem detachedTupleOfCut_mapBase_id_components
    (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    (source.detachedTupleOfCut cut).map
        (fun factor =>
          (factor.mapBase (BaseHom.id T.base)).component) =
      (source.detachedTupleOfCut cut).map
        (fun factor => factor.component) := rfl

/-- Staged and composite transport have the same addressed component tuple. -/
@[simp]
theorem detachedTupleOfCut_mapBase_comp_components
    {C D : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (g : BaseHom C D)
    (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    (source.detachedTupleOfCut cut).map
        (fun factor => ((factor.mapBase f).mapBase g).component) =
      (source.detachedTupleOfCut cut).map
        (fun factor => (factor.mapBase (g.comp f)).component) := rfl

/-- Identity transport leaves distinguished realised reconstruction unchanged. -/
theorem fill_detachedOfCut_mapBase_id
    (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    cut.fill (fun site =>
        ((source.detachedOfCut cut site).mapBase
          (BaseHom.id T.base)).component.tree) =
      source.component.tree := by
  simpa using source.fill_detachedOfCut_reconstructs cut

/-- Staged and composite transport give the same distinguished reconstruction. -/
theorem fill_detachedOfCut_mapBase_comp
    {C D : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C) (g : BaseHom C D)
    (source : RealizedOpenComponent P)
    (cut : CKCut source.component.tree) :
    cut.fill (fun site =>
        (((source.detachedOfCut cut site).mapBase f).mapBase g).component.tree) =
      (source.mapBase (g.comp f)).component.tree := by
  simpa using source.fill_detachedOfCut_reconstructs cut

end RealizedOpenComponent

end Potkin

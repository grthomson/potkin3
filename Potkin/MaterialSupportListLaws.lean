import Potkin.MaterialSupport
import Potkin.GeneralFilling
import Potkin.CKCutValidity
import Potkin.NestedCoherence

/-!
# List and multiset laws for material support under CK filling

The primary observation carrier retains both the exact source address and the
exact occurrence-indexed base member.  The filling theorem is stated first as
a `List.Perm`: the left side keeps preorder traversal, while the right side
separates retained-context uses from the canonically site-ordered filler uses.
The permutation is an explicit multiplicity-preserving occurrence bijection,
not merely equality of counts.
-/

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-- One material occurrence together with its exact address in a presented
tree. -/
abbrev AddressedMaterialOccurrence
    {pi : PrimitiveFragment sigma}
    (B : MaterialBase sigma InstanceData pi) :=
  InternalAddress × MaterialBase.ExactOccurrence B

namespace AddressedMaterialOccurrence

variable {pi : PrimitiveFragment sigma}
variable {B : MaterialBase sigma InstanceData pi}

/-- Prefix an addressed occurrence by its insertion site. -/
def prefixUse (outer : InternalAddress)
    (use : AddressedMaterialOccurrence B) :
    AddressedMaterialOccurrence B :=
  (outer ++ use.1, use.2)

/-- Embed a use from the tail of an ordered child tuple. -/
def shiftHead (use : AddressedMaterialOccurrence B) :
    AddressedMaterialOccurrence B :=
  (InternalAddress.shiftHead use.1, use.2)

@[simp]
theorem prefixUse_nil (use : AddressedMaterialOccurrence B) :
    prefixUse [] use = use := by
  rcases use with ⟨address, occurrence⟩
  rfl

@[simp]
theorem prefixUse_prefixUse (outer inner : InternalAddress)
    (use : AddressedMaterialOccurrence B) :
    prefixUse outer (prefixUse inner use) =
      prefixUse (outer ++ inner) use := by
  rcases use with ⟨address, occurrence⟩
  simp [prefixUse, List.append_assoc]

theorem shiftHead_prefix (outer : InternalAddress)
    (nonempty : outer ≠ []) (use : AddressedMaterialOccurrence B) :
    shiftHead (prefixUse outer use) =
      prefixUse (InternalAddress.shiftHead outer) use := by
  rcases use with ⟨address, occurrence⟩
  simp [shiftHead, prefixUse,
    InternalAddress.shiftHead_append_of_ne_nil outer address nonempty]

end AddressedMaterialOccurrence

/-! ## Addressed extraction -/

/-- Addressed exact occurrences underlying the proof-relevant material-use
list. -/
def CKTree.addressedMaterialOccurrences
    {T : ProofTheory sigma InstanceData} (P : EquippedPresentation T)
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (admitted : LocallyAdmittedTree P tree) :
    List (AddressedMaterialOccurrence T.base) :=
  (tree.materialUseList P admitted).map fun use =>
    (use.sourceAddress, use.exactOccurrence)

/-- Ordered-child form of addressed exact material occurrences. -/
def CKChildren.addressedMaterialOccurrences
    {T : ProofTheory sigma InstanceData} (P : EquippedPresentation T)
    {boundaries : List (Hypersequent sigma)}
    (children : CKChildren sigma InstanceData boundaries)
    (admitted : LocallyAdmittedChildren P children) :
    List (AddressedMaterialOccurrence T.base) :=
  (children.materialUseList P admitted).map fun use =>
    (use.sourceAddress, use.exactOccurrence)

/-- The existing address-forgetting material profile is exactly the multiset
projection of the addressed occurrence list. -/
theorem CKTree.materialProfile_eq_addressedMaterialOccurrences
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (admitted : LocallyAdmittedTree P tree) :
    tree.materialProfile admitted =
      Multiset.ofList ((tree.addressedMaterialOccurrences P admitted).map
        Prod.snd) := by
  apply congrArg Multiset.ofList
  unfold CKTree.addressedMaterialOccurrences
  simp only [List.map_map]
  apply List.map_congr_left
  intro use _
  rfl

namespace CKTree

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

@[simp]
theorem addressedMaterialOccurrences_interface (G : Hypersequent sigma) :
    addressedMaterialOccurrences P (.interface G) trivial = [] := rfl

theorem addressedMaterialOccurrences_ordinary_material
    (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (admitted : LocallyAdmittedTree P (.ordinary o children))
    (kind : o.kind = .material) :
    addressedMaterialOccurrences P (.ordinary o children) admitted =
      ([], ⟨o, ProofTheory.Admits.materialMembership_of_kind
        admitted.rootAdmitted kind⟩) ::
        children.addressedMaterialOccurrences P admitted.2 := by
  rw [addressedMaterialOccurrences,
    materialUseList_ordinary_material o children admitted kind]
  simp only [List.map_cons, List.map_map]
  apply congrArg₂ List.cons
  · rfl
  · apply List.map_congr_left
    intro use _
    rfl

theorem addressedMaterialOccurrences_ordinary_nonmaterial
    (o : LocalOccurrence sigma InstanceData)
    (children : CKChildren sigma InstanceData o.shape.premises)
    (admitted : LocallyAdmittedTree P (.ordinary o children))
    (kind : o.kind ≠ .material) :
    addressedMaterialOccurrences P (.ordinary o children) admitted =
      children.addressedMaterialOccurrences P admitted.2 := by
  rw [addressedMaterialOccurrences,
    materialUseList_ordinary_nonmaterial o children admitted kind]
  simp only [List.map_map]
  apply List.map_congr_left
  intro use _
  rfl

end CKTree

namespace CKChildren

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}

@[simp]
theorem addressedMaterialOccurrences_nil :
    addressedMaterialOccurrences P
      (.nil : CKChildren sigma InstanceData []) trivial = [] := rfl

theorem addressedMaterialOccurrences_cons
    {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
    (head : CKTree sigma InstanceData G)
    (tail : CKChildren sigma InstanceData Gs)
    (admitted : LocallyAdmittedChildren P (.cons head tail)) :
    addressedMaterialOccurrences P (.cons head tail) admitted =
      (head.addressedMaterialOccurrences P admitted.1).map
          (AddressedMaterialOccurrence.prefixUse [0]) ++
        (tail.addressedMaterialOccurrences P admitted.2).map
          AddressedMaterialOccurrence.shiftHead := by
  unfold CKChildren.addressedMaterialOccurrences
  unfold CKTree.addressedMaterialOccurrences
  rw [CKChildren.materialUseList]
  simp only [List.map_append, List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro use _
    rfl
  · apply List.map_congr_left
    intro use _
    rfl

end CKChildren

/-! ## Canonically ordered filler contributions -/

mutual

/-- Material occurrences supplied at every plan site, embedded at their exact
source addresses in constructor/canonical-site order. -/
def CKCutPlan.fillerAddressedMaterialOccurrences
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    ((site : cut.Site) -> LocallyAdmittedTree P (fillers site)) ->
    List (AddressedMaterialOccurrence T.base)
  | _, _, .interface _, _, _ => []
  | _, _, .ordinary _ _ cuts, fillers, fillersAdmitted =>
      cuts.fillerAddressedMaterialOccurrences fillers fillersAdmitted

/-- Ordered-child implementation of source-addressed filler support. -/
def CKChildCuts.fillerAddressedMaterialOccurrences
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    ((site : cuts.Site) -> LocallyAdmittedTree P (fillers site)) ->
    List (AddressedMaterialOccurrence T.base)
  | _, _, .nil, _, _ => []
  | _, _, .cons _ _ headCut tailCuts, fillers, fillersAdmitted =>
      (headCut.fillerAddressedMaterialOccurrences
          (fun site => fillers (Sum.inl site))
          (fun site => fillersAdmitted (Sum.inl site))).map
            (AddressedMaterialOccurrence.prefixUse [0]) ++
        (tailCuts.fillerAddressedMaterialOccurrences
          (fun site => fillers (Sum.inr site))
          (fun site => fillersAdmitted (Sum.inr site))).map
            AddressedMaterialOccurrence.shiftHead

/-- A detached branch contributes its filler; descent embeds recursively. -/
def CKBranchCut.fillerAddressedMaterialOccurrences
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    ((site : cut.Site) -> LocallyAdmittedTree P (fillers site)) ->
    List (AddressedMaterialOccurrence T.base)
  | _, _, .detach _, fillers, fillersAdmitted =>
      (fillers PUnit.unit).addressedMaterialOccurrences P
        (fillersAdmitted PUnit.unit)
  | _, _, .descend cut, fillers, fillersAdmitted =>
      cut.fillerAddressedMaterialOccurrences fillers fillersAdmitted

end

/-! The recursive contribution list is exactly the canonical `siteOrder`
flat-map.  This connects the constructor proof to the public occurrence
ordering and exposes every site's source-address prefix literally. -/

private theorem List.flatMap_map_sum_append
    {α β γ : Type*} (left : List α) (right : List β)
    (f : Sum α β → List γ) :
    (left.map Sum.inl ++ right.map Sum.inr).flatMap f =
      left.flatMap (fun value => f (Sum.inl value)) ++
        right.flatMap (fun value => f (Sum.inr value)) := by
  have leftMap : (left.map Sum.inl).flatMap f =
      left.flatMap (fun value => f (Sum.inl value)) := by
    induction left with
    | nil => rfl
    | cons value tail ih =>
        exact congrArg₂ List.append rfl ih
  have rightMap : (right.map Sum.inr).flatMap f =
      right.flatMap (fun value => f (Sum.inr value)) := by
    induction right with
    | nil => rfl
    | cons value tail ih =>
        exact congrArg₂ List.append rfl ih
  rw [List.flatMap_append, leftMap, rightMap]

mutual

theorem CKCutPlan.fillerAddressedMaterialOccurrences_eq_siteOrder
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) ->
    cut.fillerAddressedMaterialOccurrences fillers fillersAdmitted =
      cut.siteOrder.flatMap fun site =>
        ((fillers site).addressedMaterialOccurrences P
          (fillersAdmitted site)).map
            (AddressedMaterialOccurrence.prefixUse (cut.address site))
  | _, _, .interface _, _, _ => rfl
  | _, _, .ordinary _ _ cuts, fillers, fillersAdmitted => by
      exact cuts.fillerAddressedMaterialOccurrences_eq_siteOrder
        fillers fillersAdmitted

theorem CKChildCuts.fillerAddressedMaterialOccurrences_eq_siteOrder
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    (fillersAdmitted : (site : cuts.Site) ->
      LocallyAdmittedTree P (fillers site)) ->
    cuts.fillerAddressedMaterialOccurrences fillers fillersAdmitted =
      cuts.siteOrder.flatMap fun site =>
        ((fillers site).addressedMaterialOccurrences P
          (fillersAdmitted site)).map
            (AddressedMaterialOccurrence.prefixUse (cuts.address site))
  | _, _, .nil, _, _ => rfl
  | _, _, .cons head tail headCut tailCuts, fillers,
      fillersAdmitted => by
      have headIH := headCut.fillerAddressedMaterialOccurrences_eq_siteOrder
        (fun site => fillers (Sum.inl site))
        (fun site => fillersAdmitted (Sum.inl site))
      have tailIH := tailCuts.fillerAddressedMaterialOccurrences_eq_siteOrder
        (fun site => fillers (Sum.inr site))
        (fun site => fillersAdmitted (Sum.inr site))
      have headMap :
          (headCut.fillerAddressedMaterialOccurrences
            (fun site => fillers (Sum.inl site))
            (fun site => fillersAdmitted (Sum.inl site))).map
              (AddressedMaterialOccurrence.prefixUse [0]) =
          headCut.siteOrder.flatMap fun site =>
            ((fillers (Sum.inl site)).addressedMaterialOccurrences P
              (fillersAdmitted (Sum.inl site))).map
                (AddressedMaterialOccurrence.prefixUse
                  (0 :: headCut.relativeAddress site)) := by
        rw [headIH]
        simp only [List.map_flatMap, List.map_map]
        apply List.flatMap_congr
        intro site _
        apply List.map_congr_left
        intro use _
        simpa using
          (AddressedMaterialOccurrence.prefixUse_prefixUse
            [0] (headCut.relativeAddress site) use)
      have tailMap :
          (tailCuts.fillerAddressedMaterialOccurrences
            (fun site => fillers (Sum.inr site))
            (fun site => fillersAdmitted (Sum.inr site))).map
              AddressedMaterialOccurrence.shiftHead =
          tailCuts.siteOrder.flatMap fun site =>
            ((fillers (Sum.inr site)).addressedMaterialOccurrences P
              (fillersAdmitted (Sum.inr site))).map
                (AddressedMaterialOccurrence.prefixUse
                  (InternalAddress.shiftHead (tailCuts.address site))) := by
        rw [tailIH]
        simp only [List.map_flatMap, List.map_map]
        apply List.flatMap_congr
        intro site _
        apply List.map_congr_left
        intro use _
        exact AddressedMaterialOccurrence.shiftHead_prefix
          (tailCuts.address site) (tailCuts.address_nonroot site) use
      rw [CKChildCuts.fillerAddressedMaterialOccurrences, headMap, tailMap]
      rw [CKChildCuts.siteOrder]
      have split := List.flatMap_map_sum_append
        headCut.siteOrder tailCuts.siteOrder
        (fun site =>
          ((fillers site).addressedMaterialOccurrences P
            (fillersAdmitted site)).map
              (AddressedMaterialOccurrence.prefixUse
                ((CKChildCuts.cons head tail headCut tailCuts).address site)))
      exact split.symm

theorem CKBranchCut.fillerAddressedMaterialOccurrences_eq_siteOrder
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) ->
    cut.fillerAddressedMaterialOccurrences fillers fillersAdmitted =
      cut.siteOrder.flatMap fun site =>
        ((fillers site).addressedMaterialOccurrences P
          (fillersAdmitted site)).map
            (AddressedMaterialOccurrence.prefixUse
              (cut.relativeAddress site))
  | _, _, .detach _, fillers, fillersAdmitted => by
      simp only [CKBranchCut.fillerAddressedMaterialOccurrences,
        CKBranchCut.siteOrder, CKBranchCut.relativeAddress,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have prefixNil (uses : List (AddressedMaterialOccurrence T.base)) :
          uses = uses.map (AddressedMaterialOccurrence.prefixUse []) := by
        induction uses with
        | nil => rfl
        | cons use uses ih =>
            simp only [List.map_cons]
            rw [AddressedMaterialOccurrence.prefixUse_nil]
            exact congrArg (List.cons use) ih
      exact prefixNil _
  | _, _, .descend cut, fillers, fillersAdmitted =>
      cut.fillerAddressedMaterialOccurrences_eq_siteOrder
        fillers fillersAdmitted

end

/-! ## A small permutation algebra lemma -/

private theorem List.Perm.interleave
    {α : Type*} {left retainedLeft insertedLeft
      right retainedRight insertedRight : List α}
    (leftPerm : left.Perm (retainedLeft ++ insertedLeft))
    (rightPerm : right.Perm (retainedRight ++ insertedRight)) :
    (left ++ right).Perm
      ((retainedLeft ++ retainedRight) ++
        (insertedLeft ++ insertedRight)) := by
  apply (leftPerm.append rightPerm).trans
  have swap : (insertedLeft ++ retainedRight).Perm
      (retainedRight ++ insertedLeft) := List.perm_append_comm
  simpa only [List.append_assoc] using
    (swap.append_left retainedLeft).append_right insertedRight

/-- Regroup a sitewise exact partition into its retained and inserted
coordinates.  This is a permutation of occurrences, not a cardinality
calculation. -/
private theorem List.Perm.flatMap_interleave
    {ι α : Type*} (sites : List ι)
    (source retained inserted : ι → List α)
    (partition : ∀ site,
      (source site).Perm (retained site ++ inserted site)) :
    (sites.flatMap source).Perm
      (sites.flatMap retained ++ sites.flatMap inserted) := by
  induction sites with
  | nil => rfl
  | cons site sites ih =>
      simpa only [List.flatMap_cons] using
        List.Perm.interleave (partition site) ih

/-! ## Filling partitions addressed material occurrences -/

mutual

theorem CKCutPlan.fill_addressedMaterialOccurrences_perm
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    (admitted : LocallyAdmittedTree P tree) ->
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) ->
    ((cut.fill fillers).addressedMaterialOccurrences P
      (cut.fillLocallyAdmitted fillers admitted fillersAdmitted)).Perm
      ((cut.remainder.addressedMaterialOccurrences P
          (cut.remainderLocallyAdmitted admitted)) ++
        cut.fillerAddressedMaterialOccurrences fillers fillersAdmitted)
  | _, _, .interface _, _, _, _ => by
      rfl
  | _, _, .ordinary o children cuts, fillers, admitted,
      fillersAdmitted => by
      have childPerm := cuts.fill_addressedMaterialOccurrences_perm
        fillers admitted.2 fillersAdmitted
      simp only [CKCutPlan.fill, CKCutPlan.remainder,
        CKCutPlan.fillerAddressedMaterialOccurrences]
      by_cases kind : o.kind = .material
      · rw [CKTree.addressedMaterialOccurrences_ordinary_material
            o _ (CKCutPlan.fillLocallyAdmitted
              (.ordinary o children cuts) fillers admitted fillersAdmitted)
            kind,
          CKTree.addressedMaterialOccurrences_ordinary_material
            o _ ((CKCutPlan.remainderLocallyAdmitted
              (.ordinary o children cuts) admitted)) kind]
        exact childPerm.cons _
      · rw [CKTree.addressedMaterialOccurrences_ordinary_nonmaterial
            o _ (CKCutPlan.fillLocallyAdmitted
              (.ordinary o children cuts) fillers admitted fillersAdmitted)
            kind,
          CKTree.addressedMaterialOccurrences_ordinary_nonmaterial
            o _ ((CKCutPlan.remainderLocallyAdmitted
              (.ordinary o children cuts) admitted)) kind]
        exact childPerm

theorem CKChildCuts.fill_addressedMaterialOccurrences_perm
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    (fillers : (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    (admitted : LocallyAdmittedChildren P children) ->
    (fillersAdmitted : (site : cuts.Site) ->
      LocallyAdmittedTree P (fillers site)) ->
    ((cuts.fill fillers).addressedMaterialOccurrences P
      (cuts.fillLocallyAdmitted fillers admitted fillersAdmitted)).Perm
      ((cuts.remainder.addressedMaterialOccurrences P
          (cuts.remainderLocallyAdmitted admitted)) ++
        cuts.fillerAddressedMaterialOccurrences fillers fillersAdmitted)
  | _, _, .nil, _, _, _ => by
      rfl
  | _, _, .cons head tail headCut tailCuts, fillers, admitted,
      fillersAdmitted => by
      simp only [CKChildCuts.fill, CKChildCuts.remainder,
        CKChildCuts.fillerAddressedMaterialOccurrences]
      rw [CKChildren.addressedMaterialOccurrences_cons,
        CKChildren.addressedMaterialOccurrences_cons]
      apply List.Perm.interleave
      · simpa only [List.map_append] using
          (headCut.fill_addressedMaterialOccurrences_perm
          (fun site => fillers (Sum.inl site)) admitted.1
          (fun site => fillersAdmitted (Sum.inl site))).map
            (AddressedMaterialOccurrence.prefixUse [0])
      · simpa only [List.map_append] using
          (tailCuts.fill_addressedMaterialOccurrences_perm
          (fun site => fillers (Sum.inr site)) admitted.2
          (fun site => fillersAdmitted (Sum.inr site))).map
            AddressedMaterialOccurrence.shiftHead

theorem CKBranchCut.fill_addressedMaterialOccurrences_perm
    {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T} :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)) ->
    (admitted : LocallyAdmittedTree P tree) ->
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) ->
    ((cut.fill fillers).addressedMaterialOccurrences P
      (cut.fillLocallyAdmitted fillers admitted fillersAdmitted)).Perm
      ((cut.remainder.addressedMaterialOccurrences P
          (cut.remainderLocallyAdmitted admitted)) ++
        cut.fillerAddressedMaterialOccurrences fillers fillersAdmitted)
  | _, _, .detach _, _, _, _ => by
      simp only [CKBranchCut.fill, CKBranchCut.remainder,
        CKBranchCut.fillerAddressedMaterialOccurrences,
        CKTree.addressedMaterialOccurrences_interface, List.nil_append]
      exact List.Perm.refl _
  | _, _, .descend cut, fillers, admitted, fillersAdmitted =>
      cut.fill_addressedMaterialOccurrences_perm fillers admitted
        fillersAdmitted

end

/-! ## Public cut laws -/

namespace CKCut

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- The exact addressed material support supplied by a public cut's fillers,
before it is interleaved with retained-context support. -/
def fillerAddressedMaterialOccurrences (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) :
    List (AddressedMaterialOccurrence T.base) :=
  cut.plan.fillerAddressedMaterialOccurrences fillers fillersAdmitted

/-- Address-forgetting multiplicity profile contributed by all fillers. -/
def fillerMaterialProfile (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) :
    Multiset (MaterialBase.ExactOccurrence T.base) :=
  Multiset.ofList <|
    (cut.fillerAddressedMaterialOccurrences fillers fillersAdmitted).map
      Prod.snd

/-- Public canonical-site form of the filler contribution list.  Every inner
source address is prefixed by the exact outer cut address. -/
theorem fillerAddressedMaterialOccurrences_eq_orderedSites
    (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) :
    cut.fillerAddressedMaterialOccurrences fillers fillersAdmitted =
      cut.orderedSites.flatMap fun site =>
        ((fillers site).addressedMaterialOccurrences P
          (fillersAdmitted site)).map
            (AddressedMaterialOccurrence.prefixUse
              (cut.plan.address site)) :=
  cut.plan.fillerAddressedMaterialOccurrences_eq_siteOrder
    fillers fillersAdmitted

/-- Filling partitions exact addressed material occurrences into retained
context uses and filler uses.  `List.Perm` is the explicit occurrence
bijection: it preserves addresses, constructor identities, and multiplicity
while allowing the traversal interleaving to be regrouped. -/
theorem fill_addressedMaterialOccurrences_perm (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (admitted : LocallyAdmittedTree P tree)
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) :
    ((cut.fill fillers).addressedMaterialOccurrences P
      (cut.fill_locallyAdmitted fillers admitted fillersAdmitted)).Perm
      ((cut.remainder.addressedMaterialOccurrences P
          (cut.remainder_locallyAdmitted admitted)) ++
        cut.fillerAddressedMaterialOccurrences fillers fillersAdmitted) :=
  cut.plan.fill_addressedMaterialOccurrences_perm
    fillers admitted fillersAdmitted

/-- Address-forgetting form of the filling law.  Multiset addition collects
the retained-context profile and every filler profile without losing
multiplicity. -/
theorem fill_materialProfile_eq_remainder_add_fillers (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site))
    (admitted : LocallyAdmittedTree P tree)
    (fillersAdmitted : (site : cut.Site) ->
      LocallyAdmittedTree P (fillers site)) :
    (cut.fill fillers).materialProfile
        (cut.fill_locallyAdmitted fillers admitted fillersAdmitted) =
      cut.remainder.materialProfile (cut.remainder_locallyAdmitted admitted) +
        cut.fillerMaterialProfile fillers fillersAdmitted := by
  rw [CKTree.materialProfile_eq_addressedMaterialOccurrences,
    CKTree.materialProfile_eq_addressedMaterialOccurrences]
  change
    (Multiset.ofList
      (((cut.fill fillers).addressedMaterialOccurrences P
        (cut.fill_locallyAdmitted fillers admitted fillersAdmitted)).map
          Prod.snd)) =
      Multiset.ofList
        (((cut.remainder.addressedMaterialOccurrences P
          (cut.remainder_locallyAdmitted admitted)).map Prod.snd) ++
          ((cut.fillerAddressedMaterialOccurrences fillers
            fillersAdmitted).map Prod.snd))
  apply Multiset.coe_eq_coe.mpr
  simpa only [List.map_append] using
    (cut.fill_addressedMaterialOccurrences_perm fillers admitted
      fillersAdmitted).map Prod.snd

/-- Distinguished reconstruction specializes the filling partition back to
the source tree, without forgetting any detached occurrence or address. -/
theorem source_addressedMaterialOccurrences_perm_remainder_append_detached
    (cut : CKCut tree) (admitted : LocallyAdmittedTree P tree) :
    (tree.addressedMaterialOccurrences P admitted).Perm
      ((cut.remainder.addressedMaterialOccurrences P
          (cut.remainder_locallyAdmitted admitted)) ++
        cut.fillerAddressedMaterialOccurrences cut.plan.detached
          (cut.detached_locallyAdmitted admitted)) := by
  have partition := cut.fill_addressedMaterialOccurrences_perm
    cut.plan.detached admitted (cut.detached_locallyAdmitted admitted)
  have reconstructed :
      (cut.fill cut.plan.detached).addressedMaterialOccurrences P
          (cut.fill_locallyAdmitted cut.plan.detached admitted
            (cut.detached_locallyAdmitted admitted)) =
        tree.addressedMaterialOccurrences P admitted := by
    simpa only [cut.fill_detached_reconstructs]
  rw [← reconstructed]
  exact partition

/-- Address-forgetting exact CK-cut partition of the source profile. -/
theorem source_materialProfile_eq_remainder_add_detached
    (cut : CKCut tree) (admitted : LocallyAdmittedTree P tree) :
    tree.materialProfile admitted =
      cut.remainder.materialProfile (cut.remainder_locallyAdmitted admitted) +
        cut.fillerMaterialProfile cut.plan.detached
          (cut.detached_locallyAdmitted admitted) := by
  rw [CKTree.materialProfile_eq_addressedMaterialOccurrences,
    CKTree.materialProfile_eq_addressedMaterialOccurrences]
  change
    Multiset.ofList
        ((tree.addressedMaterialOccurrences P admitted).map Prod.snd) =
      Multiset.ofList
        (((cut.remainder.addressedMaterialOccurrences P
          (cut.remainder_locallyAdmitted admitted)).map Prod.snd) ++
          ((cut.fillerAddressedMaterialOccurrences cut.plan.detached
            (cut.detached_locallyAdmitted admitted)).map Prod.snd))
  apply Multiset.coe_eq_coe.mpr
  simpa only [List.map_append] using
    (cut.source_addressedMaterialOccurrences_perm_remainder_append_detached
      admitted).map Prod.snd

end CKCut

namespace ValidAddressCut

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Public extensional CK-cut partition at full addressed-occurrence level. -/
theorem source_addressedMaterialOccurrences_perm_remainder_append_detached
    (cut : ValidAddressCut tree) (admitted : LocallyAdmittedTree P tree) :
    (tree.addressedMaterialOccurrences P admitted).Perm
      ((cut.toCut.remainder.addressedMaterialOccurrences P
          (cut.toCut.remainder_locallyAdmitted admitted)) ++
        cut.toCut.fillerAddressedMaterialOccurrences cut.toCut.plan.detached
          (cut.toCut.detached_locallyAdmitted admitted)) :=
  cut.toCut.source_addressedMaterialOccurrences_perm_remainder_append_detached
    admitted

/-- Public extensional CK-cut partition after forgetting addresses. -/
theorem source_materialProfile_eq_remainder_add_detached
    (cut : ValidAddressCut tree) (admitted : LocallyAdmittedTree P tree) :
    tree.materialProfile admitted =
      cut.toCut.remainder.materialProfile
          (cut.toCut.remainder_locallyAdmitted admitted) +
        cut.toCut.fillerMaterialProfile cut.toCut.plan.detached
          (cut.toCut.detached_locallyAdmitted admitted) :=
  cut.toCut.source_materialProfile_eq_remainder_add_detached admitted

end ValidAddressCut

/-! ## Compatibility with exact two-stage opening coherence -/

namespace CanonicalTwoStageWitness.CanonicalThreeRegionDecomposition

variable {T : ProofTheory sigma InstanceData} {P : EquippedPresentation T}
variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
variable {first second : ValidAddressCut tree}
variable {witness : CanonicalTwoStageWitness first second}

/-- Material occurrences retained in the actual canonical final root. -/
def rootAddressedMaterialOccurrences
    (_decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree) :
    List (AddressedMaterialOccurrence T.base) :=
  witness.finalCut.toCut.remainder.addressedMaterialOccurrences P
    (witness.finalCut.toCut.remainder_locallyAdmitted admitted)

/-- One source-prefixed middle-region contribution. -/
def middleAddressedMaterialOccurrenceBlock
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree)
    (outer : witness.finalCut.toCut.Site) :
    List (AddressedMaterialOccurrence T.base) :=
  ((decomposition.innerCut outer).toCut.remainder.addressedMaterialOccurrences P
        ((decomposition.innerCut outer).toCut.remainder_locallyAdmitted
          (witness.finalCut.toCut.detached_locallyAdmitted admitted outer))).map
    (AddressedMaterialOccurrence.prefixUse
      (witness.finalCut.toCut.plan.address outer))

/-- One source-prefixed lower-region contribution.  The inner cut first
prefixes relative addresses by its own site; the outer prefix then restores
the literal address in the original source. -/
def lowerAddressedMaterialOccurrenceBlock
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree)
    (outer : witness.finalCut.toCut.Site) :
    List (AddressedMaterialOccurrence T.base) :=
  ((decomposition.innerCut outer).toCut.fillerAddressedMaterialOccurrences
        (decomposition.innerCut outer).toCut.plan.detached
        ((decomposition.innerCut outer).toCut.detached_locallyAdmitted
          (witness.finalCut.toCut.detached_locallyAdmitted admitted outer))).map
    (AddressedMaterialOccurrence.prefixUse
      (witness.finalCut.toCut.plan.address outer))

/-- Canonically outer-site-ordered middle-region material occurrences. -/
def middleAddressedMaterialOccurrences
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree) :
    List (AddressedMaterialOccurrence T.base) :=
  witness.finalCut.toCut.orderedSites.flatMap fun outer =>
    decomposition.middleAddressedMaterialOccurrenceBlock admitted outer

/-- Canonically outer-site-then-inner-site-ordered lower-region material
occurrences. -/
def lowerAddressedMaterialOccurrences
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree) :
    List (AddressedMaterialOccurrence T.base) :=
  witness.finalCut.toCut.orderedSites.flatMap fun outer =>
    decomposition.lowerAddressedMaterialOccurrenceBlock admitted outer

/-- The material support of one detached frontier component partitions into
its actual punctured middle remainder and its actual lower detached family. -/
theorem detachedBlock_addressedMaterialOccurrences_perm_middle_append_lower
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree)
    (outer : witness.finalCut.toCut.Site) :
    (((witness.finalCut.toCut.plan.detached outer).addressedMaterialOccurrences P
          (witness.finalCut.toCut.detached_locallyAdmitted admitted outer)).map
      (AddressedMaterialOccurrence.prefixUse
        (witness.finalCut.toCut.plan.address outer))).Perm
      (decomposition.middleAddressedMaterialOccurrenceBlock admitted outer ++
        decomposition.lowerAddressedMaterialOccurrenceBlock admitted outer) := by
  have innerPartition :=
    CKCut.source_addressedMaterialOccurrences_perm_remainder_append_detached
      (cut := (decomposition.innerCut outer).toCut)
      (witness.finalCut.toCut.detached_locallyAdmitted admitted outer)
  simpa only [middleAddressedMaterialOccurrenceBlock,
      lowerAddressedMaterialOccurrenceBlock, List.map_append] using
    (innerPartition.map
      (AddressedMaterialOccurrence.prefixUse
        (witness.finalCut.toCut.plan.address outer)))

/-- The combined frontier's detached support is exactly the source-addressed
union of canonical middle and lower support. -/
theorem frontierDetached_addressedMaterialOccurrences_perm_middle_append_lower
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree) :
    (witness.finalCut.toCut.fillerAddressedMaterialOccurrences
      witness.finalCut.toCut.plan.detached
      (witness.finalCut.toCut.detached_locallyAdmitted admitted)).Perm
      (decomposition.middleAddressedMaterialOccurrences admitted ++
        decomposition.lowerAddressedMaterialOccurrences admitted) := by
  rw [CKCut.fillerAddressedMaterialOccurrences_eq_orderedSites]
  simpa only [middleAddressedMaterialOccurrences,
      lowerAddressedMaterialOccurrences] using
    List.Perm.flatMap_interleave witness.finalCut.toCut.orderedSites
      (fun outer =>
        ((witness.finalCut.toCut.plan.detached outer).addressedMaterialOccurrences P
            (witness.finalCut.toCut.detached_locallyAdmitted admitted outer)).map
          (AddressedMaterialOccurrence.prefixUse
            (witness.finalCut.toCut.plan.address outer)))
      (fun outer =>
        decomposition.middleAddressedMaterialOccurrenceBlock admitted outer)
      (fun outer =>
        decomposition.lowerAddressedMaterialOccurrenceBlock admitted outer)
      (decomposition.detachedBlock_addressedMaterialOccurrences_perm_middle_append_lower
        admitted)

/-- Exact occurrence-level material partition over the canonical two-stage
root/middle/lower decomposition.  Every inner use carries the literal
concatenated source address, exact occurrence, decoration, and multiplicity. -/
theorem source_addressedMaterialOccurrences_perm_root_middle_lower
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree) :
    (tree.addressedMaterialOccurrences P admitted).Perm
      ((decomposition.rootAddressedMaterialOccurrences admitted ++
        decomposition.middleAddressedMaterialOccurrences admitted) ++
        decomposition.lowerAddressedMaterialOccurrences admitted) := by
  have outerPartition :=
    CKCut.source_addressedMaterialOccurrences_perm_remainder_append_detached
      (cut := witness.finalCut.toCut) admitted
  have innerPartition :=
    frontierDetached_addressedMaterialOccurrences_perm_middle_append_lower
      decomposition admitted
  apply outerPartition.trans
  simpa only [rootAddressedMaterialOccurrences, List.append_assoc] using
    innerPartition.append_left
      (decomposition.rootAddressedMaterialOccurrences admitted)

/-- Address-forgetting corollary of the exact canonical three-region
partition. -/
theorem source_materialProfile_eq_root_add_middle_add_lower
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree) :
    tree.materialProfile admitted =
      (Multiset.ofList
          ((decomposition.rootAddressedMaterialOccurrences admitted).map
            Prod.snd) +
        Multiset.ofList
          ((decomposition.middleAddressedMaterialOccurrences admitted).map
            Prod.snd)) +
      Multiset.ofList
        ((decomposition.lowerAddressedMaterialOccurrences admitted).map
          Prod.snd) := by
  rw [CKTree.materialProfile_eq_addressedMaterialOccurrences]
  apply Multiset.coe_eq_coe.mpr
  simpa only [List.map_append] using
    (decomposition.source_addressedMaterialOccurrences_perm_root_middle_lower
      admitted).map Prod.snd

/-- Compatibility package for Stage A and Stage B: the two actual schedules
have the same decorated three-region basis data, while material support of the
source is bijectively partitioned over that canonical root/middle/lower data.
The occurrence permutation is primary; the collected profile is only its
corollary. -/
theorem exactTwoStageMaterialPartitionCoherence
    (decomposition : CanonicalThreeRegionDecomposition witness)
    (admitted : LocallyAdmittedTree P tree) :
    witness.firstScheduleRegionData = witness.secondScheduleRegionData ∧
      (tree.addressedMaterialOccurrences P admitted).Perm
        ((decomposition.rootAddressedMaterialOccurrences admitted ++
          decomposition.middleAddressedMaterialOccurrences admitted) ++
          decomposition.lowerAddressedMaterialOccurrences admitted) :=
  ⟨witness.scheduleRegionData_cohere,
    decomposition.source_addressedMaterialOccurrences_perm_root_middle_lower
      admitted⟩

end CanonicalTwoStageWitness.CanonicalThreeRegionDecomposition


end Potkin

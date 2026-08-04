import Potkin.MaterialSupport
import Potkin.CKCutValidity

/-!
# Maximal wholly-material regions

This module turns the nonroot part of `CKTree.maximalMaterialAddresses` into
an intrinsic CK cut.  The exceptional whole-tree case remains an address
antichain containing `[]`; it is deliberately not represented as a root cut.
-/

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

mutual

/-- Descend through the source root and choose the maximal material regions
in its ordered premises. -/
def CKTree.maximalMaterialPlan : {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) -> CKCutPlan tree
  | _, .interface G => .interface G
  | _, .ordinary o children =>
      .ordinary o children children.maximalMaterialCuts

/-- Constructor-recursive choices in an exact ordered premise tuple. -/
def CKChildren.maximalMaterialCuts :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
      CKChildCuts children
  | _, .nil => .nil
  | _, .cons head tail =>
      .cons head tail head.maximalMaterialBranch
        tail.maximalMaterialCuts

/-- Detach a positive branch exactly when the entire branch is material;
otherwise continue recursively below its root.  Interfaces are vacancies and
are never detached despite satisfying `AllVerticesMaterial` vacuously. -/
def CKTree.maximalMaterialBranch : {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) -> CKBranchCut tree
  | _, .interface G => .descend (.interface G)
  | _, .ordinary o children =>
      if pure : (CKTree.ordinary o children).AllVerticesMaterial then
        .detach (by trivial)
      else
        .descend (.ordinary o children children.maximalMaterialCuts)

end

mutual

/-- The recursive child choices have exactly the advertised finite set of
maximal roots. -/
theorem CKChildren.maximalMaterialCuts_addressFinset :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    children.maximalMaterialCuts.addressFinset =
      children.maximalMaterialAddresses.toFinset
  | _, .nil => by
      simp [CKChildren.maximalMaterialCuts, CKChildCuts.addressFinset,
        CKChildren.maximalMaterialAddresses]
  | _, .cons head tail => by
      simp [CKChildren.maximalMaterialCuts, CKChildCuts.addressFinset,
        CKChildren.maximalMaterialAddresses,
        CKTree.maximalMaterialBranch_addressFinset head,
        CKChildren.maximalMaterialCuts_addressFinset tail]
      ext address
      simp

/-- A branch detaches exactly its whole positive pure source, or inherits the
maximal finite set found strictly below its root. -/
theorem CKTree.maximalMaterialBranch_addressFinset :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    tree.maximalMaterialBranch.relativeAddressFinset =
      tree.maximalMaterialAddresses.toFinset
  | _, .interface G => by
      simp [CKTree.maximalMaterialBranch,
        CKBranchCut.relativeAddressFinset, CKCutPlan.addressFinset,
        CKTree.maximalMaterialAddresses]
  | _, .ordinary o children => by
      by_cases pure : (CKTree.ordinary o children).AllVerticesMaterial
      · simp [CKTree.maximalMaterialBranch,
          CKBranchCut.relativeAddressFinset,
          CKTree.maximalMaterialAddresses, pure]
      · simp [CKTree.maximalMaterialBranch,
          CKBranchCut.relativeAddressFinset, CKCutPlan.addressFinset,
          CKTree.maximalMaterialAddresses, pure,
          CKChildren.maximalMaterialCuts_addressFinset children]

end

/-- Below a nonmaterial source root, the recursive plan selects exactly the
advertised maximal material roots.  The hypothesis is essential: if the whole
tree is pure, the advertised maximal root is `[]`, which no CK plan may select.
-/
theorem CKTree.maximalMaterialPlan_addressFinset_of_notPure
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (notPure : ¬ tree.AllVerticesMaterial) :
    tree.maximalMaterialPlan.addressFinset =
      tree.maximalMaterialAddresses.toFinset := by
  cases tree with
  | interface _ => exact (notPure trivial).elim
  | ordinary o children =>
      simp [CKTree.maximalMaterialPlan, CKCutPlan.addressFinset,
        CKTree.maximalMaterialAddresses, notPure,
        CKChildren.maximalMaterialCuts_addressFinset]

/-! ## The root exception and the public nonroot cut -/

/-- A positive wholly-material tree has one maximal region, namely its whole
root. -/
theorem CKTree.maximalMaterialAddresses_eq_root
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) (pure : tree.AllVerticesMaterial) :
    tree.maximalMaterialAddresses = [[]] := by
  cases tree with
  | interface _ => exact False.elim ordinary
  | ordinary o children =>
      simp [CKTree.maximalMaterialAddresses, pure]

/-- No valid nonroot CK address cut can have the singleton root address. -/
theorem CKTree.root_singleton_not_validAddressCut
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G) :
    ¬ ∃ cut : ValidAddressCut tree, cut.addresses = {[]} := by
  rintro ⟨cut, addresses⟩
  have rootMember : [] ∈ cut.addresses := by
    rw [addresses]
    simp
  exact cut.address_nonroot rootMember rfl

/-- Hence the whole-pure singleton is explicitly an address-antichain case,
not a nonroot CK cut. -/
theorem CKTree.wholeMaterialRoot_not_validAddressCut
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) (pure : tree.AllVerticesMaterial) :
    tree.maximalMaterialAddresses = [[]] ∧
      ¬ ∃ cut : ValidAddressCut tree,
        cut.addresses = tree.maximalMaterialAddresses.toFinset := by
  refine ⟨tree.maximalMaterialAddresses_eq_root ordinary pure, ?_⟩
  rw [tree.maximalMaterialAddresses_eq_root ordinary pure]
  simpa using tree.root_singleton_not_validAddressCut

/-- When the whole source is not material, the constructor-recursive maximal
region plan is a genuine CK cut.  It may be the empty cut if no positive pure
subtree exists. -/
def CKTree.maximalMaterialCut
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) (_notPure : ¬ tree.AllVerticesMaterial) :
    CKCut tree where
  sourceOrdinary := ordinary
  plan := tree.maximalMaterialPlan

/-- Public extensional form of the maximal-region cut. -/
def CKTree.maximalMaterialExtensionalCut
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) (notPure : ¬ tree.AllVerticesMaterial) :
    ExtensionalCKCut tree :=
  ExtensionalCKCut.ofCKCut (tree.maximalMaterialCut ordinary notPure)

/-- The public valid address family is exactly the finite set of maximal
material roots. -/
theorem CKTree.maximalMaterialCut_validAddresses
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (ordinary : tree.IsOrdinary) (notPure : ¬ tree.AllVerticesMaterial) :
    (tree.maximalMaterialCut ordinary notPure).validAddressCut.addresses =
      tree.maximalMaterialAddresses.toFinset := by
  rw [show (tree.maximalMaterialCut ordinary notPure).validAddressCut.addresses =
      (tree.maximalMaterialCut ordinary notPure).plan.addressFinset from rfl]
  exact tree.maximalMaterialPlan_addressFinset_of_notPure notPure

/-! ## Purity of every selected detached region -/

/-- Every detached subtree selected by one branch satisfies whole-vertex
materiality.  Naming this dependent property keeps branch replacement
transport explicit and proof-irrelevant. -/
def CKBranchCut.DetachedAllVerticesMaterial
    {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKBranchCut tree) : Prop :=
  ∀ site : cut.Site, (cut.detached site).AllVerticesMaterial

mutual

/-- Every region detached by the maximal-region plan is wholly material. -/
theorem CKTree.maximalMaterialPlan_detached_allVerticesMaterial :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    (site : tree.maximalMaterialPlan.Site) ->
    (tree.maximalMaterialPlan.detached site).AllVerticesMaterial
  | _, .interface _, site => nomatch site
  | _, .ordinary _ children, site =>
      CKChildren.maximalMaterialCuts_detached_allVerticesMaterial
        children site

/-- Ordered-child form of detached-region purity. -/
theorem CKChildren.maximalMaterialCuts_detached_allVerticesMaterial :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    (site : children.maximalMaterialCuts.Site) ->
    (children.maximalMaterialCuts.detached site).AllVerticesMaterial
  | _, .nil, site => nomatch site
  | _, .cons head tail, site => by
      change Sum head.maximalMaterialBranch.Site
        tail.maximalMaterialCuts.Site at site
      cases site with
      | inl site =>
          exact CKTree.maximalMaterialBranch_detached_allVerticesMaterial
            head site
      | inr site =>
          exact CKChildren.maximalMaterialCuts_detached_allVerticesMaterial
            tail site

/-- Branch form of detached-region purity. -/
theorem CKTree.maximalMaterialBranch_detached_allVerticesMaterial :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    tree.maximalMaterialBranch.DetachedAllVerticesMaterial
  | _, .interface _ => by
      change CKBranchCut.DetachedAllVerticesMaterial
        (CKBranchCut.descend (CKCutPlan.interface _))
      intro site
      nomatch site
  | _, .ordinary o children => by
      by_cases pure : (CKTree.ordinary o children).AllVerticesMaterial
      · have branchEq :
            (CKTree.ordinary o children).maximalMaterialBranch =
              CKBranchCut.detach (tree := CKTree.ordinary o children)
                (by trivial) := by
            simp [CKTree.maximalMaterialBranch, pure]
        rw [branchEq]
        intro site
        change PUnit at site
        cases site
        exact pure
      · have branchEq :
            (CKTree.ordinary o children).maximalMaterialBranch =
              CKBranchCut.descend
                (CKCutPlan.ordinary o children
                  children.maximalMaterialCuts) := by
            simp [CKTree.maximalMaterialBranch, pure]
        rw [branchEq]
        intro site
        exact CKChildren.maximalMaterialCuts_detached_allVerticesMaterial
          children site

end

/-! ## Downward stratification and material-use coverage -/

mutual

/-- Material is downward closed when every material vertex has wholly
material premise subtrees, and the same condition holds recursively below
all (including nonmaterial) vertices.  This is static constructor
stratification, not an execution or reachability condition. -/
def CKTree.MaterialDownwardClosed : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> Prop
  | _, .interface _ => True
  | _, .ordinary o children =>
      children.MaterialDownwardClosed ∧
        (o.kind = .material → children.AllVerticesMaterial)

/-- Ordered-child form of `CKTree.MaterialDownwardClosed`. -/
def CKChildren.MaterialDownwardClosed :
    {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries -> Prop
  | _, .nil => True
  | _, .cons head tail =>
      head.MaterialDownwardClosed ∧ tail.MaterialDownwardClosed

end

mutual

/-- A wholly material tree satisfies downward stratification. -/
theorem CKTree.AllVerticesMaterial.materialDownwardClosed :
    {G : Hypersequent sigma} -> {tree : CKTree sigma InstanceData G} ->
    tree.AllVerticesMaterial -> tree.MaterialDownwardClosed
  | _, .interface _, _ => trivial
  | _, .ordinary _ children, pure =>
      ⟨CKChildren.AllVerticesMaterial.materialDownwardClosed pure.2,
        fun _ => pure.2⟩

/-- Ordered-child form of pure-to-stratified transport. -/
theorem CKChildren.AllVerticesMaterial.materialDownwardClosed :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    children.AllVerticesMaterial -> children.MaterialDownwardClosed
  | _, .nil, _ => trivial
  | _, .cons _ _, pure =>
      ⟨CKTree.AllVerticesMaterial.materialDownwardClosed pure.1,
        CKChildren.AllVerticesMaterial.materialDownwardClosed pure.2⟩

end


/-- At a material root, downward stratification makes the whole rooted tree
wholly material. -/
theorem CKTree.MaterialDownwardClosed.allVerticesMaterial_of_rootMaterial
    {o : LocalOccurrence sigma InstanceData}
    {children : CKChildren sigma InstanceData o.shape.premises}
    (closed : (CKTree.ordinary o children).MaterialDownwardClosed)
    (kind : o.kind = .material) :
    (CKTree.ordinary o children).AllVerticesMaterial :=
  ⟨kind, closed.2 kind⟩

namespace CKTree.MaterialUse

variable {pi : PrimitiveFragment sigma}
variable {B : MaterialBase sigma InstanceData pi}

/-- A material use is covered when its exact source address lies below one
of the maximal wholly-material roots. -/
def CoveredByMaximalMaterialRegion {G : Hypersequent sigma}
    {tree : CKTree sigma InstanceData G}
    (use : CKTree.MaterialUse B tree) : Prop :=
  ∃ root ∈ tree.maximalMaterialAddresses,
    AddressPrefix root use.sourceAddress

end CKTree.MaterialUse

namespace CKChildren.MaterialUse

variable {pi : PrimitiveFragment sigma}
variable {B : MaterialBase sigma InstanceData pi}

/-- Child-tuple coverage uses addresses relative to the node owning the
tuple. -/
def CoveredByMaximalMaterialRegion
    {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (use : CKChildren.MaterialUse B children) : Prop :=
  ∃ root ∈ children.maximalMaterialAddresses,
    AddressPrefix root use.sourceAddress

/-- Every child-tuple material-use address starts with an exact premise
selector. -/
theorem sourceAddress_ne_nil
    {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (use : CKChildren.MaterialUse B children) :
    use.sourceAddress ≠ [] := by
  cases use with
  | head use =>
      simp [CKChildren.MaterialUse.sourceAddress]
  | tail use =>
      have ih := sourceAddress_ne_nil use
      cases addressEq : use.sourceAddress with
      | nil => exact (ih addressEq).elim
      | cons slot rest =>
          simp [CKChildren.MaterialUse.sourceAddress, addressEq,
            InternalAddress.shiftHead]

end CKChildren.MaterialUse

/-- Maximal-region addresses in a child tuple are all nonempty because each
begins with an ordered premise selector. -/
theorem CKChildren.maximalMaterialAddress_ne_nil_of_mem :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    {address : InternalAddress} ->
    address ∈ children.maximalMaterialAddresses -> address ≠ []
  | _, .nil, _, member => by
      simp [CKChildren.maximalMaterialAddresses] at member
  | _, .cons head tail, address, member => by
      rw [CKChildren.maximalMaterialAddresses] at member
      rcases List.mem_append.mp member with headMember | tailMember
      · rcases List.mem_map.mp headMember with ⟨relative, _, rfl⟩
        simp
      · rcases List.mem_map.mp tailMember with
          ⟨relative, relativeMember, rfl⟩
        have relativeNonempty :=
          CKChildren.maximalMaterialAddress_ne_nil_of_mem tail
            relativeMember
        cases relative with
        | nil => exact (relativeNonempty rfl).elim
        | cons slot rest => simp [InternalAddress.shiftHead]

mutual

/-- Downward stratification covers every proof-relevant material use by one
maximal wholly-material region. -/
theorem CKTree.MaterialUse.coveredByMaximalMaterialRegion_of_downwardClosed
    {pi : PrimitiveFragment sigma}
    {B : MaterialBase sigma InstanceData pi} :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    tree.MaterialDownwardClosed ->
    (use : CKTree.MaterialUse B tree) ->
    use.CoveredByMaximalMaterialRegion
  | _, _, closed, .root member => by
      have kind := B.member_material member
      have pure : _ ∧ _ :=
        ⟨kind, closed.2 kind⟩
      simp [CKTree.MaterialUse.CoveredByMaximalMaterialRegion,
        CKTree.MaterialUse.sourceAddress,
        CKTree.maximalMaterialAddresses, CKTree.AllVerticesMaterial,
        pure, AddressPrefix]
  | _, _, closed, .descend use => by
      simp only [CKTree.MaterialUse.CoveredByMaximalMaterialRegion,
        CKTree.MaterialUse.sourceAddress,
        CKTree.maximalMaterialAddresses]
      split
      next pure =>
        refine ⟨[], by simp, ?_⟩
        simp [AddressPrefix]
      next notPure =>
        simpa [CKChildren.MaterialUse.CoveredByMaximalMaterialRegion] using
          CKChildren.MaterialUse.coveredByMaximalMaterialRegion_of_downwardClosed
            closed.1 use

/-- Ordered-child form of stratified coverage. -/
theorem CKChildren.MaterialUse.coveredByMaximalMaterialRegion_of_downwardClosed
    {pi : PrimitiveFragment sigma}
    {B : MaterialBase sigma InstanceData pi} :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    children.MaterialDownwardClosed ->
    (use : CKChildren.MaterialUse B children) ->
    use.CoveredByMaximalMaterialRegion
  | _, _, closed, .head use => by
      rcases
          CKTree.MaterialUse.coveredByMaximalMaterialRegion_of_downwardClosed
            closed.1 use with ⟨root, rootMember, prefixProof⟩
      refine ⟨0 :: root, ?_, ?_⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨root, rootMember, rfl⟩
      · simpa [CKTree.MaterialUse.CoveredByMaximalMaterialRegion,
          CKChildren.MaterialUse.CoveredByMaximalMaterialRegion,
          CKChildren.MaterialUse.sourceAddress, AddressPrefix] using
            prefixProof
  | _, _, closed, .tail use => by
      rcases
          CKChildren.MaterialUse.coveredByMaximalMaterialRegion_of_downwardClosed
            closed.2 use with ⟨root, rootMember, prefixProof⟩
      refine ⟨InternalAddress.shiftHead root, ?_, ?_⟩
      · apply List.mem_append_right
        exact List.mem_map.mpr ⟨root, rootMember, rfl⟩
      · exact (InternalAddress.shiftHead_prefix_iff
          (CKChildren.maximalMaterialAddress_ne_nil_of_mem _ rootMember)
          use.sourceAddress_ne_nil).mpr prefixProof

end

/-!
The downward-closure hypothesis in the coverage theorem is essential.  An
isolated material constructor may have a nonmaterial descendant, in which
case that use lies under no wholly-material maximal root.  A small concrete
counterfixture belongs in `Potkin.Examples.MaterialSupport`; it is not part of
this universal theorem module.
-/

end Potkin

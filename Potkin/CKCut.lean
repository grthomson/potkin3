import Mathlib.Data.List.Lex
import Mathlib.Data.List.Nodup
import Potkin.RootCut

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

namespace InternalAddress

/-- Increment the first selector.  This embeds an address for a tail of an
ordered child tuple into the tuple obtained by adjoining one child on the
left. -/
def shiftHead : InternalAddress -> InternalAddress
  | [] => []
  | i :: rest => (i + 1) :: rest

@[simp]
theorem shiftHead_nil : shiftHead [] = [] := rfl

@[simp]
theorem shiftHead_cons (i : Nat) (rest : InternalAddress) :
    shiftHead (i :: rest) = (i + 1) :: rest := rfl

@[simp]
theorem toRacket_append (p q : InternalAddress) :
    (p ++ q).toRacket.slots = p.toRacket.slots ++ q.toRacket.slots := by
  simp [InternalAddress.toRacket]

/-- Incrementing the first selector preserves strict lexicographic order on
nonempty child addresses. -/
theorem shiftHead_lt_of_lt {p q : InternalAddress}
    (p_nonempty : p ≠ []) (q_nonempty : q ≠ []) (less : p < q) :
    shiftHead p < shiftHead q := by
  cases p with
  | nil => exact (p_nonempty rfl).elim
  | cons i p =>
      cases q with
      | nil => exact (q_nonempty rfl).elim
      | cons j q =>
          change List.Lex (fun a b : Nat => a < b) (i :: p) (j :: q) at less
          change List.Lex (fun a b : Nat => a < b)
            ((i + 1) :: p) ((j + 1) :: q)
          cases less with
          | rel headLess => exact .rel (Nat.add_lt_add_right headLess 1)
          | cons tailLess => exact .cons tailLess

/-- First-selector shifting preserves and reflects prefixing on nonempty
child addresses. -/
theorem shiftHead_prefix_iff {p q : InternalAddress}
    (p_nonempty : p ≠ []) (q_nonempty : q ≠ []) :
    AddressPrefix (shiftHead p) (shiftHead q) ↔ AddressPrefix p q := by
  cases p with
  | nil => exact (p_nonempty rfl).elim
  | cons i p =>
      cases q with
      | nil => exact (q_nonempty rfl).elim
      | cons j q =>
          simp [AddressPrefix, shiftHead]

end InternalAddress

namespace RacketAddress

/-- Positive prefixing commutes with the zero/one-based interchange. -/
@[simp]
theorem toInternal_append (p q : RacketAddress) :
    ({ slots := p.slots ++ q.slots
       positive := by
         intro n hn
         rcases List.mem_append.mp hn with hn | hn
         · exact p.positive n hn
         · exact q.positive n hn } : RacketAddress).toInternal =
      p.toInternal ++ q.toInternal := by
  simp [RacketAddress.toInternal]

end RacketAddress

namespace CKTree

/-- Interfaces are addressable vacancies but are never ordinary vertices. -/
inductive InterfaceAt : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> InternalAddress -> Prop where
  | root (G : Hypersequent sigma) : InterfaceAt (.interface G) []
  | child (o : LocalOccurrence sigma InstanceData)
      (children : CKChildren sigma InstanceData o.shape.premises)
      (i : Fin o.shape.premises.length) {address : InternalAddress}
      (below : InterfaceAt (children.get i) address) :
      InterfaceAt (.ordinary o children) (i.1 :: address)

/-- Recover the whole boundary carried by the tree index. -/
def rootBoundary {G : Hypersequent sigma}
    (_tree : CKTree sigma InstanceData G) : Hypersequent sigma := G

end CKTree

mutual

/-- Ordinary-vertex degree; interfaces contribute zero. -/
def CKTree.degree : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> Nat
  | _, .interface _ => 0
  | _, .ordinary _ children => children.degree + 1

/-- Degree of one ordered child tuple. -/
def CKChildren.degree : {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries -> Nat
  | _, .nil => 0
  | _, .cons head tail => head.degree + tail.degree

end

mutual

/-- A structural cut below a tree root.  This helper may be empty even when
the tree is an interface; the public `CKCut` wrapper requires a positive
ordinary source. -/
inductive CKCutPlan : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> Type (max (max u v) w) where
  | interface (G : Hypersequent sigma) : CKCutPlan (.interface G)
  | ordinary (o : LocalOccurrence sigma InstanceData)
      (children : CKChildren sigma InstanceData o.shape.premises)
      (cuts : CKChildCuts children) : CKCutPlan (.ordinary o children)

/-- Independent recursive choices for an exact ordered child tuple. -/
inductive CKChildCuts : {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries -> Type (max (max u v) w) where
  | nil : CKChildCuts (.nil : CKChildren sigma InstanceData [])
  | cons {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
      (head : CKTree sigma InstanceData G)
      (tail : CKChildren sigma InstanceData Gs)
      (headCut : CKBranchCut head) (tailCuts : CKChildCuts tail) :
      CKChildCuts (.cons head tail)

/-- At one premise either detach its ordinary root, or descend strictly below
that root.  The alternatives are disjoint and make ancestor/descendant cuts
unrepresentable. -/
inductive CKBranchCut : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> Type (max (max u v) w) where
  | detach {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
      (ordinary : tree.IsOrdinary) : CKBranchCut tree
  | descend {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
      (cut : CKCutPlan tree) : CKBranchCut tree

end

/-- A CK cut of a positive rooted source.  Empty cuts are represented by an
all-descend plan containing no detach choice. -/
structure CKCut {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) where
  sourceOrdinary : tree.IsOrdinary
  plan : CKCutPlan tree

mutual

/-- Occurrence identities are a finite recursive sum in canonical premise
order. -/
def CKCutPlan.Site : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    CKCutPlan tree -> Type
  | _, _, .interface _ => PEmpty
  | _, _, .ordinary _ _ cuts => cuts.Site

/-- A child-tuple site lies in the head branch or the ordered tail. -/
def CKChildCuts.Site : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    CKChildCuts children -> Type
  | _, _, .nil => PEmpty
  | _, _, .cons _ _ headCut tailCuts => Sum headCut.Site tailCuts.Site

/-- Detachment contributes one site; descent inherits its nested sites. -/
def CKBranchCut.Site : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    CKBranchCut tree -> Type
  | _, _, .detach _ => PUnit
  | _, _, .descend cut => cut.Site

end

namespace CKCut

/-- Exact selected occurrence type. -/
abbrev Site {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}
    (cut : CKCut tree) := cut.plan.Site

end CKCut

mutual

/-- Canonical occurrence order induced by ordered premises and recursive
descent. -/
def CKCutPlan.siteOrder : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> List cut.Site
  | _, _, .interface _ => []
  | _, _, .ordinary _ _ cuts => cuts.siteOrder

def CKChildCuts.siteOrder : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> List cuts.Site
  | _, _, .nil => []
  | _, _, .cons _ _ headCut tailCuts =>
      headCut.siteOrder.map Sum.inl ++ tailCuts.siteOrder.map Sum.inr

def CKBranchCut.siteOrder : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> List cut.Site
  | _, _, .detach _ => [PUnit.unit]
  | _, _, .descend cut => cut.siteOrder

end

mutual

/-- Every structural site occurs in the canonical premise-recursive order. -/
theorem CKCutPlan.site_mem_siteOrder : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (site : cut.Site) ->
      site ∈ cut.siteOrder
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary _ _ cuts, site => cuts.site_mem_siteOrder site

/-- The canonical child-tuple traversal is complete. -/
theorem CKChildCuts.site_mem_siteOrder :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (site : cuts.Site) ->
      site ∈ cuts.siteOrder
  | _, _, .nil, site => nomatch site
  | _, _, .cons _ _ headCut tailCuts, site => by
      change Sum headCut.Site tailCuts.Site at site
      cases site with
      | inl site =>
          apply List.mem_append_left
          exact List.mem_map.mpr
            ⟨site, headCut.site_mem_siteOrder site, rfl⟩
      | inr site =>
          apply List.mem_append_right
          exact List.mem_map.mpr
            ⟨site, tailCuts.site_mem_siteOrder site, rfl⟩

/-- The canonical branch traversal is complete. -/
theorem CKBranchCut.site_mem_siteOrder : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (site : cut.Site) ->
      site ∈ cut.siteOrder
  | _, _, .detach _, site => by
      change PUnit at site
      cases site
      simp [CKBranchCut.siteOrder]
  | _, _, .descend cut, site => cut.site_mem_siteOrder site

end

mutual

/-- Canonical site traversal contains each occurrence identity once. -/
theorem CKCutPlan.siteOrder_nodup : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> cut.siteOrder.Nodup
  | _, _, .interface _ => by simp [CKCutPlan.siteOrder]
  | _, _, .ordinary _ _ cuts => cuts.siteOrder_nodup

/-- Ordered child branches have disjoint sum-tagged site traversals. -/
theorem CKChildCuts.siteOrder_nodup :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> cuts.siteOrder.Nodup
  | _, _, .nil => by simp [CKChildCuts.siteOrder]
  | _, _, .cons _ _ headCut tailCuts => by
      apply List.Nodup.append
        (headCut.siteOrder_nodup.map Sum.inl_injective)
        (tailCuts.siteOrder_nodup.map Sum.inr_injective)
      simp [List.disjoint_left]

/-- A detach singleton or recursively inherited descent order has no repeats. -/
theorem CKBranchCut.siteOrder_nodup : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> cut.siteOrder.Nodup
  | _, _, .detach _ => by simp [CKBranchCut.siteOrder]
  | _, _, .descend cut => cut.siteOrder_nodup

end

mutual

/-- Relative address inside one selected child branch. -/
def CKBranchCut.relativeAddress : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> cut.Site -> InternalAddress
  | _, _, .detach _, _ => []
  | _, _, .descend cut, site => cut.address site

/-- Address below the node owning an ordered child tuple. -/
def CKChildCuts.address : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> cuts.Site -> InternalAddress
  | _, _, .nil => fun site => nomatch site
  | _, _, .cons head tail headCut tailCuts => fun site =>
      match site with
      | Sum.inl headSite => 0 :: headCut.relativeAddress headSite
      | Sum.inr tailSite =>
          InternalAddress.shiftHead (tailCuts.address tailSite)

/-- Exact zero-based root-to-vertex address of one site. -/
def CKCutPlan.address : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> cut.Site -> InternalAddress
  | _, _, .ordinary _ _ cuts, site => cuts.address site

end

mutual

/-- A plan address selects an existing ordinary vertex of its exact source. -/
theorem CKCutPlan.address_vertexAt : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (site : cut.Site) ->
      tree.VertexAt (cut.address site)
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary o children cuts, site => by
      rcases cuts.address_selects_vertex site with
        ⟨i, rest, address_eq, below⟩
      change (CKTree.ordinary o children).VertexAt (cuts.address site)
      rw [address_eq]
      exact .child o children i below

/-- A child-tuple address decomposes into its exact ordered slot and a valid
ordinary relative vertex below that child. -/
theorem CKChildCuts.address_selects_vertex :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (site : cuts.Site) ->
      ∃ (i : Fin boundaries.length) (rest : InternalAddress),
        cuts.address site = i.1 :: rest ∧
          (children.get i).VertexAt rest
  | _, _, .nil, site => nomatch site
  | _, _, .cons _ _ headCut tailCuts, site => by
      change Sum headCut.Site tailCuts.Site at site
      cases site with
      | inl site =>
          exact
            ⟨⟨0, by simp⟩, headCut.relativeAddress site, rfl,
              headCut.relativeAddress_vertexAt site⟩
      | inr site =>
          rcases tailCuts.address_selects_vertex site with
            ⟨i, rest, address_eq, below⟩
          refine ⟨i.succ, rest, ?_, ?_⟩
          · simp only [CKChildCuts.address, address_eq,
              InternalAddress.shiftHead_cons, Fin.val_succ]
          · exact below

/-- Relative branch addresses select ordinary vertices in that branch. -/
theorem CKBranchCut.relativeAddress_vertexAt : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (site : cut.Site) ->
      tree.VertexAt (cut.relativeAddress site)
  | _, _, .detach ordinary, site => by
      change PUnit at site
      cases site
      exact CKTree.vertexAt_root_of_isOrdinary ordinary
  | _, _, .descend cut, site => cut.address_vertexAt site

end


/-- Every child-tuple cut address is nonempty, since it begins with an
ordered premise selector. -/
theorem CKChildCuts.address_nonroot
    {boundaries : List (Hypersequent sigma)}
    {children : CKChildren sigma InstanceData boundaries}
    (cuts : CKChildCuts children) (site : cuts.Site) :
    cuts.address site ≠ [] := by
  rcases cuts.address_selects_vertex site with ⟨i, rest, address_eq, _⟩
  rw [address_eq]
  simp

mutual

/-- Distinct structural plan sites are prefix-incomparable. -/
theorem CKCutPlan.addresses_prefixIncomparable : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> {p q : cut.Site} -> p ≠ q ->
      PrefixIncomparable (cut.address p) (cut.address q)
  | _, _, .interface _, p, _, _ => nomatch p
  | _, _, .ordinary _ _ cuts, _, _, different =>
      cuts.addresses_prefixIncomparable different

/-- Independent premise branches are disjoint, while recursive sites in one
branch inherit prefix-incomparability. -/
theorem CKChildCuts.addresses_prefixIncomparable :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> {p q : cuts.Site} -> p ≠ q ->
      PrefixIncomparable (cuts.address p) (cuts.address q)
  | _, _, .nil, p, _, _ => nomatch p
  | _, _, .cons _ _ headCut tailCuts, p, q, different => by
      change Sum headCut.Site tailCuts.Site at p q
      cases p with
      | inl p =>
          cases q with
          | inl q =>
              have nestedDifferent : p ≠ q := by
                intro equal
                exact different (congrArg Sum.inl equal)
              simpa [CKChildCuts.address, PrefixIncomparable,
                AddressPrefix] using
                headCut.relativeAddresses_prefixIncomparable nestedDifferent
          | inr q =>
              rcases tailCuts.address_selects_vertex q with
                ⟨i, rest, address_eq, _⟩
              simp [CKChildCuts.address, address_eq, PrefixIncomparable,
                AddressPrefix]
      | inr p =>
          cases q with
          | inl q =>
              rcases tailCuts.address_selects_vertex p with
                ⟨i, rest, address_eq, _⟩
              simp [CKChildCuts.address, address_eq, PrefixIncomparable,
                AddressPrefix]
          | inr q =>
              have nestedDifferent : p ≠ q := by
                intro equal
                exact different (congrArg Sum.inr equal)
              rcases tailCuts.address_selects_vertex p with
                ⟨i, rest, addressP, _⟩
              rcases tailCuts.address_selects_vertex q with
                ⟨j, rest', addressQ, _⟩
              simpa [CKChildCuts.address, addressP, addressQ,
                PrefixIncomparable, AddressPrefix] using
                tailCuts.addresses_prefixIncomparable nestedDifferent

/-- Detachment has one relative site; descent inherits the nested antichain. -/
theorem CKBranchCut.relativeAddresses_prefixIncomparable :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> {p q : cut.Site} -> p ≠ q ->
      PrefixIncomparable (cut.relativeAddress p) (cut.relativeAddress q)
  | _, _, .detach _, p, q, different => by
      change PUnit at p q
      cases p
      cases q
      exact (different rfl).elim
  | _, _, .descend cut, p, q, different =>
      cut.addresses_prefixIncomparable different

end

mutual

/-- Canonical plan traversal is strictly lexicographic by exact address. -/
theorem CKCutPlan.addresses_lexPairwise : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
      cut.siteOrder.Pairwise
        (fun p q => cut.address p < cut.address q)
  | _, _, .interface _ => by simp [CKCutPlan.siteOrder]
  | _, _, .ordinary _ _ cuts => cuts.addresses_lexPairwise

/-- Ordered premises give a lexicographic block decomposition: all head
sites precede every tail site, and recursion orders each block. -/
theorem CKChildCuts.addresses_lexPairwise :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
      cuts.siteOrder.Pairwise
        (fun p q => cuts.address p < cuts.address q)
  | _, _, .nil => by simp [CKChildCuts.siteOrder]
  | _, _, .cons _ _ headCut tailCuts => by
      change (headCut.siteOrder.map Sum.inl ++
        tailCuts.siteOrder.map Sum.inr).Pairwise
          (fun p q : Sum headCut.Site tailCuts.Site =>
            (match p with
              | Sum.inl site => 0 :: headCut.relativeAddress site
              | Sum.inr site =>
                  InternalAddress.shiftHead (tailCuts.address site)) <
            (match q with
              | Sum.inl site => 0 :: headCut.relativeAddress site
              | Sum.inr site =>
                  InternalAddress.shiftHead (tailCuts.address site)))
      apply List.pairwise_append.mpr
      refine ⟨?_, ?_, ?_⟩
      · exact headCut.relativeAddresses_lexPairwise.map Sum.inl (by
          intro p q less
          change List.Lex (fun a b : Nat => a < b)
            (0 :: headCut.relativeAddress p)
            (0 :: headCut.relativeAddress q)
          exact .cons less)
      · exact tailCuts.addresses_lexPairwise.map Sum.inr (by
          intro p q less
          change InternalAddress.shiftHead (tailCuts.address p) <
            InternalAddress.shiftHead (tailCuts.address q)
          exact InternalAddress.shiftHead_lt_of_lt
            (tailCuts.address_nonroot p) (tailCuts.address_nonroot q) less)
      · intro p p_mem q q_mem
        rcases List.mem_map.mp p_mem with ⟨p, _, rfl⟩
        rcases List.mem_map.mp q_mem with ⟨q, _, rfl⟩
        rcases tailCuts.address_selects_vertex q with
          ⟨i, rest, address_eq, _⟩
        change (0 :: headCut.relativeAddress p) <
          InternalAddress.shiftHead (tailCuts.address q)
        rw [address_eq]
        change List.Lex (fun a b : Nat => a < b)
          (0 :: headCut.relativeAddress p) ((i.1 + 1) :: rest)
        exact .rel (by simp)

/-- A detach singleton is ordered; descent inherits its nested order. -/
theorem CKBranchCut.relativeAddresses_lexPairwise :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
      cut.siteOrder.Pairwise
        (fun p q => cut.relativeAddress p < cut.relativeAddress q)
  | _, _, .detach _ => by simp [CKBranchCut.siteOrder]
  | _, _, .descend cut => cut.addresses_lexPairwise

end

mutual

/-- Whole boundary of the selected occurrence. -/
def CKCutPlan.siteBoundary : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> cut.Site -> Hypersequent sigma
  | _, _, .ordinary _ _ cuts, site => cuts.siteBoundary site

def CKChildCuts.siteBoundary : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> cuts.Site -> Hypersequent sigma
  | _, _, .nil => fun site => nomatch site
  | _, _, .cons head tail headCut tailCuts => fun site =>
      match site with
      | Sum.inl headSite => headCut.siteBoundary headSite
      | Sum.inr tailSite => tailCuts.siteBoundary tailSite

def CKBranchCut.siteBoundary : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> cut.Site -> Hypersequent sigma
  | G, _, .detach _, _ => G
  | _, _, .descend cut, site => cut.siteBoundary site

end

mutual

/-- Address-aligned detached tree, retaining its exact indexed boundary. -/
def CKCutPlan.detached : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)
  | _, _, .ordinary _ _ cuts, site => cuts.detached site

def CKChildCuts.detached : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (site : cuts.Site) ->
      CKTree sigma InstanceData (cuts.siteBoundary site)
  | _, _, .nil => fun site => nomatch site
  | _, _, .cons head tail headCut tailCuts => fun site =>
      match site with
      | Sum.inl headSite => headCut.detached headSite
      | Sum.inr tailSite => tailCuts.detached tailSite

def CKBranchCut.detached : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (site : cut.Site) ->
      CKTree sigma InstanceData (cut.siteBoundary site)
  | _, tree, .detach _, _ => tree
  | _, _, .descend cut, site => cut.detached site

end

mutual

/-- Selected subtrees have positive ordinary roots. -/
def CKCutPlan.detachedOrdinary : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (site : cut.Site) ->
      (cut.detached site).IsOrdinary
  | _, _, .ordinary _ _ cuts, site => cuts.detachedOrdinary site

def CKChildCuts.detachedOrdinary : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (site : cuts.Site) ->
      (cuts.detached site).IsOrdinary
  | _, _, .nil => fun site => nomatch site
  | _, _, .cons head tail headCut tailCuts => fun site =>
      match site with
      | Sum.inl headSite => headCut.detachedOrdinary headSite
      | Sum.inr tailSite => tailCuts.detachedOrdinary tailSite

def CKBranchCut.detachedOrdinary : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (site : cut.Site) ->
      (cut.detached site).IsOrdinary
  | _, _, .detach ordinary, _ => ordinary
  | _, _, .descend cut, site => cut.detachedOrdinary site

end

mutual

/-- Retained punctured remainder.  Existing interfaces are left in place;
only detach choices create new ones. -/
def CKCutPlan.remainder : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    CKCutPlan tree -> CKTree sigma InstanceData G
  | _, _, .interface G => .interface G
  | _, _, .ordinary o _ cuts => .ordinary o cuts.remainder

def CKChildCuts.remainder : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    CKChildCuts children -> CKChildren sigma InstanceData boundaries
  | _, _, .nil => .nil
  | _, _, .cons _ _ headCut tailCuts =>
      .cons headCut.remainder tailCuts.remainder

def CKBranchCut.remainder : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    CKBranchCut tree -> CKTree sigma InstanceData G
  | G, _, .detach _ => .interface G
  | _, _, .descend cut => cut.remainder

end

mutual

/-- Every structural site becomes an interface at the same exact address in
the retained remainder. -/
theorem CKCutPlan.remainder_interfaceAt_site :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (site : cut.Site) ->
      cut.remainder.InterfaceAt (cut.address site)
  | _, _, .interface _, site => nomatch site
  | _, _, .ordinary o children cuts, site => by
      rcases cuts.remainder_selects_interface site with
        ⟨i, rest, address_eq, below⟩
      change (CKTree.ordinary o cuts.remainder).InterfaceAt
        (cuts.address site)
      rw [address_eq]
      exact .child o cuts.remainder i below

/-- Child-tuple remainders retain the exact selected slot while replacing its
selected relative vertex by an interface. -/
theorem CKChildCuts.remainder_selects_interface :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (site : cuts.Site) ->
      ∃ (i : Fin boundaries.length) (rest : InternalAddress),
        cuts.address site = i.1 :: rest ∧
          (cuts.remainder.get i).InterfaceAt rest
  | _, _, .nil, site => nomatch site
  | _, _, .cons _ _ headCut tailCuts, site => by
      change Sum headCut.Site tailCuts.Site at site
      cases site with
      | inl site =>
          exact
            ⟨⟨0, by simp⟩, headCut.relativeAddress site, rfl,
              headCut.remainder_interfaceAt_site site⟩
      | inr site =>
          rcases tailCuts.remainder_selects_interface site with
            ⟨i, rest, address_eq, below⟩
          refine ⟨i.succ, rest, ?_, ?_⟩
          · simp only [CKChildCuts.address, address_eq,
              InternalAddress.shiftHead_cons, Fin.val_succ]
          · exact below

/-- A detached branch creates its root interface; descent inherits the
corresponding nested new interface. -/
theorem CKBranchCut.remainder_interfaceAt_site :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (site : cut.Site) ->
      cut.remainder.InterfaceAt (cut.relativeAddress site)
  | G, _, .detach _, site => by
      change PUnit at site
      cases site
      exact .root G
  | _, _, .descend cut, site => cut.remainder_interfaceAt_site site

end

mutual

/-- Fill exactly the newly created sites; old interfaces have no site and
therefore remain untouched. -/
def CKCutPlan.fill : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
    ((site : cut.Site) -> CKTree sigma InstanceData (cut.siteBoundary site)) ->
    CKTree sigma InstanceData G
  | _, _, .interface G, _ => .interface G
  | _, _, .ordinary o _ cuts, fillers =>
      .ordinary o (cuts.fill fillers)

def CKChildCuts.fill : {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
    ((site : cuts.Site) -> CKTree sigma InstanceData (cuts.siteBoundary site)) ->
    CKChildren sigma InstanceData boundaries
  | _, _, .nil, _ => .nil
  | _, _, .cons _ _ headCut tailCuts, fillers =>
      .cons
        (headCut.fill (fun site => fillers (Sum.inl site)))
        (tailCuts.fill (fun site => fillers (Sum.inr site)))

def CKBranchCut.fill : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
    ((site : cut.Site) -> CKTree sigma InstanceData (cut.siteBoundary site)) ->
    CKTree sigma InstanceData G
  | _, _, .detach _, fillers => fillers PUnit.unit
  | _, _, .descend cut, fillers => cut.fill fillers

end

mutual

/-- Filling every new site by its aligned detached tree reconstructs the
source exactly. -/
theorem CKCutPlan.fill_detached_reconstructs :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
      cut.fill cut.detached = tree
  | _, _, .interface _ => rfl
  | _, _, .ordinary o _ cuts => by
      change CKTree.ordinary o
        (cuts.fill (fun site => cuts.detached site)) =
          CKTree.ordinary o _
      rw [cuts.fill_detached_reconstructs]

/-- Reconstruction respects the exact ordered child tuple. -/
theorem CKChildCuts.fill_detached_reconstructs :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
      cuts.fill cuts.detached = children
  | _, _, .nil => rfl
  | _, _, .cons head tail headCut tailCuts => by
      change CKChildren.cons
          (headCut.fill (fun site => headCut.detached site))
          (tailCuts.fill (fun site => tailCuts.detached site)) =
        CKChildren.cons head tail
      rw [headCut.fill_detached_reconstructs,
        tailCuts.fill_detached_reconstructs]

/-- Detach is refilled by its unique factor, and descent reconstructs
recursively. -/
theorem CKBranchCut.fill_detached_reconstructs :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
      cut.fill cut.detached = tree
  | _, _, .detach _ => rfl
  | _, _, .descend cut => cut.fill_detached_reconstructs

end

mutual

/-- Total degree of the occurrence-aligned detached family. -/
def CKCutPlan.detachedDegreeSum : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    CKCutPlan tree -> Nat
  | _, _, .interface _ => 0
  | _, _, .ordinary _ _ cuts => cuts.detachedDegreeSum

def CKChildCuts.detachedDegreeSum :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    CKChildCuts children -> Nat
  | _, _, .nil => 0
  | _, _, .cons _ _ headCut tailCuts =>
      headCut.detachedDegreeSum + tailCuts.detachedDegreeSum

def CKBranchCut.detachedDegreeSum : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    CKBranchCut tree -> Nat
  | _, tree, .detach _ => tree.degree
  | _, _, .descend cut => cut.detachedDegreeSum

end

mutual

/-- The recursive detached degree is exactly the sum in canonical site
order, not a collected or quotient-level count. -/
theorem CKCutPlan.detachedDegreeSum_eq_siteOrder :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
      cut.detachedDegreeSum =
        (cut.siteOrder.map (fun site => (cut.detached site).degree)).sum
  | _, _, .interface _ => rfl
  | _, _, .ordinary _ _ cuts => cuts.detachedDegreeSum_eq_siteOrder

theorem CKChildCuts.detachedDegreeSum_eq_siteOrder :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
      cuts.detachedDegreeSum =
        (cuts.siteOrder.map (fun site => (cuts.detached site).degree)).sum
  | _, _, .nil => rfl
  | _, _, .cons _ _ headCut tailCuts => by
      simp only [CKChildCuts.detachedDegreeSum, CKChildCuts.siteOrder,
        CKChildCuts.Site]
      rw [List.map_append, List.sum_append, List.map_map, List.map_map]
      change headCut.detachedDegreeSum + tailCuts.detachedDegreeSum =
        (headCut.siteOrder.map
          (fun site => (headCut.detached site).degree)).sum +
        (tailCuts.siteOrder.map
          (fun site => (tailCuts.detached site).degree)).sum
      rw [headCut.detachedDegreeSum_eq_siteOrder,
        tailCuts.detachedDegreeSum_eq_siteOrder]

theorem CKBranchCut.detachedDegreeSum_eq_siteOrder :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
      cut.detachedDegreeSum =
        (cut.siteOrder.map (fun site => (cut.detached site).degree)).sum
  | _, _, .detach _ => rfl
  | _, _, .descend cut => cut.detachedDegreeSum_eq_siteOrder

end

mutual

/-- Vertex degree partitions between the retained remainder and all exact
detached occurrences. -/
theorem CKCutPlan.degree_partition : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) ->
      tree.degree = cut.remainder.degree + cut.detachedDegreeSum
  | _, _, .interface _ => rfl
  | _, _, .ordinary _ _ cuts => by
      have partition := cuts.degree_partition
      simp only [CKTree.degree, CKCutPlan.remainder,
        CKCutPlan.detachedDegreeSum]
      rw [partition]
      ac_rfl

theorem CKChildCuts.degree_partition :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) ->
      children.degree = cuts.remainder.degree + cuts.detachedDegreeSum
  | _, _, .nil => rfl
  | _, _, .cons _ _ headCut tailCuts => by
      have headPartition := headCut.degree_partition
      have tailPartition := tailCuts.degree_partition
      simp only [CKChildren.degree, CKChildCuts.remainder,
        CKChildCuts.detachedDegreeSum]
      rw [headPartition, tailPartition]
      ac_rfl

theorem CKBranchCut.degree_partition : {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) ->
      tree.degree = cut.remainder.degree + cut.detachedDegreeSum
  | _, _, .detach _ => by
      simp [CKBranchCut.remainder, CKBranchCut.detachedDegreeSum,
        CKTree.degree]
  | _, _, .descend cut => cut.degree_partition

end

/-- One addressed occurrence before commutative forest projection. -/
structure CKCutEntry (sigma : Signature.{u, v}) (InstanceData : Type w) where
  address : InternalAddress
  boundary : Hypersequent sigma
  tree : CKTree sigma InstanceData boundary
  ordinary : tree.IsOrdinary

namespace CKCut

variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Deterministic recursive site order. -/
def orderedSites (cut : CKCut tree) : List cut.Site := cut.plan.siteOrder

/-- Deterministic lexicographic address list exposed by the witness. -/
def orderedAddresses (cut : CKCut tree) : List InternalAddress :=
  cut.orderedSites.map cut.plan.address

/-- Positive one-based form of the exact same ordered sites. -/
def orderedRacketAddresses (cut : CKCut tree) : List RacketAddress :=
  cut.orderedAddresses.map InternalAddress.toRacket

/-- Address-indexed occurrence tuple retained before collection. -/
def detachedTuple (cut : CKCut tree) : List (CKCutEntry sigma InstanceData) :=
  cut.orderedSites.map (fun site =>
    { address := cut.plan.address site
      boundary := cut.plan.siteBoundary site
      tree := cut.plan.detached site
      ordinary := cut.plan.detachedOrdinary site })

/-- Commutative projection of the addressed tuple, retaining occurrence
multiplicity. -/
def detachedForest (cut : CKCut tree) : CKForest sigma InstanceData :=
  Multiset.ofList <| cut.detachedTuple.map (fun entry =>
    ({ boundary := entry.boundary
       tree := entry.tree
       ordinary := entry.ordinary } : CKComponent sigma InstanceData))

/-- The retained tree has definitionally the exact source root boundary. -/
def remainder (cut : CKCut tree) : CKTree sigma InstanceData G :=
  cut.plan.remainder

/-- Fill only sites created by this cut. -/
def fill (cut : CKCut tree)
    (fillers : (site : cut.Site) ->
      CKTree sigma InstanceData (cut.plan.siteBoundary site)) :
    CKTree sigma InstanceData G :=
  cut.plan.fill fillers

/-- Total ordinary-vertex degree of the addressed detached tuple. -/
def detachedDegreeSum (cut : CKCut tree) : Nat :=
  cut.plan.detachedDegreeSum

/-- A cut is empty exactly when its canonical site type is empty. -/
def IsEmpty (cut : CKCut tree) : Prop := cut.orderedSites = []

/-- The canonical order enumerates every structural site. -/
theorem siteOrder_complete (cut : CKCut tree) (site : cut.Site) :
    site ∈ cut.orderedSites :=
  cut.plan.site_mem_siteOrder site

/-- The canonical occurrence traversal retains every site exactly once. -/
theorem siteOrder_nodup (cut : CKCut tree) : cut.orderedSites.Nodup :=
  cut.plan.siteOrder_nodup

/-- Canonical addresses are strictly increasing in the standard
lexicographic order on zero-based selector lists. -/
theorem orderedAddresses_lexIncreasing (cut : CKCut tree) :
    cut.orderedAddresses.Pairwise (fun p q => p < q) := by
  apply List.pairwise_map.mpr
  exact cut.plan.addresses_lexPairwise

/-- Every selected address denotes an existing source vertex. -/
theorem address_exists (cut : CKCut tree) (site : cut.Site) :
    tree.VertexAt (cut.plan.address site) :=
  cut.plan.address_vertexAt site

/-- The public positive-source cut never selects its source root. -/
theorem address_nonroot (cut : CKCut tree) (site : cut.Site) :
    cut.plan.address site ≠ [] := by
  rcases cut with ⟨sourceOrdinary, plan⟩
  cases plan with
  | interface _ => exact False.elim sourceOrdinary
  | ordinary _ _ cuts => exact cuts.address_nonroot site

/-- Distinct occurrence sites have prefix-incomparable addresses. -/
theorem addresses_prefixFree (cut : CKCut tree) {p q : cut.Site}
    (different : p ≠ q) :
    PrefixIncomparable (cut.plan.address p) (cut.plan.address q) :=
  cut.plan.addresses_prefixIncomparable different

/-- Canonical sites are determined by their exact addresses. -/
theorem address_injective (cut : CKCut tree) :
    Function.Injective cut.plan.address := by
  intro p q addressEq
  by_contra different
  have incomparable := cut.addresses_prefixFree different
  rw [addressEq] at incomparable
  exact incomparable.1 (by simp [AddressPrefix])

/-- At a selected address the source ordinary vertex is replaced by a typed
interface in the remainder. -/
theorem selected_vertex_becomes_interface (cut : CKCut tree)
    (site : cut.Site) :
    tree.VertexAt (cut.plan.address site) ∧
      cut.remainder.InterfaceAt (cut.plan.address site) :=
  ⟨cut.address_exists site, cut.plan.remainder_interfaceAt_site site⟩

/-- The remainder is indexed by exactly the source whole boundary. -/
@[simp]
theorem remainder_rootBoundary (cut : CKCut tree) :
    cut.remainder.rootBoundary = tree.rootBoundary := rfl

/-- Distinguished filling touches only the new occurrence sites and exactly
reconstructs the source. -/
theorem fill_detached_reconstructs (cut : CKCut tree) :
    cut.fill cut.plan.detached = tree :=
  cut.plan.fill_detached_reconstructs

/-- Recursive degree agrees with the canonical addressed-tuple sum. -/
theorem detachedDegreeSum_eq_orderedSites (cut : CKCut tree) :
    cut.detachedDegreeSum =
      (cut.orderedSites.map
        (fun site => (cut.plan.detached site).degree)).sum :=
  cut.plan.detachedDegreeSum_eq_siteOrder

/-- Ordinary-vertex degree partitions exactly across remainder and detached
occurrences; interfaces contribute zero. -/
theorem degree_partition (cut : CKCut tree) :
    tree.degree = cut.remainder.degree +
      (cut.orderedSites.map
        (fun site => (cut.plan.detached site).degree)).sum := by
  rw [← cut.detachedDegreeSum_eq_orderedSites]
  exact cut.plan.degree_partition

end CKCut

/-- Nonempty recursive CK cuts. -/
abbrev ProperCKCut {G : Hypersequent sigma}
    (tree : CKTree sigma InstanceData G) :=
  {cut : CKCut tree // Nonempty cut.Site}

end Potkin

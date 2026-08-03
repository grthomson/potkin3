import Potkin.CKCut

namespace Potkin

universe u v w

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-- Total computational classification of one address in an open CK tree. -/
inductive CKAddressStatus where
  | missing
  | interface
  | ordinary
deriving DecidableEq, Repr

/-- Prefix order on positive one-based interchange addresses. -/
def RacketAddressPrefix (a b : RacketAddress) : Prop := a.slots <+: b.slots

mutual

/-- Look up whether an internal address is absent, a typed interface, or an
ordinary rule vertex. -/
def CKTree.statusAt : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> InternalAddress -> CKAddressStatus
  | _, .interface _, [] => .interface
  | _, .interface _, _ :: _ => .missing
  | _, .ordinary _ _, [] => .ordinary
  | _, .ordinary _ children, slot :: rest =>
      children.statusAt slot rest

/-- Total zero-based child-tuple lookup used by `CKTree.statusAt`. -/
def CKChildren.statusAt :
    {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries -> Nat ->
      InternalAddress -> CKAddressStatus
  | _, .nil, _, _ => .missing
  | _, .cons head _, 0, rest => head.statusAt rest
  | _, .cons _ tail, slot + 1, rest => tail.statusAt slot rest

end

namespace CKChildren

/-- Natural-slot lookup agrees with the existing dependent `Fin` child
projection whenever the slot is in range. -/
theorem statusAt_get :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    (i : Fin boundaries.length) -> (address : InternalAddress) ->
    children.statusAt i.1 address = (children.get i).statusAt address
  | _ :: _, .cons _ _, ⟨0, _⟩, _ => rfl
  | _ :: _, .cons _ tail, ⟨n + 1, h⟩, address =>
      statusAt_get tail ⟨n, Nat.lt_of_succ_lt_succ h⟩ address

end CKChildren

namespace CKTree

/-- Every relational ordinary-vertex witness computes to ordinary status. -/
theorem VertexAt.statusAt_eq_ordinary :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {address : InternalAddress} ->
    tree.VertexAt address -> tree.statusAt address = .ordinary
  | _, _, _, .root _ _ => rfl
  | _, _, _, .child _ children i below => by
      change children.statusAt i.1 _ = .ordinary
      rw [CKChildren.statusAt_get]
      exact below.statusAt_eq_ordinary

/-- Every relational interface witness computes to interface status. -/
theorem InterfaceAt.statusAt_eq_interface :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    {address : InternalAddress} ->
    tree.InterfaceAt address -> tree.statusAt address = .interface
  | _, _, _, .root _ => rfl
  | _, _, _, .child _ children i below => by
      change children.statusAt i.1 _ = .interface
      rw [CKChildren.statusAt_get]
      exact below.statusAt_eq_interface

end CKTree

mutual

/-- Successful ordinary status lookup reconstructs an exact relational
vertex witness. -/
theorem CKTree.vertexAt_of_statusAt_eq_ordinary :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    (address : InternalAddress) ->
    tree.statusAt address = .ordinary -> tree.VertexAt address
  | _, .interface _, address, status => by
      cases address <;> simp [CKTree.statusAt] at status
  | _, .ordinary o children, [], _ => .root o children
  | _, .ordinary o children, slot :: rest, status => by
      rcases children.vertexAt_of_statusAt_eq_ordinary slot rest status with
        ⟨i, slotEq, below⟩
      have selected := CKTree.VertexAt.child o children i below
      simpa [slotEq] using selected

/-- Child-tuple ordinary lookup returns the exact in-range dependent slot
and its relative vertex witness. -/
theorem CKChildren.vertexAt_of_statusAt_eq_ordinary :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    (slot : Nat) -> (address : InternalAddress) ->
    children.statusAt slot address = .ordinary ->
      ∃ i : Fin boundaries.length,
        i.1 = slot ∧ (children.get i).VertexAt address
  | _, .nil, _, _, status => by
      simp [CKChildren.statusAt] at status
  | _, .cons head _, 0, address, status =>
      ⟨⟨0, by simp⟩, rfl,
        head.vertexAt_of_statusAt_eq_ordinary address status⟩
  | _, .cons _ tail, slot + 1, address, status => by
      rcases tail.vertexAt_of_statusAt_eq_ordinary slot address status with
        ⟨i, slotEq, below⟩
      exact ⟨i.succ, by simp [slotEq], below⟩

end

mutual

/-- Successful interface status lookup reconstructs an exact relational
interface witness. -/
theorem CKTree.interfaceAt_of_statusAt_eq_interface :
    {G : Hypersequent sigma} ->
    (tree : CKTree sigma InstanceData G) ->
    (address : InternalAddress) ->
    tree.statusAt address = .interface -> tree.InterfaceAt address
  | _, .interface G, [], _ => .root G
  | _, .interface _, _ :: _, status => by
      simp [CKTree.statusAt] at status
  | _, .ordinary _ _, [], status => by
      simp [CKTree.statusAt] at status
  | _, .ordinary o children, slot :: rest, status => by
      rcases children.interfaceAt_of_statusAt_eq_interface slot rest status with
        ⟨i, slotEq, below⟩
      have selected := CKTree.InterfaceAt.child o children i below
      simpa [slotEq] using selected

/-- Child-tuple interface lookup returns the exact in-range dependent slot
and its relative interface witness. -/
theorem CKChildren.interfaceAt_of_statusAt_eq_interface :
    {boundaries : List (Hypersequent sigma)} ->
    (children : CKChildren sigma InstanceData boundaries) ->
    (slot : Nat) -> (address : InternalAddress) ->
    children.statusAt slot address = .interface ->
      ∃ i : Fin boundaries.length,
        i.1 = slot ∧ (children.get i).InterfaceAt address
  | _, .nil, _, _, status => by
      simp [CKChildren.statusAt] at status
  | _, .cons head _, 0, address, status =>
      ⟨⟨0, by simp⟩, rfl,
        head.interfaceAt_of_statusAt_eq_interface address status⟩
  | _, .cons _ tail, slot + 1, address, status => by
      rcases tail.interfaceAt_of_statusAt_eq_interface slot address status with
        ⟨i, slotEq, below⟩
      exact ⟨i.succ, by simp [slotEq], below⟩

end

namespace CKTree

/-- Computational ordinary status decides the existing vertex relation. -/
theorem vertexAt_iff_statusAt_eq_ordinary
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (address : InternalAddress) :
    tree.VertexAt address ↔ tree.statusAt address = .ordinary :=
  ⟨fun vertex => vertex.statusAt_eq_ordinary,
    tree.vertexAt_of_statusAt_eq_ordinary address⟩

/-- Computational interface status decides the existing interface relation. -/
theorem interfaceAt_iff_statusAt_eq_interface
    {G : Hypersequent sigma} (tree : CKTree sigma InstanceData G)
    (address : InternalAddress) :
    tree.InterfaceAt address ↔ tree.statusAt address = .interface :=
  ⟨fun interface => interface.statusAt_eq_interface,
    tree.interfaceAt_of_statusAt_eq_interface address⟩

end CKTree

namespace InternalAddress

/-- Zero/one-based conversion preserves and reflects address prefixing. -/
theorem toRacket_prefix_iff (p q : InternalAddress) :
    RacketAddressPrefix p.toRacket q.toRacket ↔ AddressPrefix p q := by
  simpa [RacketAddressPrefix, AddressPrefix, InternalAddress.toRacket] using
    (List.prefix_map_iff_of_injective
      (l₁ := p) (l₂ := q) Nat.succ_injective)

/-- First-selector shifting is injective when both child addresses are
nonempty. -/
theorem shiftHead_injective_of_nonempty {p q : InternalAddress}
    (p_nonempty : p ≠ []) (q_nonempty : q ≠ [])
    (shifted : shiftHead p = shiftHead q) : p = q := by
  cases p with
  | nil => exact (p_nonempty rfl).elim
  | cons i p =>
      cases q with
      | nil => exact (q_nonempty rfl).elim
      | cons j q =>
          simp only [shiftHead_cons, List.cons.injEq] at shifted
          rcases shifted with ⟨headEq, tailEq⟩
          have : i = j := Nat.add_right_cancel headEq
          cases this
          cases tailEq
          rfl

end InternalAddress

mutual

/-- A plan creates a new interface at exactly one of its selected addresses:
the source address is ordinary and the remainder address is an interface. -/
theorem CKCutPlan.newHole_iff_site :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (address : InternalAddress) ->
    (tree.statusAt address = .ordinary ∧
      cut.remainder.statusAt address = .interface) ↔
      ∃ site : cut.Site, cut.address site = address
  | _, _, .interface _, address => by
      cases address <;> simp [CKTree.statusAt, CKCutPlan.Site]
  | _, _, .ordinary _ _ cuts, address => by
      cases address with
      | nil =>
          constructor
          · intro statuses
            simp [CKTree.statusAt, CKCutPlan.remainder] at statuses
          · rintro ⟨site, addressEq⟩
            exact (cuts.address_nonroot site addressEq).elim
      | cons slot rest =>
          simpa [CKTree.statusAt, CKCutPlan.remainder, CKCutPlan.Site,
            CKCutPlan.address] using
            cuts.newHole_iff_site slot rest

/-- Child-tuple form of exact new-hole classification. -/
theorem CKChildCuts.newHole_iff_site :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (slot : Nat) ->
    (address : InternalAddress) ->
    (children.statusAt slot address = .ordinary ∧
      cuts.remainder.statusAt slot address = .interface) ↔
      ∃ site : cuts.Site, cuts.address site = slot :: address
  | _, _, .nil, _, _ => by
      simp [CKChildren.statusAt, CKChildCuts.Site]
  | _, _, .cons _ _ headCut tailCuts, slot, address => by
      cases slot with
      | zero =>
          constructor
          · intro statuses
            rcases (headCut.newHole_iff_site address).mp statuses with
              ⟨site, addressEq⟩
            exact ⟨Sum.inl site, by
              simp [CKChildCuts.address, addressEq]⟩
          · rintro ⟨site, addressEq⟩
            change Sum headCut.Site tailCuts.Site at site
            cases site with
            | inl site =>
                apply (headCut.newHole_iff_site address).mpr
                exact ⟨site, by
                  simpa [CKChildCuts.address] using addressEq⟩
            | inr site =>
                rcases tailCuts.address_selects_vertex site with
                  ⟨i, rest, tailAddress, _⟩
                simp [CKChildCuts.address, tailAddress] at addressEq
      | succ slot =>
          constructor
          · intro statuses
            rcases (tailCuts.newHole_iff_site slot address).mp statuses with
              ⟨site, addressEq⟩
            exact ⟨Sum.inr site, by
              simp [CKChildCuts.address, addressEq]⟩
          · rintro ⟨site, addressEq⟩
            change Sum headCut.Site tailCuts.Site at site
            cases site with
            | inl site =>
                simp [CKChildCuts.address] at addressEq
            | inr site =>
                apply (tailCuts.newHole_iff_site slot address).mpr
                refine ⟨site, ?_⟩
                apply InternalAddress.shiftHead_injective_of_nonempty
                  (tailCuts.address_nonroot site) (by simp)
                simpa [CKChildCuts.address] using addressEq

/-- Branch-relative form of exact new-hole classification. -/
theorem CKBranchCut.newHole_iff_site :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (address : InternalAddress) ->
    (tree.statusAt address = .ordinary ∧
      cut.remainder.statusAt address = .interface) ↔
      ∃ site : cut.Site, cut.relativeAddress site = address
  | _, tree, .detach ordinary, address => by
      cases tree with
      | interface => exact False.elim ordinary
      | ordinary _ _ =>
          cases address <;>
            simp [CKTree.statusAt, CKBranchCut.remainder,
              CKBranchCut.Site, CKBranchCut.relativeAddress]
  | _, _, .descend cut, address => cut.newHole_iff_site address

end

mutual

/-- A computational source interface outside every detached-address prefix
survives in the retained remainder. -/
theorem CKCutPlan.oldInterfaceOutside_preserved :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKCutPlan tree) -> (address : InternalAddress) ->
    tree.statusAt address = .interface ->
    (∀ site : cut.Site,
      ¬ AddressPrefix (cut.address site) address) ->
    cut.remainder.statusAt address = .interface
  | _, _, .interface _, address, oldInterface, _ => by
      simpa [CKCutPlan.remainder] using oldInterface
  | _, _, .ordinary _ _ cuts, address, oldInterface, outside => by
      cases address with
      | nil => simp [CKTree.statusAt] at oldInterface
      | cons slot rest =>
          simpa [CKTree.statusAt, CKCutPlan.remainder,
            CKCutPlan.Site, CKCutPlan.address] using
            cuts.oldInterfaceOutside_preserved slot rest oldInterface
              (by
                intro site
                exact outside site)

/-- Ordered-child form of old-interface preservation. -/
theorem CKChildCuts.oldInterfaceOutside_preserved :
    {boundaries : List (Hypersequent sigma)} ->
    {children : CKChildren sigma InstanceData boundaries} ->
    (cuts : CKChildCuts children) -> (slot : Nat) ->
    (address : InternalAddress) ->
    children.statusAt slot address = .interface ->
    (∀ site : cuts.Site,
      ¬ AddressPrefix (cuts.address site) (slot :: address)) ->
    cuts.remainder.statusAt slot address = .interface
  | _, _, .nil, _, _, oldInterface, _ => by
      simp [CKChildren.statusAt] at oldInterface
  | _, _, .cons _ _ headCut tailCuts, slot, address, oldInterface,
      outside => by
      cases slot with
      | zero =>
          apply headCut.oldInterfaceOutside_preserved address oldInterface
          intro site isPrefix
          apply outside (Sum.inl site)
          simpa [CKChildCuts.address, AddressPrefix] using isPrefix
      | succ slot =>
          apply tailCuts.oldInterfaceOutside_preserved slot address
            oldInterface
          intro site isPrefix
          apply outside (Sum.inr site)
          have shiftedPrefix :=
            (InternalAddress.shiftHead_prefix_iff
              (tailCuts.address_nonroot site) (by simp)).mpr isPrefix
          simpa [CKChildCuts.address] using shiftedPrefix

/-- A whole detached branch has no address outside its unique root prefix;
recursive descent preserves old interfaces by the plan theorem. -/
theorem CKBranchCut.oldInterfaceOutside_preserved :
    {G : Hypersequent sigma} ->
    {tree : CKTree sigma InstanceData G} ->
    (cut : CKBranchCut tree) -> (address : InternalAddress) ->
    tree.statusAt address = .interface ->
    (∀ site : cut.Site,
      ¬ AddressPrefix (cut.relativeAddress site) address) ->
    cut.remainder.statusAt address = .interface
  | _, _, .detach _, _, _, outside => by
      have impossible : False := outside PUnit.unit (by
        simp [CKBranchCut.relativeAddress, AddressPrefix])
      exact impossible.elim
  | _, _, .descend cut, address, oldInterface, outside =>
      cut.oldInterfaceOutside_preserved address oldInterface outside

end

namespace CKCut

variable {G : Hypersequent sigma} {tree : CKTree sigma InstanceData G}

/-- Exact whole boundary required by one newly created typed puncture. -/
def requirement (cut : CKCut tree) (site : cut.Site) : Hypersequent sigma :=
  cut.plan.siteBoundary site

/-- Exact detached occurrence aligned with one site and its requirement. -/
def detachedAt (cut : CKCut tree) (site : cut.Site) :
    CKTree sigma InstanceData (cut.requirement site) :=
  cut.plan.detached site

/-- A selected remainder interface and its detached occurrence carry exactly
the same whole boundary. -/
theorem selectedPuncture_matches_detachedRoot
    (cut : CKCut tree) (site : cut.Site) :
    cut.remainder.InterfaceAt (cut.plan.address site) ∧
      cut.requirement site = (cut.detachedAt site).rootBoundary :=
  ⟨cut.plan.remainder_interfaceAt_site site, rfl⟩

/-- Positive one-based interchange address of one exact selected site. -/
def selectedRacketAddress (cut : CKCut tree) (site : cut.Site) :
    RacketAddress :=
  (cut.plan.address site).toRacket

/-- Converting a selected interchange address back recovers its exact
internal occurrence address. -/
@[simp]
theorem selectedRacketAddress_toInternal
    (cut : CKCut tree) (site : cut.Site) :
    (cut.selectedRacketAddress site).toInternal = cut.plan.address site :=
  RacketAddress.toInternal_toRacket _

/-- Lookup through a selected positive address identifies the exact source
ordinary vertex. -/
theorem selectedRacketAddress_exists
    (cut : CKCut tree) (site : cut.Site) :
    tree.VertexAt (cut.selectedRacketAddress site).toInternal := by
  simpa using cut.address_exists site

/-- A new hole is computationally an ordinary source vertex replaced by an
interface in this cut's remainder. -/
def NewHoleAt (cut : CKCut tree) (address : InternalAddress) : Prop :=
  tree.statusAt address = .ordinary ∧
    cut.remainder.statusAt address = .interface

/-- New holes occur exactly at selected occurrence addresses. -/
theorem newHoleAt_iff_selectedSite (cut : CKCut tree)
    (address : InternalAddress) :
    cut.NewHoleAt address ↔
      ∃ site : cut.Site, cut.plan.address site = address :=
  cut.plan.newHole_iff_site address

/-- Every selected occurrence is computationally a genuinely new hole. -/
theorem selectedSite_isNewHole (cut : CKCut tree) (site : cut.Site) :
    cut.NewHoleAt (cut.plan.address site) :=
  (cut.newHoleAt_iff_selectedSite _).mpr ⟨site, rfl⟩

/-- The same selected positive address computes to a genuinely new hole. -/
theorem selectedRacketAddress_isNewHole
    (cut : CKCut tree) (site : cut.Site) :
    cut.NewHoleAt (cut.selectedRacketAddress site).toInternal := by
  simpa using cut.selectedSite_isNewHole site

/-- The selected positive address also locates the new relational interface
in the retained remainder. -/
theorem selectedRacketAddress_remainderInterface
    (cut : CKCut tree) (site : cut.Site) :
    cut.remainder.InterfaceAt
      (cut.selectedRacketAddress site).toInternal := by
  simpa using (cut.selectedPuncture_matches_detachedRoot site).1

/-- A new hole determines one unique occurrence site. -/
theorem newHoleAt_uniqueSite (cut : CKCut tree) {address : InternalAddress}
    (newHole : cut.NewHoleAt address) :
    ∃! site : cut.Site, cut.plan.address site = address := by
  rcases (cut.newHoleAt_iff_selectedSite address).mp newHole with
    ⟨site, addressEq⟩
  refine ⟨site, addressEq, ?_⟩
  intro other otherEq
  apply cut.address_injective
  exact otherEq.trans addressEq.symm

/-- A source interface is outside the detached regions exactly when no
selected site address prefixes it. -/
def OldInterfaceOutside (cut : CKCut tree)
    (address : InternalAddress) : Prop :=
  tree.statusAt address = .interface ∧
    ∀ site : cut.Site,
      ¬ AddressPrefix (cut.plan.address site) address

/-- Every old source interface outside all detached regions remains an
interface at the identical address in the remainder. -/
theorem oldInterfaceOutside_preserved (cut : CKCut tree)
    {address : InternalAddress}
    (oldInterface : cut.OldInterfaceOutside address) :
    cut.remainder.statusAt address = .interface :=
  cut.plan.oldInterfaceOutside_preserved address
    oldInterface.1 oldInterface.2

/-- Argument-separated form convenient for downstream cut witnesses. -/
theorem oldInterface_outside_selectedPrefixes_preserved
    (cut : CKCut tree) {address : InternalAddress}
    (oldInterface : tree.statusAt address = .interface)
    (outside : ∀ site : cut.Site,
      ¬ AddressPrefix (cut.plan.address site) address) :
    cut.remainder.statusAt address = .interface :=
  cut.plan.oldInterfaceOutside_preserved address oldInterface outside

/-- Relational form: every old source puncture outside all detached regions
is the identical puncture of the retained remainder. -/
theorem oldInterfaceAt_outside_selectedPrefixes_preserved
    (cut : CKCut tree) {address : InternalAddress}
    (oldInterface : tree.InterfaceAt address)
    (outside : ∀ site : cut.Site,
      ¬ AddressPrefix (cut.plan.address site) address) :
    cut.remainder.InterfaceAt address :=
  cut.remainder.interfaceAt_of_statusAt_eq_interface address
    (cut.oldInterface_outside_selectedPrefixes_preserved
      oldInterface.statusAt_eq_interface outside)

/-- Relational new holes are exactly selected source vertices replaced by
remainder interfaces. -/
theorem vertexAndInterface_iff_selectedSite
    (cut : CKCut tree) (address : InternalAddress) :
    (tree.VertexAt address ∧ cut.remainder.InterfaceAt address) ↔
      ∃ site : cut.Site, cut.plan.address site = address := by
  constructor
  · rintro ⟨sourceVertex, remainderInterface⟩
    apply (cut.newHoleAt_iff_selectedSite address).mp
    exact ⟨sourceVertex.statusAt_eq_ordinary,
      remainderInterface.statusAt_eq_interface⟩
  · intro selected
    have statuses : cut.NewHoleAt address :=
      (cut.newHoleAt_iff_selectedSite address).mpr selected
    exact
      ⟨tree.vertexAt_of_statusAt_eq_ordinary address statuses.1,
        cut.remainder.interfaceAt_of_statusAt_eq_interface address statuses.2⟩

end CKCut

end Potkin

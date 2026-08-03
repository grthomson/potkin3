import Potkin.Occurrence

namespace Potkin

universe u v w

mutual

/-- Boundary-generic open CK combinatorics with arbitrary node decorations. -/
inductive OpenTree (Boundary : Type u) (Decoration : Type v) :
    Boundary -> Type (max u v) where
  | interface (G : Boundary) : OpenTree Boundary Decoration G
  | ordinary (root : Boundary) (decoration : Decoration)
      {premises : List Boundary}
      (children : OpenChildren Boundary Decoration premises) :
      OpenTree Boundary Decoration root

/-- Ordered boundary-indexed children of the generic open carrier. -/
inductive OpenChildren (Boundary : Type u) (Decoration : Type v) :
    List Boundary -> Type (max u v) where
  | nil : OpenChildren Boundary Decoration []
  | cons {G : Boundary} {Gs : List Boundary}
      (head : OpenTree Boundary Decoration G)
      (tail : OpenChildren Boundary Decoration Gs) :
      OpenChildren Boundary Decoration (G :: Gs)

end


mutual

/-- Open, occurrence-decorated CK trees indexed by their whole boundary. -/
inductive CKTree (sigma : Signature.{u, v}) (InstanceData : Type w) :
    Hypersequent sigma -> Type (max (max u v) w) where
  | interface (G : Hypersequent sigma) : CKTree sigma InstanceData G
  | ordinary (o : LocalOccurrence sigma InstanceData)
      (children : CKChildren sigma InstanceData o.shape.premises) :
      CKTree sigma InstanceData o.shape.conclusion

/-- Ordered, boundary-indexed CK children. -/
inductive CKChildren (sigma : Signature.{u, v}) (InstanceData : Type w) :
    List (Hypersequent sigma) -> Type (max (max u v) w) where
  | nil : CKChildren sigma InstanceData []
  | cons {G : Hypersequent sigma} {Gs : List (Hypersequent sigma)}
      (head : CKTree sigma InstanceData G)
      (tail : CKChildren sigma InstanceData Gs) :
      CKChildren sigma InstanceData (G :: Gs)

end

namespace CKChildren

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-- Retrieve one ordered child by its zero-based internal slot. -/
def get : {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries ->
    (i : Fin boundaries.length) ->
    CKTree sigma InstanceData (boundaries.get i)
  | _ :: _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ tail, ⟨n + 1, h⟩ =>
      get tail ⟨n, Nat.lt_of_succ_lt_succ h⟩

/-- Build ordered children from a boundary-indexed finite family. -/
def ofFn : {boundaries : List (Hypersequent sigma)} ->
    ((i : Fin boundaries.length) ->
      CKTree sigma InstanceData (boundaries.get i)) ->
    CKChildren sigma InstanceData boundaries
  | [], _ => .nil
  | _ :: _, children =>
      .cons (children ⟨0, by simp⟩)
        (ofFn (fun i => children i.succ))

@[simp]
theorem get_ofFn {boundaries : List (Hypersequent sigma)}
    (children : (i : Fin boundaries.length) ->
      CKTree sigma InstanceData (boundaries.get i))
    (i : Fin boundaries.length) :
    get (ofFn children) i = children i := by
  induction boundaries with
  | nil => exact Fin.elim0 i
  | cons G Gs ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          simpa [ofFn, get] using ih (fun j => children j.succ) i

@[ext]
theorem ext {boundaries : List (Hypersequent sigma)}
    {xs ys : CKChildren sigma InstanceData boundaries}
    (h : ∀ i, get xs i = get ys i) : xs = ys := by
  induction boundaries with
  | nil => cases xs; cases ys; rfl
  | cons G Gs ih =>
      cases xs with
      | cons x xs =>
          cases ys with
          | cons y ys =>
              have hhead : x = y := h ⟨0, by simp⟩
              have htail : xs = ys := ih (fun i => h i.succ)
              cases hhead
              cases htail
              rfl

theorem ofFn_congr {boundaries : List (Hypersequent sigma)}
    {f g : (i : Fin boundaries.length) ->
      CKTree sigma InstanceData (boundaries.get i)}
    (h : ∀ i, f i = g i) : ofFn f = ofFn g := by
  ext i
  simp [h i]

end CKChildren

namespace CKTree

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

/-- A vacancy is not an ordinary vertex. -/
def IsOrdinary : {G : Hypersequent sigma} ->
    CKTree sigma InstanceData G -> Prop
  | _, .interface _ => False
  | _, .ordinary _ _ => True

/-- Construct an ordinary node from a finite child function. -/
def ordinaryFn (o : LocalOccurrence sigma InstanceData)
    (children : (i : Fin o.shape.premises.length) ->
      CKTree sigma InstanceData (o.shape.premises.get i)) :
    CKTree sigma InstanceData o.shape.conclusion :=
  .ordinary o (CKChildren.ofFn children)

theorem ordinaryFn_congr (o : LocalOccurrence sigma InstanceData)
    {f g : (i : Fin o.shape.premises.length) ->
      CKTree sigma InstanceData (o.shape.premises.get i)}
    (h : ∀ i, f i = g i) : ordinaryFn o f = ordinaryFn o g := by
  unfold ordinaryFn
  exact congrArg (ordinary o) (CKChildren.ofFn_congr h)

/-- Whole-hypersequent instance of the boundary-generic comparison carrier. -/
abbrev Bare (sigma : Signature.{u, v}) :=
  OpenTree (Hypersequent sigma) Unit

mutual

/-- Erase occurrence IDs, kinds, instance data, and incidence. -/
def erase : {G : Hypersequent sigma} -> CKTree sigma InstanceData G ->
    Bare sigma G
  | _, .interface G => .interface G
  | _, .ordinary o children =>
      .ordinary o.shape.conclusion () (eraseChildren children)

def eraseChildren : {boundaries : List (Hypersequent sigma)} ->
    CKChildren sigma InstanceData boundaries ->
      OpenChildren (Hypersequent sigma) Unit boundaries
  | _, .nil => .nil
  | _, .cons head tail => .cons (erase head) (eraseChildren tail)

end

end CKTree

/-- A connected forest factor must have a positive ordinary root. -/
structure CKComponent
    (sigma : Signature.{u, v}) (InstanceData : Type w) where
  boundary : Hypersequent sigma
  tree : CKTree sigma InstanceData boundary
  ordinary : tree.IsOrdinary

/-- Independent commutative juxtaposition of connected proof factors. -/
abbrev CKForest
    (sigma : Signature.{u, v}) (InstanceData : Type w) :=
  Multiset (CKComponent sigma InstanceData)

end Potkin

import Potkin.Occurrence

namespace Potkin

universe u v w

/--
A chosen primitive formula fragment.  Atom-only support is one possible
choice, not part of the definition of a material base.
-/
structure PrimitiveFragment (sigma : Signature.{u, v}) where
  primitive : Formula sigma -> Prop

namespace PrimitiveFragment

variable {sigma : Signature.{u, v}}

/-- Every formula occurrence in one multiset context belongs to the fragment. -/
def SupportsContext (pi : PrimitiveFragment sigma)
    (Gamma : Context sigma) : Prop :=
  forall A, A ∈ Gamma -> pi.primitive A

/-- Both sides of one sequent are supported by the chosen fragment. -/
def SupportsSequent (pi : PrimitiveFragment sigma)
    (S : Sequent sigma) : Prop :=
  pi.SupportsContext S.lhs ∧ pi.SupportsContext S.rhs

/-- Every displayed sequent occurrence in a whole boundary is supported. -/
def SupportsHypersequent (pi : PrimitiveFragment sigma)
    (G : Hypersequent sigma) : Prop :=
  forall S, S ∈ G.components -> pi.SupportsSequent S

/-- The strict atom-only fragment is available as an explicit choice. -/
def atoms : PrimitiveFragment sigma where
  primitive
    | .atom _ => True
    | .app _ _ => False

/-- The full formula language, useful when no proper primitive subfragment is selected. -/
def full : PrimitiveFragment sigma where
  primitive := fun _ => True

end PrimitiveFragment

namespace OccurrenceShape

variable {sigma : Signature.{u, v}}

/--
Every ordered premise boundary and the conclusion lie in the selected
primitive fragment.  The occurrence shape still retains literal premise
order; this predicate merely checks every finite slot.
-/
def IsPrimitiveBoundary (pi : PrimitiveFragment sigma)
    (shape : OccurrenceShape sigma) : Prop :=
  (forall i : Fin shape.premises.length,
      pi.SupportsHypersequent (shape.premises.get i)) ∧
    pi.SupportsHypersequent shape.conclusion

end OccurrenceShape

/--
A material base is a set of exact fully instantiated material occurrences.
Membership is indexed by the whole `LocalOccurrence`, so its ID, kind,
ordered boundary profile, instance data, and supplied incidence all remain
part of the identity being admitted.
-/
structure MaterialBase
    (sigma : Signature.{u, v}) (InstanceData : Type w)
    (pi : PrimitiveFragment sigma) where
  Member : LocalOccurrence sigma InstanceData -> Prop
  member_material : forall {o}, Member o -> o.kind = .material
  member_primitiveBoundary :
    forall {o}, Member o -> o.shape.IsPrimitiveBoundary pi

/--
A persistent material inclusion preserves each exact old occurrence.  It has
no map on occurrences and therefore cannot relabel, replace, delete, or revise
one while transporting its membership evidence.
-/
structure BaseHom {sigma : Signature.{u, v}} {InstanceData : Type w}
    {pi : PrimitiveFragment sigma}
    (B C : MaterialBase sigma InstanceData pi) : Prop where
  map_member : forall {o}, B.Member o -> C.Member o

namespace BaseHom

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {pi : PrimitiveFragment sigma}

def id (B : MaterialBase sigma InstanceData pi) : BaseHom B B where
  map_member := fun evidence => evidence

def comp {B C D : MaterialBase sigma InstanceData pi}
    (g : BaseHom C D) (f : BaseHom B C) : BaseHom B D where
  map_member := fun evidence => g.map_member (f.map_member evidence)

@[simp]
theorem id_map_member (B : MaterialBase sigma InstanceData pi)
    {o : LocalOccurrence sigma InstanceData} (h : B.Member o) :
    (id B).map_member h = h := rfl

@[simp]
theorem comp_map_member {B C D : MaterialBase sigma InstanceData pi}
    (g : BaseHom C D) (f : BaseHom B C)
    {o : LocalOccurrence sigma InstanceData} (h : B.Member o) :
    (comp g f).map_member h = g.map_member (f.map_member h) := rfl

@[simp]
theorem id_comp {B C : MaterialBase sigma InstanceData pi}
    (f : BaseHom B C) : comp (id C) f = f :=
  Subsingleton.elim _ _

@[simp]
theorem comp_id {B C : MaterialBase sigma InstanceData pi}
    (f : BaseHom B C) : comp f (id B) = f :=
  Subsingleton.elim _ _

theorem comp_assoc {A B C D : MaterialBase sigma InstanceData pi}
    (h : BaseHom C D) (g : BaseHom B C) (f : BaseHom A B) :
    comp h (comp g f) = comp (comp h g) f :=
  Subsingleton.elim _ _

end BaseHom

structure RuleSystem
    (sigma : Signature.{u, v}) (InstanceData : Type w) where
  logical : LocalOccurrence sigma InstanceData -> Prop
  structural : LocalOccurrence sigma InstanceData -> Prop

structure ProofTheory
    (sigma : Signature.{u, v}) (InstanceData : Type w) where
  primitive : PrimitiveFragment sigma
  base : MaterialBase sigma InstanceData primitive
  rules : RuleSystem sigma InstanceData
  initial : Hypersequent sigma -> Prop

namespace ProofTheory

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

def withBase (T : ProofTheory sigma InstanceData)
    (C : MaterialBase sigma InstanceData T.primitive) :
    ProofTheory sigma InstanceData where
  primitive := T.primitive
  base := C
  rules := T.rules
  initial := T.initial

@[simp]
theorem withBase_self (T : ProofTheory sigma InstanceData) :
    T.withBase T.base = T := by
  cases T
  rfl

@[simp]
theorem withBase_withBase (T : ProofTheory sigma InstanceData)
    (C D : MaterialBase sigma InstanceData T.primitive) :
    (T.withBase C).withBase D = T.withBase D := rfl

inductive Admits (T : ProofTheory sigma InstanceData) :
    LocalOccurrence sigma InstanceData -> Prop where
  | material {o}
      (membership : T.base.Member o) :
      Admits T o
  | initial {o}
      (kind : o.kind = .logical)
      (nullary : o.shape.premises = [])
      (evidence : T.initial o.shape.conclusion) :
      Admits T o
  | logical {o}
      (kind : o.kind = .logical)
      (evidence : T.rules.logical o) :
      Admits T o
  | structural {o}
      (kind : o.kind = .structural)
      (evidence : T.rules.structural o) :
      Admits T o

theorem Admits.material_kind {T : ProofTheory sigma InstanceData}
    {o : LocalOccurrence sigma InstanceData} (h : T.base.Member o) :
    o.kind = .material :=
  T.base.member_material h

theorem Admits.material_primitiveBoundary
    {T : ProofTheory sigma InstanceData}
    {o : LocalOccurrence sigma InstanceData} (h : T.base.Member o) :
    o.shape.IsPrimitiveBoundary T.primitive :=
  T.base.member_primitiveBoundary h

def Admits.mapBase {T : ProofTheory sigma InstanceData}
    {C : MaterialBase sigma InstanceData T.primitive}
    (f : BaseHom T.base C)
    {o : LocalOccurrence sigma InstanceData} :
    T.Admits o -> (T.withBase C).Admits o
  | .material membership => .material (f.map_member membership)
  | .initial kind nullary evidence => .initial kind nullary evidence
  | .logical kind evidence => .logical kind evidence
  | .structural kind evidence => .structural kind evidence

end ProofTheory

end Potkin

import Mathlib.Data.Finset.Basic
import Potkin.Boundary

namespace Potkin

universe u v w

inductive OccurrenceKind where
  | material
  | logical
  | structural
deriving DecidableEq, Repr

structure OccurrenceShape (sigma : Signature.{u, v}) : Type (max u v) where
  premises : List (Hypersequent sigma)
  conclusion : Hypersequent sigma

namespace OccurrenceShape

variable {sigma : Signature.{u, v}}

def arity (shape : OccurrenceShape sigma) : Nat := shape.premises.length

end OccurrenceShape

/--
A supplied local occurrence profile for one exact multiset boundary.  The list
gives every displayed occurrence a stable local slot, including duplicates,
and `exact` ties those slots to the original multiset without quotienting
multiplicity.
-/
structure ComponentProfile {sigma : Signature.{u, v}}
    (G : Hypersequent sigma) where
  displayed : List (Sequent sigma)
  exact : (displayed : Multiset (Sequent sigma)) = G.components

/-- Profiles for every ordered premise and the conclusion of one occurrence. -/
structure OccurrenceProfiles {sigma : Signature.{u, v}}
    (shape : OccurrenceShape sigma) where
  premise : (i : Fin shape.premises.length) ->
    ComponentProfile (shape.premises.get i)
  conclusion : ComponentProfile shape.conclusion

/-- One edge between exact locally indexed displayed component occurrences. -/
structure ComponentEdge {sigma : Signature.{u, v}}
    {shape : OccurrenceShape sigma} (profiles : OccurrenceProfiles shape) where
  premiseSlot : Fin shape.premises.length
  premiseComponent :
    Fin ((profiles.premise premiseSlot).displayed.length)
  conclusionComponent : Fin profiles.conclusion.displayed.length
deriving DecidableEq

structure ComponentIncidence {sigma : Signature.{u, v}}
    (shape : OccurrenceShape sigma) where
  profiles : OccurrenceProfiles shape
  edges : Finset (ComponentEdge profiles)

structure LocalOccurrence
    (sigma : Signature.{u, v}) (InstanceData : Type w) :
    Type (max (max u v) w) where
  id : Nat
  kind : OccurrenceKind
  shape : OccurrenceShape sigma
  instanceData : InstanceData
  incidence : Option (ComponentIncidence shape)

namespace LocalOccurrence

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

def arity (o : LocalOccurrence sigma InstanceData) : Nat :=
  o.shape.premises.length

end LocalOccurrence

end Potkin

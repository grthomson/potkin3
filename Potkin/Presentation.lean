import Potkin.ProofTheory

namespace Potkin

universe u v w

structure EquippedPresentation
    {sigma : Signature.{u, v}} {InstanceData : Type w}
    (T : ProofTheory sigma InstanceData) where
  registry : List (LocalOccurrence sigma InstanceData)
  uniqueIds : (registry.map LocalOccurrence.id).Nodup
  admitted : (o : LocalOccurrence sigma InstanceData) -> o ∈ registry -> T.Admits o

namespace EquippedPresentation

variable {sigma : Signature.{u, v}} {InstanceData : Type w}
variable {T : ProofTheory sigma InstanceData}

structure LookupResult (P : EquippedPresentation T) (id : Nat) where
  occurrence : LocalOccurrence sigma InstanceData
  registered : occurrence ∈ P.registry
  id_eq : occurrence.id = id

private def lookupList (id : Nat) :
    (xs : List (LocalOccurrence sigma InstanceData)) ->
      Option {o // o ∈ xs ∧ o.id = id}
  | [] => none
  | o :: os =>
      if h : o.id = id then
        some ⟨o, by simp, h⟩
      else
        match lookupList id os with
        | none => none
        | some found =>
            some ⟨found.1, by simp [found.2.1], found.2.2⟩

def lookup (P : EquippedPresentation T) (id : Nat) : Option (LookupResult P id) :=
  match lookupList id P.registry with
  | none => none
  | some found => some ⟨found.1, found.2.1, found.2.2⟩

def mapBase (P : EquippedPresentation T) {C : MaterialBase sigma}
    (f : BaseHom T.base C) : EquippedPresentation (T.withBase C) where
  registry := P.registry
  uniqueIds := P.uniqueIds
  admitted := fun o ho => (P.admitted o ho).mapBase f

@[simp]
theorem mapBase_registry (P : EquippedPresentation T) {C : MaterialBase sigma}
    (f : BaseHom T.base C) :
    (P.mapBase f).registry = P.registry := rfl

end EquippedPresentation

end Potkin

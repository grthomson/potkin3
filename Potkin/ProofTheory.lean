import Potkin.Occurrence

namespace Potkin

universe u v w x y

structure MaterialBase (sigma : Signature.{u, v}) where
  Evidence : Hypersequent sigma -> Type w

structure BaseHom {sigma : Signature.{u, v}}
    (B : MaterialBase.{u, v, w} sigma)
    (C : MaterialBase.{u, v,x} sigma) where
  mapEvidence : {G : Hypersequent sigma} -> B.Evidence G -> C.Evidence G

namespace BaseHom

variable {sigma : Signature.{u, v}}

def id (B : MaterialBase.{u, v, w} sigma) : BaseHom B B where
  mapEvidence := fun evidence => evidence

def comp {B : MaterialBase.{u, v,w} sigma}
    {C : MaterialBase.{u, v,x} sigma}
    {D : MaterialBase.{u, v,y} sigma}
    (g : BaseHom C D) (f : BaseHom B C) : BaseHom B D where
  mapEvidence := fun evidence => g.mapEvidence (f.mapEvidence evidence)

@[simp]
theorem id_mapEvidence (B : MaterialBase.{u, v,w} sigma)
    {G : Hypersequent sigma} (e : B.Evidence G) :
    (id B).mapEvidence e = e := rfl

end BaseHom

structure RuleSystem
    (sigma : Signature.{u, v}) (InstanceData : Type w) where
  logical : LocalOccurrence sigma InstanceData -> Prop
  structural : LocalOccurrence sigma InstanceData -> Prop

structure ProofTheory
    (sigma : Signature.{u, v}) (InstanceData : Type w) where
  base : MaterialBase sigma
  rules : RuleSystem sigma InstanceData
  initial : Hypersequent sigma -> Prop

namespace ProofTheory

variable {sigma : Signature.{u, v}} {InstanceData : Type w}

def withBase (T : ProofTheory sigma InstanceData)
    (C : MaterialBase sigma) : ProofTheory sigma InstanceData where
  base := C
  rules := T.rules
  initial := T.initial

inductive Admits (T : ProofTheory sigma InstanceData) :
    LocalOccurrence sigma InstanceData -> Prop where
  | material {o}
      (kind : o.kind = .material)
      (nullary : o.shape.premises = [])
      (evidence : Nonempty (T.base.Evidence o.shape.conclusion)) :
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

def Admits.mapBase {T : ProofTheory sigma InstanceData}
    {C : MaterialBase sigma} (f : BaseHom T.base C)
    {o : LocalOccurrence sigma InstanceData} :
    T.Admits o -> (T.withBase C).Admits o
  | .material kind nullary evidence =>
      .material kind nullary (evidence.map f.mapEvidence)
  | .initial kind nullary evidence => .initial kind nullary evidence
  | .logical kind evidence => .logical kind evidence
  | .structural kind evidence => .structural kind evidence

end ProofTheory

end Potkin

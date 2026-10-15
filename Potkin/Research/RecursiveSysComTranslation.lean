import Potkin.Research.RecursiveSysComSource
import Potkin.Research.RecursiveSysComNative
import Potkin.Research.RecursiveSysComCopy
import Potkin.Research.StructuralLemmaCuts

/-!
# Recursive marked-premise translation, before commutative collection

All recursive control is source-only. A phase first constructs each actual
ordered Com pair, translates the left context for that fixed right marked
component, and then translates the right context with the completed left
sequent as passive context. The physical native interfaces retain each copy.
`Ports` is occurrence/boundary metadata on existing native trees, not a proof,
forest, context or cut carrier.
-/
namespace Potkin.Research.RecursiveSysComTranslation
open RecursiveSysComSource ContractionPostponement

abbrev Sig := D3SourceEncoding.signature
abbrev Data := HLJInternalWeakening.Data Sig
abbrev Theory := HLJInternalWeakening.theory Sig
abbrev Seq := D3SourceEncoding.Sequent
abbrev Ctx := D3SourceEncoding.Context
abbrev Parameters := RecursiveSysComSource.Parameters
abbrev Key := Nat → Data → Nat

/-- A deterministic source-pair hint, not an occurrence identity. Registry
allocation also compares the complete native descriptor; physical copies are
retained by native addresses independently of this hint. -/
def pairHint (a b : Nat) : Nat := if a < b then b * b + a else a * a + a + b

def enc (S : Seq) : Potkin.Sequent Sig := D3SourceEncoding.encodeSequent S
def framed (K : Multiset (Potkin.Sequent Sig)) (S : Seq) : Hypersequent Sig :=
  RecursiveSysComNative.frame K (enc S)

def castTree {G H : Hypersequent Sig} (equal : G = H) (tree : CKTree Sig Data G) :
    CKTree Sig Data H := equal ▸ tree

theorem swap_frame (K : Multiset (Potkin.Sequent Sig)) (S U : Seq) :
    framed (K + {enc U}) S = framed (K + {enc S}) U :=
  (RecursiveSysComNative.frame_pair K (enc S) (enc U)).trans
    (RecursiveSysComNative.frame_pair_right K (enc S) (enc U)).symm

noncomputable def iwInstance (key : Key) (hint : Nat)
    (K : Multiset (Potkin.Sequent Sig)) (a : D3SourceEncoding.Formula) (gamma pi : Ctx) :=
  RecursiveSysComNative.iwInstance (key hint) K (D3SourceEncoding.encodeFormula a)
    (D3SourceEncoding.encodeContext gamma) (D3SourceEncoding.encodeContext pi)

theorem iw_in (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (a : D3SourceEncoding.Formula) (gamma pi : Ctx) :
    (iwInstance key hint K a gamma pi).shape.premises = [framed K ⟨gamma, pi⟩] := rfl
theorem iw_out (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (a : D3SourceEncoding.Formula) (gamma pi : Ctx) :
    (iwInstance key hint K a gamma pi).shape.conclusion = framed K ⟨{a} + gamma, pi⟩ := by
  simp [iwInstance, RecursiveSysComNative.iw_conclusion, framed, enc,
    D3SourceEncoding.encodeSequent, D3SourceEncoding.encodeContext]

noncomputable def iw (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (a : D3SourceEncoding.Formula) (gamma pi : Ctx)
    (child : CKTree Sig Data (framed K ⟨gamma, pi⟩)) :
    CKTree Sig Data (framed K ⟨{a} + gamma, pi⟩) :=
  node (iwInstance key hint K a gamma pi) (iw_in ..) (iw_out ..) (.cons child .nil)

noncomputable def comInstance (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (p : Parameters) {U V : Seq} (l : TopSpec 0 p U) (r : TopSpec 1 p V) :=
  RecursiveSysComNative.comInstance (key hint) K
    (D3SourceEncoding.encodeContext p.phi) (D3SourceEncoding.encodeContext p.psi)
    (D3SourceEncoding.encodeContext l.gamma) (D3SourceEncoding.encodeContext r.gamma)
    (D3SourceEncoding.encodeContext l.pi) (D3SourceEncoding.encodeContext r.pi)

theorem com_in (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (p : Parameters) {U V : Seq} (l : TopSpec 0 p U) (r : TopSpec 1 p V) :
    (comInstance key hint K p l r).shape.premises = [framed K l.input, framed K r.input] := by
  simp [comInstance, RecursiveSysComNative.com_premises, framed, enc, TopSpec.input,
    D3SourceEncoding.topInput, D3SourceEncoding.encodeSequent]

theorem com_out (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (p : Parameters) {U V : Seq} (l : TopSpec 0 p U) (r : TopSpec 1 p V) :
    (comInstance key hint K p l r).shape.conclusion = framed (K + {enc V}) U := by
  rw [comInstance, RecursiveSysComNative.com_conclusion]
  have hl : (⟨D3SourceEncoding.encodeContext p.psi + D3SourceEncoding.encodeContext l.gamma,
      D3SourceEncoding.encodeContext l.pi⟩ : Potkin.Sequent Sig) = enc U := by
    simpa [enc, D3SourceEncoding.encodeSequent, D3SourceEncoding.topOutput] using
      congrArg D3SourceEncoding.encodeSequent l.output
  have hr : (⟨D3SourceEncoding.encodeContext p.phi + D3SourceEncoding.encodeContext r.gamma,
      D3SourceEncoding.encodeContext r.pi⟩ : Potkin.Sequent Sig) = enc V := by
    simpa [enc, D3SourceEncoding.encodeSequent, D3SourceEncoding.topOutput] using
      congrArg D3SourceEncoding.encodeSequent r.output
  rw [hl, hr]
  exact (RecursiveSysComNative.frame_pair K (enc U) (enc V)).symm

noncomputable def com (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (p : Parameters) {U V : Seq} (l : TopSpec 0 p U) (r : TopSpec 1 p V)
    (left : CKTree Sig Data (framed K l.input)) (right : CKTree Sig Data (framed K r.input)) :
    CKTree Sig Data (framed (K + {enc V}) U) :=
  node (comInstance key hint K p l r) (com_in ..) (com_out ..) (.cons left (.cons right .nil))

noncomputable def closeInstance (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (S : Seq) := RecursiveSysComNative.ecInstance (key hint) K (enc S)

theorem close_in (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig)) (S : Seq) :
    (closeInstance key hint K S).shape.premises = [framed (K + {enc S}) S] := by
  rw [closeInstance, RecursiveSysComNative.ec_premises]
  exact congrArg (fun G => [G]) (RecursiveSysComNative.frame_pair K (enc S) (enc S)).symm
theorem close_out (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig)) (S : Seq) :
    (closeInstance key hint K S).shape.conclusion = framed K S := by
  rw [closeInstance, RecursiveSysComNative.ec_conclusion]; rfl

noncomputable def close (key : Key) (hint : Nat) (K : Multiset (Potkin.Sequent Sig))
    (S : Seq) (child : CKTree Sig Data (framed (K + {enc S}) S)) : CKTree Sig Data (framed K S) :=
  node (closeInstance key hint K S) (close_in ..) (close_out ..) (.cons child .nil)

/-- The real marked-premise recursion. Its source origins are constructor
indices, never recovered by comparing formulae or displayed boundaries. -/
noncomputable def translate (key : Key) :
    {S : Seq} → {O : Type} → {bounds : O → Seq} → (p : Source S O bounds) →
    (K : Multiset (Potkin.Sequent Sig)) →
    ((o : O) → CKTree Sig Data (framed K (bounds o))) → CKTree Sig Data (framed K S)
  | _, _, _, .leaf _, _, F => F PUnit.unit
  | _, _, _, .iw hint a gamma pi _ body, K, F => iw key hint K a gamma pi (translate key body K F)
  | _, _, _, .phase hint _ p S _ left right topKey sl sr, K, F =>
      close key hint K S
        (translate key right (K + {enc S}) (fun v =>
          castTree (swap_frame K S _) (translate key left (K + {enc _}) (fun u =>
            com key (pairHint (topKey (.inl u)) (topKey (.inr v))) K p (sl u) (sr v)
              (F (.inl u)) (F (.inr v))))))

section Metadata
variable {I : Type} (B : I → Hypersequent Sig)

abbrev Ports {G : Hypersequent Sig} (tree : CKTree Sig Data G) :=
  (h : tree.LeafOccurrence) → {i : I // B i = tree.leafBoundary h}
abbrev ChildPorts {Gs : List (Hypersequent Sig)} (trees : CKChildren Sig Data Gs) :=
  (h : trees.LeafOccurrence) → {i : I // B i = trees.leafBoundary h}

def supply {G : Hypersequent Sig} {tree : CKTree Sig Data G} (ls : Ports B tree)
    (F : (i : I) → CKTree Sig Data (B i)) : tree.LeafAssignment :=
  fun h => (ls h).2 ▸ F (ls h).1
def plug {G : Hypersequent Sig} (tree : CKTree Sig Data G) (ls : Ports B tree)
    (F : (i : I) → CKTree Sig Data (B i)) := tree.fillAssignment (supply B ls F)

def plugChildren {Gs : List (Hypersequent Sig)} (trees : CKChildren Sig Data Gs)
    (ls : ChildPorts B trees) (F : (i : I) → CKTree Sig Data (B i)) :=
  trees.fillAssignment (fun h => (ls h).2 ▸ F (ls h).1)

def nilPorts : ChildPorts B (.nil : CKChildren Sig Data []) := fun h => nomatch h
def consPorts {G Gs} {head : CKTree Sig Data G} {tail : CKChildren Sig Data Gs}
    (lh : Ports B head) (lt : ChildPorts B tail) : ChildPorts B (.cons head tail) :=
  fun h => match h with | .inl h => lh h | .inr h => lt h
def nodePorts {Gs G} (o : LocalOccurrence Sig Data) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (cs : CKChildren Sig Data Gs) (ls : ChildPorts B cs) :
    Ports B (node o hp hc cs) := by subst Gs; subst G; exact ls
def castPorts {G H} (e : G = H) (t : CKTree Sig Data G) (ls : Ports B t) :
    Ports B (castTree e t) := by cases e; exact ls

theorem plugChildren_cons {G Gs} (h : CKTree Sig Data G) (t : CKChildren Sig Data Gs)
    (lh : Ports B h) (lt : ChildPorts B t) (F : (i : I) → CKTree Sig Data (B i)) :
    plugChildren B (.cons h t) (consPorts B lh lt) F =
      .cons (plug B h lh F) (plugChildren B t lt F) := rfl

theorem plugChildren_nil (F : (i : I) → CKTree Sig Data (B i)) :
    plugChildren B (.nil : CKChildren Sig Data []) (nilPorts B) F = .nil := rfl

theorem plug_cast {G H} (e : G = H) (t : CKTree Sig Data G) (ls : Ports B t)
    (F : (i : I) → CKTree Sig Data (B i)) :
    plug B (castTree e t) (castPorts B e t ls) F = castTree e (plug B t ls F) := by cases e; rfl

theorem plug_node {Gs G} (o : LocalOccurrence Sig Data) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (cs : CKChildren Sig Data Gs) (ls : ChildPorts B cs)
    (F : (i : I) → CKTree Sig Data (B i)) :
    plug B (node o hp hc cs) (nodePorts B o hp hc cs ls) F =
      node o hp hc (plugChildren B cs ls F) := by
  subst Gs; subst G; rfl

noncomputable def translatePorts (key : Key) :
    {S : Seq} → {O : Type} → {bounds : O → Seq} → (p : Source S O bounds) →
    (K : Multiset (Potkin.Sequent Sig)) →
    (F : (o : O) → CKTree Sig Data (framed K (bounds o))) →
    ((o : O) → Ports B (F o)) → Ports B (translate key p K F)
  | _, _, _, .leaf _, _, _, ls => ls PUnit.unit
  | _, _, _, .iw hint a gamma pi _ body, K, F, ls =>
      nodePorts B _ (iw_in ..) (iw_out ..) _
        (consPorts B (translatePorts key body K F ls) (nilPorts B))
  | _, _, _, .phase hint _ p S _ left right tk sl sr, K, F, ls =>
      nodePorts B _ (close_in ..) (close_out ..) _
        (consPorts B
          (translatePorts key right (K + {enc S}) _ (fun v =>
            castPorts B (swap_frame K S _) _
              (translatePorts key left (K + {enc _}) _ (fun u =>
                nodePorts B _ (com_in ..) (com_out ..) _
                  (consPorts B (ls (.inl u)) (consPorts B (ls (.inr v)) (nilPorts B)))))))
          (nilPorts B))

/-- The computed labels are natural under actual native simultaneous filling. -/
theorem plug_translate (key : Key) :
    {S : Seq} → {O : Type} → {bounds : O → Seq} → (p : Source S O bounds) →
    (K : Multiset (Potkin.Sequent Sig)) →
    (F : (o : O) → CKTree Sig Data (framed K (bounds o))) →
    (ls : (o : O) → Ports B (F o)) → (actual : (i : I) → CKTree Sig Data (B i)) →
    plug B (translate key p K F) (translatePorts B key p K F ls) actual =
      translate key p K (fun o => plug B (F o) (ls o) actual)
  | _, _, _, .leaf _, _, _, _, _ => rfl
  | _, _, _, .iw hint a gamma pi single body, K, F, ls, actual => by
      simp only [translate, translatePorts, iw, plug_node, plugChildren_cons,
        plugChildren_nil, plug_translate]
  | _, _, _, .phase hint uid p S single left right tk sl sr, K, F, ls, actual => by
      simp only [translate, translatePorts, close, com, plug_node, plugChildren_cons,
        plugChildren_nil, plug_cast, plug_translate]
      rfl

def word {G : Hypersequent Sig} (t : CKTree Sig Data G) (ls : Ports B t) : List I :=
  t.leafOrder.map (fun h => (ls h).1)
def childWord {Gs : List (Hypersequent Sig)} (t : CKChildren Sig Data Gs)
    (ls : ChildPorts B t) : List I := t.leafOrder.map (fun h => (ls h).1)

theorem word_node {Gs G} (o : LocalOccurrence Sig Data) (hp : o.shape.premises = Gs)
    (hc : o.shape.conclusion = G) (cs : CKChildren Sig Data Gs) (ls : ChildPorts B cs) :
    word B (node o hp hc cs) (nodePorts B o hp hc cs ls) = childWord B cs ls := by
  subst Gs; subst G; rfl
theorem word_cons {G Gs} (h : CKTree Sig Data G) (t : CKChildren Sig Data Gs)
    (lh : Ports B h) (lt : ChildPorts B t) :
    childWord B (.cons h t) (consPorts B lh lt) = word B h lh ++ childWord B t lt := by
  change (h.leafOrder.map Sum.inl ++ t.leafOrder.map Sum.inr).map _ = _
  rw [List.map_append, List.map_map, List.map_map]
  rfl
theorem word_nil : childWord B (.nil : CKChildren Sig Data []) (nilPorts B) = [] := rfl
theorem word_cast {G H} (e : G = H) (t : CKTree Sig Data G) (ls : Ports B t) :
    word B (castTree e t) (castPorts B e t ls) = word B t ls := by cases e; rfl

theorem word_translate (key : Key) :
    {S : Seq} → {O : Type} → {bounds : O → Seq} → (p : Source S O bounds) →
    (K : Multiset (Potkin.Sequent Sig)) →
    (F : (o : O) → CKTree Sig Data (framed K (bounds o))) →
    (ls : (o : O) → Ports B (F o)) →
    word B (translate key p K F) (translatePorts B key p K F ls) =
      RecursiveSysComCopy.words p (fun o => word B (F o) (ls o))
  | _, _, _, .leaf _, _, _, _ => rfl
  | _, _, _, .iw hint a gamma pi single body, K, F, ls => by
      simp only [translate, translatePorts, iw, word_node, word_cons, word_nil,
        List.append_nil, word_translate, RecursiveSysComCopy.words]
  | _, _, _, .phase hint uid p S single left right tk sl sr, K, F, ls => by
      simp only [translate, translatePorts, close, com, word_node, word_cons, word_nil,
        List.append_nil, word_cast, word_translate, RecursiveSysComCopy.words]
      rfl
end Metadata

noncomputable def scaffold (key : Key) {S O bounds} (p : Source S O bounds)
    (K : Multiset (Potkin.Sequent Sig)) : CKTree Sig Data (framed K S) :=
  translate key p K (fun o => .interface (framed K (bounds o)))

def interfacePorts {O : Type} (bounds : O → Seq) (K : Multiset (Potkin.Sequent Sig)) (o : O) :
    Ports (fun i => framed K (bounds i)) (.interface (framed K (bounds o))) := fun _ => ⟨o, rfl⟩

noncomputable def origins (key : Key) {S O bounds} (p : Source S O bounds)
    (K : Multiset (Potkin.Sequent Sig)) : Ports (fun o => framed K (bounds o)) (scaffold key p K) :=
  translatePorts _ key p K _ (interfacePorts bounds K)

/-- Literal scaffold filling for EVERY source constructor and every native
provider family; no completed-proof cut enumeration is involved. -/
theorem scaffold_fill (key : Key) {S O bounds} (p : Source S O bounds)
    (K : Multiset (Potkin.Sequent Sig)) (F : (o : O) → CKTree Sig Data (framed K (bounds o))) :
    plug _ (scaffold key p K) (origins key p K) F = translate key p K F := by
  simpa only [scaffold, origins, plug, supply, interfacePorts, CKTree.fillAssignment] using
    plug_translate (fun o => framed K (bounds o)) key p K
      (fun o => .interface (framed K (bounds o))) (interfacePorts bounds K) F

theorem native_copy_word (key : Key) {S O bounds} (p : Source S O bounds)
    (K : Multiset (Potkin.Sequent Sig)) :
    (scaffold key p K).leafOrder.map (fun h => (origins key p K h).1) =
      RecursiveSysComCopy.uses p := by
  rw [show (scaffold key p K).leafOrder.map (fun h => (origins key p K h).1) =
    word _ (scaffold key p K) (origins key p K) from rfl]
  change word _ _ (translatePorts _ key p K _ (interfacePorts bounds K)) = _
  rw [word_translate, RecursiveSysComCopy.words_uses]
  simp [word, interfacePorts, CKTree.leafOrder]

#print axioms scaffold_fill
#print axioms native_copy_word
end Potkin.Research.RecursiveSysComTranslation

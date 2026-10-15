import Potkin.Research.RecursiveSysComSource

/-!
# Constructor-computed physical copy control for prepared Sys(com)

The source constructor, not an arbitrary supplied map, determines the word of
physical uses. A phase retains the right marked choice while interpreting the
left, and then the right context copies the resulting left derivations. List
positions distinguish physical uses even when their source origins agree.
Native occurrence/address correspondence is proved by the translation module.
-/
namespace Potkin.Research.RecursiveSysComCopy
open RecursiveSysComSource

abbrev Sequent := RecursiveSysComSource.Sequent
abbrev Parameters := RecursiveSysComSource.Parameters

def uses : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → List O
  | _, _, _, .leaf _ => [PUnit.unit]
  | _, _, _, .iw _ _ _ _ _ body => uses body
  | _, _, _, .phase _ _ _ _ _ left right _ _ _ =>
      (uses right).flatMap (fun v =>
        (uses left).flatMap (fun u => [Sum.inl u, Sum.inr v]))

/-- Interpretation of a source construction in ordered provider words. It
matches the actual curried marked-premise construction, not forest product. -/
def words {I : Type*} : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → (O → List I) → List I
  | _, _, _, .leaf _, W => W PUnit.unit
  | _, _, _, .iw _ _ _ _ _ body, W => words body W
  | _, _, _, .phase _ _ _ _ _ left right _ _ _, W =>
      words right (fun v => words left (fun u => W (.inl u) ++ W (.inr v)))

theorem words_uses {I : Type*} : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (p : Source S O bounds) → (W : O → List I) → words p W = (uses p).flatMap W
  | _, _, _, .leaf _, W => by simp [words, uses]
  | _, _, _, .iw _ _ _ _ _ body, W => words_uses body W
  | _, _, _, .phase _ _ _ _ _ left right _ _ _, W => by
      simp only [words, uses, words_uses, List.flatMap_assoc, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]

def phases : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    Source S O bounds → Nat
  | _, _, _, .leaf _ => 0
  | _, _, _, .iw _ _ _ _ _ body => phases body
  | _, _, _, .phase _ _ _ _ _ left right _ _ _ => 1 + phases left + phases right

private theorem row_length {A B : Type*} (xs : List A) (b : B) :
    (xs.flatMap (fun a => [Sum.inl a, Sum.inr b])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]; omega

private theorem rectangle_length {A B : Type*} (xs : List A) (ys : List B) :
    (ys.flatMap (fun b => xs.flatMap (fun a => [Sum.inl a, Sum.inr b]))).length =
      2 * xs.length * ys.length := by
  induction ys with
  | nil => simp
  | cons b ys ih =>
      simp only [List.flatMap_cons, List.length_append, row_length, ih, List.length_cons]
      simp [Nat.mul_add, Nat.add_comm]

theorem phase_uses_length {S OL OR BL BR} (key uid : Nat) (p : Parameters)
    (single : S.rhs.card ≤ 1) (left : Source S OL BL) (right : Source S OR BR)
    (topKey : OL ⊕ OR → Nat) (specL : ∀ o, TopSpec 0 p (BL o))
    (specR : ∀ o, TopSpec 1 p (BR o)) :
    (uses (.phase key uid p S single left right topKey specL specR)).length =
      2 * (uses left).length * (uses right).length := rectangle_length _ _

/-- An unbounded structural theorem, not agreement at finitely many depths. -/
theorem uses_length : {S : Sequent} → {O : Type} → {bounds : O → Sequent} →
    (p : Source S O bounds) → (uses p).length = 2 ^ phases p
  | _, _, _, .leaf _ => rfl
  | _, _, _, .iw _ _ _ _ _ body => uses_length body
  | _, _, _, .phase key uid p S single left right tk sl sr => by
      rw [phase_uses_length, uses_length left, uses_length right]
      simp only [phases, pow_add, pow_one, mul_assoc]

def affected {S O bounds} (p : Source S O bounds) (changed : O → Bool) : List O :=
  (uses p).filter changed

def affectedIndices {S O bounds} (p : Source S O bounds) (changed : O → Bool) : List Nat :=
  ((uses p).zipIdx).filterMap (fun entry => if changed entry.1 then some entry.2 else none)

private theorem row_affected {A B : Type*} (xs : List A) (b : B)
    (f : A → Bool) (g : B → Bool) :
    ((xs.flatMap (fun a => [Sum.inl a, Sum.inr b])).filter (Sum.elim f g)).length =
      (xs.filter f).length + (if g b then xs.length else 0) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases hf : f a <;> cases hg : g b <;>
        simp [List.flatMap_cons, List.filter_append, hf, hg, ih] <;> omega

private theorem rectangle_affected {A B : Type*} (xs : List A) (ys : List B)
    (f : A → Bool) (g : B → Bool) :
    ((ys.flatMap (fun b => xs.flatMap (fun a => [Sum.inl a, Sum.inr b]))).filter
      (Sum.elim f g)).length =
        (xs.filter f).length * ys.length + xs.length * (ys.filter g).length := by
  induction ys with
  | nil => simp
  | cons b ys ih =>
      cases hg : g b <;>
        simp only [List.flatMap_cons, List.filter_append, List.length_append,
          row_affected, ih, hg, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
          List.length_cons, List.filter_cons]
      all_goals simp_all [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Exact affected physical-use budget. This is not an assembly-node or
runtime bound, and shared logical origins are not deduplicated. -/
theorem phase_affected {S OL OR BL BR} (key uid : Nat) (p : Parameters)
    (single : S.rhs.card ≤ 1) (left : Source S OL BL) (right : Source S OR BR)
    (topKey : OL ⊕ OR → Nat) (specL : ∀ o, TopSpec 0 p (BL o))
    (specR : ∀ o, TopSpec 1 p (BR o)) (changed : OL ⊕ OR → Bool) :
    (affected (.phase key uid p S single left right topKey specL specR) changed).length =
      (affected left (fun i => changed (.inl i))).length * (uses right).length +
      (uses left).length * (affected right (fun j => changed (.inr j))).length := by
  have eta : Sum.elim (fun i => changed (.inl i)) (fun j => changed (.inr j)) = changed := by
    funext s
    cases s <;> rfl
  simpa only [affected, uses, eta] using
    rectangle_affected (uses left) (uses right)
      (fun i => changed (.inl i)) (fun j => changed (.inr j))

theorem affected_le {S O bounds} (p : Source S O bounds) (changed : O → Bool) :
    (affected p changed).length ≤ 2 ^ phases p := by
  rw [← uses_length]
  exact List.length_filter_le _ _

#print axioms words_uses
#print axioms uses_length
#print axioms phase_affected
#print axioms affected_le
end Potkin.Research.RecursiveSysComCopy

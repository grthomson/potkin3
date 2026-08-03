import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Potkin.Language

/-!
# Whole hypersequent boundaries

Formula contexts and displayed hypersequent components are finite multisets.
A hypersequent is nonempty by construction.
-/

namespace Potkin

universe u v

/-- Formula contexts are finite multisets: exchange is canonical, multiplicity remains. -/
abbrev Context (sigma : Signature.{u, v}) := Multiset (Formula sigma)

/-- A two-sided multiset sequent. -/
structure Sequent (sigma : Signature.{u, v}) : Type (max u v) where
  lhs : Context sigma
  rhs : Context sigma

instance {sigma : Signature.{u, v}} [DecidableEq (Formula sigma)] :
    DecidableEq (Sequent sigma)
  | ⟨lhs, rhs⟩, ⟨lhs', rhs'⟩ =>
      if hl : lhs = lhs' then
        if hr : rhs = rhs' then
          isTrue (by cases hl; cases hr; rfl)
        else
          isFalse (by intro h; cases h; exact hr rfl)
      else
        isFalse (by intro h; cases h; exact hl rfl)

namespace Sequent

variable {sigma : Signature.{u, v}}

@[ext]
theorem ext {S T : Sequent sigma} (hl : S.lhs = T.lhs) (hr : S.rhs = T.rhs) : S = T := by
  cases S
  cases T
  cases hl
  cases hr
  rfl

end Sequent

/-- A nonempty finite multiset of displayed sequents. -/
structure Hypersequent (sigma : Signature.{u, v}) : Type (max u v) where
  components : Multiset (Sequent sigma)
  nonempty : components = 0 -> False

instance {sigma : Signature.{u, v}} [DecidableEq (Formula sigma)] :
    DecidableEq (Hypersequent sigma)
  | ⟨components, nonempty⟩, ⟨components', nonempty'⟩ =>
      if h : components = components' then
        isTrue (by cases h; rfl)
      else
        isFalse (by intro equality; cases equality; exact h rfl)

namespace Hypersequent

variable {sigma : Signature.{u, v}}

@[ext]
theorem ext {G H : Hypersequent sigma} (h : G.components = H.components) : G = H := by
  cases G
  cases H
  cases h
  rfl

/-- The one-component whole hypersequent. -/
def singleton (S : Sequent sigma) : Hypersequent sigma where
  components := {S}
  nonempty := by simp

/-- A whole hypersequent with two displayed component occurrences. -/
def pair (S T : Sequent sigma) : Hypersequent sigma where
  components := {S, T}
  nonempty := by simp

@[simp]
theorem singleton_components (S : Sequent sigma) :
    (singleton S).components = {S} := rfl

@[simp]
theorem pair_components (S T : Sequent sigma) :
    (pair S T).components = {S, T} := rfl

end Hypersequent

end Potkin

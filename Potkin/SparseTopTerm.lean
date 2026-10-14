import Mathlib.Data.Multiset.Count

/-!
# Reading a unique highest-degree term from collected finite observations

These lemmas concern a finite multiset of monomials, with multiplicity.
They define no proof, cut, coefficient or record carrier. The degree function
is supplied independently, and the strict-greatest hypotheses must be proved
from the actual cut decomposition by the application.

In particular, this is not a linear-independence or linear-kernel theorem:
multiset observations have nonnegative multiplicities and no cancellation.
-/

namespace Potkin.SparseTopTerm

universe u

/-- Every member of at least the distinguished degree is the unique greatest
monomial. This conclusion does not assume monomial equality in advance. -/
theorem member_eq_of_degree_ge {Monomial : Type u}
    (degree : Monomial → Nat) (terms : Multiset Monomial)
    (greatest candidate : Monomial)
    (strict : ∀ term ∈ terms, term ≠ greatest → degree term < degree greatest)
    (member : candidate ∈ terms) (atLeast : degree greatest ≤ degree candidate) :
    candidate = greatest := by
  classical
  by_contra different
  exact (Nat.not_lt_of_ge atLeast) (strict candidate member different)

/-- Equality of the collected finite observations recovers their unique
greatest-degree monomials, even when their degrees were not known equal. -/
theorem greatest_eq_of_multiset_eq {Monomial : Type u}
    (degree : Monomial → Nat) (left right : Multiset Monomial)
    (leftTop rightTop : Monomial)
    (leftMember : leftTop ∈ left) (rightMember : rightTop ∈ right)
    (leftStrict : ∀ term ∈ left, term ≠ leftTop → degree term < degree leftTop)
    (rightStrict : ∀ term ∈ right, term ≠ rightTop → degree term < degree rightTop)
    (equal : left = right) : leftTop = rightTop := by
  classical
  by_contra different
  have rightInLeft : rightTop ∈ left := by
    rw [equal]
    exact rightMember
  have leftInRight : leftTop ∈ right := by
    rw [← equal]
    exact leftMember
  have smallerRight := leftStrict rightTop rightInLeft (Ne.symm different)
  have smallerLeft := rightStrict leftTop leftInRight different
  exact Nat.lt_asymm smallerRight smallerLeft

/-- The recovered term's multiplicity is also retained by collection.
Uniqueness of the supporting term does not by itself assert coefficient one. -/
theorem greatest_multiplicity_eq_of_multiset_eq {Monomial : Type u}
    [DecidableEq Monomial]
    (degree : Monomial → Nat) (left right : Multiset Monomial)
    (leftTop rightTop : Monomial)
    (leftMember : leftTop ∈ left) (rightMember : rightTop ∈ right)
    (leftStrict : ∀ term ∈ left, term ≠ leftTop → degree term < degree leftTop)
    (rightStrict : ∀ term ∈ right, term ≠ rightTop → degree term < degree rightTop)
    (equal : left = right) :
    left.count leftTop = right.count rightTop := by
  have same := greatest_eq_of_multiset_eq degree left right leftTop rightTop
    leftMember rightMember leftStrict rightStrict equal
  rw [equal, same]

end Potkin.SparseTopTerm

#print axioms Potkin.SparseTopTerm.greatest_eq_of_multiset_eq
#print axioms Potkin.SparseTopTerm.greatest_multiplicity_eq_of_multiset_eq

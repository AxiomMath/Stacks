module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Algebra.Group.Idempotent

/-!
# Idempotents of a local ring

In a local ring the only idempotents are `0` and `1`.

## Main results

* `IsLocalRing.isIdempotentElem_eq_zero_or_one`.
-/

@[expose] public section

namespace IsLocalRing

/-- In a local ring the only idempotents are `0` and `1`: an idempotent unit is `1`, and if
`1 - e` is a unit then `e = 0`. -/
theorem isIdempotentElem_eq_zero_or_one {R : Type*} [CommRing R] [IsLocalRing R] {e : R}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp he)
  · exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp he.one_sub))

end IsLocalRing

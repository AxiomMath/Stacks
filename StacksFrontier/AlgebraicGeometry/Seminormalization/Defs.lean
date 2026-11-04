module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Ring
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Seminormal and absolutely weakly normal rings

A commutative ring `A` is *seminormal* when for every pair `x, y : A` with `x ^ 3 = y ^ 2`
there is a unique `a : A` with `x = a ^ 2` and `y = a ^ 3`.  It is *absolutely weakly normal*
when in addition, for every prime number `p` and every pair `x, y : A` with
`(p : A) ^ p * x = y ^ p`, there is a unique `a : A` with `x = a ^ p` and `y = (p : A) * a`.

The content of this file is Costa's observation, recorded in the footnote to
[Stacks, Tag 0EUL](https://stacks.math.columbia.edu/tag/0EUL): the uniqueness clause in the
definition of seminormality is *implied* by the existence clause.  Indeed a ring satisfying
only the existence clause is reduced, and in a reduced ring an element is determined by its
square together with its cube.  Consequently a seminormal ring is reduced
([Stacks, Tag 0EUQ](https://stacks.math.columbia.edu/tag/0EUQ)), and seminormality may be
checked by producing roots without proving them unique.

That reformulation is what makes the two localization arguments of
`StacksFrontier.AlgebraicGeometry.Seminormalization.LocalProperty` short: in both of them
uniqueness is obtained from reducedness of the ring at hand rather than transported along the
localization maps.

## Main definitions

* `Stacks.RingTheory.Seminormal.IsSeminormalRing`: `A` is seminormal.
* `Stacks.RingTheory.Seminormal.IsAbsolutelyWeaklyNormalRing`: `A` is absolutely weakly normal.

## Main results

* `Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq`: in a reduced ring, two elements with
  the same square and the same cube are equal.
* `Stacks.RingTheory.Seminormal.isReduced_of_exists_sq_cube`: a ring in which every `x, y` with
  `x ^ 3 = y ^ 2` have *some* common square-and-cube root is reduced.
* `Stacks.RingTheory.Seminormal.isSeminormalRing_iff_exists`: seminormality is equivalent to
  the existence clause alone.
* `Stacks.RingTheory.Seminormal.IsSeminormalRing.isReduced`: a seminormal ring is reduced.

## Implementation notes

The predicates are stated exactly as in the source, uniqueness clause included, so that they
are the propositions the Stacks Project writes down; `isSeminormalRing_iff_exists` is the
derived working form.  The natural number `p` enters the second condition through the
canonical cast `Nat.cast`, and the condition is quantified over all primes rather than being
bundled into a structure, matching the source's two-clause definition.

Costa's observation is about the seminormality clause only.  No analogue is claimed for the
prime-power clause of absolute weak normality: the argument for uniqueness uses that an
element of a reduced ring is determined by its square and its cube, which has no counterpart
for the pair `(a ^ p, p * a)`.

Both predicates are universe polymorphic in the ring, with no constraint relating the ring's
universe to anything else, as in the source.

## References

* [Stacks Project, Tag 0EUL](https://stacks.math.columbia.edu/tag/0EUL)
* [Stacks Project, Tag 0EUQ](https://stacks.math.columbia.edu/tag/0EUQ)
-/

@[expose] public section

namespace Stacks.RingTheory.Seminormal

variable {A : Type*} [CommRing A]

/-- In a reduced commutative ring an element is determined by its square together with its
cube: if `a ^ 2 = b ^ 2` and `a ^ 3 = b ^ 3` then `a = b`.  This is the second half of the
footnote to [Stacks, Tag 0EUL](https://stacks.math.columbia.edu/tag/0EUL). -/
theorem eq_of_sq_eq_of_cube_eq [IsReduced A] {a b : A} (h2 : a ^ 2 = b ^ 2)
    (h3 : a ^ 3 = b ^ 3) : a = b := by
  have key : (a - b) ^ 3 = 0 := by
    linear_combination (-3 * b - 3 * a) * h2 + 4 * h3
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨3, key⟩)

/-- A commutative ring in which every `x, y` with `x ^ 3 = y ^ 2` have *some* `a` with
`x = a ^ 2` and `y = a ^ 3` is reduced.  This is the first half of the footnote to
[Stacks, Tag 0EUL](https://stacks.math.columbia.edu/tag/0EUL). -/
theorem isReduced_of_exists_sq_cube
    (h : ∀ x y : A, x ^ 3 = y ^ 2 → ∃ a : A, x = a ^ 2 ∧ y = a ^ 3) : IsReduced A := by
  rw [isReduced_iff_pow_one_lt 2 one_lt_two]
  intro x hx
  obtain ⟨a, ha2, ha3⟩ := h x x (by linear_combination (x - 1) * hx)
  linear_combination hx + (1 + a) * ha3 - (a + a ^ 2 + x) * ha2

/-- Seminormality is equivalent to the existence clause of its definition alone: the
uniqueness clause is automatic. -/
theorem isSeminormalRing_iff_exists :
    IsSeminormalRing A ↔ ∀ x y : A, x ^ 3 = y ^ 2 → ∃ a : A, x = a ^ 2 ∧ y = a ^ 3 := by
  refine ⟨fun hA x y hxy => (hA x y hxy).exists, fun h x y hxy => ?_⟩
  have := isReduced_of_exists_sq_cube h
  obtain ⟨a, ha⟩ := h x y hxy
  exact ⟨a, ha, fun b hb =>
    eq_of_sq_eq_of_cube_eq (by rw [← ha.1, ← hb.1]) (by rw [← ha.2, ← hb.2])⟩

/-- A seminormal ring is reduced.  This is the ring half of
[Stacks, Tag 0EUQ](https://stacks.math.columbia.edu/tag/0EUQ). -/
theorem IsSeminormalRing.isReduced (hA : IsSeminormalRing A) : IsReduced A :=
  isReduced_of_exists_sq_cube (isSeminormalRing_iff_exists.mp hA)

/-- An absolutely weakly normal ring is seminormal. -/
theorem IsAbsolutelyWeaklyNormalRing.isSeminormalRing
    (hA : IsAbsolutelyWeaklyNormalRing A) : IsSeminormalRing A := hA.1

/-- An absolutely weakly normal ring is reduced. -/
theorem IsAbsolutelyWeaklyNormalRing.isReduced
    (hA : IsAbsolutelyWeaklyNormalRing A) : IsReduced A :=
  IsSeminormalRing.isReduced hA.1

end Stacks.RingTheory.Seminormal

end

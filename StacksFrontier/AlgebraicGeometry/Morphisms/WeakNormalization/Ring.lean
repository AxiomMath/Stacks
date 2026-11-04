module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Seminormal and absolutely weakly normal rings

A commutative ring is seminormal when every pair whose cube and square agree comes uniquely
from the square and cube of one element. It is absolutely weakly normal when it is seminormal
and satisfies the analogous unique-root condition associated to every prime number.

## Main definitions

* `IsSeminormalRing` is the predicate that a ring is seminormal.
* `IsAbsolutelyWeaklyNormalRing` is the predicate that a ring is absolutely weakly normal.

## Main results

* `isSeminormalRing_iff` characterizes seminormal rings.
* `isAbsolutelyWeaklyNormalRing_iff` characterizes absolutely weakly normal rings.
* `seminormalRing_isReduced` and `absolutelyWeaklyNormalRing_isReduced` state that both
  classes of rings are reduced.

## Implementation notes

The natural number `p` in the second condition is mapped into the ring by the canonical
natural number cast. Both definitions retain the uniqueness assertion, rather than merely
asserting existence of the required element. Absolute weak normality is a short extension of
seminormality and is therefore an abbreviation. The characterizing lemmas are the rewriting
API; the namespaced lemmas extract the two unique-root conditions without requiring clients
to unfold seminormality.

## References

* [Stacks Project, Tag 0EUL](https://stacks.math.columbia.edu/tag/0EUL)
* [Stacks Project, Tag 0EUQ](https://stacks.math.columbia.edu/tag/0EUQ)
-/

@[expose] public section

/-- A commutative ring is seminormal if every `x, y` with `x ^ 3 = y ^ 2` are uniquely the
square and cube of a common element.

Use `isSeminormalRing_iff` to rewrite this predicate and
`IsSeminormalRing.existsUnique_of_cube_eq_square` to apply its defining condition. -/
@[stacks 0EUL "part (1)"]
def IsSeminormalRing (A : Type*) [CommRing A] : Prop :=
  ∀ x y : A, x ^ 3 = y ^ 2 → ∃! a : A, (x = a ^ 2 ∧ y = a ^ 3)

/-- The defining unique-root characterization of a seminormal ring. -/
@[simp]
theorem isSeminormalRing_iff (A : Type*) [CommRing A] :
    IsSeminormalRing A ↔ ∀ x y : A, x ^ 3 = y ^ 2 → ∃! a : A, (x = a ^ 2 ∧ y = a ^ 3) :=
  Iff.rfl

/-- Extract the unique common square and cube root supplied by seminormality. -/
theorem IsSeminormalRing.existsUnique_of_cube_eq_square {A : Type*} [CommRing A]
    (hA : IsSeminormalRing A) {x y : A} (hxy : x ^ 3 = y ^ 2) :
    ∃! a : A, (x = a ^ 2 ∧ y = a ^ 3) :=
  hA x y hxy

/-- A commutative ring is absolutely weakly normal if it is seminormal and, for every prime
number `p`, every solution of `p ^ p * x = y ^ p` uniquely has the prescribed form
`x = a ^ p`, `y = p * a`.

Use `isAbsolutelyWeaklyNormalRing_iff` to rewrite this predicate,
`IsAbsolutelyWeaklyNormalRing.isSeminormalRing` for its seminormal part, and
`IsAbsolutelyWeaklyNormalRing.existsUnique_of_prime_pow_mul_eq_pow` for its prime-root
condition. -/
@[stacks 0EUL "part (2)"]
abbrev IsAbsolutelyWeaklyNormalRing (A : Type*) [CommRing A] : Prop :=
  IsSeminormalRing A ∧ (∀ (p : ℕ) (_hp : p.Prime) (x y : A),
    (p : A) ^ p * x = y ^ p → ∃! a : A, (x = a ^ p ∧ y = (p : A) * a))

/-- The defining characterization of an absolutely weakly normal ring. -/
@[simp]
theorem isAbsolutelyWeaklyNormalRing_iff (A : Type*) [CommRing A] :
    IsAbsolutelyWeaklyNormalRing A ↔ (IsSeminormalRing A ∧ (∀ (p : ℕ) (_hp : p.Prime) (x y : A),
      (p : A) ^ p * x = y ^ p → ∃! a : A, (x = a ^ p ∧ y = (p : A) * a))) :=
  Iff.rfl

/-- An absolutely weakly normal ring is seminormal. -/
theorem IsAbsolutelyWeaklyNormalRing.isSeminormalRing {A : Type*} [CommRing A]
    (hA : IsAbsolutelyWeaklyNormalRing A) : IsSeminormalRing A :=
  hA.1

/-- Extract the unique root supplied by absolute weak normality at a prime. -/
theorem IsAbsolutelyWeaklyNormalRing.existsUnique_of_prime_pow_mul_eq_pow {A : Type*}
    [CommRing A] (hA : IsAbsolutelyWeaklyNormalRing A) {p : ℕ} (hp : p.Prime) {x y : A}
    (hxy : (p : A) ^ p * x = y ^ p) : ∃! a : A, (x = a ^ p ∧ y = (p : A) * a) :=
  hA.2 p hp x y hxy

/-- **Stacks Project, Tag 0EUQ.** A seminormal commutative ring is reduced. -/
@[stacks 0EUQ "seminormal rings"]
theorem seminormalRing_isReduced {A : Type*} [CommRing A]
    (hA : IsSeminormalRing A) : IsReduced A := by
  rw [isReduced_iff_pow_one_lt 2 (by decide)]
  intro x hx
  exact (hA 0 0 (by simp)).unique ⟨hx.symm, by simp [pow_succ, hx]⟩ (by simp)

/-- **Stacks Project, Tag 0EUQ.** An absolutely weakly normal commutative ring is reduced. -/
@[stacks 0EUQ "absolutely weakly normal rings"]
theorem absolutelyWeaklyNormalRing_isReduced {A : Type*} [CommRing A]
    (hA : IsAbsolutelyWeaklyNormalRing A) : IsReduced A :=
  seminormalRing_isReduced hA.isSeminormalRing

end

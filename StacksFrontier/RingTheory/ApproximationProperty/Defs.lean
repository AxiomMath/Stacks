module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The approximation property of a local ring

Stacks Project, Chapter 16 "Smoothing Ring Maps", Section 16.1 (Tag 07BX): a local ring `A` has
the *approximation property* if a system of polynomial equations `f_1 = … = f_m = 0` with
`f_j ∈ A[x_1, …, x_n]` has a solution in the completion `A^∧` of `A` if and only if it has a
solution in `A`. Since `A → A^∧` is a ring map, a solution in `A` always gives one in `A^∧`, so
only the implication "a solution in `A^∧` gives a solution in `A`" carries content, and that is
what the predicate records.

## Main definitions

* `IsLocalRing.HasApproximationProperty A`: every finite system of polynomial equations over `A`
  which is solvable in the `𝔪`-adic completion of `A` is solvable in `A`.

## Implementation notes

The completion is `AdicCompletion (maximalIdeal A) A`, with its canonical `A`-algebra structure.
The source defines the property for henselian Noetherian local rings; neither of these standing
assumptions is part of the predicate. The results using it impose the Noetherian hypothesis
themselves, and henselianity is a consequence of the property.

## References

* [Stacks Project, Tag 07BX](https://stacks.math.columbia.edu/tag/07BX)
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A local ring `A` has the *approximation property* if every finite system of polynomial
equations over `A` which has a solution in the `𝔪`-adic completion of `A` has a solution in `A`
(Stacks, Section 16.1). -/
def HasApproximationProperty (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) A)
    (x : Fin n → AdicCompletion (maximalIdeal A) A),
    (∀ j, MvPolynomial.aeval x (f j) = 0) →
      ∃ y : Fin n → A, ∀ j, MvPolynomial.aeval y (f j) = 0

end IsLocalRing

end

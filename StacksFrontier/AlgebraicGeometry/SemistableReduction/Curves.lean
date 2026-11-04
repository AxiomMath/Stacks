module

public import Mathlib.NumberTheory.PrimeCounting
public import StacksCore.Tactic.StacksAttribute

/-!
# A uniform degree bound for semistable reduction

For a genus `g`, let `ℓ` be the second prime strictly greater than `768 g`. The
degree bound used in the semistable reduction theorem for curves is
`(2g - 2) (ℓ ^ (2g))!`.

## Main definitions

* `AlgebraicGeometry.SemistableReduction.semistableReductionDegreeBound`.

## Implementation notes

`Nat.primeCounting n` is the number of primes at most `n` and
`Nat.nth Nat.Prime` enumerates the primes from index zero, so the prime of index
`Nat.primeCounting (768 * g) + 1` is the second prime strictly greater than
`768 g`. The formula is defined for every natural number `g`, although the
source uses it only for `g ≥ 2`.

## References

* [Stacks Project, Tag 0CEJ](https://stacks.math.columbia.edu/tag/0CEJ)
-/

@[expose] public section

namespace AlgebraicGeometry.SemistableReduction

/-- The genus-dependent degree bound used in the semistable reduction theorem.
Here `ℓ` is the second prime strictly greater than `768 * g`. -/
@[stacks 0CEJ]
public noncomputable def semistableReductionDegreeBound (g : ℕ) : ℕ :=
  let ℓ := Nat.nth Nat.Prime (Nat.primeCounting (768 * g) + 1)
  (2 * g - 2) * (ℓ ^ (2 * g)).factorial

end AlgebraicGeometry.SemistableReduction

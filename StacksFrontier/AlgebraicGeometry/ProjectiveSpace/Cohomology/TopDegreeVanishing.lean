module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation

/-!
# The vanishing range of the top cohomology of `𝒪(d)` on projective space

On `ℙⁿ_R = Proj R[T₀, …, Tₙ]` with `n = m + 1 ≥ 1` the top-degree row of Serre's computation
presents `Hⁿ(ℙⁿ_R, 𝒪(d))` as the `R`-dual of the degree-`(-n-1-d)` part of `R[T₀, …, Tₙ]`. A
polynomial algebra has no homogeneous part in a negative degree, so that dual is zero as soon
as `-n - 1 - d < 0`, which is the range

`Hⁿ(ℙⁿ_R, 𝒪(d)) = 0` for `-n - 1 < d`.

Together with `Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology`, which covers every
degree outside `{0, n}` and the degree `0` at a negative twist, this completes the list of
degrees and twists in which the cohomology of `𝒪(d)` on `ℙⁿ_R` vanishes.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_top_of_lt`: **`Hⁿ(ℙⁿ_R, 𝒪(d)) = 0`
  for `-n - 1 < d`**, over an arbitrary commutative ring `R` and for `n = m + 1 ≥ 1`.

## Implementation notes

The statement at `n = 1` is
`Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_one_of_neg_one_le`, and the proof
below is that proof with the dimension left free; the two are kept apart only because that
module is about the projective line and states the companion vanishing of `H⁰` as well.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

/-- **`Hⁿ(ℙⁿ_R, 𝒪(d)) = 0` for `-n - 1 < d`**, over an arbitrary commutative ring `R` and for
`n = m + 1 ≥ 1`.

The top-degree row of Serre's computation presents this module as the `R`-dual of the chart of
degree-`(-n-1-d)` forms with no variable inverted. That chart is zero exactly when
`-n - 1 - d < 0`, which is the hypothesis, and the dual of a zero module is zero. -/
theorem isZero_twistCohomology_top_of_lt (R : Type u) [CommRing R] (m : ℕ) {d : ℤ}
    (hd : -((m + 1 : ℕ) : ℤ) - 1 < d) :
    IsZero (twistCohomology R (m + 1) d (m + 1)) := by
  refine ((serreTwistCohomology R m d).degreeTop).isZero_iff.2 ?_
  have hneg : -d - (((m + 1 : ℕ) : ℤ) + 1) < 0 := by push_cast at hd ⊢; omega
  rw [ModuleCat.isZero_iff_subsingleton, twistChart_eq_bot_of_neg (R := R) (m + 1) hneg]
  refine ⟨fun f g => ?_⟩
  ext x
  obtain rfl : x = 0 := Subsingleton.elim _ _
  simp

end Stacks.ProjectiveSpace.Cohomology

end

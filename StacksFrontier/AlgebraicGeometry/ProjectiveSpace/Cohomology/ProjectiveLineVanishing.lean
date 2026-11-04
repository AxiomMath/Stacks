module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation

/-!
# The vanishing range of the cohomology of `𝒪(d)` on the projective line

On `ℙ¹_R = Proj R[T₀, T₁]` the cohomology of the twist `𝒪(d)` is concentrated in the degrees
`0` and `1`, and each of the two surviving degrees vanishes on a half-line of twists:

* `H⁰(ℙ¹_R, 𝒪(d)) = 0` for `d ≤ -1`, and
* `H¹(ℙ¹_R, 𝒪(d)) = 0` for `d ≥ -1`.

Both are read off Serre's computation of the cohomology of `𝒪(d)` on `ℙⁿ_R`
(`Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology`, [Stacks, Tag 01XU]) at `n = 1`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_zero_of_neg`:
  `H⁰(ℙ¹_R, 𝒪(d)) = 0` for `d < 0`.
* `Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_one_of_neg_one_le`:
  `H¹(ℙ¹_R, 𝒪(d)) = 0` for `-1 ≤ d`.
* `Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_of_two_le`:
  `H^q(ℙ¹_R, 𝒪(d)) = 0` for `2 ≤ q`, every `d`.
* `Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_zero_of_neg` and
  `Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le`: the same two
  vanishings for the sheaf cohomology itself, before restriction of scalars along
  `Stacks.ProjectiveSpace.Cohomology.coeffScalar`.

## Implementation notes

`twistCohomology R 1 d q` is `H^q(ℙ¹_R, 𝒪(d))` as an `R`-module, obtained by restricting scalars
along the structure morphism. The `isZero_lineCohomology_*` statements are the same vanishings
for the unrestricted right derived functor of sections
`((Stacks.Cohomology.sectionsFunctor (Proj (polyGrading R 1)) ⊤).rightDerived q).obj 𝒪(d)`.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.ProjectiveCohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R]

/-! ### The two vanishing half-lines, as `R`-modules -/

/-- `H⁰(ℙ¹_R, 𝒪(d)) = 0` for `d < 0`. -/
theorem isZero_twistCohomology_zero_of_neg {d : ℤ} (hd : d < 0) :
    IsZero (twistCohomology R 1 d 0) := by
  refine ((serreTwistCohomology R 0 d).degreeZero).isZero_iff.2 ?_
  rw [ModuleCat.isZero_iff_subsingleton, twistChart_eq_bot_of_neg (R := R) 1 hd]
  infer_instance

/-- `H¹(ℙ¹_R, 𝒪(d)) = 0` for `-1 ≤ d`. -/
theorem isZero_twistCohomology_one_of_neg_one_le {d : ℤ} (hd : -1 ≤ d) :
    IsZero (twistCohomology R 1 d 1) := by
  refine ((serreTwistCohomology R 0 d).degreeTop).isZero_iff.2 ?_
  have hneg : -d - (((0 + 1 : ℕ) : ℤ) + 1) < 0 := by push_cast; lia
  rw [ModuleCat.isZero_iff_subsingleton, twistChart_eq_bot_of_neg (R := R) 1 hneg]
  infer_instance

/-- `H^q(ℙ¹_R, 𝒪(d)) = 0` for `2 ≤ q`: the projective line has cohomological dimension one. -/
theorem isZero_twistCohomology_of_two_le (d : ℤ) {q : ℕ} (hq : 2 ≤ q) :
    IsZero (twistCohomology R 1 d q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by lia⟩
  exact (serreTwistCohomology R 0 d).vanishing p (by lia)

/-! ### The same vanishings for the sheaf cohomology itself -/

/-- `H⁰(ℙ¹_R, 𝒪(d)) = 0` for `d < 0`, as the degree-zero right derived functor of sections
on `Proj R[T₀, T₁]` rather than as an `R`-module. -/
theorem isZero_lineCohomology_zero_of_neg {d : ℤ} (hd : d < 0) :
    IsZero (((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading R 1)) ⊤).rightDerived 0).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R 1) d)) := by
  have h := ModuleCat.subsingleton_of_isZero (isZero_twistCohomology_zero_of_neg R hd)
  exact ModuleCat.isZero_iff_subsingleton.2 h

/-- `H¹(ℙ¹_R, 𝒪(d)) = 0` for `-1 ≤ d`, as the degree-one right derived functor of sections
on `Proj R[T₀, T₁]` rather than as an `R`-module. -/
theorem isZero_lineCohomology_one_of_neg_one_le {d : ℤ} (hd : -1 ≤ d) :
    IsZero (((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading R 1)) ⊤).rightDerived 1).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R 1) d)) := by
  have h := ModuleCat.subsingleton_of_isZero (isZero_twistCohomology_one_of_neg_one_le R hd)
  exact ModuleCat.isZero_iff_subsingleton.2 h

end Stacks.ProjectiveSpace.Cohomology

end

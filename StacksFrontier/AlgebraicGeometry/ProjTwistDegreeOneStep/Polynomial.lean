module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneStep.Twist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistGlobalSectionsPolynomial

/-!
# The twisted global sections of a twisting sheaf on `ℙⁿ_R` are generated in degree one

Let `R` be a commutative ring, `ℙⁿ_R = Proj R[T₀, …, Tₙ]` and `e`, `d` integers with
`e + d ≥ 0`. Every global section of `𝒪(e)(1 + d)` is a finite sum `∑ⱼ aⱼ · tⱼ` with `aⱼ` a
linear form and `tⱼ` a global section of `𝒪(e)(d)`, the scalars acting by the graded
`R[T₀, …, Tₙ]`-module structure of [Stacks, Tag 03GK] on `⨁_m Γ(ℙⁿ_R, 𝒪(e)(m))`.

This is `Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep`
`.exists_sum_homogeneousScalar_twistingSheaf` for the polynomial ring, whose two hypotheses are
`MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top` and the surjectivity half of
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_mvPolynomial`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.surjective_degreeZeroToGlobalSections_twistGrading`: the
  canonical map of [Stacks, Tag 01MP] onto `Γ(ℙⁿ_R, 𝒪(b))` is surjective for every `b ≥ 0`, in
  the `ℤ`-indexed spelling.
* `Stacks.ProjectiveSpace.Cohomology.exists_sum_homogeneousScalar_twistingSheaf`: the generation
  statement above.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep
  (surjective_degreeZeroToGlobalSections_of_degreeSection)
open Stacks.ProjectiveCohomology (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The canonical map of [Stacks, Tag 01MP] onto `Γ(ℙⁿ_R, 𝒪(b))` is surjective for every
`b ≥ 0`**, in the spelling whose degree is an integer: every global section of a nonnegative
twist on `ℙⁿ_R` is `a / 1` for a homogeneous polynomial `a`. -/
theorem surjective_degreeZeroToGlobalSections_twistGrading (b : ℤ) (hb : 0 ≤ b) :
    Function.Surjective (degreeZeroToGlobalSections (polyGrading R n)
      (twistGrading (S := MvPolynomial (Fin (n + 1)) R) (polyGrading R n) b)) :=
  surjective_degreeZeroToGlobalSections_of_degreeSection (polyGrading R n)
    (fun k => (bijective_degreeSection_mvPolynomial R n k).2) b hb

/-- **The twisted global sections of a twisting sheaf on `ℙⁿ_R` are generated in degree one,
degreewise.** For `e + d ≥ 0` every global section of `𝒪(e)(1 + d)` is a finite sum `∑ⱼ aⱼ · tⱼ`
with `aⱼ` a linear form and `tⱼ` a global section of `𝒪(e)(d)`. -/
theorem exists_sum_homogeneousScalar_twistingSheaf (e d : ℤ) (hed : 0 ≤ e + d)
    (s : twistedSectionsComponent (polyGrading R n)
      (twistingSheaf (polyGrading R n) e) ((1 : ℤ) + d)) :
    ∃ (r : ℕ) (a : Fin r → polyGrading R n 1)
      (t : Fin r → twistedSectionsComponent (polyGrading R n)
        (twistingSheaf (polyGrading R n) e) d),
      s = ∑ j, homogeneousScalarTwistedSections (polyGrading R n)
        (twistingSheaf (polyGrading R n) e) 1 d (a j) (t j) :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.exists_sum_homogeneousScalar_twistingSheaf
    (polyGrading R n) (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) R)
    (surjective_degreeZeroToGlobalSections_twistGrading R n) e d hed s

end Stacks.ProjectiveSpace.Cohomology

end

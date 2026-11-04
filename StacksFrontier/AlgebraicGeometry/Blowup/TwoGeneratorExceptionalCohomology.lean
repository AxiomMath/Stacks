module

public import
  StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineGloballyGenerated
public import StacksFrontier.AlgebraicGeometry.TwoGeneratorSquare

/-!
# `H¹` of a globally generated module on the exceptional fibre of the two-generator square

The exceptional fibre `E = Proj ((A/(f₁,f₂))[T₀, T₁]) = 𝐏¹_Z` of the almost blowup square of
[Stacks, Example 0EVH] is the projective line over `centerRing A f₁ f₂`. For every globally
generated quasi-coherent `𝒪_E`-module `ℱ` we have `H¹(E, ℱ) = 0`.

## Main results

* `Stacks.AlmostBlowUp.isZero_cohomology_one_exceptional_of_generatingSections`: `H¹(E, ℱ) = 0`
  for a globally generated quasi-coherent module `ℱ` on `E`.

## References

* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- `H¹(E, ℱ) = 0` for a globally generated quasi-coherent module `ℱ` on the exceptional fibre
`E = Proj (exceptionalGrading A f₁ f₂)` of the two-generator almost blowup square, with no
hypothesis on `A`, `f₁` or `f₂`. -/
public theorem isZero_cohomology_one_exceptional_of_generatingSections
    (F : (AlgebraicGeometry.Proj (exceptionalGrading A f₁ f₂)).Modules) [F.IsQuasicoherent]
    (σ : SheafOfModules.GeneratingSections F) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (AlgebraicGeometry.Proj (exceptionalGrading A f₁ f₂))).rightDerivedPlus 1).obj F) :=
  Stacks.ProjectiveSpace.Cohomology.isZero_cohomology_one_of_generatingSections_line
    (centerRing A f₁ f₂) F σ

end Stacks.AlmostBlowUp

end

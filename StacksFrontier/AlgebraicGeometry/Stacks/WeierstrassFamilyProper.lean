module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamily

/-!
# The plane cubic of a Weierstrass equation is proper over the base

Let `R` be a ring and `E ⊂ P²_R` the plane cubic cut out by a Weierstrass equation over `R`. This
file proves that the projection `E → Spec R` is proper, the first of the conditions of
[Stacks, Tag 072J] that [Stacks, Tag 072S] asserts for the Weierstrass family.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isProper_projectionOf`: the projection
  `E → Spec R` of the plane cubic is proper.

## Implementation notes

`E` is `Proj` of `R[x, y, z]/(F)`, whose degree-zero part is `R`, and the projection is
`AlgebraicGeometry.Proj.toSpecZero` followed by `Spec` of the isomorphism of `R` with that
degree-zero part. `Proj` of a graded ring of finite type over its degree-zero part is proper over
it (`AlgebraicGeometry.Proj.toSpecZero`'s `IsProper` instance), and `R[x, y, z]/(F)` is of finite
type over `R`, hence over its degree-zero part, through which the structure map of `R` factors.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072J](https://stacks.math.columbia.edu/tag/072J)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (C : WeierstrassCurve R)

/-- The structure map of `R` into the homogeneous coordinate ring of the plane cubic factors
through the degree-zero part. -/
theorem algebraMap_comp_toGradingZeroOf :
    (algebraMap (gradingOf C 0) (coordRingOf C)).comp (toGradingZeroOf C) =
      algebraMap R (coordRingOf C) := rfl

/-- The homogeneous coordinate ring of the plane cubic is of finite type over its degree-zero
part. -/
instance : Algebra.FiniteType (gradingOf C 0) (coordRingOf C) := by
  rw [← RingHom.finiteType_algebraMap]
  refine RingHom.FiniteType.of_comp_finiteType (f := toGradingZeroOf C) ?_
  rw [algebraMap_comp_toGradingZeroOf, RingHom.finiteType_algebraMap]
  infer_instance

/-- **The plane cubic of a Weierstrass equation is proper over the base.** -/
@[stacks 072S "f_W is proper"]
instance isProper_projectionOf : IsProper (projectionOf C) := by
  have h₁ : IsProper (Proj.toSpecZero (gradingOf C)) := inferInstance
  have h₂ : IsProper (Spec.map (CommRingCat.ofHom (toGradingZeroOf C))) := inferInstance
  exact MorphismProperty.comp_mem _ _ _ h₁ h₂

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

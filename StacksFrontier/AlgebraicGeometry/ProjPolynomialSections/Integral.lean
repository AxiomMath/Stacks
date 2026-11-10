module

public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.GradedIso
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso

/-!
# Coefficient change on the polynomial model of projective space

`Stacks.AlgebraicGeometry.ProjPolyChart.coordinateProjMap` is the morphism
`Proj R[T₀, …, Tₙ] ⟶ ℙⁿ_ℤ` induced by the canonical coefficient homomorphism out of the integral
model. **This file proves that it is natural in the coefficient ring**: a ring homomorphism
`R ⟶ R'` induces a morphism `Proj R'[T] ⟶ Proj R[T]`, and composing it with the morphism to the
integral model over `R` gives the morphism to the integral model over `R'`.

That naturality is the whole compatibility obligation of
`Stacks.AlgebraicGeometry.RelativeProjIsProjectiveSpace.IntegralCharts`: there is only one ring
homomorphism `ℤ ⟶ R'`, so the two routes from `Proj R'[T]` to the integral model agree.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.coeffMap`: the morphism of polynomial
  projective spectra induced by a change of coefficient ring.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.polyToIntegral`: the morphism from the
  polynomial model to the integral model.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.coeffMap_polyToIntegral`: **the morphism to
  the integral model is natural in the coefficient ring.**

## Implementation notes

`coordinateProjMap R n ψ hdom` is `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` of `ψ`,
retyped so that its codomain is the `def` `AlgebraicGeometry.projectiveSpaceAtUniverse n` rather
than `AlgebraicGeometry.Proj` of the integral polynomial grading. The two are definitionally
equal, so the identification is `rfl` and the composition law of
`Stacks.AlgebraicGeometry.ProjBundleSurjection.mapHomOfTop_comp` transfers by `exact`; it does
**not** transfer by `rw`, because the codomain of the rewritten subterm changes.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)

## Not done here

No project tag is attached.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal MvPolynomial
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjBundleSurjection

namespace Stacks.AlgebraicGeometry.ProjPolynomialSections

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R R' : Type u} [CommRing R] [CommRing R'] (n : ℕ)

/-- **Change of coefficient ring on the polynomial model of projective space.** A ring
homomorphism `R ⟶ R'` induces a morphism `Proj R'[T₀, …, Tₙ] ⟶ Proj R[T₀, …, Tₙ]`, defined
everywhere because the image of the coefficient change contains each variable. -/
public def coeffMap (θ : R →+* R') :
    AlgebraicGeometry.Proj (polyGrading R' n) ⟶ AlgebraicGeometry.Proj (polyGrading R n) :=
  mapHomOfTop (polyGrading R n) (polyGrading R' n) (coeffGradedHom R n θ)
    (mapDomain_coeffGradedHom_eq_top R n θ)

/-- The canonical coefficient homomorphism out of the integers is unchanged by composing with any
ring homomorphism: there is exactly one ring homomorphism `ℤ ⟶ R'`. -/
public theorem comp_integralCoeffHom (θ : R →+* R') :
    θ.comp (integralCoeffHom R) = integralCoeffHom R' := by
  rw [integralCoeffHom, integralCoeffHom, ← RingHom.comp_assoc]
  exact congrArg (fun f : ℤ →+* R' => f.comp ULift.ringEquiv.toRingHom)
    (RingHom.eq_intCast' (θ.comp (Int.castRingHom R)))

/-- Coefficient change is compatible with the canonical coefficient homomorphism out of the
integral model. -/
public theorem coeffGradedHom_comp_integralGradedHom (θ : R →+* R') :
    (coeffGradedHom R n θ).comp (integralGradedHom R n) = integralGradedHom R' n := by
  refine GradedRingHom.ext fun F => ?_
  change MvPolynomial.map θ (MvPolynomial.map (integralCoeffHom R) F) =
    MvPolynomial.map (integralCoeffHom R') F
  rw [MvPolynomial.map_map, comp_integralCoeffHom]

/-- The morphism from the polynomial model of projective `n`-space over `R` to the integral
model, induced by the canonical coefficient homomorphism. -/
public abbrev polyToIntegral (R : Type u) [CommRing R] (n : ℕ) :
    AlgebraicGeometry.Proj (polyGrading R n) ⟶ projectiveSpaceAtUniverse.{u} n :=
  coordinateProjMap R n (integralGradedHom R n) (mapDomain_integralGradedHom_eq_top R n)

/-- **The morphism to the integral model is natural in the coefficient ring.** -/
public theorem coeffMap_polyToIntegral (θ : R →+* R') :
    coeffMap n θ ≫ polyToIntegral R n = polyToIntegral R' n := by
  have hdc : mapDomain (polyGrading (ULift.{u} ℤ) n) (polyGrading R' n)
      ((coeffGradedHom R n θ).comp (integralGradedHom R n)) = ⊤ :=
    mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (irrelevant_le_map_comp (irrelevant_le_map_coeffGradedHom (ULift.{u} ℤ) n
        (integralCoeffHom R)) (irrelevant_le_map_coeffGradedHom R n θ))
  have h := mapHomOfTop_comp (polyGrading (ULift.{u} ℤ) n) (polyGrading R n)
    (polyGrading R' n) (integralGradedHom R n) (coeffGradedHom R n θ)
    (irrelevant_le_map_coeffGradedHom (ULift.{u} ℤ) n (integralCoeffHom R))
    (irrelevant_le_map_coeffGradedHom R n θ)
    (mapDomain_integralGradedHom_eq_top R n) (mapDomain_coeffGradedHom_eq_top R n θ) hdc
  exact h.symm.trans (mapHomOfTop_congr _ _
    (coeffGradedHom_comp_integralGradedHom n θ) hdc (mapDomain_integralGradedHom_eq_top R' n))

end Stacks.AlgebraicGeometry.ProjPolynomialSections

end

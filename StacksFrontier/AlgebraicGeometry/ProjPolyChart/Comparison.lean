module

public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.MapDomain
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjMapData.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Comparing the base-change and polynomial models of projective space

Projective `n`-space over a ring `R` is defined in this repository as the base change of the
integral model `Proj (ULift ℤ)[T₀, …, Tₙ]` along `Spec R ⟶ Spec ℤ`, realized as a pullback over
the terminal scheme. The other model is `Proj R[T₀, …, Tₙ]` itself. This file builds the
canonical morphism between them and reduces their comparison to a single statement: that this
morphism is an isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjPolyChart.coordinateProjMap`: the morphism
  `Proj R[T] ⟶ Proj (ULift ℤ)[T]` induced by a coefficient homomorphism whose Tag 01MY domain
  of definition is all of `Proj R[T]`.
* `Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`: the structure morphism
  `Proj R[T] ⟶ Spec R`, through the degree-zero part of the grading.
* `Stacks.AlgebraicGeometry.ProjPolyChart.projCompare`: the canonical comparison
  `Proj R[T] ⟶ ℙⁿ_R`, the pullback lift of the two morphisms above.
* `Stacks.AlgebraicGeometry.ProjPolyChart.PolynomialComparison`: the coordinate-pinned
  comparison of the two models, as a bundle of the coefficient homomorphism, the isomorphism,
  and the two compatibilities.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_fst` and
  `Stacks.AlgebraicGeometry.ProjPolyChart.projCompare_snd`: the comparison commutes with both
  projections, by construction.
* `Stacks.AlgebraicGeometry.ProjPolyChart.polynomialComparisonOfIsIso`: **the reduction.** As
  soon as `projCompare` is an isomorphism, the whole coordinate-pinned comparison follows; the
  coefficient homomorphism is `integralGradedHom`, its description on polynomials holds by
  `rfl`, and its domain of definition is everything by
  `mapDomain_integralGradedHom_eq_top`.

## Implementation notes

The comparison is built out of the pullback, not out of a gluing, so the two compatibilities are
`Limits.pullback.lift_fst` and `Limits.pullback.lift_snd`; the pullback square commutes because
both composites land in the terminal scheme. Consequently the only content left in the
comparison is invertibility of `projCompare`, which is the statement that `Proj` of a polynomial
ring is the base change of `Proj` of the integral polynomial ring — "`Proj` commutes with base
change" in the one case the construction of projective space needs. The direction of the
isomorphism recorded in `PolynomialComparison` is from the base-change model to the polynomial
model, so the bundle takes the inverse of `projCompare`, which is why `toIntegral` and `toBase`
are the two projection identities read backwards.

`projToSpecCoeff` composes `AlgebraicGeometry.Proj.toSpecZero` with `Spec` of the identification
of `R` with the degree-zero part of the total-degree grading; that identification is spelled as
`GradedRing.projZeroRingHom'` composed with the structure map of `R`, rather than as the inverse
of a ring equivalence, so that the comparison's `toBase` clause names the same ring homomorphism
the tagged statement does.

## Where invertibility is proved

Invertibility of `projCompare` is **not** proved in this file, but it is proved: it is
`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare` of
`StacksFrontier/AlgebraicGeometry/ProjBaseChange/IsIso.lean`, and
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison` there is the resulting term of
`PolynomialComparison`. The route is the one this file's charts were prepared for: the standard
affine charts of both sides are identified by
`Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`, naturally in `R` by
`Stacks.AlgebraicGeometry.ProjPolyChart.chartBaseChange_chartHom`; the chart square is then shown
to be a pullback square, and being an isomorphism is local on the target over the cover of the
integral model by its standard opens.

So nothing in this file is open. `polynomialComparisonOfIsIso` takes invertibility as an
instance hypothesis only so that the packaging lives here and the proof lives with the rest of
the base-change material.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The morphism of polynomial projective spectra induced by a coefficient homomorphism, when
its Tag 01MY domain of definition is all of `Proj R[T]`. -/
public def coordinateProjMap
    (ψ : polyGrading (ULift.{u} ℤ) n →+*ᵍ polyGrading R n)
    (hdom : Stacks.AlgebraicGeometry.ProjShared.mapDomain
      (polyGrading (ULift.{u} ℤ) n) (polyGrading R n) ψ = ⊤) :
    AlgebraicGeometry.Proj (polyGrading R n) ⟶
      AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n :=
  (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hdom.symm).hom ≫
    Stacks.AlgebraicGeometry.ProjTwistChain.mapHom
      (polyGrading (ULift.{u} ℤ) n) (polyGrading R n) ψ

/-- The structure morphism `Proj R[T] ⟶ Spec R`, through the degree-zero part of the
total-degree grading. -/
public def projToSpecCoeff :
    AlgebraicGeometry.Proj (polyGrading R n) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (polyGrading R n) ≫
    Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' (polyGrading R n)).comp
      (algebraMap R (MvPolynomial (Fin (n + 1)) R))))

/-- **The canonical comparison of the two models of projective `n`-space over `R`**, from the
polynomial model to the base-change model: the pullback lift of the structure morphism and of
the morphism to the integral model induced by the canonical coefficient homomorphism. -/
public def projCompare :
    AlgebraicGeometry.Proj (polyGrading R n) ⟶
      AlgebraicGeometry.projectiveSpaceOverRing.{u} n (CommRingCat.of R) :=
  pullback.lift (projToSpecCoeff R n)
    (coordinateProjMap R n (integralGradedHom R n) (mapDomain_integralGradedHom_eq_top R n))
    (terminal.hom_ext _ _)

/-- The comparison morphism followed by the first pullback projection is the structure morphism
`projToSpecCoeff R n`. -/
@[simp] public theorem projCompare_fst :
    projCompare R n ≫ pullback.fst _ _ = projToSpecCoeff R n :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the second pullback projection is the morphism to the
integral model induced by `integralGradedHom R n`. -/
@[simp] public theorem projCompare_snd :
    projCompare R n ≫ pullback.snd _ _ =
      coordinateProjMap R n (integralGradedHom R n)
        (mapDomain_integralGradedHom_eq_top R n) :=
  pullback.lift_snd _ _ _

/-- The coordinate-pinned comparison between the base-change and polynomial models of
projective `n`-space over `R`: a coefficient homomorphism that preserves each named homogeneous
coordinate, everywhere defined, together with an isomorphism of the two models commuting with
the projection to the integral model and with the structure morphism to `Spec R`. -/
public structure PolynomialComparison where
  /-- The coefficient homomorphism, as a homomorphism of graded rings. -/
  coordinateMap : polyGrading (ULift.{u} ℤ) n →+*ᵍ polyGrading R n
  /-- On polynomials the coefficient homomorphism is the canonical coefficient map: it
  preserves each named homogeneous coordinate. -/
  coordinateMap_apply : ∀ F : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ),
    coordinateMap F = MvPolynomial.map ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom) F
  /-- The coefficient homomorphism is everywhere defined, so it induces a morphism out of all of
  `Proj R[T]`. -/
  domain_eq_top : Stacks.AlgebraicGeometry.ProjShared.mapDomain
    (polyGrading (ULift.{u} ℤ) n) (polyGrading R n) coordinateMap = ⊤
  /-- The comparison isomorphism, from the base-change model to the polynomial model. -/
  iso : AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of R) ≅
    AlgebraicGeometry.Proj (polyGrading R n)
  /-- The isomorphism commutes with the projection to the integral model. -/
  toIntegral : iso.hom ≫ coordinateProjMap R n coordinateMap domain_eq_top =
    AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n (Spec (CommRingCat.of R))
  /-- The isomorphism commutes with the structure morphism to `Spec R`. -/
  toBase : iso.hom ≫ Proj.toSpecZero (polyGrading R n) ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' (polyGrading R n)).comp
        (algebraMap R (MvPolynomial (Fin (n + 1)) R)))) = pullback.fst _ _

/-- **The comparison of the two models of projective space, reduced to one statement.** Once the
canonical comparison `projCompare` is known to be an isomorphism, the whole coordinate-pinned
comparison follows: the coefficient homomorphism is the canonical one, its description on
polynomials holds by definition, it is everywhere defined, and the two compatibilities are the
defining identities of the pullback lift read through the inverse. -/
public def polynomialComparisonOfIsIso [IsIso (projCompare R n)] :
    PolynomialComparison R n where
  coordinateMap := integralGradedHom R n
  coordinateMap_apply _ := rfl
  domain_eq_top := mapDomain_integralGradedHom_eq_top R n
  iso := (asIso (projCompare R n)).symm
  toIntegral := by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, projCompare_snd]
  toBase := by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
    exact (projCompare_fst R n).symm

end Stacks.AlgebraicGeometry.ProjPolyChart

end

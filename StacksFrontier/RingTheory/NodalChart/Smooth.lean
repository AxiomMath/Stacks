module

public import StacksFrontier.RingTheory.NodalChart.Blowup
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The nodal chart ring with unit parameter is smooth

The standard nodal model `R[x, y]/(xy - h)` degenerates when `h` is a unit: the relation then
makes `x` invertible, so the ring is the localization `R[x]_x` of the polynomial ring in one
variable away from `x`. For `h = 1` this is proved here as an `R`-algebra isomorphism, and it
gives smoothness of `R[x, y]/(xy - 1)` over `R`, hence smoothness of
`Spec R[x, y]/(xy - 1) → Spec R`: the composite of the smooth map `R → R[x]` with the étale
localization `R[x] → R[x]_x`.

This is the case `n = 0` of the standard nodal model `R[x, y]/(xy - πⁿ)` over a discrete
valuation ring with uniformizer `π`, where the exponent is zero and the equation reads `xy = 1`.

## Main definitions

* `Stacks.nodalChartRingOneEquiv` — the isomorphism `R[x, y]/(xy - 1) ≃ₐ[R] R[x]_x`.

## Main results

* `Stacks.smooth_nodalChartRing_one` — `R[x, y]/(xy - 1)` is a smooth `R`-algebra.
* `Stacks.smooth_specMap_nodalChartRing_one` — the structure morphism
  `Spec R[x, y]/(xy - 1) → Spec R` is smooth.
* `Stacks.smooth_specMap_nodalChartRing_pow_zero` — the same statement for the exponent `0`
  member of the family `R[x, y]/(xy - πⁿ)`.

## Implementation notes

The isomorphism is `Stacks.nodalChartAwayMap` at `h = 1`, whose inverse is the lift to the
localization of the map `R[x] → R[x, y]/(xy - 1)` sending `x` to the first coordinate; that
coordinate is a unit precisely because the defining relation reads `xy = 1`. Both composites are
checked on generators, using `Polynomial.algHom_ext` on one side and
`Stacks.nodalChartRing_ringHom_ext` on the other.

Smoothness is then transported along the isomorphism with `Algebra.FormallySmooth.of_equiv` and
`Algebra.FinitePresentation.equiv`, and the scheme-level statement is
`AlgebraicGeometry.HasRingHomProperty.Spec_iff` for the morphism property
`AlgebraicGeometry.Smooth`.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks

variable (R : Type u) [CommRing R]

/-- The defining relation makes the first coordinate of `R[x, y]/(xy - 1)` a unit. -/
public theorem isUnit_nodalGen_one_zero : IsUnit (nodalGen R 1 0) := by
  have h : nodalGen R 1 0 * nodalGen R 1 1 = 1 := by
    rw [nodalGen_zero_mul_nodalGen_one]
    exact map_one _
  exact ⟨Units.mkOfMulEqOne _ _ h, rfl⟩

/-- The `R`-algebra map `R[x] → R[x, y]/(xy - 1)` sending `x` to the first coordinate. -/
public def nodalOneLift : Polynomial R →ₐ[R] nodalChartRing R 1 :=
  Polynomial.aeval (nodalGen R 1 0)

public theorem nodalOneLift_X : nodalOneLift R Polynomial.X = nodalGen R 1 0 := by
  simp [nodalOneLift]

public theorem isUnit_nodalOneLift_X :
    IsUnit ((nodalOneLift R).toRingHom Polynomial.X) := by
  simpa [nodalOneLift] using isUnit_nodalGen_one_zero R

/-- The inverse of `Stacks.nodalChartAwayMap` at `h = 1`: the lift of `Stacks.nodalOneLift` to the
localization of `R[x]` away from `x`. -/
public def nodalOneInv :
    Localization.Away (Polynomial.X : Polynomial R) →+* nodalChartRing R 1 :=
  IsLocalization.Away.lift Polynomial.X (isUnit_nodalOneLift_X R)

public theorem nodalChartAwayMap_comp_nodalOneLift :
    (nodalChartAwayMap R 1).comp (nodalOneLift R) =
      IsScalarTower.toAlgHom R (Polynomial R)
        (Localization.Away (Polynomial.X : Polynomial R)) :=
  Polynomial.algHom_ext <| by
    simp only [AlgHom.coe_comp, Function.comp_apply, nodalOneLift_X,
      nodalChartAwayMap_nodalGen_zero, IsScalarTower.coe_toAlgHom']

public theorem nodalChartAwayMap_nodalOneInv (w : Localization.Away (Polynomial.X : Polynomial R)) :
    nodalChartAwayMap R 1 (nodalOneInv R w) = w := by
  have hcomp : (nodalChartAwayMap R 1).toRingHom.comp (nodalOneInv R) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
      (RingHom.ext fun p ↦ ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, nodalOneInv,
      IsLocalization.Away.lift_eq]
    exact AlgHom.congr_fun (nodalChartAwayMap_comp_nodalOneLift R) p
  exact RingHom.congr_fun hcomp w

public theorem nodalOneInv_nodalChartAwayMap (z : nodalChartRing R 1) :
    nodalOneInv R (nodalChartAwayMap R 1 z) = z := by
  have hcomp : (nodalOneInv R).comp (nodalChartAwayMap R 1).toRingHom = RingHom.id _ := by
    refine nodalChartRing_ringHom_ext (fun r ↦ ?_) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, nodalOneInv,
        IsScalarTower.algebraMap_apply R (Polynomial R)
          (Localization.Away (Polynomial.X : Polynomial R)),
        IsLocalization.Away.lift_eq]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, nodalChartAwayMap_nodalGen_zero, nodalOneInv,
        IsLocalization.Away.lift_eq]
      simp [nodalOneLift]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, nodalChartAwayMap_nodalGen_one, nodalOneInv]
      refine awayLift_mk'_eq (isUnit_nodalOneLift_X R) _ _ ?_
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, nodalOneLift_X, map_one]
      simpa [mul_comm] using nodalGen_zero_mul_nodalGen_one (1 : R)
  exact RingHom.congr_fun hcomp z

/-- **The nodal chart ring with parameter one is a localization of `R[x]`.** The relation
`xy = 1` makes `x` invertible, and `R[x, y]/(xy - 1)` is the localization of `R[x]` away from
`x`. -/
public def nodalChartRingOneEquiv :
    nodalChartRing R 1 ≃ₐ[R] Localization.Away (Polynomial.X : Polynomial R) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (nodalChartAwayMap R 1).toRingHom
    ⟨Function.LeftInverse.injective (nodalOneInv_nodalChartAwayMap R),
      fun w ↦ ⟨nodalOneInv R w, nodalChartAwayMap_nodalOneInv R w⟩⟩)
    (fun r ↦ by simp)

/-- The localization of `R[x]` away from `x` is a smooth `R`-algebra: `R → R[x]` is smooth and
`R[x] → R[x]_x` is étale. -/
public theorem smooth_away_polynomialX :
    Algebra.Smooth R (Localization.Away (Polynomial.X : Polynomial R)) := by
  have h1 : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
  have h2 : Algebra.Smooth (Polynomial R)
      (Localization.Away (Polynomial.X : Polynomial R)) :=
    ⟨Algebra.FormallySmooth.of_isLocalization (Submonoid.powers Polynomial.X),
      IsLocalization.Away.finitePresentation Polynomial.X⟩
  exact Algebra.Smooth.comp R (Polynomial R) _

/-- **`R[x, y]/(xy - 1)` is a smooth `R`-algebra.** -/
public theorem smooth_nodalChartRing_one : Algebra.Smooth R (nodalChartRing R 1) := by
  have h := smooth_away_polynomialX R
  have h1 : Algebra.FormallySmooth R (Localization.Away (Polynomial.X : Polynomial R)) := h.1
  have h2 : Algebra.FinitePresentation R (Localization.Away (Polynomial.X : Polynomial R)) := h.2
  exact ⟨Algebra.FormallySmooth.of_equiv (nodalChartRingOneEquiv R).symm,
    Algebra.FinitePresentation.equiv (nodalChartRingOneEquiv R).symm⟩

/-- **The structure morphism `Spec R[x, y]/(xy - 1) → Spec R` is smooth.** -/
public theorem smooth_specMap_nodalChartRing_one :
    AlgebraicGeometry.Smooth (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap R (nodalChartRing R 1)))) :=
  AlgebraicGeometry.HasRingHomProperty.Spec_iff.2
    ((RingHom.smooth_algebraMap).2 (smooth_nodalChartRing_one R))

/-- The exponent zero member of the family `R[x, y]/(xy - πⁿ)` is smooth over `R`: this is the
case `n = 0` of the standard nodal model. -/
public theorem smooth_specMap_nodalChartRing_pow_zero (π : R) :
    AlgebraicGeometry.Smooth (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap R (nodalChartRing R (π ^ 0))))) := by
  rw [pow_zero]
  exact smooth_specMap_nodalChartRing_one R

end Stacks

end

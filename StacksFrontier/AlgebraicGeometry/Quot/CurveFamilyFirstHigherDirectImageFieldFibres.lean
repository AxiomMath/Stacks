module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatFirstHigherDirectImageLocallyFree

/-!
# `R¹f_*𝒪_X` of a family of curves with `k = H⁰(X_k, 𝒪)` on the fibres over fields

Let `f : X → S` be a family of curves such that `k = H⁰(X_k, 𝒪_{X_k})` for every morphism
`Spec k → S` from the spectrum of a field. Then `R¹f_*𝒪_X` is a finite locally free
`𝒪_S`-module whose formation commutes with arbitrary base change. This is parts (2) and (3) of
Stacks 0E1J under the hypothesis on all fibres over fields: the fibres `X_k` are curves, so
`Hᵠ(X_k, 𝒪_{X_k}) = 0` for `q ≥ 2`
(`CurveFamily.isZero_rightDerived_globalSectionsFunctor_fiberProduct_fieldValuedPoint`),
and the statements for proper flat families with these two properties are
`AlgebraicGeometry.Space.isFiniteLocallyFree_rightDerived_one_structureSheafModule` and
`AlgebraicGeometry.Space.nonempty_modulePullback_rightDerived_one_iso`.

## Main results

In namespace `AlgebraicGeometry.CurveFamily`:

* `hasFiniteLocallyFreeFirstHigherDirectImage_of_hasBijectiveGlobalFunctionsOnFieldFibres`
* `firstHigherDirectImageCommutesWithBaseChange_of_hasBijectiveGlobalFunctionsOnFieldFibres`

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **The fibres of a family of curves over fields have no cohomology above degree `1`.** -/
theorem hasVanishingFieldFibreCohomologyAboveOne (X : CurveFamily B hZ) :
    Space.HasVanishingFieldFibreCohomologyAboveOne B integerBase hZ X.toBase :=
  fun p _ hq => isZero_rightDerived_globalSectionsFunctor_fiberProduct_fieldValuedPoint X p _
    (SheafOfModules.isQuasicoherentOnSite_unit _) hq

/-- `k = H⁰(X_k, 𝒪)` on the fibres over fields, formed in the site over `Spec k`. -/
theorem hasBijectiveFieldFibreGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
    {X : CurveFamily B hZ} (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) :
    Space.HasBijectiveFieldFibreGlobalFunctions B integerBase hZ X.toBase := fun p =>
  Space.bijective_algebraMap_fibreOverFieldValuedPoint_of_bijective B integerBase hZ
    X.toBase.hom p X.total.2 (schemeSpace X.base).2 (hX p)

/-- **Part (2) of Stacks 0E1J, under `k = H⁰(X_k, 𝒪)` on all fibres over fields.**
`R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module. -/
theorem hasFiniteLocallyFreeFirstHigherDirectImage_of_hasBijectiveGlobalFunctionsOnFieldFibres
    {X : CurveFamily B hZ} (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) :
    X.HasFiniteLocallyFreeFirstHigherDirectImage :=
  Space.isFiniteLocallyFree_rightDerived_one_structureSheafModule B integerBase hZ X.toBase
    X.proper X.flat X.finitePresentation
    (hasBijectiveFieldFibreGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres hX)
    X.hasVanishingFieldFibreCohomologyAboveOne

/-- **Part (3) of Stacks 0E1J, under `k = H⁰(X_k, 𝒪)` on all fibres over fields.** The formation
of `R¹f_*𝒪_X` commutes with arbitrary base change. -/
theorem firstHigherDirectImageCommutesWithBaseChange_of_hasBijectiveGlobalFunctionsOnFieldFibres
    {X : CurveFamily B hZ} (hX : HasBijectiveGlobalFunctionsOnFieldFibres B hZ X) :
    X.FirstHigherDirectImageCommutesWithBaseChange := fun F a =>
  Space.nonempty_modulePullback_rightDerived_one_iso B integerBase hZ X.toBase X.proper X.flat
    X.finitePresentation
    (hasBijectiveFieldFibreGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres hX)
    X.hasVanishingFieldFibreCohomologyAboveOne (schemeSpaceMap a.baseMap) F.toBase a.totalMap
    a.cartesian

end CurveFamily

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence

/-!
# Quasi-coherence of the two module functors of a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  This file proves that both the direct image `i_*` and the inverse image `i^*` of
Stacks 03LU carry quasi-coherent modules to quasi-coherent modules, with no hypothesis beyond
the closed immersion.  These are the closed-immersion cases of [Stacks, Tag 03M9] and
[Stacks, Tag 03GA], and together they are what makes the functor
`i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` of [Stacks, Tag 04CJ], part (3) exist.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isClosedImmersion`:
  **Stacks 03GA along a closed immersion.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion`:
  **Stacks 03M9 along a closed immersion**, for an arbitrary quasi-coherent module.

## The proofs

*Direct image.*  Quasi-coherence is cartesianity on the affine étale charts
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, Descent,
Proposition 03DX (2)), the chart comparison
`AlgebraicGeometry.Space.modulePushforwardChartIso` identifies `i_*` with the direct image
computed on base-changed charts, and for an affine morphism that one is cartesian on affine
charts by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallBaseChangeModulePushforward`:
the sections of `i_*M` over a chart `A` are the sections of `M` over `A ×_X Z`, and the base
change of chart rings along the closed immersion is a pushout.  A closed immersion is affine by
Stacks 07U2.

*Inverse image.*  Quasi-coherence is local on the source
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_coversTop_etaleModulePullback`), and the base
changes `A ×_X Z` of the affine étale charts `A` of `X` cover `Z`
(`AlgebraicGeometry.Space.coversTop_smallBaseChange_affineCharts`).  Over such a chart the
composite `A ×_X Z ⟶ Z ⟶ X` factors through the affine chart `A`, where Stacks 03GA is already
proved — `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_affineChartFactorization`
— and the composition comparison of Stacks 03LU together with Equation 03LW identifies the
restriction of `i^*F` to that chart with the pullback along the composite.  This is precisely the
covering that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackQuasicoherence.lean` record as the
missing input for a general morphism; for a representable affine one it is available.

## References

* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **Stacks 03GA along a closed immersion of algebraic spaces.**  The inverse image `i^*F` of a
quasi-coherent `𝒪_X`-module along a closed immersion `i : Z ⟶ X` is quasi-coherent.

Quasi-coherence is local on `Z`, the base changes of the affine étale charts of `X` cover `Z`,
and over such a chart the composite to `X` factors through an affine chart, which is the case of
Stacks 03GA already available. -/
@[stacks 03GA "the inverse image along a closed immersion of algebraic spaces"]
theorem isQuasicoherentOnSite_modulePullback_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    ((modulePullback B S hS i).obj F).IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_coversTop_etaleModulePullback B S hS Z
    (fun A : {A : SmallEtale B S hS X.1 // IsAffine (chartScheme A)} =>
      (smallBaseChange B S hS i hi.rep).obj A.1)
    (coversTop_smallBaseChange_affineCharts B S hS i hi.rep) _ fun A => ?_
  set W := (smallBaseChange B S hS i hi.rep).obj A.1 with hW
  set ψ := chartToSpace B S hS Z W with hψ
  have hψe : IsEtale B S hS ψ.hom := isEtale_chartToSpace B S hS Z W
  have hfac : ψ ≫ i =
      (smallBaseChange_projection B S hS i hi.rep).app A.1 ≫ chartToSpace B S hS X A.1 :=
    (smallBaseChange_isPullback B S hS i hi.rep A.1).w.symm
  have hqc : ((modulePullback B S hS (ψ ≫ i)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_affineChartFactorization B S hS (ψ ≫ i) A.1 A.2
      ((smallBaseChange_projection B S hS i hi.rep).app A.1) hfac F hF
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso ?_ hqc
  exact ((modulePullbackCompIso B S hS ψ i).app F).symm ≪≫
    (modulePullbackIsoEtaleModulePullback B S hS ψ hψe).app
      ((modulePullback B S hS i).obj F)

/-- **Stacks 03M9 along a closed immersion of algebraic spaces.**  The direct image `i_*G` of a
quasi-coherent `𝒪_Z`-module along a closed immersion `i : Z ⟶ X` is quasi-coherent.

A closed immersion is representable and affine, so its direct image is computed on base-changed
charts by `AlgebraicGeometry.Space.modulePushforwardChartIso` and that one is cartesian on affine
charts. -/
@[stacks 03M9 "the direct image along a closed immersion of algebraic spaces"]
theorem isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, u} B S hS Z.1 Z.2)
    (hG : G.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS i).obj G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (IsCartesianOnAffineCharts.of_iso ((modulePushforwardChartIso B S hS i hi.rep).app G).symm
      (isCartesianOnAffineCharts_smallBaseChangeModulePushforward B S hS i hi.rep G
        (isAffineHom_of_isClosedImmersion B S hS i.hom hi)
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Z.1 Z.2 G hG)))

end AlgebraicGeometry.Space

end

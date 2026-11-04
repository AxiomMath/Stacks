module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeAdjunct

/-!
# The adjunct of the represented base-change isomorphism

All names are in the namespace `AlgebraicGeometry.Space`.

`restrictToChartSchemeBaseChangeIso` is the base change of the Zariski restriction of a
quasi-coherent module to the scheme of an identity chart: for `r : U' ⟶ U` in the big fppf
category over `S`, an isomorphism between the restriction to `U'` of the inverse image of Stacks
03LU and the Zariski pullback along `r` of the restriction to `U`. This file computes the adjunct
of its inverse along the Zariski pullback–pushforward adjunction, and from it the adjunct of the
base-change isomorphism `restrictToChartBaseChangeIso` of the chart restriction of Stacks 07SI.

## Main results

* `restrictToChartSchemeBaseChangeIso_inv_eq`: the inverse is the Zariski pullback of the reading
  of the restriction as a Zariski restriction, followed by the inverse of
  `restrictToChartSchemeBaseChangeIsoHead`.
* `homEquiv_restrictToChartSchemeBaseChangeIso_inv`: **the adjunct of the inverse of the
  represented base-change isomorphism** is that reading, followed by the adjunct of the inverse of
  the head.
* `homEquiv_restrictToChartSchemeBaseChangeIso_inv_unit`: the same with the remaining adjunct
  written out as the unit of the Zariski adjunction followed by the direct image of the head's
  inverse.
* `homEquiv_restrictToChartBaseChangeIso_hom_peeled`: **the adjunct of the base-change
  isomorphism of the chart restriction**: the readings of the chart restriction, then the adjunct
  of the inverse of the head, then the direct image of `restrictToChartBaseChangeEtaleTail`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse, with its pullback-image factor in front -/

/-- **The inverse of the represented base-change isomorphism, regrouped**: the Zariski pullback
of `AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`, followed by the inverse of
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIsoHead`. -/
theorem restrictToChartSchemeBaseChangeIso_inv_eq {U' U : BigFppfOver B S hS} (r : U' ⟶ U)
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    (restrictToChartSchemeBaseChangeIso r N hN).inv =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
          (restrictToChartSchemeIdEtaleChartIso B S hS U N).hom ≫
        (restrictToChartSchemeBaseChangeIsoHead r N hN).inv :=
  rfl

/-! ### The adjunct -/

/-- **The adjunct of the inverse of the represented base-change isomorphism.**  Along the Zariski
pullback–pushforward adjunction of the morphism of schemes underlying `r`, the adjunct of the
inverse of `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso` is the reading of the
restriction to the scheme of the identity chart as a Zariski restriction, followed by the adjunct
of the inverse of `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIsoHead`. -/
theorem homEquiv_restrictToChartSchemeBaseChangeIso_inv {U' U : BigFppfOver B S hS} (r : U' ⟶ U)
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullbackPushforwardAdjunction
          ((BigFppfOver.toScheme B S hS).map r)).homEquiv _ _
        (restrictToChartSchemeBaseChangeIso r N hN).inv =
      (restrictToChartSchemeIdEtaleChartIso B S hS U N).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
              ((BigFppfOver.toScheme B S hS).map r)).homEquiv _ _
          (restrictToChartSchemeBaseChangeIsoHead r N hN).inv := by
  rw [restrictToChartSchemeBaseChangeIso_inv_eq B S hS r N hN]
  exact Adjunction.homEquiv_naturality_left _ _ _

/-- **The adjunct of the inverse of the represented base-change isomorphism, with no `homEquiv`
left.**  The remaining adjunct is written as the unit of the Zariski adjunction followed by the
direct image of the inverse of `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIsoHead`.
-/
theorem homEquiv_restrictToChartSchemeBaseChangeIso_inv_unit {U' U : BigFppfOver B S hS}
    (r : U' ⟶ U)
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullbackPushforwardAdjunction
          ((BigFppfOver.toScheme B S hS).map r)).homEquiv _ _
        (restrictToChartSchemeBaseChangeIso r N hN).inv =
      (restrictToChartSchemeIdEtaleChartIso B S hS U N).hom ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction
                ((BigFppfOver.toScheme B S hS).map r)).unit.app
            ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)) ≫
          (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map r)).map
            (restrictToChartSchemeBaseChangeIsoHead r N hN).inv) := by
  rw [homEquiv_restrictToChartSchemeBaseChangeIso_inv B S hS r N hN]
  exact congrArg _ (Adjunction.homEquiv_unit _ _ _ _)

/-! ### The adjunct of the chart base-change isomorphism, with the represented half peeled -/

section Chart

variable {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    (V : SmallEtale B S hS Z.1) (W : SmallEtale B S hS X.1)
    (g : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Z.1).obj V)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite)

/-- **The adjunct of `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, with its represented
half peeled.**  Along the Zariski pullback–pushforward adjunction of the morphism of chart
schemes, the adjunct of the base change of the chart restriction is the two readings of the chart
restriction, then the reading of the restriction to the scheme of the identity chart as a Zariski
restriction, then the adjunct of the inverse of
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIsoHead`, then the direct image of
`AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`. -/
theorem homEquiv_restrictToChartBaseChangeIso_hom_peeled :
    (Scheme.Modules.pullbackPushforwardAdjunction
          ((BigFppfOver.toScheme B S hS).map g)).homEquiv _ _
        (restrictToChartBaseChangeIso B S hS a G hG V W g hg).hom =
      (restrictToChartIsoRestrictToChartScheme B S hS Z.2 G V ≪≫
          restrictToChartSchemeIsoIdEtaleChart B S hS Z G hG V).hom ≫
        (((restrictToChartSchemeIdEtaleChartIso B S hS
                ((SmallEtale.toOver B S hS Z.1).obj V)
                (chartSmallEtaleRestriction B S hS Z G V)).hom ≫
            (Scheme.Modules.pullbackPushforwardAdjunction
                  ((BigFppfOver.toScheme B S hS).map g)).homEquiv _ _
              (restrictToChartSchemeBaseChangeIsoHead g
                (chartSmallEtaleRestriction B S hS Z G V)
                (isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS Z G hG V)).inv) ≫
          (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).map
            (restrictToChartBaseChangeEtaleTail B S hS a V W g hg G hG).hom) := by
  rw [homEquiv_restrictToChartBaseChangeIso_hom B S hS a V W g hg G hG,
    homEquiv_restrictToChartSchemeBaseChangeIso_inv B S hS g
      (chartSmallEtaleRestriction B S hS Z G V)
      (isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS Z G hG V)]
  rfl

end Chart

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionIdChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Quasi-coherence and base change of the Zariski chart restriction

The chartwise properties of a module on an algebraic space are read on
`AlgebraicGeometry.Space.restrictToChart`, its restriction to the Zariski site of the scheme of
an étale chart.  This file proves that the restriction of a quasi-coherent module is
quasi-coherent (`AlgebraicGeometry.Space.IsQuasicoherentOnCharts`), and that the restriction
commutes with base change along a morphism of chart schemes over a morphism of algebraic spaces
(`AlgebraicGeometry.Space.ChartRestrictionBaseChange`).

By `AlgebraicGeometry.Space.restrictToChart_eq_restrictToChartScheme` and
`AlgebraicGeometry.Space.restrictToChartScheme_eq_atIdEtaleChart`, the Zariski restriction to a
chart `V` of `X` is the Zariski restriction, at the identity chart of the chart space, of the
pullback of the module along the structure morphism of `V`.  With it both facts reduce to their
counterparts at an identity chart of a representable algebraic space.

## Main results

* `AlgebraicGeometry.Space.restrictToChartSchemeIsoAtIdEtaleChart`: the Zariski restriction to a
  chart is the Zariski restriction, at the identity chart of the chart space, of the pullback of
  modules of Stacks 03LU along the chart's structure morphism.
* `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart_viaIdEtaleChart`: **the Zariski
  restriction of a quasi-coherent module to the scheme of an étale chart is quasi-coherent**.
* `AlgebraicGeometry.Space.chartRestrictionBaseChangeIso`: **the Zariski chart restriction
  of a quasi-coherent module commutes with base change**;
  `AlgebraicGeometry.Space.nonempty_chartRestrictionBaseChange` is its existence statement.

## Implementation notes

Quasi-coherence at an identity chart of a representable algebraic space is
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`, which presents the restriction as
the right adjoint of the associated-module functor of Stacks 03DU applied to the module read on
the small étale site of the scheme, together with
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`.  Quasi-coherence of the module
being restricted comes from Stacks 03GA,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.

Base change at an identity chart is
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`.  What
carries it to a square of two arbitrary charts over a morphism of algebraic spaces is
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChange`, the same compatibility in the
inverse-image reading, which holds with no quasi-coherence and for a square which is not
assumed cartesian.  Quasi-coherence enters only through the identity-chart statement.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart restriction as an identity-chart restriction -/

/-- **The Zariski restriction of an `𝒪_X`-module to the scheme of an étale chart `V` is its
Zariski restriction, at the identity chart of the chart space, after pullback along the
structure morphism of `V`.**

`AlgebraicGeometry.Space.restrictToChartScheme_eq_atIdEtaleChart` is this with the pullback of
modules replaced by étale restriction of sections, which it is along an étale morphism by
Stacks 03LW. -/
def restrictToChartSchemeIsoAtIdEtaleChart (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2) :
    restrictToChartScheme B S hS X.1 X.2 F V ≅
      restrictToChartScheme B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2
        ((modulePullback B S hS (chartToSpace B S hS X V)).obj F)
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)) :=
  eqToIso (restrictToChartScheme_eq_atIdEtaleChart B S hS X V F) ≪≫
    (restrictToChartSchemeFunctor B S hS (chartSpace B S hS X V).1
        (chartSpace B S hS X V).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V))).mapIso
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).app F).symm

/-! ### Quasi-coherence -/

/-- **The Zariski restriction of a quasi-coherent module on a representable algebraic space to
the scheme of its identity chart is quasi-coherent.** -/
theorem isQuasicoherent_restrictToChartScheme_idEtaleChart (A : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj A)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A))
    (hN : N.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent
      (restrictToChartScheme B S hS (yoneda.obj A)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A) N (idEtaleChart B S hS A)) := by
  set M := (representedSmallEtaleModuleEquivalence B S hS A).inverse.obj N with hMdef
  have eN : (representedSmallEtaleModuleEquivalence B S hS A).functor.obj M ≅ N :=
    (representedSmallEtaleModuleEquivalence B S hS A).counitIso.app N
  have hM : M.IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS A M).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso eN.symm hN)
  exact ObjectProperty.prop_of_iso
    (SheafOfModules.isQuasicoherent (chartScheme (idEtaleChart B S hS A)).ringCatSheaf)
    (restrictToChartSchemeIdEtaleChartIso B S hS A N).symm
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj A) A.left.property M hM)

/-- **The Zariski restriction of a quasi-coherent `𝒪_X`-module to the scheme of an étale chart
is quasi-coherent.** -/
theorem isQuasicoherent_restrictToChart_viaIdEtaleChart (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) :
    (restrictToChart B S hS X.2 F V).IsQuasicoherent := by
  rw [restrictToChart_eq_restrictToChartScheme]
  exact ObjectProperty.prop_of_iso
    (SheafOfModules.isQuasicoherent (chartScheme V).ringCatSheaf)
    (restrictToChartSchemeIsoAtIdEtaleChart B S hS X V F).symm
    (isQuasicoherent_restrictToChartScheme_idEtaleChart B S hS
      ((SmallEtale.toOver B S hS X.1).obj V) _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (chartToSpace B S hS X V) F hF))

/-! ### Base change -/

/-- **The Zariski chart restriction of a quasi-coherent module commutes with base change.**  For
a morphism `a : X ⟶ Z` of algebraic spaces, an étale chart `V` of `Z` and an étale chart `W` of
`X` joined by a morphism `g` of the underlying objects of the site over `a`, the pullback along
`g` of the restriction of a quasi-coherent `𝒪_Z`-module to `V` is the restriction to `W` of its
inverse image along `a`.

It is built from `AlgebraicGeometry.Space.chartModuleRestrictionBaseChange`, the same
compatibility in the inverse-image reading, and from base change at an identity chart,
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, which is where quasi-coherence is
used. -/
def chartRestrictionBaseChangeIso {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS Z.1) (W : SmallEtale B S hS X.1)
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
        (restrictToChart B S hS Z.2 G V) ≅
      restrictToChart B S hS X.2 ((modulePullback B S hS a).obj G) W :=
  (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapIso
      (eqToIso (restrictToChart_eq_restrictToChartScheme B S hS Z.2 G V) ≪≫
        restrictToChartSchemeIsoAtIdEtaleChart B S hS Z V G) ≪≫
    (restrictToChartSchemeBaseChangeIso g ((chartModuleRestriction B S hS Z V).obj G)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (chartToSpace B S hS Z V) G hG)).symm ≪≫
    (restrictToChartSchemeFunctor B S hS (chartSpace B S hS X W).1
        (chartSpace B S hS X W).2
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj W))).mapIso
      (chartModuleRestrictionBaseChange B S hS a G V W g hg) ≪≫
    (restrictToChartSchemeIsoAtIdEtaleChart B S hS X W
        ((modulePullback B S hS a).obj G)).symm ≪≫
    eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2
      ((modulePullback B S hS a).obj G) W).symm

/-- **The Zariski chart restriction of a quasi-coherent module commutes with base change**, as an
existence statement; `AlgebraicGeometry.Space.chartRestrictionBaseChangeIso` is the
isomorphism itself. -/
theorem nonempty_chartRestrictionBaseChange {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS Z.1) (W : SmallEtale B S hS X.1)
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    Nonempty ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
        (restrictToChart B S hS Z.2 G V) ≅
      restrictToChart B S hS X.2 ((modulePullback B S hS a).obj G) W) :=
  ⟨chartRestrictionBaseChangeIso B S hS a G hG V W g hg⟩

end AlgebraicGeometry.Space

end

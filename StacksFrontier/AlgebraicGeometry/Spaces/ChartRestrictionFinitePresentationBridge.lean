module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPullbackRestrictionIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFinitePresentation

/-!
# Finite presentation on a chart: the Zariski reading and the small étale reading

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `F` be a
quasi-coherent `𝒪_X`-module and let `V` be an étale scheme chart of `X`.  Two things are called
"the restriction of `F` to `V`": `AlgebraicGeometry.Space.restrictToChart`, a module on the
*Zariski* site of the chart scheme, which the chartwise properties of Stacks 03M0 are read on;
and `F.over V`, a module on the slice of the small étale site of `X` at `V`, which the site-level
properties of Modules on Sites are read on.  This file proves that the two have the same finite
presentation.

The passage runs along the chain already in the tree for quasi-coherence: the Zariski chart
restriction is the identity-chart restriction of the étale pullback to the chart space, that one
is the right adjoint of the associated-module functor of Stacks 03DU applied to the pullback read
on the small étale site of the chart scheme, and the étale pullback to the chart space is the
04M0 reading of `F.over V`.  Each link is an equivalence for finite presentation.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_restrictToChartScheme_idEtaleChart_iff`: at a
  representable algebraic space and its identity chart, the Zariski restriction is of finite
  presentation exactly when the module is.
* `AlgebraicGeometry.Space.isFinitePresentation_restrictToChart_iff`: **the Zariski chart
  restriction of a quasi-coherent `𝒪_X`-module is of finite presentation exactly when its
  restriction to the slice of the small étale site at that chart is.**

## Implementation notes

This is the finite-presentation companion of
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`, and it follows the same four links;
quasi-coherence, being a condition on the restriction to every object, only ever needs the
implications in one direction, while finite presentation needs the equivalences, so each link is
used here through the `iff` its file provides and the isomorphisms are used in both directions.
The quasi-coherence hypothesis is the one the source carries: Stacks 05VG, which the third link
rests on, is false without it.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Finite presentation of sheaves of modules is invariant under isomorphism, as an `iff`. -/
private theorem isFinitePresentation_iff_of_iso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) : M.IsFinitePresentation ↔ N.IsFinitePresentation :=
  ⟨Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso e,
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso e.symm⟩

/-- **Finite presentation of the Zariski restriction at an identity chart.**  A quasi-coherent
module on a representable algebraic space restricts, along the identity chart, to a module of
finite presentation on the Zariski site of the underlying scheme exactly when it is itself of
finite presentation.

The restriction is the right adjoint of the associated-module functor of Stacks 03DU applied to
the module read on the small étale site of the scheme, by
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`; finite presentation crosses that
right adjoint by `AlgebraicGeometry.SmallEtale.isFinitePresentation_restrictModule_iff` and the
reading by `AlgebraicGeometry.Space.isFinitePresentation_representedSmallEtaleModule_iff`. -/
theorem isFinitePresentation_restrictToChartScheme_idEtaleChart_iff (A : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj A)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A))
    (hN : N.IsQuasicoherentOnSite) :
    (restrictToChartScheme B S hS (yoneda.obj A)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A) N
        (idEtaleChart B S hS A)).IsFinitePresentation ↔
      N.IsFinitePresentation := by
  set M := (representedSmallEtaleModuleEquivalence B S hS A).inverse.obj N with hMdef
  have eN : (representedSmallEtaleModuleEquivalence B S hS A).functor.obj M ≅ N :=
    (representedSmallEtaleModuleEquivalence B S hS A).counitIso.app N
  have hM : M.IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS A M).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso eN.symm hN)
  refine Iff.trans (isFinitePresentation_iff_of_iso
    (restrictToChartSchemeIdEtaleChartIso B S hS A N)) ?_
  refine Iff.trans (_root_.AlgebraicGeometry.SmallEtale.isFinitePresentation_restrictModule_iff
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj A) A.left.property M hM) ?_
  refine Iff.trans (isFinitePresentation_representedSmallEtaleModule_iff B S hS A M) ?_
  exact isFinitePresentation_iff_of_iso eN

/-- **The two readings of the restriction of a quasi-coherent `𝒪_X`-module to an étale scheme
chart have the same finite presentation.**  The Zariski restriction of Stacks 03M0 to the chart
scheme is of finite presentation exactly when the restriction to the slice of the small étale
site of `X` at that chart is.

The Zariski restriction is the identity-chart restriction of the étale pullback to the chart
space, by `AlgebraicGeometry.Space.restrictToChartSchemeIsoAtIdEtaleChart`; that pullback is
quasi-coherent by Stacks 03GA, so
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChartScheme_idEtaleChart_iff` applies to
it, and it is the 04M0 reading of `F.over V` by
`AlgebraicGeometry.Space.isFinitePresentation_etaleModulePullback_chartToSpace_iff`. -/
theorem isFinitePresentation_restrictToChart_iff (X : AlgebraicSpaces B S hS)
    (F : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hF : F.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) :
    (restrictToChart B S hS X.2 F V).IsFinitePresentation ↔
      (F.over V).IsFinitePresentation := by
  have e := eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 F V) ≪≫
    restrictToChartSchemeIsoAtIdEtaleChart B S hS X V F
  refine Iff.trans (isFinitePresentation_iff_of_iso e) ?_
  refine Iff.trans (isFinitePresentation_restrictToChartScheme_idEtaleChart_iff B S hS
    ((SmallEtale.toOver B S hS X.1).obj V) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS X V) F hF)) ?_
  refine Iff.trans (isFinitePresentation_iff_of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).app F)) ?_
  exact isFinitePresentation_etaleModulePullback_chartToSpace_iff B S hS X F V

end AlgebraicGeometry.Space

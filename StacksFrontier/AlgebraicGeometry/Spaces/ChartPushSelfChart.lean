module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSemilinear
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiIdealChartPush
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# The chart restriction at the identity chart of a represented algebraic space

Let `B` be a big fppf site containing a scheme `S` and let `V` be an object of the big fppf
category over `S`. The identity of `yoneda.obj V` is an étale scheme chart of it,
`AlgebraicGeometry.Space.selfChart`, whose scheme is the scheme underlying `V`, and
`AlgebraicGeometry.Space.chartPush` restricts an `𝒪`-module on the small étale site of
`yoneda.obj V` along it to a sheaf of modules on the small Zariski site of that scheme. At the
identity chart this restriction is the restriction of Stacks 03DX: it is
`AlgebraicGeometry.SmallEtale.restrictModule`, restriction along the inclusion of the small
Zariski site into the small étale site of the scheme, applied to the module read on the scheme's
small étale site through `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`. For a
quasi-coherent module, the associated module of this restriction is the module itself.

## Main results

* `AlgebraicGeometry.Space.chartComparisonFunctor_selfChart`: the composite comparison functor of
  the identity chart is the inclusion of the small Zariski site of the representing scheme
  followed by the inverse of the comparison of the two small étale sites.
* `AlgebraicGeometry.Space.chartPush_selfChart`: the chart restriction at the identity chart is
  `AlgebraicGeometry.SmallEtale.restrictModule` of the reindexed module.
* `AlgebraicGeometry.Space.associatedModuleChartPushSelfChartIso`: the associated module of the
  chart restriction at the identity chart is the module itself, for a quasi-coherent module.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse`: a
  quasi-coherent module on the small étale site of a representable algebraic space is
  quasi-coherent read on the small étale site of the representing scheme.
* `AlgebraicGeometry.Space.associatedModuleChartZariskiIdealSheafSelfChartIso` and
  `AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso`: a
  quasi-coherent sheaf of ideals of a representable algebraic space is the associated module of
  its Zariski restriction, the latter read as a submodule of the structure sheaf of the
  representing scheme by `AlgebraicGeometry.Space.chartZariskiIdealSheaf`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS)

/-! ### The comparison functor at the identity chart -/

/-- **The composite comparison functor of the identity chart is the inclusion of the small Zariski
site of the representing scheme followed by the inverse of the comparison of the two small étale
sites**. -/
theorem chartComparisonFunctor_selfChart :
    chartComparisonFunctor B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V) =
      (_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          (chartScheme (selfChart B S hS V))
          (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V)).left.property) ⋙
        (representedSmallEtaleEquivalence B S hS
          (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V))).inverse := rfl

/-! ### The chart restriction at the identity chart -/

/-- **The chart restriction at the identity chart of a represented algebraic space is the
restriction of Stacks 03DX along the inclusion of the small Zariski site of the representing
scheme**, applied to the module read on the scheme's small étale site through the comparison of
the two small étale sites. -/
theorem chartPush_selfChart
    (M : SheafOfModules.{u} (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) :
    chartPush B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ M
        (selfChart B S hS V) =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme (selfChart B S hS V))
          (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V)).left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M) := by
  have := isContinuous_opensToSmallEtale_comp_representedInverse B S hS
    ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ (selfChart B S hS V)
  have := isContinuous_chartComparisonFunctor B S hS
    ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ (selfChart B S hS V)
  set ρ := Stacks.SheafOfModules.reindexBackSharp
    (J' := SmallEtale.topology B S hS (yoneda.obj
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V))))
    (representedSmallEtaleEquivalence B S hS
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)))
    (representedSchemeStructureSheaf B S hS
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)))
  have hring : chartComparisonRingMap B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ (selfChart B S hS V) =
      SheafOfModules.comparisonComp
        (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
          (chartScheme (selfChart B S hS V))
          (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V)).left.property) ρ :=
    Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl))
  exact (congrArg (fun φ => (_root_.SheafOfModules.pushforward.{u} φ).obj M) hring).trans
    (Stacks.SheafOfModules.pushforward_pushforward_obj _ ρ M).symm

/-! ### Recovering the module from its chart restriction -/

/-- **A quasi-coherent module on the small étale site of a representable algebraic space is
quasi-coherent on the small étale site of the representing scheme**, read there through the
inverse of the comparison of the two sites. -/
theorem isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse
    (M : SheafOfModules.{u} (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩))
    (hM : M.IsQuasicoherentOnSite) :
    ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS V
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M)).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((representedSmallEtaleModuleEquivalence B S hS V).counitIso.app M).symm hM)

/-- **The associated module of the chart restriction at the identity chart is the module it came
from.** For a quasi-coherent `𝒪`-module `M` on the small étale site of a representable algebraic
space, the associated module of the Zariski chart restriction of `M` along the identity chart is
`M` read on the small étale site of the representing scheme. -/
noncomputable def associatedModuleChartPushSelfChartIso
    (M : SheafOfModules.{u} (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩))
    (hM : M.IsQuasicoherentOnSite) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          (chartScheme (selfChart B S hS V))
          (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V)).left.property).obj
        (chartPush B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ M
          (selfChart B S hS V)) ≅
      (representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M :=
  eqToIso (congrArg
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          (chartScheme (selfChart B S hS V))
          (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
            (selfChart B S hS V)).left.property).obj
      (chartPush_selfChart B S hS V M)) ≪≫
    _root_.AlgebraicGeometry.SmallEtale.associatedModuleRestrictModuleIso
      (associatedBigEtaleSite B) (chartScheme (selfChart B S hS V))
      (chartFppfObject B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (selfChart B S hS V)).left.property
      ((representedSmallEtaleModuleEquivalence B S hS V).inverse.obj M)
      (isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse B S hS V M hM)

/-! ### The Zariski restriction of a sheaf of ideals recovers it -/

/-- **The associated module of the Zariski restriction of a sheaf of ideals of a representable
algebraic space, read as a submodule of the structure sheaf of the representing scheme, is the
sheaf of ideals itself**, on the small étale site of the representing scheme. -/
noncomputable def associatedModuleChartZariskiIdealSheafSelfChartIso
    (N : (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
        (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
          (selfChart B S hS V)).toSheafOfModules ≅
      (representedSmallEtaleModuleEquivalence B S hS V).inverse.obj N.toSheafOfModules :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property).mapIso
      (chartZariskiIdealSheafIsoChartPush B S hS
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N (selfChart B S hS V)) ≪≫
    associatedModuleChartPushSelfChartIso B S hS V N.toSheafOfModules hN

/-- **The sheaf of ideals of a representable algebraic space is the associated module of its
Zariski restriction**, read back on the small étale site of the algebraic space. -/
noncomputable def representedAssociatedModuleChartZariskiIdealSheafIso
    (N : (SheafOfModules.unit (structureRingSheaf B S hS
      ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite) :
    (representedSmallEtaleModuleEquivalence B S hS V).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
          (chartZariskiIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ N
            (selfChart B S hS V)).toSheafOfModules) ≅
      N.toSheafOfModules :=
  (representedSmallEtaleModuleEquivalence B S hS V).functor.mapIso
      (associatedModuleChartZariskiIdealSheafSelfChartIso B S hS V N hN) ≪≫
    (representedSmallEtaleModuleEquivalence B S hS V).counitIso.app N.toSheafOfModules

end AlgebraicGeometry.Space

end

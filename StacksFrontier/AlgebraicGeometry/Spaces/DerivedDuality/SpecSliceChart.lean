module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartSliceIso
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SliceChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SpecChart

/-!
# Full duality charts on the slices of the model of an algebraic space

An affine Noetherian scheme `T` satisfying the étale vanishing bound of Stacks 0E50 has a full
duality chart on the model of its small étale site
(`AlgebraicGeometry.SmallEtale.baseDualityChart`; for `T = Spec R`,
`AlgebraicGeometry.SmallEtale.specDualityChart`). Such a chart transports to the model of `h_U`
(`AlgebraicGeometry.Space.reprChart`) and to the slice of the model of an algebraic space `F` at
an object `V` whose chart is isomorphic to an étale chart `c`
(`AlgebraicGeometry.Space.sliceChartOfIso`).

## Main definitions

* `AlgebraicGeometry.Space.reprChart`: the full duality chart on the model of `h_U`.
* `AlgebraicGeometry.Space.sliceRestrictIsoOfIso`: the restriction of a derived module to the
  slice at `V`, identified with the transport of its restriction to the chart.
* `AlgebraicGeometry.Space.sliceChartOfIso`: the full duality chart on the slice at `V`.

## References

* [Stacks Project, Tag 0E51](https://stacks.math.columbia.edu/tag/0E51)
* [Stacks Project, Tag 0E50](https://stacks.math.columbia.edu/tag/0E50)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Repr

variable (U : BigFppfOver B S hS)
  [_root_.AlgebraicGeometry.IsAffine (reprScheme B S hS U)]
  [_root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS U)]

/-- **The full duality chart on the model of `h_U`**, transported from the model of the scheme
of `U` along `reprModelEquiv`, given the étale vanishing bound on the scheme of `U`. -/
def reprChart (ω : RingedSite.SchemeStdDerived (reprScheme B S hS U))
    (hω : letI : HasDerivedCategory (reprScheme B S hS U).Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω)
    (bEt : ℤ)
    (hEt : ∀ (m : ℤ) (Y : RingedSite.SchemeStdDerived (reprScheme B S hS U)),
      RingedSite.SchemeCoherent _ Y →
      (∀ i : ℤ, i < m → IsZero ((RingedSite.schemeStdHomology _ i).obj Y)) →
        ∀ j : ℤ, bEt - m < j → IsZero ((RingedSite.stdHomology (SmallEtale.modelSite
          (associatedBigEtaleSite B) (reprScheme B S hS U) U.left.property) j).obj
          (((RingedSite.stdSheafHom (SmallEtale.modelSite (associatedBigEtaleSite B)
            (reprScheme B S hS U) U.left.property)).obj
            (op ((SmallEtale.chartFunctor (associatedBigEtaleSite B) (reprScheme B S hS U)
              U.left.property).derived.obj Y))).obj
              ((SmallEtale.chartFunctor (associatedBigEtaleSite B) (reprScheme B S hS U)
                U.left.property).derived.obj ω)))) :
    RingedSite.DualityChart (reprSite B S hS U)
      ((RingedSite.siteEquivDerivedEquivalence (reprModelEquiv B S hS U)
        (reprModelRingMap B S hS U)).functor.obj
          ((SmallEtale.chartFunctor (associatedBigEtaleSite B) (reprScheme B S hS U)
            U.left.property).derived.obj ω))
      RingedSite.ChartClass.all :=
  (SmallEtale.baseDualityChart (associatedBigEtaleSite B) (reprScheme B S hS U)
    U.left.property ω hω bEt hEt).transport

end Repr

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (V : SmallEtaleModel B S hS F) (c : SmallEtale B S hS F) (i : chartObj B S hS F V ≅ c)

/-- **Restriction to the slice at `V`, on derived categories**: the restriction of `K` to the
slice of the model at `V` is the transport along `chartSliceEquiv` of the transport to the model
of `h_U` of the restriction `K|_U` of `K` to the chart. -/
def sliceRestrictIsoOfIso (K : DerivedModules B S hS F hF) :
    (RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) V).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj K) ≅
      (RingedSite.siteEquivDerivedEquivalence (chartSliceEquivOfIso B S hS F hF V c i)
        (chartSliceModelRingMapOfIso B S hS F hF V c i)).functor.obj
        ((modelDerivedEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))
          (isAlgebraicSpace_yoneda B S hS _)).functor.obj
          ((representedChartDerivedRestriction B S hS hF (etaleChartBase B S hS F c)
            c.obj.hom (etaleChartMap_isEtale B S hS F hF c)).obj K)) := by
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj (etaleChartBase B S hS F c))
      (isAlgebraicSpace_yoneda B S hS _))
  letI := HasDerivedCategory.standard (ModelModules B S hS F hF)
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (etaleChartSite B S hS F c).O))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleModelRingedSite B S hS F hF).over V).O))
  letI := additive_modulesEquivModelModules_functor B S hS F hF
  letI := additive_modulesEquivModelModules_functor B S hS (yoneda.obj (etaleChartBase B S hS F c))
    (isAlgebraicSpace_yoneda B S hS _)
  haveI := etaleModulePullback_additive.{u, u} B S hS (etaleChartMap B S hS F hF c)
    (etaleChartMap_isEtale B S hS F hF c)
  haveI := preservesFiniteLimits_etaleModulePullback B S hS (etaleChartMap B S hS F hF c)
    (etaleChartMap_isEtale B S hS F hF c)
  haveI := preservesFiniteColimits_etaleModulePullback B S hS (etaleChartMap B S hS F hF c)
    (etaleChartMap_isEtale B S hS F hF c)
  letI := RingedSite.pushforward_preservesFiniteLimitsOfIso (chartSliceEquivOfIso B S hS F hF V c i)
    (chartSliceModelRingMapOfIso B S hS F hF V c i)
  letI := RingedSite.pushforward_preservesFiniteColimitsOfIso
    (chartSliceEquivOfIso B S hS F hF V c i) (chartSliceModelRingMapOfIso B S hS F hF V c i)
  haveI := RingedSite.restrictModules_additive (smallEtaleModelRingedSite B S hS F hF) V
  haveI := RingedSite.restrictModules_preservesFiniteLimits
    (smallEtaleModelRingedSite B S hS F hF) V
  haveI := RingedSite.restrictModules_preservesFiniteColimits
    (smallEtaleModelRingedSite B S hS F hF) V
  haveI : PreservesFiniteLimits (modulesEquivModelModules B S hS F hF).functor := inferInstance
  haveI : PreservesFiniteColimits (modulesEquivModelModules B S hS F hF).functor := inferInstance
  let e := chartSliceModulesIsoOfIso B S hS F hF V c i
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  exact (RingedSite.stdRestrictCompIso (smallEtaleModelRingedSite B S hS F hF) V
      (modulesEquivModelModules B S hS F hF).functor).app K ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCongr e).app K ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso
      (etaleModulePullback.{u, u} B S hS (etaleChartMap B S hS F hF c)
        (etaleChartMap_isEtale B S hS F hF c))
      ((modulesEquivModelModules B S hS (yoneda.obj (etaleChartBase B S hS F c))
          (isAlgebraicSpace_yoneda B S hS _)).functor ⋙
        SheafOfModules.pushforward.{u}
          (chartSliceModelRingMapOfIso B S hS F hF V c i))).symm.app K ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso
      (modulesEquivModelModules B S hS (yoneda.obj (etaleChartBase B S hS F c))
          (isAlgebraicSpace_yoneda B S hS _)).functor
      (SheafOfModules.pushforward.{u} (chartSliceModelRingMapOfIso B S hS F hF V c i))).symm.app _

/-- **The full duality chart on the slice of the model at a chart**: if the scheme of the chart is
affine Noetherian with the étale vanishing bound and `K|_U ≅ ε^* ω` with `ω` dualizing, the full
duality chart of the scheme is a duality chart for the restriction of `K` to the slice at `V`. -/
def sliceChartOfIso
    [_root_.AlgebraicGeometry.IsAffine (reprScheme B S hS (etaleChartBase B S hS F c))]
    [_root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS (etaleChartBase B S hS F c))]
    (K : DerivedModules B S hS F hF)
    (ω : RingedSite.SchemeStdDerived (reprScheme B S hS (etaleChartBase B S hS F c)))
    (hω : letI : HasDerivedCategory (reprScheme B S hS (etaleChartBase B S hS F c)).Modules :=
      HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω)
    (bEt : ℤ)
    (hEt : ∀ (m : ℤ)
      (Y : RingedSite.SchemeStdDerived (reprScheme B S hS (etaleChartBase B S hS F c))),
      RingedSite.SchemeCoherent _ Y →
      (∀ i : ℤ, i < m → IsZero ((RingedSite.schemeStdHomology _ i).obj Y)) →
        ∀ j : ℤ, bEt - m < j → IsZero ((RingedSite.stdHomology (SmallEtale.modelSite
          (associatedBigEtaleSite B) (reprScheme B S hS (etaleChartBase B S hS F c))
          (etaleChartBase B S hS F c).left.property) j).obj
          (((RingedSite.stdSheafHom (SmallEtale.modelSite (associatedBigEtaleSite B)
            (reprScheme B S hS (etaleChartBase B S hS F c))
            (etaleChartBase B S hS F c).left.property)).obj
            (op ((SmallEtale.chartFunctor (associatedBigEtaleSite B)
              (reprScheme B S hS (etaleChartBase B S hS F c))
              (etaleChartBase B S hS F c).left.property).derived.obj Y))).obj
              ((SmallEtale.chartFunctor (associatedBigEtaleSite B)
                (reprScheme B S hS (etaleChartBase B S hS F c))
                (etaleChartBase B S hS F c).left.property).derived.obj ω))))
    (e : (representedChartDerivedRestriction B S hS hF (etaleChartBase B S hS F c)
        c.obj.hom (etaleChartMap_isEtale B S hS F hF c)).obj K ≅
      (representedDerivedAssociatedModule B S hS (etaleChartBase B S hS F c)).obj ω) :
    RingedSite.DualityChart ((smallEtaleModelRingedSite B S hS F hF).over V)
      ((RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) V).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj K))
      RingedSite.ChartClass.all :=
  ((reprChart B S hS (etaleChartBase B S hS F c) ω hω bEt hEt).transport
      (eqv := chartSliceEquivOfIso B S hS F hF V c i)
      (φ := chartSliceModelRingMapOfIso B S hS F hF V c i)).ofIso
    ((RingedSite.siteEquivDerivedEquivalence (chartSliceEquivOfIso B S hS F hF V c i)
        (chartSliceModelRingMapOfIso B S hS F hF V c i)).functor.mapIso
        (reprChartDerivedIso B S hS (etaleChartBase B S hS F c) ω ≪≫
          (modelDerivedEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))
            (isAlgebraicSpace_yoneda B S hS _)).functor.mapIso e.symm) ≪≫
      (sliceRestrictIsoOfIso B S hS F hF V c i K).symm)

end AlgebraicGeometry.Space

end

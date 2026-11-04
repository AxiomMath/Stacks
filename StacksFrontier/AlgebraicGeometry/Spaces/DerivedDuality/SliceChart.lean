module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartModel
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra

/-!
# Duality charts on the slices of the model of an algebraic space

Let `F` be an algebraic space and `V` an object of the equi-universe model of its small étale
ringed site whose chart `h_U ⟶ F` has an affine Noetherian scheme `T`. Restriction to the slice
at `V` is restriction to the chart (`AlgebraicGeometry.Space.chartSliceModulesIso`), the slice is
the model of `h_U`, which is the model of `T` (`AlgebraicGeometry.Space.reprModelEquiv`), and the
two comparisons `ε^*` of `T` with the model of `h_U` agree. So if `K|_U ≅ ε^* ω` for a dualizing
complex `ω` on `T` (Stacks 0E4X), the duality chart of `T` is a duality chart for the restriction
of `K` to the slice at `V`.

## Main definitions

* `AlgebraicGeometry.Space.sliceChart`: the duality chart on the slice.

## References

* [Stacks Project, Tag 0E4X](https://stacks.math.columbia.edu/tag/0E4X)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [_root_.AlgebraicGeometry.IsAffine (reprScheme B S hS U)]
  [_root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS U)]

/-- **The two comparisons `ε^*` of the scheme of `U` with the model of `h_U` agree**: the chart
functor of the scheme followed by the pushforward along `reprModelEquiv`, and the represented
associated module followed by transport to the model. -/
def reprChartModulesIso :
    (SmallEtale.chartFunctor (associatedBigEtaleSite B) (reprScheme B S hS U)
        U.left.property).Φ ⋙ SheafOfModules.pushforward.{u} (reprModelRingMap B S hS U) ≅
      representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U) ⋙
        (modulesEquivModelModules B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).functor :=
  Functor.isoWhiskerRight (SmallEtale.pullbackToposIsoAssociatedModel (associatedBigEtaleSite B)
      (reprScheme B S hS U) U.left.property) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (reprModelModulesIso B S hS U) ≪≫ (Functor.associator _ _ _).symm

/-- **The derived comparison**: transporting `ε^* ω` from the model of the scheme to the model of
`h_U` is transporting the represented `ε^* ω`. -/
def reprChartDerivedIso (ω : RingedSite.SchemeStdDerived (reprScheme B S hS U)) :
    (RingedSite.siteEquivDerivedEquivalence (reprModelEquiv B S hS U)
        (reprModelRingMap B S hS U)).functor.obj
        ((SmallEtale.chartFunctor (associatedBigEtaleSite B) (reprScheme B S hS U)
          U.left.property).derived.obj ω) ≅
      (modelDerivedEquivalence B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).functor.obj
        ((representedDerivedAssociatedModule B S hS U).obj ω) := by
  letI : HasDerivedCategory (reprScheme B S hS U).Modules := HasDerivedCategory.standard _
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (reprBaseSite B S hS U).O))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (reprSite B S hS U).O))
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
  let c := SmallEtale.chartFunctor (associatedBigEtaleSite B) (reprScheme B S hS U) U.left.property
  letI := c.additive
  letI := c.preservesFiniteLimits
  letI := c.preservesFiniteColimits
  letI := RingedSite.pushforward_preservesFiniteLimitsOfIso (reprModelEquiv B S hS U)
    (reprModelRingMap B S hS U)
  letI := RingedSite.pushforward_preservesFiniteColimitsOfIso (reprModelEquiv B S hS U)
    (reprModelRingMap B S hS U)
  letI := additive_modulesEquivModelModules_functor B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U)
  let e := reprChartModulesIso B S hS U
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  exact ((Stacks.DerivedFunctor.mapDerivedCategoryCompIso c.Φ
      (SheafOfModules.pushforward.{u} (reprModelRingMap B S hS U))).app ω ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCongr e).app ω ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso
      (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U))
      (modulesEquivModelModules B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).functor).symm.app ω)

section Slice

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (V : SmallEtaleModel B S hS F)

/-- The slice of the model at `V` has fibre products. -/
instance sliceModel_hasPullbacks :
    HasPullbacks ((smallEtaleModelRingedSite B S hS F hF).over V).C :=
  inferInstanceAs (HasPullbacks (Over (show SmallEtaleModel B S hS F from V)))

/-- **Restriction to the slice at `V`, on derived categories**: the restriction of `K` to the
slice of the model at `V` is the transport along `chartSliceEquiv` of the transport to the model
of `h_U` of the restriction `K|_U` of `K` to the chart. -/
def sliceRestrictIso (K : DerivedModules B S hS F hF) :
    (RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) V).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj K) ≅
      (RingedSite.siteEquivDerivedEquivalence (chartSliceEquiv B S hS F hF V)
        (chartSliceModelRingMap B S hS F hF V)).functor.obj
        ((modelDerivedEquivalence B S hS (yoneda.obj (chartBase B S hS F V))
          (isAlgebraicSpace_yoneda B S hS _)).functor.obj
          ((representedChartDerivedRestriction B S hS hF (chartBase B S hS F V)
            (chartObj B S hS F V).obj.hom (modelChartMap_isEtale B S hS F hF V)).obj K)) := by
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj (chartBase B S hS F V))
    (isAlgebraicSpace_yoneda B S hS _))
  letI := HasDerivedCategory.standard (ModelModules B S hS F hF)
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (chartSite B S hS F V).O))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleModelRingedSite B S hS F hF).over V).O))
  letI := additive_modulesEquivModelModules_functor B S hS F hF
  letI := additive_modulesEquivModelModules_functor B S hS (yoneda.obj (chartBase B S hS F V))
    (isAlgebraicSpace_yoneda B S hS _)
  haveI := etaleModulePullback_additive.{u, u} B S hS (modelChartMap B S hS F hF V)
    (modelChartMap_isEtale B S hS F hF V)
  haveI := preservesFiniteLimits_etaleModulePullback B S hS (modelChartMap B S hS F hF V)
    (modelChartMap_isEtale B S hS F hF V)
  haveI := preservesFiniteColimits_etaleModulePullback B S hS (modelChartMap B S hS F hF V)
    (modelChartMap_isEtale B S hS F hF V)
  letI := RingedSite.pushforward_preservesFiniteLimitsOfIso (chartSliceEquiv B S hS F hF V)
    (chartSliceModelRingMap B S hS F hF V)
  letI := RingedSite.pushforward_preservesFiniteColimitsOfIso (chartSliceEquiv B S hS F hF V)
    (chartSliceModelRingMap B S hS F hF V)
  haveI := RingedSite.restrictModules_additive (smallEtaleModelRingedSite B S hS F hF) V
  haveI := RingedSite.restrictModules_preservesFiniteLimits
    (smallEtaleModelRingedSite B S hS F hF) V
  haveI := RingedSite.restrictModules_preservesFiniteColimits
    (smallEtaleModelRingedSite B S hS F hF) V
  haveI : PreservesFiniteLimits (modulesEquivModelModules B S hS F hF).functor := inferInstance
  haveI : PreservesFiniteColimits (modulesEquivModelModules B S hS F hF).functor := inferInstance
  let e := chartSliceModulesIso B S hS F hF V
  letI := Functor.additive_of_iso e
  letI := preservesFiniteLimits_of_natIso e
  letI := preservesFiniteColimits_of_natIso e
  exact (RingedSite.stdRestrictCompIso (smallEtaleModelRingedSite B S hS F hF) V
      (modulesEquivModelModules B S hS F hF).functor).app K ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCongr e).app K ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso
      (etaleModulePullback.{u, u} B S hS (modelChartMap B S hS F hF V)
        (modelChartMap_isEtale B S hS F hF V))
      ((modulesEquivModelModules B S hS (yoneda.obj (chartBase B S hS F V))
          (isAlgebraicSpace_yoneda B S hS _)).functor ⋙
        SheafOfModules.pushforward.{u} (chartSliceModelRingMap B S hS F hF V))).symm.app K ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso
      (modulesEquivModelModules B S hS (yoneda.obj (chartBase B S hS F V))
          (isAlgebraicSpace_yoneda B S hS _)).functor
      (SheafOfModules.pushforward.{u} (chartSliceModelRingMap B S hS F hF V))).symm.app _

/-- **The duality chart on the slice of the model at a chart**, at the class of bounded objects:
if the scheme of the chart is affine Noetherian and `K|_U ≅ ε^* ω` with `ω` dualizing, the bounded
duality chart of the scheme is a duality chart for the restriction of `K` to the slice at `V`. -/
def sliceBoundedChart
    [_root_.AlgebraicGeometry.IsAffine (reprScheme B S hS (chartBase B S hS F V))]
    [_root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS (chartBase B S hS F V))]
    (K : DerivedModules B S hS F hF)
    (ω : RingedSite.SchemeStdDerived (reprScheme B S hS (chartBase B S hS F V)))
    (hω : letI : HasDerivedCategory (reprScheme B S hS (chartBase B S hS F V)).Modules :=
      HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω)
    (e : (representedChartDerivedRestriction B S hS hF (chartBase B S hS F V)
        (chartObj B S hS F V).obj.hom (modelChartMap_isEtale B S hS F hF V)).obj K ≅
      (representedDerivedAssociatedModule B S hS (chartBase B S hS F V)).obj ω) :
    RingedSite.DualityChart ((smallEtaleModelRingedSite B S hS F hF).over V)
      ((RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) V).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj K))
      RingedSite.ChartClass.bounded :=
  ((reprBoundedChart B S hS (chartBase B S hS F V) ω hω).transport
      (eqv := chartSliceEquiv B S hS F hF V) (φ := chartSliceModelRingMap B S hS F hF V)).ofIso
    ((RingedSite.siteEquivDerivedEquivalence (chartSliceEquiv B S hS F hF V)
        (chartSliceModelRingMap B S hS F hF V)).functor.mapIso
        (reprChartDerivedIso B S hS (chartBase B S hS F V) ω ≪≫
          (modelDerivedEquivalence B S hS (yoneda.obj (chartBase B S hS F V))
            (isAlgebraicSpace_yoneda B S hS _)).functor.mapIso e.symm) ≪≫
      (sliceRestrictIso B S hS F hF V K).symm)

/-! ### The affine charts cover the model -/

omit [_root_.AlgebraicGeometry.IsAffine (reprScheme B S hS U)]
  [_root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS U)] in
/-- A morphism into `e.functor.obj W` is the counit followed by the image of its transpose. -/
theorem eq_counitInv_comp_functor_map {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {c' : D} {W : C} (g : c' ⟶ e.functor.obj W) :
    g = e.counitInv.app c' ≫ e.functor.map (e.inverse.map g ≫ e.unitInv.app W) := by
  rw [Functor.map_comp, Equivalence.fun_inv_map, ← Equivalence.counit_app_functor]
  simp

/-- The objects of the model whose chart has an affine scheme. -/
def AffineChart : Type u :=
  {V : SmallEtaleModel B S hS F //
    _root_.AlgebraicGeometry.IsAffine (reprScheme B S hS (chartBase B S hS F V))}

/-- **The affine charts cover the model of the small étale site.** -/
theorem affineChart_coversTop :
    (smallEtaleModelRingedSite B S hS F hF).J.CoversTop
      (fun i : AffineChart B S hS F => (i.1 : (smallEtaleModelRingedSite B S hS F hF).C)) := by
  intro W
  let e := smallEtaleModelEquivalence B S hS F
  show Sieve.ofObjects _ W ∈ smallEtaleModelTopology B S hS F W
  refine (Functor.functorPushforward_mem_iff (G := e.functor) (smallEtaleModelTopology B S hS F)
    (SmallEtale.topology B S hS F)).1 ?_
  apply smallEtale_sieve_of_pointwise_covering B S hS F (e.functor.obj W)
  intro z
  obtain ⟨A, hA, hzA, -⟩ := exists_isAffineOpen_mem_and_subset (x := z)
    (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
      (e.functor.obj W))).Opens)) (by simp)
  let c' := chartOpenRestriction B S hS F (e.functor.obj W) A
  let g : c' ⟶ e.functor.obj W := chartOpenRestrictionHom B S hS F (e.functor.obj W) A
  have hc' : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj c')) := hA
  have hW' : _root_.AlgebraicGeometry.IsAffine
      (reprScheme B S hS (chartBase B S hS F (e.inverse.obj c'))) := by
    have : _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj ((𝟭 (SmallEtale B S hS F)).obj c'))) := hc'
    have : IsIso ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (e.counit.app c'))) := inferInstance
    exact IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map (e.counit.app c')))
  refine ⟨c', g, ⟨e.inverse.obj c', e.inverse.map g ≫ e.unitInv.app W, e.counitInv.app c',
    (show ∃ i : AffineChart B S hS F, Nonempty (e.inverse.obj c' ⟶ i.1) from
      ⟨⟨e.inverse.obj c', hW'⟩, ⟨𝟙 _⟩⟩), eq_counitInv_comp_functor_map e g⟩, ⟨z, hzA⟩, ?_⟩
  rw [show (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map g) = A.ι from
    chartOpenRestrictionHom_toScheme B S hS F (e.functor.obj W) A]
  rfl

end Slice

end AlgebraicGeometry.Space

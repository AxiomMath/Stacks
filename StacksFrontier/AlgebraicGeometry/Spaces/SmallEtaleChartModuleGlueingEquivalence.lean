module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceDictionarySquares

/-!
# The chartwise description of modules is an equivalence

A sheaf of `𝒪_X`-modules on the small étale site of an algebraic space `X` is described by a
family of modules on the small étale sites of the étale scheme charts of `X`, with transition
isomorphisms satisfying a cocycle condition. The slice-indexed description
`CategoryTheory.SiteGlueing.canonicalModuleEquivalence`, with the slices `X_étale/U` in place of
the charts, is an equivalence. This file constructs an equivalence between slice-indexed and
chartwise glueing data for modules, identifies the canonical chartwise description with the
canonical slice-indexed one read through it, and so proves that
`AlgebraicGeometry.Space.chartModuleGlueingFunctor` is an equivalence.

## Main definitions

* `AlgebraicGeometry.Space.sliceToChartModuleGlueingData` and
  `AlgebraicGeometry.Space.sliceToChartModuleFunctor`: a slice-indexed glueing datum for modules,
  read chartwise.
* `AlgebraicGeometry.Space.chartModuleGlueingFunctorIso`: the canonical chartwise description is
  the canonical slice-indexed description read chartwise.
* `AlgebraicGeometry.Space.chartModuleGlueingEquivalence`: the equivalence between
  `𝒪_X`-modules and chartwise glueing data for modules.

## Main results

* `AlgebraicGeometry.Space.sliceToChartModuleFunctor_faithful` and
  `AlgebraicGeometry.Space.sliceToChartModuleFunctor_full`: the chartwise reading of slice-indexed
  glueing data for modules is fully faithful.
* `AlgebraicGeometry.Space.sliceToChartModuleFunctor_isEquivalence`: it is an equivalence.
* `AlgebraicGeometry.Space.chartModuleGlueingFunctor_isEquivalence`: the canonical chartwise
  description of `𝒪_X`-modules is an equivalence.

## Implementation notes

Every comparison is applied through `AlgebraicGeometry.Space.chartModuleInverseImageSliceApp`,
`AlgebraicGeometry.Space.overMapCompInvApp` and
`AlgebraicGeometry.Space.chartModuleInverseImageCompApp`, whose types are written out
uncomposed, so that no composite-functor spelling is ever compared with an uncomposed one. The
naturality of a comparison of composite functors is isolated, at a variable module, in
`AlgebraicGeometry.Space.chartModuleInverseImageCompApp_naturality`.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The naturality of the chartwise composition comparison, uncomposed -/

/-- The naturality of `AlgebraicGeometry.Space.chartModuleInverseImageComp`, read at the
uncomposed source `g^*(f^*M)` through
`AlgebraicGeometry.Space.chartModuleInverseImageCompApp`. -/
theorem chartModuleInverseImageCompApp_naturality {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V)
    {M N : Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2}
    (φ : M ⟶ N) :
    (chartModuleInverseImage B S hS X g).map ((chartModuleInverseImage B S hS X f).map φ) ≫
        chartModuleInverseImageCompApp B S hS X f g N =
      chartModuleInverseImageCompApp B S hS X f g M ≫
        (chartModuleInverseImage B S hS X (g ≫ f)).map φ :=
  (chartModuleInverseImageComp B S hS X f g).hom.naturality φ

/-! ### Slice-indexed glueing data for modules, read chartwise -/

/-- A slice-indexed glueing datum for modules, read chartwise: the modules on the slices
`X_étale/U`, read as modules on the small étale sites of the charts through the comparison
equivalence `AlgebraicGeometry.Space.chartModuleSliceEquiv`, form a chartwise glueing datum. -/
def sliceToChartModuleGlueingData
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X)) :
    ChartModuleGlueingData B S hS X :=
  ⟨sliceToChartModuleFamily B S hS X D,
    sliceToChartModuleTransitionFamily B S hS X D,
    isChartModuleCocycle_sliceToChartModuleTransitionFamily_unconditional B S hS X D⟩

/-- The chartwise reading of slice-indexed glueing data for modules, as a functor to chartwise
glueing data. -/
def sliceToChartModuleFunctor :
    SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X) ⥤
      ChartModuleGlueingData B S hS X where
  obj D := sliceToChartModuleGlueingData B S hS X D
  map {D E} α :=
    { app := fun U ↦ (chartModuleSliceReindex B S hS X U).map
        (SiteGlueing.ModuleGlueingData.Hom.app α U)
      w := fun {V U} f ↦ by
        have hmix : (chartModuleSliceReindex B S hS X V).map
                ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).map
                  (SiteGlueing.ModuleGlueingData.Hom.app α U)) ≫
              (chartModuleSliceReindex B S hS X V).map (E.iso f).hom =
            (chartModuleSliceReindex B S hS X V).map (D.iso f).hom ≫
              (chartModuleSliceReindex B S hS X V).map
                (SiteGlueing.ModuleGlueingData.Hom.app α V) := by
          rw [← Functor.map_comp, ← Functor.map_comp,
            SiteGlueing.ModuleGlueingData.Hom.w α f]
        exact comp_naturality_rearrange
          ((chartModuleInverseImage B S hS X f).map
            ((chartModuleSliceReindex B S hS X U).map
              (SiteGlueing.ModuleGlueingData.Hom.app α U)))
          (chartModuleInverseImageSliceApp B S hS X f (E.sheaf U))
          ((chartModuleSliceReindex B S hS X V).map (E.iso f).hom)
          ((chartModuleSliceReindex B S hS X V).map (D.iso f).hom)
          ((chartModuleSliceReindex B S hS X V).map
            (SiteGlueing.ModuleGlueingData.Hom.app α V))
          (chartModuleInverseImageSliceApp_naturality B S hS X f
            (SiteGlueing.ModuleGlueingData.Hom.app α U)) hmix }
  map_id D := ChartModuleGlueingData.hom_ext B S hS X fun U ↦
    (chartModuleSliceReindex B S hS X U).map_id (D.sheaf U)
  map_comp α β := ChartModuleGlueingData.hom_ext B S hS X fun U ↦
    (chartModuleSliceReindex B S hS X U).map_comp
      (SiteGlueing.ModuleGlueingData.Hom.app α _)
      (SiteGlueing.ModuleGlueingData.Hom.app β _)

/-- The chartwise reading of a slice-indexed glueing datum for modules carries the module on a
slice to the module on the chart, by `rfl`. -/
theorem sliceToChartModuleFunctor_obj_sheaf
    (D : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X))
    (U : SmallEtale B S hS X.1) :
    ((sliceToChartModuleFunctor B S hS X).obj D).sheaf U =
      (chartModuleSliceReindex B S hS X U).obj (D.sheaf U) := rfl

/-- On morphisms, the chartwise reading of a slice-indexed glueing datum for modules is
`AlgebraicGeometry.Space.chartModuleSliceReindex` chart by chart, by `rfl`. -/
theorem sliceToChartModuleFunctor_map_app
    {D E : SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X)} (α : D ⟶ E)
    (U : SmallEtale B S hS X.1) :
    ChartModuleGlueingData.Hom.app ((sliceToChartModuleFunctor B S hS X).map α) U =
      (chartModuleSliceReindex B S hS X U).map
        (SiteGlueing.ModuleGlueingData.Hom.app α U) := rfl

/-! ### Full faithfulness -/

/-- The chartwise reading of slice-indexed glueing data for modules is faithful. -/
instance sliceToChartModuleFunctor_faithful :
    (sliceToChartModuleFunctor B S hS X).Faithful where
  map_injective {D E} {_ _} h :=
    SiteGlueing.ModuleGlueingData.hom_ext (structureRingSheaf B S hS X) fun U ↦
      (chartModuleSliceReindex B S hS X U).map_injective
        (congrArg (fun γ : (sliceToChartModuleFunctor B S hS X).obj D ⟶
          (sliceToChartModuleFunctor B S hS X).obj E ↦
            ChartModuleGlueingData.Hom.app γ U) h)

/-- The chartwise reading of slice-indexed glueing data for modules is full. -/
instance sliceToChartModuleFunctor_full : (sliceToChartModuleFunctor B S hS X).Full where
  map_surjective {D E} γ := by
    choose ap hap using fun U : SmallEtale B S hS X.1 ↦
      (chartModuleSliceReindex B S hS X U).map_surjective
        (ChartModuleGlueingData.Hom.app γ U)
    refine ⟨{ app := ap, w := fun {V U} f ↦ ?_ },
      ChartModuleGlueingData.hom_ext B S hS X hap⟩
    refine (chartModuleSliceReindex B S hS X V).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    refine (Iso.cancel_iso_hom_left
      (chartModuleInverseImageSliceIsoApp B S hS X f (D.sheaf U)) _ _).mp ?_
    refine comp_cancel_rearrange
      ((chartModuleInverseImage B S hS X f).map (ChartModuleGlueingData.Hom.app γ U))
      (chartModuleInverseImageSliceApp B S hS X f (E.sheaf U))
      ((chartModuleSliceReindex B S hS X V).map (E.iso f).hom)
      (chartModuleInverseImageSliceApp B S hS X f (D.sheaf U))
      ((chartModuleSliceReindex B S hS X V).map
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).map (ap U)))
      ((chartModuleSliceReindex B S hS X V).map (D.iso f).hom)
      ((chartModuleSliceReindex B S hS X V).map (ap V)) ?_ ?_
    · rw [← hap U]
      exact chartModuleInverseImageSliceApp_naturality B S hS X f (ap U)
    · rw [hap V]
      exact ChartModuleGlueingData.Hom.w γ f

/-! ### The canonical chartwise description is the canonical slice-indexed one -/

/-- The comparison of the canonical chartwise glueing datum of a module with the chartwise
reading of its canonical slice-indexed glueing datum, whose component at a chart is
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`. -/
def chartModuleGlueingFunctorHom (F : Modules.{u, u} B S hS X.1 X.2) :
    (chartModuleGlueingFunctor B S hS X).obj F ⟶
      (sliceToChartModuleFunctor B S hS X).obj
        ((SiteGlueing.canonicalModuleFunctor (structureRingSheaf B S hS X)).obj F) where
  app U := (chartModuleRestrictionSliceIso B S hS X U).hom.app F
  w f := chartModuleRestrictionSliceIso_comp_unconditional B S hS X f F

/-- The comparison `chartModuleGlueingFunctorHom` of the chartwise glueing datum of a module with
the chartwise reading of its slice-indexed glueing datum is an isomorphism. -/
instance isIso_chartModuleGlueingFunctorHom (F : Modules.{u, u} B S hS X.1 X.2) :
    IsIso (chartModuleGlueingFunctorHom B S hS X F) :=
  ChartModuleGlueingData.isIso_of_isIso_app B S hS X _ fun U ↦
    inferInstanceAs (IsIso ((chartModuleRestrictionSliceIso B S hS X U).app F).hom)

/-- The canonical chartwise description of modules is the canonical slice-indexed description,
read chartwise. Its component at a module is `chartModuleGlueingFunctorHom`, built from
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`. -/
def chartModuleGlueingFunctorIso :
    chartModuleGlueingFunctor B S hS X ≅
      SiteGlueing.canonicalModuleFunctor (structureRingSheaf B S hS X) ⋙
        sliceToChartModuleFunctor B S hS X :=
  NatIso.ofComponents (fun F ↦ asIso (chartModuleGlueingFunctorHom B S hS X F))
    fun ψ ↦ ChartModuleGlueingData.hom_ext B S hS X fun U ↦
      (chartModuleRestrictionSliceIso B S hS X U).hom.naturality ψ

/-! ### Chartwise glueing data for modules read on the slices -/

/-- The module on the slice `X_étale/U` attached to a chartwise glueing datum, by the
quasi-inverse of the comparison equivalence `AlgebraicGeometry.Space.chartModuleSliceEquiv`. -/
def chartToSliceModuleSheaf (D : ChartModuleGlueingData B S hS X) (U : SmallEtale B S hS X.1) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over U) :=
  (chartModuleSliceEquiv B S hS X U).inverse.obj (D.sheaf U)

/-- The counit of the comparison equivalence `AlgebraicGeometry.Space.chartModuleSliceEquiv` at a
chart module, with its source written out uncomposed: the chart module read on the slice and
back is the chart module again. -/
def chartModuleSliceCounitIsoApp (D : ChartModuleGlueingData B S hS X)
    (U : SmallEtale B S hS X.1) :
    (chartModuleSliceReindex B S hS X U).obj (chartToSliceModuleSheaf B S hS X D U) ≅
      D.sheaf U :=
  (chartModuleSliceEquiv B S hS X U).counitIso.app (D.sheaf U)

/-- The transition isomorphism of a chartwise glueing datum for modules, transported to the
slice modules and read back on the charts: the chart-to-slice dictionary, the counits of the
comparison equivalence `AlgebraicGeometry.Space.chartModuleSliceEquiv` at the two charts, and the
datum's own transition. -/
def chartToSliceModuleTransitionIso (D : ChartModuleGlueingData B S hS X)
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleSliceReindex B S hS X V).obj
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
          (chartToSliceModuleSheaf B S hS X D U)) ≅
      (chartModuleSliceReindex B S hS X V).obj (chartToSliceModuleSheaf B S hS X D V) :=
  (chartModuleInverseImageSliceIsoApp B S hS X f
        (chartToSliceModuleSheaf B S hS X D U)).symm ≪≫
    (chartModuleInverseImage B S hS X f).mapIso
        (chartModuleSliceCounitIsoApp B S hS X D U) ≪≫
      D.transition f ≪≫ (chartModuleSliceCounitIsoApp B S hS X D V).symm

/-- The transition isomorphism of the slice-indexed reading of a chartwise glueing datum for
modules: the preimage of `AlgebraicGeometry.Space.chartToSliceModuleTransitionIso` under the
fully faithful functor `AlgebraicGeometry.Space.chartModuleSliceReindex`. -/
def chartToSliceModuleTransition (D : ChartModuleGlueingData B S hS X)
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
        (chartToSliceModuleSheaf B S hS X D U) ≅ chartToSliceModuleSheaf B S hS X D V :=
  (chartModuleSliceReindex B S hS X V).preimageIso
    (chartToSliceModuleTransitionIso B S hS X D f)

/-- The functor `AlgebraicGeometry.Space.chartModuleSliceReindex` carries
`AlgebraicGeometry.Space.chartToSliceModuleTransition` back to
`AlgebraicGeometry.Space.chartToSliceModuleTransitionIso`. -/
theorem map_chartToSliceModuleTransition_hom (D : ChartModuleGlueingData B S hS X)
    {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartModuleSliceReindex B S hS X V).map
        (chartToSliceModuleTransition B S hS X D f).hom =
      (chartToSliceModuleTransitionIso B S hS X D f).hom := by
  rw [chartToSliceModuleTransition, Functor.preimageIso_hom, Functor.map_preimage]

/-- A chartwise glueing datum for modules, read on the slices `X_étale/U`. -/
def chartToSliceModuleGlueingData (D : ChartModuleGlueingData B S hS X) :
    SiteGlueing.ModuleGlueingData.{u} (structureRingSheaf B S hS X) where
  sheaf U := chartToSliceModuleSheaf B S hS X D U
  iso f := chartToSliceModuleTransition B S hS X D f
  comp {W V U} f g := by
    have hnat : (chartModuleInverseImage B S hS X g).map
            (chartToSliceModuleTransitionIso B S hS X D f).hom ≫
          chartModuleInverseImageSliceApp B S hS X g
            (chartToSliceModuleSheaf B S hS X D V) =
        chartModuleInverseImageSliceApp B S hS X g
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
              (chartToSliceModuleSheaf B S hS X D U)) ≫
          (chartModuleSliceReindex B S hS X W).map
            ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map
              (chartToSliceModuleTransition B S hS X D f).hom) := by
      rw [← map_chartToSliceModuleTransition_hom B S hS X D f]
      exact chartModuleInverseImageSliceApp_naturality B S hS X g
        (chartToSliceModuleTransition B S hS X D f).hom
    have hpgεf : (chartModuleInverseImage B S hS X g).map
          (chartToSliceModuleTransitionIso B S hS X D f).hom =
        (chartModuleInverseImage B S hS X g).map
            ((chartModuleInverseImageSliceIsoApp B S hS X f
              (chartToSliceModuleSheaf B S hS X D U)).inv) ≫
          (chartModuleInverseImage B S hS X g).map
              ((chartModuleInverseImage B S hS X f).map
                (chartModuleSliceCounitIsoApp B S hS X D U).hom) ≫
            (chartModuleInverseImage B S hS X g).map (D.transition f).hom ≫
              (chartModuleInverseImage B S hS X g).map
                (chartModuleSliceCounitIsoApp B S hS X D V).inv := by
      simp only [← Functor.map_comp]
      rfl
    have hcV : (chartModuleInverseImage B S hS X g).map
          (chartModuleSliceCounitIsoApp B S hS X D V).inv ≫
        (chartModuleInverseImage B S hS X g).map
          (chartModuleSliceCounitIsoApp B S hS X D V).hom = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id,
        (chartModuleInverseImage B S hS X g).map_id]
    have hpga : (chartModuleInverseImage B S hS X g).map
          ((chartModuleInverseImageSliceIsoApp B S hS X f
            (chartToSliceModuleSheaf B S hS X D U)).inv) ≫
        (chartModuleInverseImage B S hS X g).map
          (chartModuleInverseImageSliceApp B S hS X f
            (chartToSliceModuleSheaf B S hS X D U)) = 𝟙 _ := by
      rw [← Functor.map_comp,
        show (chartModuleInverseImageSliceIsoApp B S hS X f
                (chartToSliceModuleSheaf B S hS X D U)).inv ≫
              chartModuleInverseImageSliceApp B S hS X f
                (chartToSliceModuleSheaf B S hS X D U) = 𝟙 _ from
          (chartModuleInverseImageSliceIsoApp B S hS X f
            (chartToSliceModuleSheaf B S hS X D U)).inv_hom_id,
        (chartModuleInverseImage B S hS X g).map_id]
    have heh : (chartModuleSliceReindex B S hS X W).map
          (overMapCompInvApp B S hS X f g (chartToSliceModuleSheaf B S hS X D U)) ≫
        (chartModuleSliceReindex B S hS X W).map
          ((SiteGlueing.overMapComp (structureRingSheaf B S hS X) f g).hom.app
            (chartToSliceModuleSheaf B S hS X D U)) = 𝟙 _ := by
      rw [← Functor.map_comp,
        show overMapCompInvApp B S hS X f g (chartToSliceModuleSheaf B S hS X D U) ≫
              (SiteGlueing.overMapComp (structureRingSheaf B S hS X) f g).hom.app
                (chartToSliceModuleSheaf B S hS X D U) = 𝟙 _ from
          ((SiteGlueing.overMapComp (structureRingSheaf B S hS X) f g).app
            (chartToSliceModuleSheaf B S hS X D U)).inv_hom_id,
        (chartModuleSliceReindex B S hS X W).map_id]
    have hnatCIC : (chartModuleInverseImage B S hS X g).map
            ((chartModuleInverseImage B S hS X f).map
              (chartModuleSliceCounitIsoApp B S hS X D U).hom) ≫
          chartModuleInverseImageCompApp B S hS X f g (D.sheaf U) =
        chartModuleInverseImageCompApp B S hS X f g
            ((chartModuleSliceReindex B S hS X U).obj
              (chartToSliceModuleSheaf B S hS X D U)) ≫
          (chartModuleInverseImage B S hS X (g ≫ f)).map
            (chartModuleSliceCounitIsoApp B S hS X D U).hom :=
      chartModuleInverseImageCompApp_naturality B S hS X f g _
    have hεg : (chartModuleSliceReindex B S hS X W).map
          (chartToSliceModuleTransition B S hS X D g).hom =
        (chartModuleInverseImageSliceIsoApp B S hS X g
              (chartToSliceModuleSheaf B S hS X D V)).inv ≫
          (chartModuleInverseImage B S hS X g).map
              (chartModuleSliceCounitIsoApp B S hS X D V).hom ≫
            (D.transition g).hom ≫
              (chartModuleSliceCounitIsoApp B S hS X D W).inv :=
      map_chartToSliceModuleTransition_hom B S hS X D g
    have hεgf : (chartModuleSliceReindex B S hS X W).map
          (chartToSliceModuleTransition B S hS X D (g ≫ f)).hom =
        (chartModuleInverseImageSliceIsoApp B S hS X (g ≫ f)
              (chartToSliceModuleSheaf B S hS X D U)).inv ≫
          (chartModuleInverseImage B S hS X (g ≫ f)).map
              (chartModuleSliceCounitIsoApp B S hS X D U).hom ≫
            (D.transition (g ≫ f)).hom ≫
              (chartModuleSliceCounitIsoApp B S hS X D W).inv :=
      map_chartToSliceModuleTransition_hom B S hS X D (g ≫ f)
    refine (chartModuleSliceReindex B S hS X W).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    exact cocycle_transport
      ((chartModuleSliceReindex B S hS X W).map
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) g).map
          (chartToSliceModuleTransition B S hS X D f).hom))
      ((chartModuleSliceReindex B S hS X W).map
        ((SiteGlueing.overMapComp (structureRingSheaf B S hS X) f g).hom.app
          (chartToSliceModuleSheaf B S hS X D U)))
      ((chartModuleSliceReindex B S hS X W).map
        (chartToSliceModuleTransition B S hS X D g).hom)
      ((chartModuleSliceReindex B S hS X W).map
        (chartToSliceModuleTransition B S hS X D (g ≫ f)).hom)
      (chartModuleInverseImageSliceApp B S hS X g
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
          (chartToSliceModuleSheaf B S hS X D U)))
      ((chartModuleInverseImageSliceIsoApp B S hS X g
        ((SheafOfModules.overMap (structureRingSheaf B S hS X) f).obj
          (chartToSliceModuleSheaf B S hS X D U))).inv)
      ((chartModuleInverseImage B S hS X g).map
        (chartToSliceModuleTransitionIso B S hS X D f).hom)
      (chartModuleInverseImageSliceApp B S hS X g
        (chartToSliceModuleSheaf B S hS X D V))
      ((chartModuleInverseImageSliceIsoApp B S hS X g
        (chartToSliceModuleSheaf B S hS X D V)).inv)
      ((chartModuleInverseImage B S hS X g).map
        (chartModuleSliceCounitIsoApp B S hS X D V).hom)
      ((chartModuleInverseImage B S hS X g).map
        (chartModuleSliceCounitIsoApp B S hS X D V).inv)
      ((D.transition g).hom)
      ((chartModuleSliceCounitIsoApp B S hS X D W).inv)
      ((chartModuleInverseImage B S hS X g).map
        ((chartModuleInverseImageSliceIsoApp B S hS X f
          (chartToSliceModuleSheaf B S hS X D U)).inv))
      ((chartModuleInverseImage B S hS X g).map
        (chartModuleInverseImageSliceApp B S hS X f
          (chartToSliceModuleSheaf B S hS X D U)))
      ((chartModuleInverseImage B S hS X g).map
        ((chartModuleInverseImage B S hS X f).map
          (chartModuleSliceCounitIsoApp B S hS X D U).hom))
      ((chartModuleInverseImage B S hS X g).map (D.transition f).hom)
      (chartModuleInverseImageCompApp B S hS X f g (D.sheaf U))
      ((D.transition (g ≫ f)).hom)
      (chartModuleInverseImageCompApp B S hS X f g
        ((chartModuleSliceReindex B S hS X U).obj
          (chartToSliceModuleSheaf B S hS X D U)))
      ((chartModuleInverseImage B S hS X (g ≫ f)).map
        (chartModuleSliceCounitIsoApp B S hS X D U).hom)
      (chartModuleInverseImageSliceApp B S hS X (g ≫ f)
        (chartToSliceModuleSheaf B S hS X D U))
      ((chartModuleInverseImageSliceIsoApp B S hS X (g ≫ f)
        (chartToSliceModuleSheaf B S hS X D U)).inv)
      ((chartModuleSliceReindex B S hS X W).map
        (overMapCompInvApp B S hS X f g (chartToSliceModuleSheaf B S hS X D U)))
      (Iso.inv_hom_id _) hnat hεg (Iso.hom_inv_id _) hpgεf hcV
      (D.transition_comp f g) hnatCIC
      (chartModuleInverseImageSliceApp_comp_unconditional B S hS X f g
        (chartToSliceModuleSheaf B S hS X D U))
      hpga heh (Iso.hom_inv_id _) hεgf

/-- The comparison from the chartwise reading of the slice-indexed reading of a chartwise
glueing datum for modules back to the datum: the counit of the comparison equivalence
`AlgebraicGeometry.Space.chartModuleSliceEquiv` at every chart. -/
def sliceToChartOfChartToSliceModuleHom (D : ChartModuleGlueingData B S hS X) :
    (sliceToChartModuleFunctor B S hS X).obj (chartToSliceModuleGlueingData B S hS X D) ⟶ D where
  app U := (chartModuleSliceCounitIsoApp B S hS X D U).hom
  w {V U} f := by
    have h1 : (((sliceToChartModuleFunctor B S hS X).obj
          (chartToSliceModuleGlueingData B S hS X D)).transition f).hom =
        chartModuleInverseImageSliceApp B S hS X f
            (chartToSliceModuleSheaf B S hS X D U) ≫
          (chartModuleSliceReindex B S hS X V).map
            (chartToSliceModuleTransition B S hS X D f).hom := rfl
    rw [h1, map_chartToSliceModuleTransition_hom B S hS X D f,
      show (chartToSliceModuleTransitionIso B S hS X D f).hom =
        (chartModuleInverseImageSliceIsoApp B S hS X f
              (chartToSliceModuleSheaf B S hS X D U)).inv ≫
          (chartModuleInverseImage B S hS X f).map
              (chartModuleSliceCounitIsoApp B S hS X D U).hom ≫
            (D.transition f).hom ≫
              (chartModuleSliceCounitIsoApp B S hS X D V).inv from rfl]
    exact (comp_sandwich_cancel
      (chartModuleInverseImageSliceApp B S hS X f (chartToSliceModuleSheaf B S hS X D U))
      ((chartModuleInverseImageSliceIsoApp B S hS X f
        (chartToSliceModuleSheaf B S hS X D U)).inv)
      ((chartModuleInverseImage B S hS X f).map
        (chartModuleSliceCounitIsoApp B S hS X D U).hom)
      ((D.transition f).hom)
      ((chartModuleSliceCounitIsoApp B S hS X D V).inv)
      ((chartModuleSliceCounitIsoApp B S hS X D V).hom)
      (Iso.hom_inv_id _) (Iso.inv_hom_id _)).symm

/-- The comparison `sliceToChartOfChartToSliceModuleHom` from the chartwise reading of the
slice-indexed reading of a chartwise glueing datum back to the datum is an isomorphism. -/
instance isIso_sliceToChartOfChartToSliceModuleHom (D : ChartModuleGlueingData B S hS X) :
    IsIso (sliceToChartOfChartToSliceModuleHom B S hS X D) :=
  ChartModuleGlueingData.isIso_of_isIso_app B S hS X _ fun U ↦
    inferInstanceAs
      (IsIso (chartModuleSliceCounitIsoApp B S hS X D U).hom)

/-- The chartwise reading of slice-indexed glueing data for modules is essentially surjective:
every chartwise glueing datum is the chartwise reading of its own slice-indexed reading. -/
instance sliceToChartModuleFunctor_essSurj :
    (sliceToChartModuleFunctor B S hS X).EssSurj where
  mem_essImage D :=
    ⟨chartToSliceModuleGlueingData B S hS X D,
      ⟨asIso (sliceToChartOfChartToSliceModuleHom B S hS X D)⟩⟩

/-- The chartwise reading `sliceToChartModuleFunctor` of slice-indexed glueing data for modules
is an equivalence of categories. -/
instance sliceToChartModuleFunctor_isEquivalence :
    (sliceToChartModuleFunctor B S hS X).IsEquivalence where

/-- A sheaf of `𝒪_X`-modules on the small étale site of an algebraic space `X` is the same thing
as a family of `𝒪_U`-modules `F_U` on the small étale sites of the étale scheme charts `U` of
`X`, together with isomorphisms `c_f : f^*F_U ≅ F_V` for the morphisms `f : V ⟶ U` of charts
satisfying the cocycle condition `c_g ∘ g^*c_f = c_{g ≫ f}`: an equivalence of categories, given
by sending a module to the family of its restrictions to the charts. -/
@[stacks 03LY "the equivalence of modules with chartwise glueing data"]
def chartModuleGlueingEquivalence :
    Modules.{u, u} B S hS X.1 X.2 ≌ ChartModuleGlueingData B S hS X :=
  ((SiteGlueing.canonicalModuleEquivalence (structureRingSheaf B S hS X)).trans
      (sliceToChartModuleFunctor B S hS X).asEquivalence).changeFunctor
    (chartModuleGlueingFunctorIso B S hS X).symm

/-- The functor of `AlgebraicGeometry.Space.chartModuleGlueingEquivalence` is the canonical
chartwise description: it sends a module to the family of its restrictions to the étale scheme
charts, by `rfl`. -/
theorem chartModuleGlueingEquivalence_functor :
    (chartModuleGlueingEquivalence B S hS X).functor =
      chartModuleGlueingFunctor B S hS X := rfl

/-- The canonical chartwise description of `𝒪_X`-modules is an equivalence. -/
instance chartModuleGlueingFunctor_isEquivalence :
    (chartModuleGlueingFunctor B S hS X).IsEquivalence :=
  (chartModuleGlueingEquivalence B S hS X).isEquivalence_functor

end AlgebraicGeometry.Space

end

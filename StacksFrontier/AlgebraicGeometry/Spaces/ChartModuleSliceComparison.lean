module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleGlueing

/-!
# Restriction of modules to the charts is restriction to the slices

Let `X` be an algebraic space and `U` an étale scheme chart of `X`. Restriction of
`𝒪_X`-modules to the small étale site of `U` is restriction to the slice `X_étale/U`, read
through the comparison equivalence of Stacks 04M0, compatibly with the pullback of modules along
a morphism of charts; and restriction along that comparison equivalence is an equivalence of
categories of sheaves of modules.

## Main definitions

* `AlgebraicGeometry.Space.chartModuleSliceReindex`: modules on the slice of the small étale
  site of `X` at a chart, read as modules on the small étale site of that chart.

## Main results

* `AlgebraicGeometry.Space.chartModuleRestrictionSliceIso` and
  `AlgebraicGeometry.Space.chartModuleInverseImageSliceIso`: restriction of an `𝒪_X`-module to
  an étale scheme chart is restriction to the slice, and the chartwise pullback of modules along
  a morphism of charts is the slice pullback `SheafOfModules.overMap`, both read through the
  comparison equivalence of Stacks 04M0.
* `AlgebraicGeometry.Space.chartModuleSliceEquiv` and
  `AlgebraicGeometry.Space.isEquivalence_chartModuleSliceReindex`: restriction along the
  comparison functor of Stacks 04M0 is an equivalence on sheaves of modules.
* `AlgebraicGeometry.Space.chartPostcompRingMap_natTrans`: the comparison
  `AlgebraicGeometry.Space.chartLocalizationPostcompIso` of the two composite functors of sites
  carries one structure map to the other.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Modules on the slice of the small étale site of `X` at an étale scheme chart `U`, read as
modules on the small étale site of the chart through the comparison equivalence of
Stacks 04M0. -/
noncomputable def chartModuleSliceReindex (U : SmallEtale B S hS X.1) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over U) ⥤
      Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2 :=
  @SheafOfModules.pushforward _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.chartLocalization B S hS X.1 U)
    (structureRingSheaf B S hS (chartSpace B S hS X U))
    ((structureRingSheaf B S hS X).over U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    (𝟙 _)

/-- The composite of the comparison functor of Stacks 04M0 with the slice projection is
continuous. -/
instance isContinuous_chartLocalization_comp_forget (U : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (SmallEtale.topology B S hS X.1) :=
  smallEtalePostcomp_isContinuous B S hS (chartToSpace B S hS X U)
    (isEtale_chartToSpace B S hS X U)

/-- The structure map of the comparison of Stacks 04M0 at a chart: the two structure sheaves
agree, so the structure map is the identity. -/
noncomputable abbrev chartSliceRingMap (U : SmallEtale B S hS X.1) :
    structureRingSheaf B S hS (chartSpace B S hS X U) ⟶
      ((SmallEtale.chartLocalization B S hS X.1 U).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        ((SmallEtale.topology B S hS X.1).over U)).obj
          ((structureRingSheaf B S hS X).over U) :=
  𝟙 _

/-- The structure map of restriction to the slice at a chart: the restriction of `𝒪_X` to the
slice is the structure sheaf of the slice, so the structure map is the identity. -/
noncomputable abbrev sliceRingMap (U : SmallEtale B S hS X.1) :
    (structureRingSheaf B S hS X).over U ⟶
      ((Over.forget U).sheafPushforwardContinuous RingCat.{u}
        ((SmallEtale.topology B S hS X.1).over U)
        (SmallEtale.topology B S hS X.1)).obj (structureRingSheaf B S hS X) :=
  𝟙 _

/-- The composite structure map of the two-step restriction is the identity. -/
theorem chartSliceRingMap_comp (U : SmallEtale B S hS X.1) :
    chartSliceRingMap B S hS X U ≫
        ((SmallEtale.chartLocalization B S hS X.1 U).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
          ((SmallEtale.topology B S hS X.1).over U)).map (sliceRingMap B S hS X U) =
      𝟙 _ :=
  (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)

/-- Restriction of an `𝒪_X`-module to an étale scheme chart `U`, the pullback of modules of
Stacks 03LU along the structure morphism of the chart, is restriction to the slice `X_étale/U`,
read through the comparison equivalence of Stacks 04M0. -/
noncomputable def chartModuleRestrictionSliceIso (U : SmallEtale B S hS X.1) :
    chartModuleRestriction B S hS X U ≅
      SheafOfModules.overFunctor (structureRingSheaf B S hS X) U ⋙
        chartModuleSliceReindex B S hS X U :=
  modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U) ≪≫
    (@SheafOfModules.pushforwardComp
        (SmallEtale B S hS (chartSpace B S hS X U).1) _ (Over U) _
        (SmallEtale B S hS X.1) _
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        ((SmallEtale.topology B S hS X.1).over U)
        (SmallEtale.chartLocalization B S hS X.1 U)
        (structureRingSheaf B S hS (chartSpace B S hS X U))
        ((structureRingSheaf B S hS X).over U)
        (isContinuous_chartLocalization_chartSpace B S hS X U)
        (chartSliceRingMap B S hS X U)
        (SmallEtale.topology B S hS X.1) (Over.forget U)
        (structureRingSheaf B S hS X) inferInstance (sliceRingMap B S hS X U) ≪≫
      @SheafOfModules.pushforwardCongr
        (SmallEtale B S hS (chartSpace B S hS X U).1) _ (SmallEtale B S hS X.1) _
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        (SmallEtale.topology B S hS X.1)
        (SmallEtale.chartLocalization B S hS X.1 U ⋙ Over.forget U)
        (structureRingSheaf B S hS (chartSpace B S hS X U))
        (structureRingSheaf B S hS X)
        (isContinuous_chartLocalization_comp_forget B S hS X U) _ _
        (chartSliceRingMap_comp B S hS X U)).symm

/-! ### The chartwise pullback of modules is the slice pullback -/

/-- The composite of postcomposition along a morphism of charts with the comparison functor of
Stacks 04M0 at the larger chart is continuous. -/
instance isContinuous_smallEtalePostcomp_comp_chartLocalization
    {V U : SmallEtale B S hS X.1} {f : V ⟶ U} :
    (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
  @Functor.isContinuous_comp _ _ _ _ _ _
    (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f))
    (SmallEtale.chartLocalization B S hS X.1 U)
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    ((SmallEtale.topology B S hS X.1).over U) inferInstance
    (isContinuous_chartLocalization_chartSpace B S hS X U)

/-- The composite of the comparison functor of Stacks 04M0 at the smaller chart with the slice
functor along a morphism of charts is continuous. -/
instance isContinuous_chartLocalization_comp_overMap
    {V U : SmallEtale B S hS X.1} {f : V ⟶ U} :
    (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f).IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
  Functor.isContinuous_comp _ _ _ ((SmallEtale.topology B S hS X.1).over V) _

/-- The structure map of the chartwise étale restriction: postcomposition leaves the underlying
scheme of a chart unchanged, so the structure map is the identity. -/
noncomputable abbrev chartMapRingMap {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    structureRingSheaf B S hS (chartSpace B S hS X V) ⟶
      ((smallEtalePostcomp B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)).obj
          (structureRingSheaf B S hS (chartSpace B S hS X U)) :=
  𝟙 _

/-- The structure map along postcomposition followed by the comparison of Stacks 04M0 at the
larger chart. -/
noncomputable abbrev chartPostcompRingMap {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    structureRingSheaf B S hS (chartSpace B S hS X V) ⟶
      ((smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
          SmallEtale.chartLocalization B S hS X.1 U).sheafPushforwardContinuous
        RingCat.{u} (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U)).obj
          ((structureRingSheaf B S hS X).over U) :=
  𝟙 _

/-- The structure map along the comparison of Stacks 04M0 at the smaller chart followed by the
slice functor. -/
noncomputable abbrev chartOverMapRingMap {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    structureRingSheaf B S hS (chartSpace B S hS X V) ⟶
      ((SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f).sheafPushforwardContinuous
        RingCat.{u} (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        ((SmallEtale.topology B S hS X.1).over U)).obj
          ((structureRingSheaf B S hS X).over U) :=
  𝟙 _

/-- The composite structure map of chartwise étale restriction after the comparison of
Stacks 04M0 is the identity. -/
theorem chartMapRingMap_comp {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartMapRingMap B S hS X f ≫
        ((smallEtalePostcomp B S hS (chartMap B S hS X f)
          (isEtale_chartMap B S hS X f)).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          (SmallEtale.topology B S hS (chartSpace B S hS X U).1)).map
            (chartSliceRingMap B S hS X U) =
      chartPostcompRingMap B S hS X f :=
  (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)

/-- The composite structure map of the slice pullback after the comparison of Stacks 04M0 is
the identity. -/
theorem chartOverMapRingMap_comp {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartSliceRingMap B S hS X V ≫
        ((SmallEtale.chartLocalization B S hS X.1 V).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          ((SmallEtale.topology B S hS X.1).over V)).map
            (Sheaf.pushforwardOverMapIso (structureRingSheaf B S hS X) f).inv =
      chartOverMapRingMap B S hS X f := by
  apply Sheaf.hom_ext
  ext A
  rfl

/-- The two structure maps agree across the comparison
`AlgebraicGeometry.Space.chartLocalizationPostcompIso` of the two composite functors of
sites. -/
theorem chartPostcompRingMap_natTrans {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartPostcompRingMap B S hS X f ≫
        (@Functor.sheafPushforwardContinuousNatTrans
          (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
          (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)
          (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
            SmallEtale.chartLocalization B S hS X.1 U)
          (chartLocalizationPostcompIso B S hS X f).inv RingCat.{u} _
          (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
          ((SmallEtale.topology B S hS X.1).over U)
          (isContinuous_chartLocalization_comp_overMap B S hS X)
          (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X)).app
            ((structureRingSheaf B S hS X).over U) =
      chartOverMapRingMap B S hS X f := by
  apply Sheaf.hom_ext
  ext A
  rfl

/-- The chartwise pullback of modules along a morphism `f : V ⟶ U` of étale scheme charts of `X`
is the slice pullback `SheafOfModules.overMap` along `f`, read through the comparison
equivalences of Stacks 04M0 at the two charts. -/
noncomputable def chartModuleInverseImageSliceIso {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartModuleSliceReindex B S hS X U ⋙ chartModuleInverseImage B S hS X f ≅
      SheafOfModules.overMap (structureRingSheaf B S hS X) f ⋙
        chartModuleSliceReindex B S hS X V :=
  Functor.isoWhiskerLeft (chartModuleSliceReindex B S hS X U)
      (modulePullbackIsoEtaleModulePullback B S hS (chartMap B S hS X f)
        (isEtale_chartMap B S hS X f)) ≪≫
    @SheafOfModules.pushforwardComp
      (SmallEtale B S hS (chartSpace B S hS X V).1) _
      (SmallEtale B S hS (chartSpace B S hS X U).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f))
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      (structureRingSheaf B S hS (chartSpace B S hS X U)) inferInstance
      (chartMapRingMap B S hS X f)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 U)
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_chartSpace B S hS X U)
      (chartSliceRingMap B S hS X U) ≪≫
    @SheafOfModules.pushforwardCongr
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X) _ _
      (chartMapRingMap_comp B S hS X f) ≪≫
    @SheafOfModules.pushforwardCongr₂
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)
      (smallEtalePostcomp B S hS (chartMap B S hS X f) (isEtale_chartMap B S hS X f) ⋙
        SmallEtale.chartLocalization B S hS X.1 U)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_comp_overMap B S hS X)
      (isContinuous_smallEtalePostcomp_comp_chartLocalization B S hS X)
      (chartPostcompRingMap B S hS X f) _ (chartLocalizationPostcompIso B S hS X f).symm
      (chartPostcompRingMap_natTrans B S hS X f) ≪≫
    (@SheafOfModules.pushforwardCongr
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.chartLocalization B S hS X.1 V ⋙ Over.map f)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over U)
      (isContinuous_chartLocalization_comp_overMap B S hS X) _ _
      (chartOverMapRingMap_comp B S hS X f)).symm ≪≫
    (@SheafOfModules.pushforwardComp
      (SmallEtale B S hS (chartSpace B S hS X V).1) _ (Over V) _ (Over U) _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over V)
      (SmallEtale.chartLocalization B S hS X.1 V)
      (structureRingSheaf B S hS (chartSpace B S hS X V))
      ((structureRingSheaf B S hS X).over V)
      (isContinuous_chartLocalization_chartSpace B S hS X V)
      (chartSliceRingMap B S hS X V)
      ((SmallEtale.topology B S hS X.1).over U) (Over.map f)
      ((structureRingSheaf B S hS X).over U) inferInstance
      (Sheaf.pushforwardOverMapIso (structureRingSheaf B S hS X) f).inv).symm

/-! ### The reindexing is an equivalence -/

/-- The inverse of the comparison equivalence of Stacks 04M0 is continuous. -/
instance isContinuous_chartLocalizationEquivalence_inverse_chartSpace (U : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.IsContinuous
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U)

/-- The structure map of the comparison of Stacks 04M0 read in the inverse direction: the
restriction of `𝒪_X` to the slice at a chart, pushed back along the inverse of the comparison
equivalence, receives a map from itself by the counit. -/
noncomputable def chartSliceRingMapInverse (U : SmallEtale B S hS X.1) :
    (structureRingSheaf B S hS X).over U ⟶
      ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.sheafPushforwardContinuous
        RingCat.{u} ((SmallEtale.topology B S hS X.1).over U)
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)).obj
          (structureRingSheaf B S hS (chartSpace B S hS X U)) :=
  ⟨Functor.whiskerRight
    (NatTrans.op (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).counit)
    ((structureRingSheaf B S hS X).over U).obj⟩

/-- Modules on the slice of the small étale site of `X` at an étale scheme chart `U` are
equivalent to modules on the small étale site of the chart, by restriction along the comparison
functor of Stacks 04M0. -/
noncomputable def chartModuleSliceEquiv (U : SmallEtale B S hS X.1) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over U) ≌
      Modules.{u, u} B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2 :=
  haveI : (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
    isContinuous_chartLocalization_chartSpace B S hS X U
  SheafOfModules.pushforwardPushforwardEquivalence
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (S := structureRingSheaf B S hS (chartSpace B S hS X U))
    (R := (structureRingSheaf B S hS X).over U)
    (chartSliceRingMap B S hS X U) (chartSliceRingMapInverse B S hS X U)
    (NatTrans.ext (funext fun _ => (Category.comp_id _).symm))
    (by
      apply NatTrans.ext
      funext V
      change ((structureRingSheaf B S hS X).over U).obj.map
            ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).counit.app
              ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.obj V.unop)).op ≫
          ((structureRingSheaf B S hS X).over U).obj.map
            ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.map
              ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).unit.app V.unop)).op =
        𝟙 _
      rw [← ((structureRingSheaf B S hS X).over U).obj.map_comp, ← op_comp,
        Equivalence.counit_app_functor, ← Functor.map_comp,
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).unitIso.hom_inv_id_app,
        CategoryTheory.Functor.map_id, op_id]
      exact ((structureRingSheaf B S hS X).over U).obj.map_id _)

/-- The functor of `AlgebraicGeometry.Space.chartModuleSliceEquiv` is the reindexing
`AlgebraicGeometry.Space.chartModuleSliceReindex`. -/
theorem chartModuleSliceEquiv_functor (U : SmallEtale B S hS X.1) :
    (chartModuleSliceEquiv B S hS X U).functor = chartModuleSliceReindex B S hS X U := rfl

/-- Reading modules on the slice at a chart as modules on the chart is an equivalence. -/
instance isEquivalence_chartModuleSliceReindex (U : SmallEtale B S hS X.1) :
    (chartModuleSliceReindex B S hS X U).IsEquivalence :=
  (chartModuleSliceEquiv B S hS X U).isEquivalence_functor


end AlgebraicGeometry.Space


end

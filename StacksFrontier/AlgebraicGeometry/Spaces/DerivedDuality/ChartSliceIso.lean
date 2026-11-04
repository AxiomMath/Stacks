module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartSlice

/-!
# The slice of the model of an algebraic space at an object isomorphic to a chart

`AlgebraicGeometry.Space.chartSliceEquiv` identifies the slice of the equi-universe model of the
small étale ringed site of an algebraic space `F` at an object `V` with the model of the small
étale site of the chart `h_U ⟶ F` underlying `V`. The chart underlying `V` is only determined up
to isomorphism by the choice of the small model; this file allows an arbitrary étale chart `c`
together with an isomorphism `i` from the chart underlying `V` to `c`.

## Main definitions

* `AlgebraicGeometry.Space.chartSliceEquivOfIso`: the equivalence of sites
  `(model of F)/V ≌ model of h_{U_c}`.
* `AlgebraicGeometry.Space.chartSliceModelRingMapOfIso`: its invertible structure map.
* `AlgebraicGeometry.Space.chartSliceModulesIsoOfIso`: restriction to the slice is étale pullback
  to `c` followed by transport.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

section Chart

variable (c : SmallEtale B S hS F)

/-- The object of the big fppf site underlying an étale chart. -/
abbrev etaleChartBase : BigFppfOver B S hS := (SmallEtale.toOver B S hS F).obj c

/-- The model of the small étale ringed site of the represented space of an étale chart. -/
abbrev etaleChartSite : RingedSite.{u, u, u} :=
  smallEtaleModelRingedSite B S hS (yoneda.obj (etaleChartBase B S hS F c))
    (isAlgebraicSpace_yoneda B S hS (etaleChartBase B S hS F c))

/-- An étale chart `h_U ⟶ F`, as a morphism of algebraic spaces. -/
abbrev etaleChartMap : (⟨yoneda.obj (etaleChartBase B S hS F c), isAlgebraicSpace_yoneda B S hS _⟩ :
    AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩ :=
  ObjectProperty.homMk c.obj.hom

/-- The morphism of algebraic spaces given by an étale chart is étale. -/
theorem etaleChartMap_isEtale : IsEtale B S hS (etaleChartMap B S hS F hF c).hom :=
  isEtale_of_presheaf_etale B S hS c.property

end Chart

variable (V : SmallEtaleModel B S hS F) (c : SmallEtale B S hS F) (i : chartObj B S hS F V ≅ c)

/-- The slice of the model of `F` at `V` is equivalent to the model of the small étale site of any
chart `c` isomorphic to the chart underlying `V`. -/
def chartSliceEquivOfIso :
    ((smallEtaleModelRingedSite B S hS F hF).over V).C ≌ (etaleChartSite B S hS F c).C :=
  (Over.postEquiv V (smallEtaleModelEquivalence B S hS F)).trans
    ((Over.mapIso i).trans
      ((SmallEtale.chartLocalizationEquivalence B S hS F c).symm.trans
        (smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).symm))

/-- `Over.map` along an isomorphism is a dense subsite inclusion. -/
instance overMapIso_functor_isDenseSubsite {C : Type*} [Category C] (J : GrothendieckTopology C)
    {X Y : C} (e : X ≅ Y) : (Over.mapIso e).functor.IsDenseSubsite (J.over X) (J.over Y) :=
  haveI : (Over.mapIso e).functor.IsCocontinuous (J.over X) (J.over Y) :=
    inferInstanceAs ((Over.map e.hom).IsCocontinuous _ _)
  haveI : (Over.mapIso e).inverse.IsCocontinuous (J.over Y) (J.over X) :=
    inferInstanceAs ((Over.map e.inv).IsCocontinuous _ _)
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ _

/-- The functor of `chartSliceEquivOfIso` is a dense subsite inclusion. -/
instance chartSliceEquivOfIso_functor_isDenseSubsite :
    (chartSliceEquivOfIso B S hS F hF V c i).functor.IsDenseSubsite
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (etaleChartSite B S hS F c).J := by
  have : (Over.postEquiv V (smallEtaleModelEquivalence B S hS F)).functor.IsDenseSubsite
      ((smallEtaleModelTopology B S hS F).over V)
      ((SmallEtale.topology B S hS F).over (chartObj B S hS F V)) :=
    inferInstanceAs
      ((Over.post (X := V) (smallEtaleModelEquivalence B S hS F).functor).IsDenseSubsite _ _)
  have : (SmallEtale.chartLocalizationEquivalence B S hS F c).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj (etaleChartBase B S hS F c)))
      ((SmallEtale.topology B S hS F).over c) :=
    SmallEtale.isDenseSubsite_chartLocalizationEquivalence_functor B S hS F c
  have : (SmallEtale.chartLocalizationEquivalence B S hS F c).symm.functor.IsDenseSubsite
      ((SmallEtale.topology B S hS F).over c)
      (SmallEtale.topology B S hS (yoneda.obj (etaleChartBase B S hS F c))) := inferInstance
  have : (smallEtaleModelEquivalence B S hS
      (yoneda.obj (etaleChartBase B S hS F c))).symm.functor.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj (etaleChartBase B S hS F c)))
      (smallEtaleModelTopology B S hS (yoneda.obj (etaleChartBase B S hS F c))) :=
    smallEtaleModelEquivalence_inverse_isDenseSubsite B S hS _
  have h₂ := Equivalence.isDenseSubsite_trans_functor
    (SmallEtale.chartLocalizationEquivalence B S hS F c).symm
    (smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).symm
    (JA := (SmallEtale.topology B S hS F).over c)
    (JB := SmallEtale.topology B S hS (yoneda.obj (etaleChartBase B S hS F c)))
    (JC := smallEtaleModelTopology B S hS (yoneda.obj (etaleChartBase B S hS F c)))
  have h₃ := @Equivalence.isDenseSubsite_trans_functor _ _ _ _ _ _
    ((SmallEtale.topology B S hS F).over (chartObj B S hS F V))
    ((SmallEtale.topology B S hS F).over c)
    (smallEtaleModelTopology B S hS (yoneda.obj (etaleChartBase B S hS F c))) (Over.mapIso i) _
    (overMapIso_functor_isDenseSubsite _ i) h₂
  exact @Equivalence.isDenseSubsite_trans_functor _ _ _ _ _ _
    ((smallEtaleModelTopology B S hS F).over V)
    ((SmallEtale.topology B S hS F).over (chartObj B S hS F V))
    (smallEtaleModelTopology B S hS (yoneda.obj (etaleChartBase B S hS F c))) _ _ inferInstance h₃

/-- The functor of `chartSliceEquivOfIso` is continuous. -/
instance chartSliceEquivOfIso_functor_isContinuous :
    (chartSliceEquivOfIso B S hS F hF V c i).functor.IsContinuous
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (etaleChartSite B S hS F c).J :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (chartSliceEquivOfIso_functor_isDenseSubsite B S hS F hF V c i)

/-- The inverse of `chartSliceEquivOfIso` is a dense subsite inclusion. -/
instance chartSliceEquivOfIso_inverse_isDenseSubsite :
    (chartSliceEquivOfIso B S hS F hF V c i).inverse.IsDenseSubsite
      (etaleChartSite B S hS F c).J ((smallEtaleModelRingedSite B S hS F hF).over V).J :=
  haveI : (chartSliceEquivOfIso B S hS F hF V c i).symm.inverse.IsDenseSubsite
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (etaleChartSite B S hS F c).J :=
    chartSliceEquivOfIso_functor_isDenseSubsite B S hS F hF V c i
  inferInstanceAs ((chartSliceEquivOfIso B S hS F hF V c i).symm.functor.IsDenseSubsite _ _)

/-- The inverse of `chartSliceEquivOfIso` is continuous. -/
instance chartSliceEquivOfIso_inverse_isContinuous :
    (chartSliceEquivOfIso B S hS F hF V c i).inverse.IsContinuous
      (etaleChartSite B S hS F c).J ((smallEtaleModelRingedSite B S hS F hF).over V).J :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (chartSliceEquivOfIso_inverse_isDenseSubsite B S hS F hF V c i)

/-- The chart equivalence followed by the model equivalence of the chart and postcomposition with
the chart. -/
def sliceChartProjOfIso :
    ((smallEtaleModelRingedSite B S hS F hF).over V).C ⥤ SmallEtale B S hS F :=
  (chartSliceEquivOfIso B S hS F hF V c i).functor ⋙
    (smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).functor ⋙
      smallEtalePostcomp B S hS (etaleChartMap B S hS F hF c) (etaleChartMap_isEtale B S hS F hF c)

/-- The two functors from the slice of the model at `V` to the small étale site of `F`: the slice
projection followed by the model equivalence, and the chart equivalence followed by the model
equivalence of the chart and postcomposition with the chart, are isomorphic. -/
def chartSliceFunctorIsoOfIso :
    (chartSliceEquivOfIso B S hS F hF V c i).functor ⋙
        (smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).functor ⋙
          smallEtalePostcomp B S hS (etaleChartMap B S hS F hF c)
            (etaleChartMap_isEtale B S hS F hF c) ≅
      Over.forget V ⋙ (smallEtaleModelEquivalence B S hS F).functor :=
  Functor.isoWhiskerLeft
      (Over.post (X := V) (smallEtaleModelEquivalence B S hS F).functor ⋙ Over.map i.hom ⋙
        SmallEtale.chartLocalizationInverse B S hS F c)
      (Functor.isoWhiskerRight
        (smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).counitIso
        (smallEtalePostcomp B S hS (etaleChartMap B S hS F hF c)
          (etaleChartMap_isEtale B S hS F hF c))) ≪≫
    Functor.isoWhiskerLeft (Over.post (X := V) (smallEtaleModelEquivalence B S hS F).functor ⋙
        Over.map i.hom)
      (Functor.isoWhiskerRight
        (SmallEtale.chartLocalizationCounitIso B S hS F c)
        (Over.forget c)) ≪≫
    Iso.refl _

/-- The functor `sliceChartProjOfIso` is continuous. -/
instance sliceChartProjOfIso_isContinuous :
    (sliceChartProjOfIso B S hS F hF V c i).IsContinuous
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (smallEtaleRingedSite B S hS F hF).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ (etaleChartSite B S hS F c).J _
    (chartSliceEquivOfIso_functor_isContinuous B S hS F hF V c i)
    (@Functor.isContinuous_comp _ _ _ _ _ _ _ _ _
      (smallEtaleRingedSite B S hS (yoneda.obj (etaleChartBase B S hS F c))
        (isAlgebraicSpace_yoneda B S hS _)).J _
      (smallEtaleModelRingedSite_functor_isContinuous B S hS _ _)
      (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS _ _))

/-- The structure map of the equivalence `chartSliceEquivOfIso`, in the form produced by
`chartSliceFunctorIsoOfIso`: restriction of regular functions along it. -/
def chartSliceModelRingMap₀OfIso :
    Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleModelRingedSite B S hS F hF).over V).O ⟶
      ((sliceChartProjOfIso B S hS F hF V c i).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  𝟙 _ ≫ (@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ (sliceChartProjOfIso B S hS F hF V c i)
    (sliceProj B S hS F hF V) (chartSliceFunctorIsoOfIso B S hS F hF V c i).hom
    RingCat.{u} _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
    (smallEtaleRingedSite B S hS F hF).J (sliceChartProjOfIso_isContinuous B S hS F hF V c i)
    (sliceProj_isContinuous B S hS F hF V)).app
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)

/-- The structure map of the equivalence `chartSliceEquivOfIso`. -/
def chartSliceModelRingMapOfIso :
    Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleModelRingedSite B S hS F hF).over V).O ⟶
      ((chartSliceEquivOfIso B S hS F hF V c i).functor.sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleModelRingedSite B S hS F hF).over V).J (etaleChartSite B S hS F c).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (etaleChartSite B S hS F c).O) :=
  chartSliceModelRingMap₀OfIso B S hS F hF V c i

/-- The structure map of `chartSliceEquivOfIso` is invertible. -/
instance isIso_chartSliceModelRingMapOfIso :
    IsIso (chartSliceModelRingMapOfIso B S hS F hF V c i) := by
  have : IsIso ((@Functor.sheafPushforwardContinuousNatTrans _ _ _ _
      (sliceChartProjOfIso B S hS F hF V c i)
      (sliceProj B S hS F hF V) (chartSliceFunctorIsoOfIso B S hS F hF V c i).hom
      RingCat.{u} _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
      (smallEtaleRingedSite B S hS F hF).J (sliceChartProjOfIso_isContinuous B S hS F hF V c i)
      (sliceProj_isContinuous B S hS F hF V)).app
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
    inferInstanceAs (IsIso ((@Functor.sheafPushforwardContinuousIso _ _ _ _
      (sliceProj B S hS F hF V) (sliceChartProjOfIso B S hS F hF V c i)
      (chartSliceFunctorIsoOfIso B S hS F hF V c i).symm RingCat.{u} _
      ((smallEtaleModelRingedSite B S hS F hF).over V).J
      (smallEtaleRingedSite B S hS F hF).J (sliceProj_isContinuous B S hS F hF V)
      (sliceChartProjOfIso_isContinuous B S hS F hF V c i)).hom.app
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
  exact (IsIso.comp_isIso' inferInstance this :
    IsIso (chartSliceModelRingMap₀OfIso B S hS F hF V c i))


/-- The pushforward along `sliceProj` is the pushforward along `sliceChartProjOfIso`, with the
structure map `chartSliceModelRingMap₀OfIso`. -/
def chartSlicePushforwardIsoOfIso :
    @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceProj B S hS F hF V) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceProj_isContinuous B S hS F hF V) (𝟙 _) ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceChartProjOfIso B S hS F hF V c i) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceChartProjOfIso_isContinuous B S hS F hF V c i)
        (chartSliceModelRingMap₀OfIso B S hS F hF V c i) :=
  @SheafOfModules.pushforwardNatIso _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
    (smallEtaleRingedSite B S hS F hF).J (sliceChartProjOfIso B S hS F hF V c i)
    (sliceProj B S hS F hF V)
    _ _ (sliceChartProjOfIso_isContinuous B S hS F hF V c i) (sliceProj_isContinuous B S hS F hF V)
    (𝟙 _) (chartSliceFunctorIsoOfIso B S hS F hF V c i)

/-- The model equivalence of the chart followed by postcomposition with the chart is continuous. -/
instance chartModelPostcomp_isContinuousOfIso :
    ((smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).functor ⋙
      smallEtalePostcomp B S hS (etaleChartMap B S hS F hF c)
        (etaleChartMap_isEtale B S hS F hF c)).IsContinuous
      (etaleChartSite B S hS F c).J (smallEtaleRingedSite B S hS F hF).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _
    (smallEtaleRingedSite B S hS (yoneda.obj (etaleChartBase B S hS F c))
      (isAlgebraicSpace_yoneda B S hS _)).J _
    (smallEtaleModelRingedSite_functor_isContinuous B S hS _ _)
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS _ _)

/-- The structure map of the model equivalence of the chart followed by postcomposition with
the chart: the identity. -/
def chartModelPostcompRingOfIso :
    Stacks.SheafOfModules.Tensor.ringSheaf (etaleChartSite B S hS F c).O ⟶
      (Functor.sheafPushforwardContinuous
        ((smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).functor ⋙
          smallEtalePostcomp B S hS (etaleChartMap B S hS F hF c)
            (etaleChartMap_isEtale B S hS F hF c)) RingCat.{u}
        (etaleChartSite B S hS F c).J (smallEtaleRingedSite B S hS F hF).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  𝟙 _

/-- The pushforward along `chartSliceEquivOfIso` sends `chartModelPostcompRingOfIso` to the
identity. -/
theorem chartSliceEquiv_map_chartModelPostcompRingOfIso :
    ((chartSliceEquivOfIso B S hS F hF V c i).functor.sheafPushforwardContinuous RingCat.{u}
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (etaleChartSite B S hS F c).J).map
      (chartModelPostcompRingOfIso B S hS F hF c) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- **Étale pullback to the chart followed by transport to the model of the chart is a
pushforward**, along the model equivalence of the chart followed by postcomposition. -/
def chartModelPullbackIsoOfIso :
    etaleModulePullback.{u, u} B S hS (etaleChartMap B S hS F hF c)
        (etaleChartMap_isEtale B S hS F hF c) ⋙
      (modulesEquivModelModules B S hS (yoneda.obj (etaleChartBase B S hS F c))
        (isAlgebraicSpace_yoneda B S hS _)).functor ≅
    @SheafOfModules.pushforward.{u} _ _ _ _ (etaleChartSite B S hS F c).J
      (smallEtaleRingedSite B S hS F hF).J
      ((smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).functor ⋙
        smallEtalePostcomp B S hS (etaleChartMap B S hS F hF c)
          (etaleChartMap_isEtale B S hS F hF c))
      (Stacks.SheafOfModules.Tensor.ringSheaf (etaleChartSite B S hS F c).O)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
      (chartModelPostcomp_isContinuousOfIso B S hS F hF c)
      (chartModelPostcompRingOfIso B S hS F hF c) :=
  haveI := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS
    (etaleChartMap B S hS F hF c) (etaleChartMap_isEtale B S hS F hF c)
  SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr
    ((Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _))

/-- The ring map of `sliceChartProjOfIso`, read along the chart equivalence. -/
def chartSliceCongrIsoOfIso :
    @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceChartProjOfIso B S hS F hF V c i) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceChartProjOfIso_isContinuous B S hS F hF V c i)
        (chartSliceModelRingMap₀OfIso B S hS F hF V c i) ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceChartProjOfIso B S hS F hF V c i) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceChartProjOfIso_isContinuous B S hS F hF V c i)
        (chartSliceModelRingMapOfIso B S hS F hF V c i ≫
          ((chartSliceEquivOfIso B S hS F hF V c i).functor.sheafPushforwardContinuous RingCat.{u}
            ((smallEtaleModelRingedSite B S hS F hF).over V).J (etaleChartSite B S hS F c).J).map
            (chartModelPostcompRingOfIso B S hS F hF c)) :=
  @SheafOfModules.pushforwardCongr _ _ _ _ _ _ _ _ _
    (sliceChartProjOfIso_isContinuous B S hS F hF V c i)
    _ _ ((congrArg (chartSliceModelRingMapOfIso B S hS F hF V c i ≫ ·)
      (chartSliceEquiv_map_chartModelPostcompRingOfIso B S hS F hF V c i)).trans
        (Category.comp_id _)).symm

/-- The pushforward along `sliceChartProjOfIso` is the pushforward along the model equivalence of
the chart and postcomposition, followed by the pushforward along the chart equivalence. -/
def chartSliceCompIsoOfIso :
    @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceChartProjOfIso B S hS F hF V c i) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceChartProjOfIso_isContinuous B S hS F hF V c i)
        (chartSliceModelRingMapOfIso B S hS F hF V c i ≫
          ((chartSliceEquivOfIso B S hS F hF V c i).functor.sheafPushforwardContinuous RingCat.{u}
            ((smallEtaleModelRingedSite B S hS F hF).over V).J (etaleChartSite B S hS F c).J).map
            (chartModelPostcompRingOfIso B S hS F hF c)) ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ (etaleChartSite B S hS F c).J
          (smallEtaleRingedSite B S hS F hF).J
          ((smallEtaleModelEquivalence B S hS (yoneda.obj (etaleChartBase B S hS F c))).functor ⋙
            smallEtalePostcomp B S hS (etaleChartMap B S hS F hF c)
              (etaleChartMap_isEtale B S hS F hF c))
          (Stacks.SheafOfModules.Tensor.ringSheaf (etaleChartSite B S hS F c).O)
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
          (chartModelPostcomp_isContinuousOfIso B S hS F hF c)
          (chartModelPostcompRingOfIso B S hS F hF c) ⋙
        SheafOfModules.pushforward.{u} (chartSliceModelRingMapOfIso B S hS F hF V c i) :=
  (@SheafOfModules.pushforwardComp _ _ _ _ _ _ _ _ _ _ _ _
    (chartSliceModelRingMapOfIso B S hS F hF V c i) _ _ _
    (chartModelPostcomp_isContinuousOfIso B S hS F hF c)
    (chartModelPostcompRingOfIso B S hS F hF c)).symm

/-- **Restriction to the slice at `V` is restriction to the chart, read on the models**: for an
`𝒪_F`-module `M`, the restriction to the slice at `V` of its transport to the model is the
transport to the model of the chart of the étale pullback of `M`, pushed along
`chartSliceEquivOfIso`. -/
def chartSliceModulesIsoOfIso :
    (modulesEquivModelModules B S hS F hF).functor ⋙
        RingedSite.restrictModules (smallEtaleModelRingedSite B S hS F hF) V ≅
      etaleModulePullback.{u, u} B S hS (etaleChartMap B S hS F hF c)
          (etaleChartMap_isEtale B S hS F hF c) ⋙
        (modulesEquivModelModules B S hS (yoneda.obj (etaleChartBase B S hS F c))
          (isAlgebraicSpace_yoneda B S hS _)).functor ⋙
          SheafOfModules.pushforward.{u} (chartSliceModelRingMapOfIso B S hS F hF V c i) :=
  sliceProjPushforwardIso B S hS F hF V ≪≫ chartSlicePushforwardIsoOfIso B S hS F hF V c i ≪≫
    chartSliceCongrIsoOfIso B S hS F hF V c i ≪≫ chartSliceCompIsoOfIso B S hS F hF V c i ≪≫
    Functor.isoWhiskerRight (chartModelPullbackIsoOfIso B S hS F hF c).symm _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Space

end

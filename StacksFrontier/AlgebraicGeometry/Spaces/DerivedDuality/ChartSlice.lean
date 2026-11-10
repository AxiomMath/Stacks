module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC

/-!
# The slice of the model of an algebraic space at a chart

Let `F` be an algebraic space and `V` an object of the equi-universe model
`AlgebraicGeometry.Space.smallEtaleModelRingedSite` of its small étale ringed site; `V` is an
étale chart `h_U ⟶ F`. The slice of the model at `V` is equivalent, as a ringed site, to the
model of the small étale ringed site of `h_U` (Stacks 04M0, read on the models).

## Main definitions

* `AlgebraicGeometry.Space.chartSliceEquiv`: the equivalence of sites.
* `AlgebraicGeometry.Space.chartSliceModelRingMap`: the invertible structure map.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Equivalence

variable {A : Type*} [Category A] {B : Type*} [Category B] {C : Type*} [Category C]
  {JA : GrothendieckTopology A} {JB : GrothendieckTopology B} {JC : GrothendieckTopology C}

/-- A composite of two equivalences whose functors are dense subsite inclusions has a dense
subsite inclusion as functor. -/
theorem isDenseSubsite_trans_functor (e₁ : A ≌ B) (e₂ : B ≌ C)
    [e₁.functor.IsDenseSubsite JA JB] [e₂.functor.IsDenseSubsite JB JC] :
    (e₁.trans e₂).functor.IsDenseSubsite JA JC where
  functorPushforward_mem_iff {X S} := by
    change Sieve.functorPushforward (e₁.functor ⋙ e₂.functor) S ∈
      JC (e₂.functor.obj (e₁.functor.obj X)) ↔ _
    rw [Sieve.functorPushforward_comp, Functor.functorPushforward_mem_iff JB JC,
      Functor.functorPushforward_mem_iff JA JB]

end CategoryTheory.Equivalence

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (V : SmallEtaleModel B S hS F)

/-- The étale chart of `F` underlying an object of the model. -/
abbrev chartObj : SmallEtale B S hS F := (smallEtaleModelEquivalence B S hS F).functor.obj V

/-- The object of the big fppf site underlying the chart. -/
abbrev chartBase : BigFppfOver B S hS := (SmallEtale.toOver B S hS F).obj (chartObj B S hS F V)

/-- The model of the small étale ringed site of the represented space `h_U` of the chart. -/
abbrev chartSite : RingedSite.{u, u, u} :=
  smallEtaleModelRingedSite B S hS (yoneda.obj (chartBase B S hS F V))
    (isAlgebraicSpace_yoneda B S hS (chartBase B S hS F V))

/-- **Stacks 04M0 on the models**: the slice of the model of `F` at `V` is equivalent to the
model of the small étale site of the chart. -/
def chartSliceEquiv :
    ((smallEtaleModelRingedSite B S hS F hF).over V).C ≌ (chartSite B S hS F V).C :=
  (Over.postEquiv V (smallEtaleModelEquivalence B S hS F)).trans
    ((SmallEtale.chartLocalizationEquivalence B S hS F (chartObj B S hS F V)).symm.trans
      (smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).symm)

/-- The functor of `chartSliceEquiv` is a dense subsite inclusion. -/
instance chartSliceEquiv_functor_isDenseSubsite :
    (chartSliceEquiv B S hS F hF V).functor.IsDenseSubsite
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (chartSite B S hS F V).J := by
  have : (Over.postEquiv V (smallEtaleModelEquivalence B S hS F)).functor.IsDenseSubsite
      ((smallEtaleModelTopology B S hS F).over V)
      ((SmallEtale.topology B S hS F).over (chartObj B S hS F V)) :=
    inferInstanceAs
      ((Over.post (X := V) (smallEtaleModelEquivalence B S hS F).functor).IsDenseSubsite _ _)
  have : (SmallEtale.chartLocalizationEquivalence B S hS F
      (chartObj B S hS F V)).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj (chartBase B S hS F V)))
      ((SmallEtale.topology B S hS F).over (chartObj B S hS F V)) :=
    SmallEtale.isDenseSubsite_chartLocalizationEquivalence_functor B S hS F (chartObj B S hS F V)
  have : (SmallEtale.chartLocalizationEquivalence B S hS F
      (chartObj B S hS F V)).symm.functor.IsDenseSubsite
      ((SmallEtale.topology B S hS F).over (chartObj B S hS F V))
      (SmallEtale.topology B S hS (yoneda.obj (chartBase B S hS F V))) := inferInstance
  have : (smallEtaleModelEquivalence B S hS
      (yoneda.obj (chartBase B S hS F V))).symm.functor.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj (chartBase B S hS F V)))
      (smallEtaleModelTopology B S hS (yoneda.obj (chartBase B S hS F V))) :=
    smallEtaleModelEquivalence_inverse_isDenseSubsite B S hS _
  have h₂ := Equivalence.isDenseSubsite_trans_functor
    (SmallEtale.chartLocalizationEquivalence B S hS F (chartObj B S hS F V)).symm
    (smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).symm
    (JA := (SmallEtale.topology B S hS F).over (chartObj B S hS F V))
    (JB := SmallEtale.topology B S hS (yoneda.obj (chartBase B S hS F V)))
    (JC := smallEtaleModelTopology B S hS (yoneda.obj (chartBase B S hS F V)))
  exact @Equivalence.isDenseSubsite_trans_functor _ _ _ _ _ _
    ((smallEtaleModelTopology B S hS F).over V)
    ((SmallEtale.topology B S hS F).over (chartObj B S hS F V))
    (smallEtaleModelTopology B S hS (yoneda.obj (chartBase B S hS F V))) _ _ inferInstance h₂

/-- The functor of `chartSliceEquiv` is continuous. -/
instance chartSliceEquiv_functor_isContinuous :
    (chartSliceEquiv B S hS F hF V).functor.IsContinuous
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (chartSite B S hS F V).J :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (chartSliceEquiv_functor_isDenseSubsite B S hS F hF V)

/-- The inverse of `chartSliceEquiv` is a dense subsite inclusion. -/
instance chartSliceEquiv_inverse_isDenseSubsite :
    (chartSliceEquiv B S hS F hF V).inverse.IsDenseSubsite
      (chartSite B S hS F V).J ((smallEtaleModelRingedSite B S hS F hF).over V).J :=
  haveI : (chartSliceEquiv B S hS F hF V).symm.inverse.IsDenseSubsite
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (chartSite B S hS F V).J :=
    chartSliceEquiv_functor_isDenseSubsite B S hS F hF V
  inferInstanceAs ((chartSliceEquiv B S hS F hF V).symm.functor.IsDenseSubsite _ _)

/-- The inverse of `chartSliceEquiv` is continuous. -/
instance chartSliceEquiv_inverse_isContinuous :
    (chartSliceEquiv B S hS F hF V).inverse.IsContinuous
      (chartSite B S hS F V).J ((smallEtaleModelRingedSite B S hS F hF).over V).J :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (chartSliceEquiv_inverse_isDenseSubsite B S hS F hF V)

/-- The chart `h_U ⟶ F` underlying `V`, as a morphism of algebraic spaces. -/
abbrev modelChartMap : (⟨yoneda.obj (chartBase B S hS F V), isAlgebraicSpace_yoneda B S hS _⟩ :
    AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩ :=
  ObjectProperty.homMk (chartObj B S hS F V).obj.hom

/-- The chart morphism `modelChartMap` is étale. -/
theorem modelChartMap_isEtale : IsEtale B S hS (modelChartMap B S hS F hF V).hom :=
  isEtale_of_presheaf_etale B S hS (chartObj B S hS F V).property

/-- The slice projection followed by the model equivalence. -/
def sliceProj : ((smallEtaleModelRingedSite B S hS F hF).over V).C ⥤ SmallEtale B S hS F :=
  Over.forget V ⋙ (smallEtaleModelEquivalence B S hS F).functor

/-- The chart equivalence followed by the model equivalence of the chart and postcomposition with
the chart. -/
def sliceChartProj : ((smallEtaleModelRingedSite B S hS F hF).over V).C ⥤ SmallEtale B S hS F :=
  (chartSliceEquiv B S hS F hF V).functor ⋙
    (smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).functor ⋙
      smallEtalePostcomp B S hS (modelChartMap B S hS F hF V) (modelChartMap_isEtale B S hS F hF V)

/-- The two functors from the slice of the model at `V` to the small étale site of `F`: the slice
projection followed by the model equivalence, and the chart equivalence followed by the model
equivalence of the chart and postcomposition with the chart, are isomorphic. -/
def chartSliceFunctorIso :
    (chartSliceEquiv B S hS F hF V).functor ⋙
        (smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).functor ⋙
          smallEtalePostcomp B S hS (modelChartMap B S hS F hF V)
            (modelChartMap_isEtale B S hS F hF V) ≅
      Over.forget V ⋙ (smallEtaleModelEquivalence B S hS F).functor :=
  Functor.isoWhiskerLeft
      (Over.post (X := V) (smallEtaleModelEquivalence B S hS F).functor ⋙
        SmallEtale.chartLocalizationInverse B S hS F (chartObj B S hS F V))
      (Functor.isoWhiskerRight
        (smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).counitIso
        (smallEtalePostcomp B S hS (modelChartMap B S hS F hF V)
          (modelChartMap_isEtale B S hS F hF V))) ≪≫
    Functor.isoWhiskerLeft (Over.post (X := V) (smallEtaleModelEquivalence B S hS F).functor)
      (Functor.isoWhiskerRight
        (SmallEtale.chartLocalizationCounitIso B S hS F (chartObj B S hS F V))
        (Over.forget (chartObj B S hS F V)))


/-- The functor `sliceChartProj` is continuous. -/
instance sliceChartProj_isContinuous :
    (sliceChartProj B S hS F hF V).IsContinuous
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (smallEtaleRingedSite B S hS F hF).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ (chartSite B S hS F V).J _
    (chartSliceEquiv_functor_isContinuous B S hS F hF V)
    (@Functor.isContinuous_comp _ _ _ _ _ _ _ _ _
      (smallEtaleRingedSite B S hS (yoneda.obj (chartBase B S hS F V))
        (isAlgebraicSpace_yoneda B S hS _)).J _
      (smallEtaleModelRingedSite_functor_isContinuous B S hS _ _)
      (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS _ _))

/-- The functor `sliceProj` is continuous. -/
instance sliceProj_isContinuous :
    (sliceProj B S hS F hF V).IsContinuous
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (smallEtaleRingedSite B S hS F hF).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
    (smallEtaleModelRingedSite B S hS F hF).J _
    (inferInstanceAs ((Over.forget V).IsContinuous ((smallEtaleModelTopology B S hS F).over V)
      (smallEtaleModelTopology B S hS F)) :
      (Over.forget V : ((smallEtaleModelRingedSite B S hS F hF).over V).C ⥤ _).IsContinuous
        ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleModelRingedSite B S hS F hF).J)
    (smallEtaleModelRingedSite_functor_isContinuous B S hS F hF)

/-- The structure map of the equivalence `chartSliceEquiv`, in the form produced by
`chartSliceFunctorIso`: restriction of regular functions along it. -/
def chartSliceModelRingMap₀ :
    Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleModelRingedSite B S hS F hF).over V).O ⟶
      ((sliceChartProj B S hS F hF V).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  𝟙 _ ≫ (@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ (sliceChartProj B S hS F hF V)
    (sliceProj B S hS F hF V) (chartSliceFunctorIso B S hS F hF V).hom
    RingCat.{u} _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
    (smallEtaleRingedSite B S hS F hF).J (sliceChartProj_isContinuous B S hS F hF V)
    (sliceProj_isContinuous B S hS F hF V)).app
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)

/-- The structure map of the equivalence `chartSliceEquiv`. -/
def chartSliceModelRingMap :
    Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleModelRingedSite B S hS F hF).over V).O ⟶
      ((chartSliceEquiv B S hS F hF V).functor.sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleModelRingedSite B S hS F hF).over V).J (chartSite B S hS F V).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (chartSite B S hS F V).O) :=
  chartSliceModelRingMap₀ B S hS F hF V

/-- The structure map of `chartSliceEquiv` is invertible. -/
instance isIso_chartSliceModelRingMap : IsIso (chartSliceModelRingMap B S hS F hF V) := by
  have : IsIso ((@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ (sliceChartProj B S hS F hF V)
      (sliceProj B S hS F hF V) (chartSliceFunctorIso B S hS F hF V).hom
      RingCat.{u} _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
      (smallEtaleRingedSite B S hS F hF).J (sliceChartProj_isContinuous B S hS F hF V)
      (sliceProj_isContinuous B S hS F hF V)).app
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
    inferInstanceAs (IsIso ((@Functor.sheafPushforwardContinuousIso _ _ _ _
      (sliceProj B S hS F hF V) (sliceChartProj B S hS F hF V)
      (chartSliceFunctorIso B S hS F hF V).symm RingCat.{u} _
      ((smallEtaleModelRingedSite B S hS F hF).over V).J
      (smallEtaleRingedSite B S hS F hF).J (sliceProj_isContinuous B S hS F hF V)
      (sliceChartProj_isContinuous B S hS F hF V)).hom.app
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
  exact (IsIso.comp_isIso' inferInstance this : IsIso (chartSliceModelRingMap₀ B S hS F hF V))


/-- The pushforward along `sliceProj` is the pushforward along `sliceChartProj`, with the
structure map `chartSliceModelRingMap₀`. -/
def chartSlicePushforwardIso :
    @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceProj B S hS F hF V) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceProj_isContinuous B S hS F hF V) (𝟙 _) ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceChartProj B S hS F hF V) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceChartProj_isContinuous B S hS F hF V) (chartSliceModelRingMap₀ B S hS F hF V) :=
  @SheafOfModules.pushforwardNatIso _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
    (smallEtaleRingedSite B S hS F hF).J (sliceChartProj B S hS F hF V) (sliceProj B S hS F hF V)
    _ _ (sliceChartProj_isContinuous B S hS F hF V) (sliceProj_isContinuous B S hS F hF V)
    (𝟙 _) (chartSliceFunctorIso B S hS F hF V)

/-- Transport to the model followed by restriction to the slice at `V` is the pushforward along
`sliceProj`. -/
def sliceProjPushforwardIso :
    (modulesEquivModelModules B S hS F hF).functor ⋙
        RingedSite.restrictModules (smallEtaleModelRingedSite B S hS F hF) V ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceProj B S hS F hF V) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceProj_isContinuous B S hS F hF V) (𝟙 _) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The model equivalence of the chart followed by postcomposition with the chart is continuous. -/
instance chartModelPostcomp_isContinuous :
    ((smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).functor ⋙
      smallEtalePostcomp B S hS (modelChartMap B S hS F hF V)
        (modelChartMap_isEtale B S hS F hF V)).IsContinuous
      (chartSite B S hS F V).J (smallEtaleRingedSite B S hS F hF).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _
    (smallEtaleRingedSite B S hS (yoneda.obj (chartBase B S hS F V))
      (isAlgebraicSpace_yoneda B S hS _)).J _
    (smallEtaleModelRingedSite_functor_isContinuous B S hS _ _)
    (smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS _ _)

/-- The structure map of the model equivalence of the chart followed by postcomposition with
the chart: the identity. -/
def chartModelPostcompRing :
    Stacks.SheafOfModules.Tensor.ringSheaf (chartSite B S hS F V).O ⟶
      (Functor.sheafPushforwardContinuous
        ((smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).functor ⋙
          smallEtalePostcomp B S hS (modelChartMap B S hS F hF V)
            (modelChartMap_isEtale B S hS F hF V)) RingCat.{u}
        (chartSite B S hS F V).J (smallEtaleRingedSite B S hS F hF).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  𝟙 _

/-- The pushforward along the functor of `chartSliceEquiv` sends `chartModelPostcompRing` to the
identity. -/
theorem chartSliceEquiv_map_chartModelPostcompRing :
    ((chartSliceEquiv B S hS F hF V).functor.sheafPushforwardContinuous RingCat.{u}
      ((smallEtaleModelRingedSite B S hS F hF).over V).J (chartSite B S hS F V).J).map
      (chartModelPostcompRing B S hS F hF V) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- **Étale pullback to the chart followed by transport to the model of the chart is a
pushforward**, along the model equivalence of the chart followed by postcomposition. -/
def chartModelPullbackIso :
    etaleModulePullback.{u, u} B S hS (modelChartMap B S hS F hF V)
        (modelChartMap_isEtale B S hS F hF V) ⋙
      (modulesEquivModelModules B S hS (yoneda.obj (chartBase B S hS F V))
        (isAlgebraicSpace_yoneda B S hS _)).functor ≅
    @SheafOfModules.pushforward.{u} _ _ _ _ (chartSite B S hS F V).J
      (smallEtaleRingedSite B S hS F hF).J
      ((smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).functor ⋙
        smallEtalePostcomp B S hS (modelChartMap B S hS F hF V)
          (modelChartMap_isEtale B S hS F hF V))
      (Stacks.SheafOfModules.Tensor.ringSheaf (chartSite B S hS F V).O)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
      (chartModelPostcomp_isContinuous B S hS F hF V) (chartModelPostcompRing B S hS F hF V) :=
  haveI := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS
    (modelChartMap B S hS F hF V) (modelChartMap_isEtale B S hS F hF V)
  SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr
    ((Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _))

/-- The ring map of `sliceChartProj`, read along the chart equivalence. -/
def chartSliceCongrIso :
    @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceChartProj B S hS F hF V) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceChartProj_isContinuous B S hS F hF V) (chartSliceModelRingMap₀ B S hS F hF V) ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceChartProj B S hS F hF V) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceChartProj_isContinuous B S hS F hF V)
        (chartSliceModelRingMap B S hS F hF V ≫
          ((chartSliceEquiv B S hS F hF V).functor.sheafPushforwardContinuous RingCat.{u}
            ((smallEtaleModelRingedSite B S hS F hF).over V).J (chartSite B S hS F V).J).map
            (chartModelPostcompRing B S hS F hF V)) :=
  @SheafOfModules.pushforwardCongr _ _ _ _ _ _ _ _ _ (sliceChartProj_isContinuous B S hS F hF V)
    _ _ ((congrArg (chartSliceModelRingMap B S hS F hF V ≫ ·)
      (chartSliceEquiv_map_chartModelPostcompRing B S hS F hF V)).trans (Category.comp_id _)).symm

/-- The pushforward along `sliceChartProj` is the pushforward along the model equivalence of the
chart and postcomposition, followed by the pushforward along the chart equivalence. -/
def chartSliceCompIso :
    @SheafOfModules.pushforward.{u} _ _ _ _ ((smallEtaleModelRingedSite B S hS F hF).over V).J
        (smallEtaleRingedSite B S hS F hF).J (sliceChartProj B S hS F hF V) _
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (sliceChartProj_isContinuous B S hS F hF V)
        (chartSliceModelRingMap B S hS F hF V ≫
          ((chartSliceEquiv B S hS F hF V).functor.sheafPushforwardContinuous RingCat.{u}
            ((smallEtaleModelRingedSite B S hS F hF).over V).J (chartSite B S hS F V).J).map
            (chartModelPostcompRing B S hS F hF V)) ≅
      @SheafOfModules.pushforward.{u} _ _ _ _ (chartSite B S hS F V).J
          (smallEtaleRingedSite B S hS F hF).J
          ((smallEtaleModelEquivalence B S hS (yoneda.obj (chartBase B S hS F V))).functor ⋙
            smallEtalePostcomp B S hS (modelChartMap B S hS F hF V)
              (modelChartMap_isEtale B S hS F hF V))
          (Stacks.SheafOfModules.Tensor.ringSheaf (chartSite B S hS F V).O)
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
          (chartModelPostcomp_isContinuous B S hS F hF V) (chartModelPostcompRing B S hS F hF V) ⋙
        SheafOfModules.pushforward.{u} (chartSliceModelRingMap B S hS F hF V) :=
  (@SheafOfModules.pushforwardComp _ _ _ _ _ _ _ _ _ _ _ _
    (chartSliceModelRingMap B S hS F hF V) _ _ _ (chartModelPostcomp_isContinuous B S hS F hF V)
    (chartModelPostcompRing B S hS F hF V)).symm

/-- **Restriction to the slice at `V` is restriction to the chart, read on the models**: for an
`𝒪_F`-module `M`, the restriction to the slice at `V` of its transport to the model is the
transport to the model of the chart of the étale pullback of `M`, pushed along
`chartSliceEquiv`. -/
def chartSliceModulesIso :
    (modulesEquivModelModules B S hS F hF).functor ⋙
        RingedSite.restrictModules (smallEtaleModelRingedSite B S hS F hF) V ≅
      etaleModulePullback.{u, u} B S hS (modelChartMap B S hS F hF V)
          (modelChartMap_isEtale B S hS F hF V) ⋙
        (modulesEquivModelModules B S hS (yoneda.obj (chartBase B S hS F V))
          (isAlgebraicSpace_yoneda B S hS _)).functor ⋙
          SheafOfModules.pushforward.{u} (chartSliceModelRingMap B S hS F hF V) :=
  sliceProjPushforwardIso B S hS F hF V ≪≫ chartSlicePushforwardIso B S hS F hF V ≪≫
    chartSliceCongrIso B S hS F hF V ≪≫ chartSliceCompIso B S hS F hF V ≪≫
    Functor.isoWhiskerRight (chartModelPullbackIso B S hS F hF V).symm _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Space

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSliceTransport
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-!
# The derived internal Hom of an algebraic space and étale charts

Let `X` be an algebraic space and `A` an étale scheme chart of `X`, with structure morphism
`φ : U ⟶ X`. This file shows that the derived internal Hom
`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom` commutes with restriction to the chart:

`Lφ^* R𝓗om(K, L) ≅ R𝓗om(Lφ^* K, Lφ^* L)`.

The derived internal Hom of an algebraic space is that of the equi-universe model of its small
étale site, read through `AlgebraicGeometry.Space.smallEtaleModelDerivedEquivalence`. The model of
the chart `U` is equivalent, as a ringed site, to the slice of the model of `X` at the object
corresponding to `A` (Stacks 04M0), and under this equivalence restriction to the chart becomes
restriction to that slice.

## Main definitions

* `AlgebraicGeometry.Space.chartModelSliceEquivalence`: the model of the chart is the slice of the
  model of `X`.
* `AlgebraicGeometry.Space.chartModelModuleIso`: restriction to the chart, read on the models.
* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomChartIso`: the derived internal Hom commutes
  with restriction to an étale chart.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.ChartTransport

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {CU : Type u₁} [Category.{v₁} CU] {DU : Type u₂} [Category.{v₂} DU]
  {DX : Type u₃} [Category.{v₃} DX] {M : Type u₄} [Category.{v₄} M]
  {JCU : GrothendieckTopology CU} {KU : GrothendieckTopology DU}
  {KX : GrothendieckTopology DX} {JM : GrothendieckTopology M}
  (eU : CU ≌ DU) [hU : eU.functor.IsContinuous JCU KU] [hU' : eU.inverse.IsContinuous KU JCU]
  (p : DU ⥤ DX) [hp : p.IsContinuous KU KX]
  (eX : M ≌ DX) [hX : eX.functor.IsContinuous JM KX] [hX' : eX.inverse.IsContinuous KX JM]
  {RU : Sheaf KU RingCat.{w}} {RX : Sheaf KX RingCat.{w}}
  (ρ : RU ⟶ (p.sheafPushforwardContinuous RingCat.{w} KU KX).obj RX)
  (A' : M) (G : CU ⥤ Over A') [hG : G.IsContinuous JCU (JM.over A')]
  (τ : G ⋙ Over.forget A' ⋙ eX.functor ≅ eU.functor ⋙ p)

/-- The structure map comparing the transported ring sheaf on `CU` with the restriction to `A'` of
the transported ring sheaf on `M`, along `G`. -/
def ringMap :
    Stacks.SheafOfModules.reindexRing JCU eU RU ⟶
      (G.sheafPushforwardContinuous RingCat.{w} JCU (JM.over A')).obj
        ((Stacks.SheafOfModules.reindexRing JM eX RX).over A') :=
  haveI : (eU.functor ⋙ p).IsContinuous JCU KX := Functor.isContinuous_comp _ _ _ KU _
  haveI : (Over.forget A' ⋙ eX.functor).IsContinuous (JM.over A') KX :=
    Functor.isContinuous_comp _ _ _ JM _
  haveI : (G ⋙ Over.forget A' ⋙ eX.functor).IsContinuous JCU KX :=
    Functor.isContinuous_comp _ _ _ (JM.over A') _
  (eU.functor.sheafPushforwardContinuous RingCat.{w} JCU KU).map ρ ≫
    (Functor.sheafPushforwardContinuousNatTrans τ.hom RingCat.{w} JCU KX).app RX

variable [hGX : (Over.forget A' ⋙ eX.functor).IsContinuous (JM.over A') KX]

/-- The chart-side composite, as one direct image. -/
def chartSideIso :
    SheafOfModules.pushforward.{w} ρ ⋙
        (Stacks.SheafOfModules.reindexEquivalence (J' := JCU) eU RU).functor ≅
      haveI : (eU.functor ⋙ p).IsContinuous JCU KX := Functor.isContinuous_comp _ _ _ KU _
      SheafOfModules.pushforward.{w} (F := eU.functor ⋙ p)
        (𝟙 _ ≫ (eU.functor.sheafPushforwardContinuous RingCat.{w} JCU KU).map ρ) :=
  SheafOfModules.pushforwardComp _ _

/-- The slice-side composite, as one direct image. -/
def sliceSideIso :
    (Stacks.SheafOfModules.reindexEquivalence (J' := JM) eX RX).functor ⋙
        SheafOfModules.overFunctor (Stacks.SheafOfModules.reindexRing JM eX RX) A' ⋙
          SheafOfModules.pushforward.{w} (ringMap eU p eX ρ A' G τ) ≅
      haveI : (G ⋙ Over.forget A').IsContinuous JCU JM :=
        Functor.isContinuous_comp _ _ _ (JM.over A') _
      haveI : ((G ⋙ Over.forget A') ⋙ eX.functor).IsContinuous JCU KX :=
        Functor.isContinuous_comp _ _ _ JM _
      SheafOfModules.pushforward.{w} (F := (G ⋙ Over.forget A') ⋙ eX.functor)
        ((ringMap eU p eX ρ A' G τ ≫
          (G.sheafPushforwardContinuous RingCat.{w} JCU (JM.over A')).map
            (𝟙 ((Stacks.SheafOfModules.reindexRing JM eX RX).over A'))) ≫
          ((G ⋙ Over.forget A').sheafPushforwardContinuous RingCat.{w} JCU JM).map
            (𝟙 (Stacks.SheafOfModules.reindexRing JM eX RX))) :=
  haveI : (G ⋙ Over.forget A').IsContinuous JCU JM :=
    Functor.isContinuous_comp _ _ _ (JM.over A') _
  Functor.isoWhiskerLeft
      (SheafOfModules.pushforward.{w} (𝟙 (Stacks.SheafOfModules.reindexRing JM eX RX)))
      (SheafOfModules.pushforwardComp (ringMap eU p eX ρ A' G τ)
        (𝟙 ((Stacks.SheafOfModules.reindexRing JM eX RX).over A'))) ≪≫
    SheafOfModules.pushforwardComp _ _

/-- The two direct images agree, along `τ`. -/
def sideComparisonIso :
      haveI : (eU.functor ⋙ p).IsContinuous JCU KX := Functor.isContinuous_comp _ _ _ KU _
      SheafOfModules.pushforward.{w} (F := eU.functor ⋙ p)
        (𝟙 _ ≫ (eU.functor.sheafPushforwardContinuous RingCat.{w} JCU KU).map ρ) ≅
      haveI : (G ⋙ Over.forget A').IsContinuous JCU JM :=
        Functor.isContinuous_comp _ _ _ (JM.over A') _
      haveI : ((G ⋙ Over.forget A') ⋙ eX.functor).IsContinuous JCU KX :=
        Functor.isContinuous_comp _ _ _ JM _
      SheafOfModules.pushforward.{w} (F := (G ⋙ Over.forget A') ⋙ eX.functor)
        ((ringMap eU p eX ρ A' G τ ≫
          (G.sheafPushforwardContinuous RingCat.{w} JCU (JM.over A')).map
            (𝟙 ((Stacks.SheafOfModules.reindexRing JM eX RX).over A'))) ≫
          ((G ⋙ Over.forget A').sheafPushforwardContinuous RingCat.{w} JCU JM).map
            (𝟙 (Stacks.SheafOfModules.reindexRing JM eX RX))) :=
  haveI : (eU.functor ⋙ p).IsContinuous JCU KX := Functor.isContinuous_comp _ _ _ KU _
  haveI : (G ⋙ Over.forget A').IsContinuous JCU JM :=
    Functor.isContinuous_comp _ _ _ (JM.over A') _
  haveI : ((G ⋙ Over.forget A') ⋙ eX.functor).IsContinuous JCU KX :=
    Functor.isContinuous_comp _ _ _ JM _
  SheafOfModules.pushforwardCongr₂ _ τ (by
    ext : 3
    simp only [ringMap]
    rfl)

/-- **Reading a module through `p` and then on `CU` is restricting it on `M` to `A'` and then
reading it on `CU` along `G`.** -/
def moduleIso :
    SheafOfModules.pushforward.{w} ρ ⋙
        (Stacks.SheafOfModules.reindexEquivalence (J' := JCU) eU RU).functor ≅
      (Stacks.SheafOfModules.reindexEquivalence (J' := JM) eX RX).functor ⋙
        SheafOfModules.overFunctor (Stacks.SheafOfModules.reindexRing JM eX RX) A' ⋙
          SheafOfModules.pushforward.{w} (ringMap eU p eX ρ A' G τ) :=
  chartSideIso eU p ρ ≪≫ sideComparisonIso eU p eX ρ A' G τ ≪≫ (sliceSideIso eU p eX ρ A' G τ).symm

/-- The structure map is invertible when `ρ` is. -/
instance isIso_ringMap [hρ : IsIso ρ] :
    IsIso (ringMap (JCU := JCU) (JM := JM) eU p eX ρ A' G τ) := by
  have : (eU.functor ⋙ p).IsContinuous JCU KX := Functor.isContinuous_comp _ _ _ KU _
  have : (Over.forget A' ⋙ eX.functor).IsContinuous (JM.over A') KX :=
    Functor.isContinuous_comp _ _ _ JM _
  have : (G ⋙ Over.forget A' ⋙ eX.functor).IsContinuous JCU KX :=
    Functor.isContinuous_comp _ _ _ (JM.over A') _
  have : IsIso ((Functor.sheafPushforwardContinuousNatTrans τ.hom RingCat.{w} JCU KX).app RX) :=
    inferInstanceAs (IsIso ((Functor.sheafPushforwardContinuousIso τ.symm RingCat.{w} JCU KX).app
      RX).hom)
  exact IsIso.comp_isIso' (Functor.map_isIso _ ρ) this

end Stacks.SheafOfModules.ChartTransport

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (A : SmallEtale B S hS X.1)

/-- The slice of the small étale site of `X` at `A`, transported to the slice of the model. -/
abbrev chartModelSlicePost :
    Over A ≌ Over ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A) :=
  Over.postEquiv A (smallEtaleModelEquivalence B S hS X.1).symm

/-- The functor of `chartModelSlicePost` is a dense subsite. -/
instance chartModelSlicePost_functor_isDenseSubsite :
    (chartModelSlicePost B S hS X A).functor.IsDenseSubsite
      ((SmallEtale.topology B S hS X.1).over A)
      ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)) :=
  haveI : (smallEtaleModelEquivalence B S hS X.1).symm.functor.IsDenseSubsite
      (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1) :=
    smallEtaleModelEquivalence_inverse_isDenseSubsite B S hS X.1
  Stacks.SheafOfModules.ModelFinitePresentation.isDenseSubsite_overPost
    (smallEtaleModelEquivalence B S hS X.1).symm A

/-- The inverse of `chartModelSlicePost` is a dense subsite. -/
instance chartModelSlicePost_inverse_isDenseSubsite :
    (chartModelSlicePost B S hS X A).inverse.IsDenseSubsite
      ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A))
      ((SmallEtale.topology B S hS X.1).over A) :=
  haveI : (chartModelSlicePost B S hS X A).symm.inverse.IsDenseSubsite
      ((SmallEtale.topology B S hS X.1).over A)
      ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)) :=
    chartModelSlicePost_functor_isDenseSubsite B S hS X A
  inferInstanceAs ((chartModelSlicePost B S hS X A).symm.functor.IsDenseSubsite _ _)

/-- **The small étale site of a chart, read on the models, is the slice of the model of `X` at the
chart** (Stacks 04M0): the model of the chart is its small étale site, which is the slice of the
small étale site of `X` at the chart, which is the slice of the model of `X`. -/
def chartModelSliceEquivalence :
    (smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).C ≌
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)).C :=
  (smallEtaleModelEquivalence B S hS (chartSpace B S hS X A).1).trans
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 A).trans (chartModelSlicePost B S hS X A))

/-- The comparison of Stacks 04M0 followed by the slice equivalence of the model. -/
abbrev chartModelSliceTail :
    SmallEtale B S hS (chartSpace B S hS X A).1 ≌
      Over ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A) :=
  (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).trans (chartModelSlicePost B S hS X A)

/-- The functor of `chartModelSliceTail` is continuous. -/
theorem chartModelSliceTail_functor_isContinuous :
    (chartModelSliceTail B S hS X A).functor.IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
      ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    ((SmallEtale.topology B S hS X.1).over A)
    ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A))
    (isContinuous_chartLocalization_chartSpace B S hS X A)
    (@Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
      (chartModelSlicePost_functor_isDenseSubsite B S hS X A))

/-- The inverse of `chartModelSliceTail` is continuous. -/
theorem chartModelSliceTail_inverse_isContinuous :
    (chartModelSliceTail B S hS X A).inverse.IsContinuous
      ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A))
      (SmallEtale.topology B S hS (chartSpace B S hS X A).1) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A))
    ((SmallEtale.topology B S hS X.1).over A)
    (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (@Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
      (chartModelSlicePost_inverse_isDenseSubsite B S hS X A))
    (isContinuous_chartLocalizationEquivalence_inverse_chartSpace B S hS X A)

/-- The functor of `chartModelSliceEquivalence` is continuous for the topology of the slice ringed
site. -/
instance chartModelSliceEquivalence_functor_isContinuous :
    (chartModelSliceEquivalence B S hS X A).functor.IsContinuous
      (smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    (smallEtaleModelTopology B S hS (chartSpace B S hS X A).1)
    (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A))
    (smallEtaleModelEquivalence_functor_isContinuous B S hS _)
    (chartModelSliceTail_functor_isContinuous B S hS X A)

/-- The functor of `chartModelSliceEquivalence` is continuous for the slice topology of the model
of `X`. -/
instance chartModelSliceEquivalence_functor_isContinuous' :
    (chartModelSliceEquivalence B S hS X A).functor.IsContinuous
      (smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J
      ((smallEtaleModelRingedSite B S hS X.1 X.2).J.over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)) :=
  chartModelSliceEquivalence_functor_isContinuous B S hS X A

/-- The inverse of `chartModelSliceEquivalence` is continuous. -/
instance chartModelSliceEquivalence_inverse_isContinuous :
    (chartModelSliceEquivalence B S hS X A).inverse.IsContinuous
      ((smallEtaleModelRingedSite B S hS X.1 X.2).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)).J
      (smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A))
    (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (smallEtaleModelTopology B S hS (chartSpace B S hS X A).1)
    (chartModelSliceTail_inverse_isContinuous B S hS X A)
    (smallEtaleModelEquivalence_inverse_isContinuous B S hS _)

/-- The chart site, read through the slice of the model, followed by the slice projection and the
model equivalence of `X`, is postcomposition with the chart, up to the counit of the model. -/
def chartModelSliceForgetIso :
    (chartModelSliceEquivalence B S hS X A).functor ⋙
        Over.forget ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A) ⋙
          (smallEtaleModelEquivalence B S hS X.1).functor ≅
      (smallEtaleModelEquivalence B S hS (chartSpace B S hS X A).1).functor ⋙
        smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A) :=
  Functor.isoWhiskerLeft ((smallEtaleModelEquivalence B S hS (chartSpace B S hS X A).1).functor ⋙
      smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
      (smallEtaleModelEquivalence B S hS X.1).counitIso ≪≫ Functor.rightUnitor _

/-- The functor of `chartModelSliceEquivalence`, followed by the slice projection and the model
equivalence of `X`, is continuous. -/
instance chartModelSliceForget_isContinuous :
    ((chartModelSliceEquivalence B S hS X A).functor ⋙
        Over.forget ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A) ⋙
          (smallEtaleModelEquivalence B S hS X.1).functor).IsContinuous
      (smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J
      (smallEtaleRingedSite B S hS X.1 X.2).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    (smallEtaleModelTopology B S hS (chartSpace B S hS X A).1)
    ((smallEtaleModelTopology B S hS X.1).over
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A))
    (SmallEtale.topology B S hS X.1)
    (chartModelSliceEquivalence_functor_isContinuous B S hS X A)
    (@Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ (smallEtaleModelTopology B S hS X.1) _
      inferInstance (smallEtaleModelEquivalence_functor_isContinuous B S hS _))

/-- The model equivalence of the chart followed by postcomposition with the chart is continuous. -/
instance chartSpaceModelPostcomp_isContinuous :
    ((smallEtaleModelEquivalence B S hS (chartSpace B S hS X A).1).functor ⋙
        smallEtalePostcomp B S hS (chartToSpace B S hS X A)
          (isEtale_chartToSpace B S hS X A)).IsContinuous
      (smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J
      (smallEtaleRingedSite B S hS X.1 X.2).J :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _
    (smallEtaleModelTopology B S hS (chartSpace B S hS X A).1)
    (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (SmallEtale.topology B S hS X.1)
    (smallEtaleModelEquivalence_functor_isContinuous B S hS _)
    (smallEtalePostcomp_isContinuous B S hS _ _)

/-- The structure map of the equivalence of ringed sites between the model of a chart and the slice
of the model of `X` at the chart: the counit of the model equivalence of `X` on functions. -/
def chartModelSliceRingMap :
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).O) ⟶
      ((chartModelSliceEquivalence B S hS X A).functor.sheafPushforwardContinuous RingCat.{u}
        (smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J
        ((smallEtaleModelRingedSite B S hS X.1 X.2).over
          ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleModelRingedSite B S hS X.1 X.2).over
          ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)).O) :=
  Stacks.SheafOfModules.ChartTransport.ringMap
    (JCU := smallEtaleModelTopology B S hS (chartSpace B S hS X A).1)
    (KU := (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J)
    (KX := (smallEtaleRingedSite B S hS X.1 X.2).J)
    (JM := smallEtaleModelTopology B S hS X.1)
    (RU := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).O))
    (RX := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (hU := smallEtaleRingedSite_functor_isContinuous B S hS _ _)
    (hp := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS _ _)
    (hX := smallEtaleRingedSite_functor_isContinuous B S hS _ _)
    (hG := chartModelSliceEquivalence_functor_isContinuous B S hS X A)
    (smallEtaleModelEquivalence B S hS (chartSpace B S hS X A).1)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (smallEtaleModelEquivalence B S hS X.1)
    (𝟙 _)
    ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
    (chartModelSliceEquivalence B S hS X A).functor
    (chartModelSliceForgetIso B S hS X A)

/-- **Restriction to a chart, read on the models, is restriction to the slice of the model at the
chart followed by the equivalence of ringed sites.** -/
def chartModelModuleIso :
    etaleModulePullback B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A) ⋙
        (smallEtaleModelModulesEquivalence B S hS (chartSpace B S hS X A)).functor ≅
      (smallEtaleModelModulesEquivalence B S hS X).functor ⋙
        RingedSite.sliceEquivTransport (X := smallEtaleModelRingedSite B S hS X.1 X.2)
          (Y := smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1
            (chartSpace B S hS X A).2)
          ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
          (chartModelSliceEquivalence B S hS X A) (chartModelSliceRingMap B S hS X A) :=
  Stacks.SheafOfModules.ChartTransport.moduleIso
    (JCU := smallEtaleModelTopology B S hS (chartSpace B S hS X A).1)
    (KU := (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J)
    (KX := (smallEtaleRingedSite B S hS X.1 X.2).J)
    (JM := smallEtaleModelTopology B S hS X.1)
    (RU := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).O))
    (RX := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (hU := smallEtaleRingedSite_functor_isContinuous B S hS _ _)
    (hU' := smallEtaleRingedSite_inverse_isContinuous B S hS _ _)
    (hp := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS _ _)
    (hX := smallEtaleRingedSite_functor_isContinuous B S hS _ _)
    (hX' := smallEtaleRingedSite_inverse_isContinuous B S hS _ _)
    (hG := chartModelSliceEquivalence_functor_isContinuous' B S hS X A)
    (smallEtaleModelEquivalence B S hS (chartSpace B S hS X A).1)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (smallEtaleModelEquivalence B S hS X.1)
    (𝟙 _)
    ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
    (chartModelSliceEquivalence B S hS X A).functor
    (chartModelSliceForgetIso B S hS X A)

/-- The structure map of the chart slice is invertible. -/
instance isIso_chartModelSliceRingMap : IsIso (chartModelSliceRingMap B S hS X A) :=
  Stacks.SheafOfModules.ChartTransport.isIso_ringMap
    (JCU := smallEtaleModelTopology B S hS (chartSpace B S hS X A).1)
    (KU := (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).J)
    (KX := (smallEtaleRingedSite B S hS X.1 X.2).J)
    (JM := smallEtaleModelTopology B S hS X.1)
    (RU := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2).O))
    (RX := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (hU := smallEtaleRingedSite_functor_isContinuous B S hS _ _)
    (hp := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS _ _)
    (hX := smallEtaleRingedSite_functor_isContinuous B S hS _ _)
    (hG := chartModelSliceEquivalence_functor_isContinuous' B S hS X A)
    (smallEtaleModelEquivalence B S hS (chartSpace B S hS X A).1)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (smallEtaleModelEquivalence B S hS X.1)
    (𝟙 _)
    ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
    (chartModelSliceEquivalence B S hS X A).functor
    (chartModelSliceForgetIso B S hS X A) (hρ := IsIso.id _)

/-- Restriction of `𝒪_X`-modules to the chart `A`, in the spelling of `D(𝒪_X)`. -/
abbrev chartModules :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X A)) :=
  etaleModulePullback B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A)

/-- Restriction of modules to the chart is additive. -/
instance chartModules_additive : (chartModules B S hS X A).Additive :=
  etaleModulePullback_additive B S hS _ _

/-- Restriction of modules to the chart preserves finite limits. -/
instance chartModules_preservesFiniteLimits : PreservesFiniteLimits (chartModules B S hS X A) :=
  preservesFiniteLimits_etaleModulePullback B S hS _ _

/-- Restriction of modules to the chart preserves finite colimits. -/
instance chartModules_preservesFiniteColimits :
    PreservesFiniteColimits (chartModules B S hS X A) :=
  preservesFiniteColimits_etaleModulePullback B S hS _ _

/-- Restriction to the slice of the model at the chart, transported to the model of the chart. -/
abbrev chartModelTransport :=
  RingedSite.sliceEquivTransport (X := smallEtaleModelRingedSite B S hS X.1 X.2)
    (Y := smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
    ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
    (chartModelSliceEquivalence B S hS X A) (chartModelSliceRingMap B S hS X A)

/-- `chartModelTransport` is additive. -/
instance chartModelTransport_additive : (chartModelTransport B S hS X A).Additive :=
  RingedSite.sliceEquivTransport_additive (X := smallEtaleModelRingedSite B S hS X.1 X.2)
    (Y := smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
    ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
    (chartModelSliceEquivalence B S hS X A) (chartModelSliceRingMap B S hS X A)

/-- `chartModelTransport` preserves finite limits. -/
instance chartModelTransport_preservesFiniteLimits :
    PreservesFiniteLimits (chartModelTransport B S hS X A) :=
  RingedSite.sliceEquivTransport_preservesFiniteLimits
    (X := smallEtaleModelRingedSite B S hS X.1 X.2)
    (Y := smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
    ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
    (chartModelSliceEquivalence B S hS X A) (chartModelSliceRingMap B S hS X A)
    (hl := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits _)

/-- `chartModelTransport` preserves finite colimits. -/
instance chartModelTransport_preservesFiniteColimits :
    PreservesFiniteColimits (chartModelTransport B S hS X A) :=
  RingedSite.sliceEquivTransport_preservesFiniteColimits
    (X := smallEtaleModelRingedSite B S hS X.1 X.2)
    (Y := smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
    ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
    (chartModelSliceEquivalence B S hS X A) (chartModelSliceRingMap B S hS X A)
    (hc := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits _)

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- The module equivalence of the model of `X` followed by `chartModelTransport` is additive. -/
instance chartModelTransport_comp_additive :
    ((smallEtaleModelModulesEquivalence B S hS X).functor ⋙
      chartModelTransport B S hS X A).Additive :=
  Functor.instAdditiveComp _ _

/-- **Restriction to a chart on derived categories, read on the models.** -/
def chartModelDerivedIso :
    (chartModules B S hS X A).mapDerivedCategory ⋙
        (smallEtaleModelDerivedEquivalence B S hS (chartSpace B S hS X A)).functor ≅
      (smallEtaleModelDerivedEquivalence B S hS X).functor ⋙
        (chartModelTransport B S hS X A).mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    @Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ _ _ _ _ _ _ _ _
      inferInstance inferInstance inferInstance
      (chartModelTransport_comp_additive B S hS X A) inferInstance inferInstance
      (chartModelModuleIso B S hS X A) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- **The derived internal Hom of an algebraic space commutes with restriction to an étale chart.**
For an étale chart `A` of `X`, with structure morphism `φ : U ⟶ X`, and `K`, `L` in `D(𝒪_X)`,
`Lφ^* R𝓗om(K, L) ≅ R𝓗om(Lφ^* K, Lφ^* L)`. -/
def smallEtaleDerivedSheafHomChartIso
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L) ≅
      ((smallEtaleDerivedSheafHom B S hS (chartSpace B S hS X A)).obj
        (op ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).obj K))).obj
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).obj L) :=
  let P := smallEtaleDerivedModulePullbackIsoEtale B S hS (chartToSpace B S hS X A)
    (isEtale_chartToSpace B S hS X A)
  let eU := smallEtaleModelDerivedEquivalence B S hS (chartSpace B S hS X A)
  let eX := smallEtaleModelDerivedEquivalence B S hS X
  let D := chartModelDerivedIso B S hS X A
  let T := (chartModelTransport B S hS X A).mapDerivedCategory
  P.app _ ≪≫ eU.unitIso.app _ ≪≫ eU.inverse.mapIso (D.app _) ≪≫
    eU.inverse.mapIso (T.mapIso (eX.counitIso.app _)) ≪≫
    eU.inverse.mapIso
      (RingedSite.sliceEquivTransportDerivedSheafHomIso
        (X := smallEtaleModelRingedSite B S hS X.1 X.2)
        (Y := smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
        ((smallEtaleModelEquivalence B S hS X.1).inverse.obj A)
        (chartModelSliceEquivalence B S hS X A) (chartModelSliceRingMap B S hS X A)
        (hl := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits _)
        (hc := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits _)
        (eX.functor.obj K) (eX.functor.obj L)) ≪≫
    eU.inverse.mapIso
      ((((RingedSite.derivedSheafHomBifunctor _).mapIso
        (eU.functor.mapIso (P.app K) ≪≫ D.app K).op).app _) ≪≫
       ((RingedSite.derivedSheafHomBifunctor _).obj _).mapIso
        ((D.app L).symm ≪≫ eU.functor.mapIso (P.app L).symm))

end AlgebraicGeometry.Space

end

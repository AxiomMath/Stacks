module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SliceChart
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Biduality on the model of a locally Noetherian algebraic space, at bounded objects

Let `X` be a locally Noetherian algebraic space and `K` a dualizing complex on `X` (Stacks 0E4Z).
On the equi-universe model of the small étale ringed site of `X`, the slices at the affine charts
carry duality charts for the restrictions of `K` at the class of bounded objects
(`AlgebraicGeometry.Space.sliceBoundedChart`), and the affine charts cover the model. So the
biduality morphism `L ⟶ R𝓗om(R𝓗om(L, K), K)` is an isomorphism for every `L` which on each affine
chart is `ε^*` of a bounded object with coherent cohomology; in particular for `L = 𝒪` and for
`L` a second dualizing complex `K'`. These are the two inputs of Stacks 0E52.

## Main results

* `AlgebraicGeometry.Space.isIso_derivedBiduality_model_of_isDualizingComplexOnSpace`: biduality
  at a dualizing complex `K'`.
* `AlgebraicGeometry.Space.isIso_derivedBiduality_model_unit`: biduality at `𝒪`.

## References

* [Stacks Project, Tag 0E51](https://stacks.math.columbia.edu/tag/0E51)
* [Stacks Project, Tag 0E52](https://stacks.math.columbia.edu/tag/0E52)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (V : SmallEtaleModel B S hS F)

/-- An object of the model of `h_U` which is the transport of `ε^* L'`, with `L'` bounded with
coherent cohomology, is modelled by the bounded chart of `h_U`. -/
theorem reprBoundedChart_models (U : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsAffine (reprScheme B S hS U)]
    [_root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS U)]
    (ω : RingedSite.SchemeStdDerived (reprScheme B S hS U))
    (hω : letI : HasDerivedCategory (reprScheme B S hS U).Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω)
    (X : DerivedModules B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (L' : RingedSite.SchemeStdDerived (reprScheme B S hS U))
    (hL' : RingedSite.SchemeCoherent _ L') (hb : RingedSite.ChartClass.bounded _ L')
    (hq : ∀ n : ℤ, ((RingedSite.schemeStdHomology _ n).obj L').IsQuasicoherent)
    (eX : X ≅ (representedDerivedAssociatedModule B S hS U).obj L') :
    (reprBoundedChart B S hS U ω hω).Models
      ((modelDerivedEquivalence B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).functor.obj X) :=
  RingedSite.DualityChart.models_transport _
    (RingedSite.DualityChart.models_derived
      (SmallEtale.boundedBaseDualityChart (associatedBigEtaleSite B) (reprScheme B S hS U)
        U.left.property ω hω) hL' hb hq)
    (reprChartDerivedIso B S hS U L' ≪≫
      (modelDerivedEquivalence B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).functor.mapIso eX.symm)

/-- **An object which on the chart is `ε^*` of a bounded coherent object is modelled by the slice
chart.** -/
theorem sliceBoundedChart_models
    [_root_.AlgebraicGeometry.IsAffine (reprScheme B S hS (chartBase B S hS F V))]
    [_root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS (chartBase B S hS F V))]
    (K : DerivedModules B S hS F hF)
    (ω : RingedSite.SchemeStdDerived (reprScheme B S hS (chartBase B S hS F V)))
    (hω : letI : HasDerivedCategory (reprScheme B S hS (chartBase B S hS F V)).Modules :=
      HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω)
    (e : (representedChartDerivedRestriction B S hS hF (chartBase B S hS F V)
        (chartObj B S hS F V).obj.hom (modelChartMap_isEtale B S hS F hF V)).obj K ≅
      (representedDerivedAssociatedModule B S hS (chartBase B S hS F V)).obj ω)
    (L : DerivedModules B S hS F hF)
    (L' : RingedSite.SchemeStdDerived (reprScheme B S hS (chartBase B S hS F V)))
    (hL' : RingedSite.SchemeCoherent _ L') (hb : RingedSite.ChartClass.bounded _ L')
    (hq : ∀ n : ℤ, ((RingedSite.schemeStdHomology _ n).obj L').IsQuasicoherent)
    (eL : (representedChartDerivedRestriction B S hS hF (chartBase B S hS F V)
        (chartObj B S hS F V).obj.hom (modelChartMap_isEtale B S hS F hF V)).obj L ≅
      (representedDerivedAssociatedModule B S hS (chartBase B S hS F V)).obj L') :
    (sliceBoundedChart B S hS F hF V K ω hω e).Models
      ((RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) V).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj L)) :=
  RingedSite.DualityChart.models_transport _
    (reprBoundedChart_models B S hS (chartBase B S hS F V) ω hω _ L' hL' hb hq eL)
    (sliceRestrictIso B S hS F hF V L).symm

/-! ### The charts of a dualizing complex -/

variable (hN : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T))

omit V in
include hF hN in
/-- The scheme of an affine chart of a locally Noetherian algebraic space is Noetherian. -/
theorem isNoetherian_affineChart (i : AffineChart B S hS F) :
    _root_.AlgebraicGeometry.IsNoetherian (reprScheme B S hS (chartBase B S hS F i.1)) :=
  have := i.2
  have : IsLocallyNoetherian (reprScheme B S hS (chartBase B S hS F i.1)) :=
    isLocallyNoetherian_of_etaleChart B S hS F hF hN _ _ (chartObj B S hS F i.1).property
  @IsNoetherian.mk _ inferInstance inferInstance

omit V in
/-- **The restriction of a dualizing complex to an affine chart is `ε^* ω`** for a dualizing
complex `ω` on the scheme of the chart (Stacks 0E4Z, 0E4X). -/
theorem exists_dualizing_affineChart (K : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K) (i : AffineChart B S hS F) :
    ∃ ω : RingedSite.SchemeStdDerived (reprScheme B S hS (chartBase B S hS F i.1)),
      (letI : HasDerivedCategory (reprScheme B S hS (chartBase B S hS F i.1)).Modules :=
        HasDerivedCategory.standard _
      haveI := isNoetherian_affineChart B S hS F hF hN i
      Stacks.Duality.IsDualizingComplex ω) ∧
      Nonempty ((representedChartDerivedRestriction B S hS hF (chartBase B S hS F i.1)
          (chartObj B S hS F i.1).obj.hom (modelChartMap_isEtale B S hS F hF i.1)).obj K.obj ≅
        (representedDerivedAssociatedModule B S hS (chartBase B S hS F i.1)).obj ω) :=
  hK _ _ (chartObj B S hS F i.1).property

/-- **The duality chart of a dualizing complex at an affine chart**, at bounded objects. -/
def affineChartBoundedChart (K : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K) (i : AffineChart B S hS F) :
    RingedSite.DualityChart ((smallEtaleModelRingedSite B S hS F hF).over i.1)
      ((RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) i.1).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj K.obj))
      RingedSite.ChartClass.bounded :=
  haveI := i.2
  haveI := isNoetherian_affineChart B S hS F hF hN i
  sliceBoundedChart B S hS F hF i.1 K.obj
    (exists_dualizing_affineChart B S hS F hF hN K hK i).choose
    (exists_dualizing_affineChart B S hS F hF hN K hK i).choose_spec.1
    (exists_dualizing_affineChart B S hS F hF hN K hK i).choose_spec.2.some

/-- A second dualizing complex is modelled at bounded objects on every affine chart. -/
theorem affineChartBoundedChart_models_dualizing
    (K K' : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K)
    (hK' : IsDualizingComplexOnSpace B S hS F hF hN K') (i : AffineChart B S hS F) :
    (affineChartBoundedChart B S hS F hF hN K hK i).Models
      ((RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) i.1).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj K'.obj)) := by
  have := i.2
  have := isNoetherian_affineChart B S hS F hF hN i
  obtain ⟨ω', hω', ⟨e'⟩⟩ := exists_dualizing_affineChart B S hS F hF hN K' hK' i
  let : HasDerivedCategory (reprScheme B S hS (chartBase B S hS F i.1)).Modules :=
    HasDerivedCategory.standard _
  exact sliceBoundedChart_models B S hS F hF i.1 K.obj _ _ _ K'.obj ω'
    (RingedSite.schemeCoherent_of_isDualizingComplex hω')
    (RingedSite.bounded_of_isDualizingComplex _ ω' hω')
    (Stacks.Duality.isQuasicoherent_homology_of_isDualizingComplex hω') e'

/-- **Biduality at a second dualizing complex, on the model** (Stacks 0E51, at the input of Stacks
0E52): for dualizing complexes `K`, `K'` on a locally Noetherian algebraic space, the biduality
morphism `K' ⟶ R𝓗om(R𝓗om(K', K), K)` of the equi-universe model is an isomorphism. -/
theorem isIso_derivedBiduality_model_of_isDualizingComplexOnSpace
    (K K' : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K)
    (hK' : IsDualizingComplexOnSpace B S hS F hF hN K') :
    IsIso (RingedSite.derivedBiduality (smallEtaleModelRingedSite B S hS F hF)
      ((modelDerivedEquivalence B S hS F hF).functor.obj K.obj)
      ((modelDerivedEquivalence B S hS F hF).functor.obj K'.obj)) :=
  RingedSite.isIso_derivedBiduality_of_models (smallEtaleModelRingedSite B S hS F hF)
    (affineChart_coversTop B S hS F hF) RingedSite.ChartClass.bounded_isStable
    (affineChartBoundedChart B S hS F hF hN K hK)
    (affineChartBoundedChart_models_dualizing B S hS F hF hN K K' hK hK')

/-! ### The structure sheaf -/

omit V in
/-- An object in degree zero has no cohomology in the other degrees. -/
theorem isZero_homology_singleFunctor_zero_of_ne {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (X : C) {n : ℤ} (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.singleFunctor C 0).obj X)) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 n h
  · exact DerivedCategory.isZero_of_isLE _ 0 n h

omit V in
/-- The structure sheaf in degree zero on a locally Noetherian scheme has coherent cohomology. -/
theorem schemeCoherent_singleFunctor_unit (T : Scheme.{u}) [IsLocallyNoetherian T] :
    RingedSite.SchemeCoherent T
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard T.Modules) 0).obj
        (SheafOfModules.unit T.ringCatSheaf)) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  intro n
  by_cases hn : n = 0
  · subst hn
    exact AlgebraicGeometry.isCoherent_of_modulesIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso T.Modules 0).app _).symm
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  · exact AlgebraicGeometry.ProperCoherentFiniteType.isCoherent_of_isZero
      (isZero_homology_singleFunctor_zero_of_ne _ hn)

omit V in
/-- The structure sheaf in degree zero is bounded. -/
theorem bounded_singleFunctor_unit (T : Scheme.{u}) :
    RingedSite.ChartClass.bounded T
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard T.Modules) 0).obj
        (SheafOfModules.unit T.ringCatSheaf)) := by
  let : HasDerivedCategory T.Modules := HasDerivedCategory.standard _
  refine ⟨0, 0, fun i hi => isZero_homology_singleFunctor_zero_of_ne _ ?_⟩
  rcases hi with h | h <;> omega

/-- The restriction of the structure sheaf to a chart is `ε^* 𝒪`. -/
def chartRestrictionUnitIso :
    (representedChartDerivedRestriction B S hS hF (chartBase B S hS F V)
        (chartObj B S hS F V).obj.hom (modelChartMap_isEtale B S hS F hF V)).obj
        ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
          (SheafOfModules.unit _)) ≅
      (representedDerivedAssociatedModule B S hS (chartBase B S hS F V)).obj
        ((@DerivedCategory.singleFunctor _ _ _
          (HasDerivedCategory.standard (reprScheme B S hS (chartBase B S hS F V)).Modules) 0).obj
          (SheafOfModules.unit (reprScheme B S hS (chartBase B S hS F V)).ringCatSheaf)) := by
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj (chartBase B S hS F V))
    (isAlgebraicSpace_yoneda B S hS _))
  letI : HasDerivedCategory (reprScheme B S hS (chartBase B S hS F V)).Modules :=
    HasDerivedCategory.standard _
  haveI := etaleModulePullback_additive.{u, u} B S hS (modelChartMap B S hS F hF V)
    (modelChartMap_isEtale B S hS F hF V)
  haveI := preservesFiniteLimits_etaleModulePullback B S hS (modelChartMap B S hS F hF V)
    (modelChartMap_isEtale B S hS F hF V)
  haveI := preservesFiniteColimits_etaleModulePullback B S hS (modelChartMap B S hS F hF V)
    (modelChartMap_isEtale B S hS F hF V)
  haveI := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS
    (modelChartMap B S hS F hF V) (modelChartMap_isEtale B S hS F hF V)
  have u₂ : (etaleModulePullback.{u, u} B S hS (modelChartMap B S hS F hF V)
      (modelChartMap_isEtale B S hS F hF V)).obj (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
    Stacks.SheafOfModules.ModelFinitePresentation.pushforwardUnitIsoOfIso _ (𝟙 _)
  exact ((etaleModulePullback.{u, u} B S hS (modelChartMap B S hS F hF V)
      (modelChartMap_isEtale B S hS F hF V)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (u₂ ≪≫
      (representedAssociatedModuleObjUnitIso B S hS (chartBase B S hS F V)
        (isAlgebraicSpace_yoneda B S hS _)).symm) ≪≫
    ((representedAssociatedModule B S hS (chartBase B S hS F V)
      (isAlgebraicSpace_yoneda B S hS _)).mapDerivedCategorySingleFunctor 0).symm.app _

omit V in
/-- The transport to the model of the structure sheaf is the structure sheaf. -/
def modelDerivedUnitIso :
    (modelDerivedEquivalence B S hS F hF).functor.obj
        ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
          (SheafOfModules.unit _)) ≅
      (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleModelRingedSite B S hS F hF).O)) := by
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  letI := HasDerivedCategory.standard (ModelModules B S hS F hF)
  letI := additive_modulesEquivModelModules_functor B S hS F hF
  have u₁ : (modulesEquivModelModules B S hS F hF).functor.obj (SheafOfModules.unit _) ≅
      SheafOfModules.unit _ :=
    Stacks.SheafOfModules.ModelFinitePresentation.pushforwardUnitIsoOfIso _ (𝟙 _)
  exact
    (((modulesEquivModelModules B S hS F hF).functor).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso u₁

/-- The structure sheaf is modelled at bounded objects on every affine chart. -/
theorem affineChartBoundedChart_models_unit
    (K : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K) (i : AffineChart B S hS F) :
    (affineChartBoundedChart B S hS F hF hN K hK i).Models
      ((RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) i.1).obj
        ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleModelRingedSite B S hS F hF).O)))) := by
  have := i.2
  have := isNoetherian_affineChart B S hS F hF hN i
  let : HasDerivedCategory (reprScheme B S hS (chartBase B S hS F i.1)).Modules :=
    HasDerivedCategory.standard _
  have hc := schemeCoherent_singleFunctor_unit (reprScheme B S hS (chartBase B S hS F i.1))
  refine RingedSite.DualityChart.models_of_iso (affineChartBoundedChart B S hS F hF hN K hK i)
    (M := (RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) i.1).obj
      ((modelDerivedEquivalence B S hS F hF).functor.obj
        ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
          (SheafOfModules.unit _)))) ?_
    ((RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF) i.1).mapIso
      (modelDerivedUnitIso B S hS F hF))
  exact sliceBoundedChart_models B S hS F hF i.1 K.obj _ _ _ _ _ hc
    (bounded_singleFunctor_unit _) (fun n => have := hc n; isQuasicoherent_of_isCoherent _)
    (chartRestrictionUnitIso B S hS F hF i.1)

/-- **Biduality at the structure sheaf, on the model** (Stacks 0E51, at the input of Stacks
0E52): for a dualizing complex `K` on a locally Noetherian algebraic space, the biduality
morphism `𝒪 ⟶ R𝓗om(R𝓗om(𝒪, K), K)` of the equi-universe model is an isomorphism. -/
theorem isIso_derivedBiduality_model_unit
    (K : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K) :
    IsIso (RingedSite.derivedBiduality (smallEtaleModelRingedSite B S hS F hF)
      ((modelDerivedEquivalence B S hS F hF).functor.obj K.obj)
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit _))) :=
  RingedSite.isIso_derivedBiduality_of_models (smallEtaleModelRingedSite B S hS F hF)
    (affineChart_coversTop B S hS F hF) RingedSite.ChartClass.bounded_isStable
    (affineChartBoundedChart B S hS F hF hN K hK)
    (affineChartBoundedChart_models_unit B S hS F hF hN K hK)

end AlgebraicGeometry.Space

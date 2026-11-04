module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCoordinateRatioValueChartUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartCoordinateIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartCoordinate
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBundleModuleSectionsBasis

/-!
# The coordinates of `U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` are the values of `q`

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module of rank `r`,
`P = 𝐏(ℰ ⊕ 𝒪_X)` with affine part `ι : U ⟶ P`, `u : U ⟶ X`, `q : u^*ℰ ⟶ 𝒪_U` the map
`m ↦ (m, 0)/s`, and `V` an affine étale chart of `X` with a morphism `m` to the presenting chart,
on which `ℰ` is free by `e : ℰ|_V ≅ 𝒪_V^{⊕ n}`. The `j`-th coordinate `λ(σ'(k_j)) / λ(σ)` of the
open immersion `U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` for the split datum of `(ℰ ⊕ 𝒪)|_V` is the value of `q`
on the inverse image of the `j`-th basis section of `ℰ(V)` at the chart `U_V` of `U`
(Stacks 0ERW, proof).

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.Space

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite
  AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
    AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]
    {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X) [IsAffine (chartScheme V)]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] in
/-- The inclusion `ι : U ⟶ P`, typed with target the projective bundle `𝐏(ℰ ⊕ 𝒪)`. -/
abbrev projectiveCompletionAffinePartHomBundle :
    projectiveCompletionAffinePart E hr ⟶
      (@projectiveBundle B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)) :=
  projectiveCompletionAffinePartHom E hr

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] in
/-- The ranges of the two spellings of the morphism of schemes of a morphism of the site. -/
theorem range_schemeHom_left_eq_range_toScheme_map {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    Set.range (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
      g.left).base =
      Set.range ((BigFppfOver.toScheme B S hS).map g).base :=
  rfl

omit [IsAffine (chartScheme V)] in
/-- The open immersion `U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` lands in the complement of `𝐏(ℰ|_V)`. -/
theorem range_chartBundleHomOfSite_affinePart_subset :
    Set.range (@chartBundleHomOfSite B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr) V
        ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
        (affinePartChartOverChart E hr m))
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)).base ⊆
      (@Stacks.RelativeProj.splitQuotientComplement _ _ _
        (@isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) V)
        (@isQuasicoherent_chartBundleModule B S hS X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V)
        (chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) V)
        (epi_chartModuleMap biprod.fst biprod.inl biprod.inl_fst V) : Set _) :=
  ((range_schemeHom_left_eq_range_toScheme_map _).trans
    ((range_affinePartOverChartToChartBundle E hr m).trans (Scheme.Opens.range_ι _))).le

/-- The chart diagram `U_V ⟶ V` over `u`, in the spelling of the quotient readings. -/
theorem affinePartChartOverChart_comm_site :
    (affinePartChartOverChart E hr m).1.hom ≫
        ((projectiveCompletionAffinePartHomBundle E hr) ≫
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).hom =
      yoneda.map
        (@CategoryStruct.comp _ _
        ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
        (affinePartChartOverChart E hr m))
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ((SmallEtale.toOver B S hS X.1).obj V)
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V)) ≫ V.1.hom :=
  affinePartChartOverChart_comm E hr m

/-- The identification `u^*𝒪_X ≅ 𝒪_U` through `ι^*𝒪_P` sends the inverse image of `1` at the
chart `U_V` to `1`. -/
theorem modulePullbackUnitCompIso_inv_comp_unitIso_chartSection_one :
    ((modulePullbackUnitCompIso (projectiveCompletionAffinePartHomBundle E hr)
      (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).inv ≫
      (modulePullbackUnitIso B S hS (projectiveCompletionAffinePartHomBundle E hr)).hom).val.app
        (op (affinePartChartOverChart E hr m))
        (modulePullbackChartSection B S hS
          ((projectiveCompletionAffinePartHomBundle E hr) ≫
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)))
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          ⟨affinePartChartOverChart E hr m, V,
            (@CategoryStruct.comp _ _
            ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
            (affinePartChartOverChart E hr m))
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ((SmallEtale.toOver B S hS X.1).obj V)
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V)),
            affinePartChartOverChart_comm_site E hr m⟩
          (1 : (structureRingSheaf B S hS X).obj.obj (op V))) =
      (1 : (structureRingSheaf B S hS (projectiveCompletionAffinePart E hr)).obj.obj
            (op (affinePartChartOverChart E hr m))) := by
  rw [← modulePullbackUnitIso_inv_val_app_one B S hS
    ((projectiveCompletionAffinePartHomBundle E hr) ≫
    (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)))]
  exact modulePullbackUnitCompIso_inv_comp_unitIso_unit
    (projectiveCompletionAffinePartHomBundle E hr)
    (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)) (Uc := affinePartChartOverChart E hr m)
    (W := presentationChart (@projectiveBundleChartPresentation B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr)))
    (V := bundleBaseChart X) (affinePartOverChartToPresenting E hr m)
    (@projectiveBundleChartProj B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr))
    (affinePartChartOverChart_hom_comp E hr m)
      (presentationChart_projectiveCompletion_hom_comp E hr)

omit [IsAffine (chartScheme V)] in
/-- The chart `U_V ⟶ V ⟶ X` is `U_V ⟶ U ⟶ X`, in the spelling of the quotient readings. -/
theorem representedSpaceMap_affinePartChartToChartSite_comp :
    representedSpaceMap B S hS
      (@CategoryStruct.comp _ _
      ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
      (affinePartChartOverChart E hr m))
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ((SmallEtale.toOver B S hS X.1).obj V)
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V)) ≫
        chartToSpace B S hS X V =
      @CategoryStruct.comp _ _
        (representedAlgebraicSpace B S hS
        ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
        (affinePartChartOverChart E hr m)))
        (projectiveCompletionAffinePart E hr) X
        (chartToSpace B S hS _ (affinePartChartOverChart E hr m))
        ((projectiveCompletionAffinePartHomBundle E hr) ≫
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))) :=
  representedSpaceMap_affinePartOverChartToChart_comp E hr m

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- The section `s : 𝒪_P ⟶ 𝒪_P(1)`, in the spelling of the projective bundle. -/
theorem projectiveCompletionSectionHom_eq_bundle :
    projectiveCompletionSectionHom E hr =
      (modulePullbackUnitIso B S hS
        (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).inv ≫
        (modulePullback B S hS
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map
          (addUnitInr X.2 E : (SheafOfModules.unit (structureRingSheaf B S hS X) :
        Modules.{u, u} B S hS X.1 X.2) ⟶ addUnit X.2 E) ≫
          (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom := by
  unfold projectiveCompletionSectionHom
  with_reducible rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- `s` is invertible on the affine part, in the spelling of the projective bundle. -/
theorem isIso_modulePullback_projectiveCompletionAffinePartHom_sectionHom_bundle :
    IsIso ((modulePullback B S hS (projectiveCompletionAffinePartHomBundle E hr)).map
      ((modulePullbackUnitIso B S hS
        (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).inv ≫
        (modulePullback B S hS
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map
          (addUnitInr X.2 E : (SheafOfModules.unit (structureRingSheaf B S hS X) :
        Modules.{u, u} B S hS X.1 X.2) ⟶ addUnit X.2 E) ≫
          (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom)) := by
  rw [← projectiveCompletionSectionHom_eq_bundle]
  exact isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom E hr

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- `AlgebraicGeometry.Space.chartUnitReadingIso` is the composite of `schemeReadingChartIso` and
`restrictToChartSchemeUnitIso`. -/
theorem chartUnitReadingIso_eq (W : SmallEtale B S hS X.1) :
    chartUnitReadingIso (X := X) W =
      (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) W ≪≫
      restrictToChartSchemeUnitIso B S hS X.1 X.2 W) :=
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- The section `σ : 𝒪_V ⟶ (ℰ ⊕ 𝒪)|_V` of the split datum on a chart. -/
theorem completionChartUnitSplitting_σ_eq :
    (completionChartUnitSplitting E V).σ =
      (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) V ≪≫
      restrictToChartSchemeUnitIso B S hS X.1 X.2 V).inv ≫
        schemeReadingMap (chartToSpace B S hS X V)
          (addUnitInr X.2 E : (SheafOfModules.unit (structureRingSheaf B S hS X) :
            Modules.{u, u} B S hS X.1 X.2) ⟶ addUnit X.2 E) := by
  show (chartUnitReadingIso (X := X) V).inv ≫ chartModuleMap (addUnitInr X.2 E) V = _
  rw [chartUnitReadingIso_eq]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- The section `σ' : ℰ|_V ⟶ (ℰ ⊕ 𝒪)|_V` of the split datum on a chart. -/
theorem completionChartUnitSplitting_σ'_eq :
    (completionChartUnitSplitting E V).σ' =
      schemeReadingMap (chartToSpace B S hS X V) (biprod.inl : E ⟶ addUnit X.2 E) :=
  rfl

/-- **The coordinates of `U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` are the values of `q`**, in the spelling of
the quotient readings: for a trivialization `e` of `ℰ` over the affine chart `V`, the `j`-th
coordinate `λ(σ'(k_j)) / λ(σ)` of the open immersion for the split datum of `(ℰ ⊕ 𝒪)|_V` is the
value of `q : u^*ℰ ⟶ 𝒪_U` on the inverse image of the `j`-th basis section of `ℰ(V)` at the chart
`U_V` of `U`. -/
theorem projectiveCompletionAffinePartQuotient_chartSection_eq_coordVector_site {n : Type u}
    [DecidableEq n] [Finite n]
    (e : (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E).over V ≅
      SheafOfModules.free (R := (structureRingSheaf B S hS X).over V) n) (j : n) :
    haveI := @isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
      (isQuasicoherentOnSite_addUnit hr) V
    haveI := @isQuasicoherent_chartBundleModule B S hS X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V
    haveI := epi_chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) biprod.inl biprod.inl_fst V
    ((modulePullbackCompIso B S hS (projectiveCompletionAffinePartHomBundle E hr)
      (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).inv.app E ≫
        (modulePullback B S hS (projectiveCompletionAffinePartHomBundle E hr)).map
          ((modulePullback B S hS
            (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map biprod.inl ≫
        (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom) ≫
        @inv _ _ _ _ ((modulePullback B S hS (projectiveCompletionAffinePartHomBundle E hr)).map
          ((modulePullbackUnitIso B S hS
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).inv ≫
        (modulePullback B S hS
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map
          (addUnitInr X.2 E : (SheafOfModules.unit (structureRingSheaf B S hS X) :
        Modules.{u, u} B S hS X.1 X.2) ⟶ addUnit X.2 E) ≫
          (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom))
          (isIso_modulePullback_projectiveCompletionAffinePartHom_sectionHom_bundle E hr) ≫
        (modulePullbackUnitIso B S hS (projectiveCompletionAffinePartHomBundle E hr)).hom).val.app
          (op (affinePartChartOverChart E hr m))
      (modulePullbackChartSection B S hS
        ((projectiveCompletionAffinePartHomBundle E hr) ≫
        (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))) E
        ⟨affinePartChartOverChart E hr m, V,
          (@CategoryStruct.comp _ _
          ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
          (affinePartChartOverChart E hr m))
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ((SmallEtale.toOver B S hS X.1).obj V)
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V)),
          affinePartChartOverChart_comm_site E hr m⟩
        (SymAlgSections.sectionsBasis B S hS X
          (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e j)) =
      Stacks.RelativeProj.UnitSplitting.coordVector
        (chartBundleModuleFreeIso E V e (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))
        ((completionChartUnitSplitting E V).splitCoordMap
          (@chartBundleHomOfSite B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr) V
        ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
        (affinePartChartOverChart E hr m))
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m))
          (chartBundleHomOfSite_comp_chartBundleToChart (hE := isQuasicoherentOnSite_addUnit hr) _
            _ _)
          (range_chartBundleHomOfSite_affinePart_subset E hr m)) j := by
  obtain ⟨ε, hML⟩ := exists_quotientReadingHyp_comp_projectiveBundleTautological (addUnit X.2 E)
    (hE := isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr) m
    (A := ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
      (affinePartChartOverChart E hr m)))
    (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
    (projectiveCompletionAffinePartHomBundle E hr)
      (chartToSpace B S hS _ (affinePartChartOverChart E hr m))
    (representedSpaceMap_affinePartOverChartToPresenting_comp_atlas E hr m)
    (representedSpaceMap_affinePartChartToChartSite_comp E hr m)
  have key1 := modulePullbackChartSection_value_eq_coordVector_of_chartUnit_site
    (projectiveCompletionAffinePartHomBundle E hr)
      (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))
        (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
    (SheafOfModules.isQuasicoherentOnSite_unit _) biprod.inl
    (addUnitInr X.2 E : (SheafOfModules.unit (structureRingSheaf B S hS X) :
        Modules.{u, u} B S hS X.1 X.2) ⟶ addUnit X.2 E)
    (affinePartChartOverChart E hr m) V
      (@CategoryStruct.comp _ _
      ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
      (affinePartChartOverChart E hr m))
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ((SmallEtale.toOver B S hS X.1).obj V)
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V))
    (affinePartChartOverChart_comm_site E hr m)
    (representedSpaceMap_affinePartChartToChartSite_comp E hr m)
    (hFq := @isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
      (isQuasicoherentOnSite_addUnit hr) V)
    (hEq' := @isQuasicoherent_chartBundleModule B S hS X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V)
    (hus := epi_chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) biprod.inl biprod.inl_fst V)
    (completionChartUnitSplitting E V)
    (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) V ≪≫
      restrictToChartSchemeUnitIso B S hS X.1 X.2 V) rfl
    (schemeReadingChartIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (projectiveCompletionAffinePart E hr).1
          (projectiveCompletionAffinePart E hr).2).O))) (affinePartChartOverChart E hr m) ≪≫
      restrictToChartSchemeUnitIso B S hS (projectiveCompletionAffinePart E hr).1
        (projectiveCompletionAffinePart E hr).2 (affinePartChartOverChart E hr m)) rfl
    (completionChartUnitSplitting_σ_eq E) (completionChartUnitSplitting_σ'_eq E)
    (@chartBundleHomOfSite B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr) V
        ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
        (affinePartChartOverChart E hr m))
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m))
    (chartBundleHomOfSite_comp_chartBundleToChart (hE := isQuasicoherentOnSite_addUnit hr) _ _ _)
    (range_chartBundleHomOfSite_affinePart_subset E hr m) ε
  have key2 := key1 ?h8
    (hs := isIso_modulePullback_projectiveCompletionAffinePartHom_sectionHom_bundle E hr)
  case h8 =>
    intro M hM σ₀
    have hh := hML M hM σ₀
    with_reducible exact hh
  have key3 := key2 (modulePullbackUnitCompIso_inv_comp_unitIso_chartSection_one E hr m)
    (chartBundleModuleFreeIso E V e (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) j _
    (basisMap_chartBundleModuleFreeIso_app_one E V e _ j)
  exact key3

end AlgebraicGeometry.Space

end

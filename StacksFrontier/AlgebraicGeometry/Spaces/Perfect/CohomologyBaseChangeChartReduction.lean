module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartPointLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfIsFinitePresentation

/-!
# Cohomology and base change: reduction to an affine base

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `E ∈ D(𝒪_X)` and `𝒢^•` a complex of
`𝒪_X`-modules. For an affine étale chart `V ⟶ Y` with base change `f_V : X_V ⟶ V`, the pullback
of `K = Rf_*(E ⊗^L 𝒢^•)` to `V` is `Rf_{V,*}(E|_{X_V} ⊗^L 𝒢^•|_{X_V})` (étale base change and
Stacks 07A4), and perfectness of `K` is local on the affine charts of `Y`. The hypotheses of
Stacks 0A1P on `f`, `E` and `𝒢^•` pass to `f_V`. This is the step "the question is local on
`Y`, hence we may assume `Y` affine" of the proof of Stacks 0A1P.

## Main results

* `AlgebraicGeometry.Space.isPerfect_of_forall_isAffineChart_smallEtaleDerivedModulePullback`
* `AlgebraicGeometry.Space.chartBaseChangeDerivedTensorPushforwardIso`
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedTensor_of_chartBaseChange`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **Perfectness is local on the affine étale charts.** If the derived pullback of `E` to every
affine étale chart of `Y` is perfect, then `E` is perfect. -/
theorem isPerfect_of_forall_isAffineChart_smallEtaleDerivedModulePullback
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (h : ∀ V : SmallEtale B S hS Y.1, IsAffineChart B S hS Y.1 V →
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1
        (chartSpace B S hS Y V).2)
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y V)).obj E)) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) E := by
  refine isPerfect_of_forall_isPerfect_etaleRestrict B S hS
    (fun V : {V : SmallEtale B S hS Y.1 // IsAffineChart B S hS Y.1 V} => chartSpace B S hS Y V.1)
    (fun V => chartToSpace B S hS Y V.1) (fun V => isEtale_chartToSpace B S hS Y V.1)
    (fun x => ?_) E fun V => isPerfect_of_iso B S hS (h V.1 V.2)
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS _ _).app E)
  obtain ⟨i, y, hy⟩ := SmallEtale.exists_mem_range_of_coversTop B S hS Y.2
    (SmallEtale.coversTop_affineCharts B S hS Y.1) x
  exact ⟨i, y, hy⟩

section ChartBaseChange

variable (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)

/-- **`Rf_*(E ⊗^L 𝒢^•)` restricted to an étale chart.** For an étale chart `j : V ⟶ Y` with
base change `f_V : X_V ⟶ V` and `j' : X_V ⟶ X`,
`Lj^* Rf_*(E ⊗^L 𝒢^•) ≅ Rf_{V,*}(Lj'^*E ⊗^L j'^*𝒢^•)`. -/
def chartBaseChangeDerivedTensorPushforwardIso
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y V)).obj
        ((derivedModulePushforward B S hS f).obj
          (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) ≅
      (derivedModulePushforward B S hS (chartBaseChangeProjection B S hS f V)).obj
        (((smallEtaleDerivedTensor B S hS (chartBaseChangeSpace B S hS f V)).obj
          ((smallEtaleDerivedModulePullback B S hS
            (chartBaseChangeInclusion B S hS f V)).obj E)).obj
          (DerivedCategory.Q.obj (((modulePullback B S hS
            (chartBaseChangeInclusion B S hS f V)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G))) :=
  haveI := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f (chartToSpace B S hS Y V)
    (chartBaseChangeProjection B S hS f V) (chartBaseChangeInclusion B S hS f V)
    (isPullback_chartBaseChangeInclusion B S hS f V) (isEtale_chartToSpace B S hS Y V)
    (relativelyRepresentable_chartToSpace B S hS Y V)
    (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))
  asIso (smallEtaleDerivedModuleBaseChangeMap B S hS f (chartToSpace B S hS Y V)
      (chartBaseChangeProjection B S hS f V) (chartBaseChangeInclusion B S hS f V)
      (isPullback_chartBaseChangeInclusion B S hS f V).w
      (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) ≪≫
    (derivedModulePushforward B S hS (chartBaseChangeProjection B S hS f V)).mapIso
      ((smallEtaleDerivedPullbackTensorIso (chartBaseChangeInclusion B S hS f V)).app
          (E, DerivedCategory.Q.obj G) ≪≫
        ((smallEtaleDerivedTensor B S hS (chartBaseChangeSpace B S hS f V)).obj
          ((smallEtaleDerivedModulePullback B S hS
            (chartBaseChangeInclusion B S hS f V)).obj E)).mapIso
          (smallEtaleDerivedModulePullbackObjQIsoOfIsEtale (chartBaseChangeInclusion B S hS f V)
            (isEtale_chartBaseChangeInclusion B S hS f V) G))

/-- **Perfectness of `Rf_*(E ⊗^L 𝒢^•)` is local on the affine charts of the base**: it holds
when it holds for every base change `f_V : X_V ⟶ V` of `f` to an affine étale chart `V` of `Y`,
with `E` and `𝒢^•` restricted to `X_V`. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_of_chartBaseChange
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (h : ∀ V : SmallEtale B S hS Y.1, IsAffineChart B S hS Y.1 V →
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1
        (chartSpace B S hS Y V).2)
        ((derivedModulePushforward B S hS (chartBaseChangeProjection B S hS f V)).obj
          (((smallEtaleDerivedTensor B S hS (chartBaseChangeSpace B S hS f V)).obj
            ((smallEtaleDerivedModulePullback B S hS
              (chartBaseChangeInclusion B S hS f V)).obj E)).obj
            (DerivedCategory.Q.obj (((modulePullback B S hS
              (chartBaseChangeInclusion B S hS f V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj G))))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) :=
  isPerfect_of_forall_isAffineChart_smallEtaleDerivedModulePullback _ fun V hV =>
    isPerfect_of_iso B S hS (h V hV) (chartBaseChangeDerivedTensorPushforwardIso f V E G).symm

/-- The base change of a morphism of finite presentation to an étale chart of the target is of
finite presentation (Stacks 03XR). -/
theorem isFinitePresentation_chartBaseChangeProjection
    (hf : IsFinitePresentation B S hS f.hom) :
    IsFinitePresentation B S hS (chartBaseChangeProjection B S hS f V).hom :=
  (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_chartBaseChangeInclusion B S hS f V) hf

/-- The base change of a morphism locally of finite type to an étale chart of the target is
locally of finite type. -/
theorem isLocallyOfFiniteType_chartBaseChangeProjection
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    IsLocallyOfFiniteType B S hS (chartBaseChangeProjection B S hS f V).hom :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_chartBaseChangeInclusion B S hS f V) hf

end ChartBaseChange

section ModulePullback

variable {X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y}

/-- A module of finite presentation on an algebraic space is quasi-coherent. -/
theorem isQuasicoherentOnSite_of_isFinitePresentation (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsFinitePresentation) : F.IsQuasicoherentOnSite :=
  have := hF
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData F).choose

/-- A module of finite presentation, viewed as a module over the tensor ring sheaf of the small
étale ringed topos, is of finite presentation. -/
private theorem isFinitePresentation_tensorRingSheaf (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsFinitePresentation) :
    SheafOfModules.IsFinitePresentation
      (show SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)) from F) :=
  hF

/-- A module of finite presentation on an algebraic space is of finite type on the site. -/
theorem isFiniteTypeOnSite_of_isFinitePresentation (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsFinitePresentation) : SheafOfModules.IsFiniteTypeOnSite F :=
  have h := @Stacks.Sheaves.FinitePresentation.isFinitePresentationOnSite_of_isFinitePresentation
    (smallEtaleRingedTopos B S hS X) _ _ _ _ _ _ _ _ (isFinitePresentation_tensorRingSheaf F hF)
  @SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _ h

/-- **The coefficient conditions of Stacks 0A1P are stable under base change.** In a cartesian
square, the pullback of a module of finite presentation, flat over `Y` and with support proper
over `Y`, is of finite presentation, flat over `Y'` and with support proper over `Y'`. -/
theorem modulePullback_coefficient_conditions (sq : IsPullback g' f' f g)
    (hft : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hFflat : IsFlatOver B S hS X.2 f.hom F)
    (hFsupp : HasProperSupport B S hS X.2 Y.2 f.hom hft ((SheafOfModules.toSheaf _).obj F)) :
    ((modulePullback B S hS g').obj F).IsFinitePresentation ∧
      IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) ∧
      HasProperSupport B S hS X'.2 Y'.2 f'.hom
        ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq hft)
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F)) := by
  have hqc := isQuasicoherentOnSite_of_isFinitePresentation F hFfp
  have hfin := isFiniteTypeOnSite_of_isFinitePresentation F hFfp
  have hqc' := isQuasicoherentOnSite_modulePullback_of_isFinitePresentation B S hS g' F hFfp
  have := isFinitePresentation_tensorRingSheaf F hFfp
  refine ⟨Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules
      (smallEtaleRingedToposModulesHom B S hS g') _,
    isFlatOver_modulePullback B S hS sq F hFflat,
    isClosed_supportOfSheaf_modulePullback B S hS g' F hfin, ?_⟩
  exact isProperOver_supportOfSheaf_modulePullback B S hS sq hft F hqc hfin hFsupp.2

end ModulePullback

end AlgebraicGeometry.Space

end

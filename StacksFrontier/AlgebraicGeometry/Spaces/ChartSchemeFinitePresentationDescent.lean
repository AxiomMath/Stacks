module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardQuasicoherent

/-!
# Finite presentation of a module and of its direct image along a finite morphism

Let `f : X ⟶ Y` be a finite morphism of finite presentation of algebraic spaces over a scheme `S`
and let `F` be a quasi-coherent `𝒪_X`-module on the small étale site of `X`. Then `F` is of finite
presentation exactly when its direct image `f_*F` is. At an étale scheme chart `V` of `Y`, the
restriction of `F` to the base change `V ×_Y X` is of finite presentation exactly when the
restriction of `f_*F` to `V` is.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSchemeModule_iff`: quasi-coherence
  transports across the chart-scheme identification.
* `AlgebraicGeometry.Space.isFinitePresentation_restrictChartSchemeModule_iff` and
  `AlgebraicGeometry.Space.isQuasicoherent_restrictChartSchemeModule`: the Zariski restriction of
  a quasi-coherent module on the small étale site of a chart scheme.
* `AlgebraicGeometry.Space.isFinitePresentation_over_baseChangeChart_iff`: the statement at an
  étale scheme chart of `Y`.
* `isFinitePresentation_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite`: a
  quasi-coherent `𝒪_X`-module is of finite presentation if and only if its direct image is.

## References

* [Stacks Project, Tag 0610](https://stacks.math.columbia.edu/tag/0610)
* [Stacks Project, Tag 05B4](https://stacks.math.columbia.edu/tag/05B4)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable (U : AlgebraicSpaces B S hS) (W : (smallEtaleRingedSite B S hS U.1 U.2).C)

/-- A module on the slice at an étale chart is quasi-coherent if and only if the module it becomes
on the small étale site of the scheme underlying that chart is. -/
theorem isQuasicoherentOnSite_chartSchemeModule_iff
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS U.1 U.2).over W).O)) :
    M.IsQuasicoherentOnSite ↔
      (chartSchemeSiteModule B S hS U W M).IsQuasicoherentOnSite := by
  have := hasWeakSheafify_chartSlice B S hS U W
  have := wEqualsLocallyBijective_chartSlice B S hS U W
  have : ∀ X : Over W,
      HasSheafify (((smallEtaleRingedSite B S hS U.1 U.2).over W).J.over X)
        AddCommGrpCat.{u} :=
    inferInstanceAs (∀ X : Over W,
      HasSheafify (((smallEtaleRingedSite B S hS U.1 U.2).J.over W).over X) AddCommGrpCat.{u})
  have : ∀ X : Over W,
      (((smallEtaleRingedSite B S hS U.1 U.2).over W).J.over X).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
    inferInstanceAs (∀ X : Over W,
      (((smallEtaleRingedSite B S hS U.1 U.2).J.over W).over X).WEqualsLocallyBijective
        AddCommGrpCat.{u})
  have := isDenseSubsite_chartSchemeIdentification_inverse B S hS U W
  have := isDenseSubsite_chartSchemeIdentification_functor B S hS U W
  have := isContinuous_chartSchemeIdentification_functor B S hS U W
  have := isContinuous_chartSchemeIdentification_inverse B S hS U W
  exact (Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff
    (chartSchemeIdentification B S hS U W) _ M).symm

/-- A quasi-coherent module on the small étale site of the scheme underlying an étale chart is of
finite presentation if and only if its restriction to the small Zariski site is. -/
theorem isFinitePresentation_restrictChartSchemeModule_iff
    (N : SheafOfModules.{u} (chartSchemeSiteStructureSheaf B S hS U W))
    (hN : N.IsQuasicoherentOnSite) :
    SheafOfModules.IsFinitePresentation
        (R := ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W)).ringCatSheaf)
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W))
          (chartOverObject B S hS U W).left.property).obj N) ↔
      N.IsFinitePresentation :=
  _root_.AlgebraicGeometry.SmallEtale.isFinitePresentation_restrictModule_iff
    (associatedBigEtaleSite B) _ _ N hN

/-- The restriction to the small Zariski site of a quasi-coherent module on the small étale site of
the scheme underlying an étale chart is quasi-coherent. -/
theorem isQuasicoherent_restrictChartSchemeModule
    (N : SheafOfModules.{u} (chartSchemeSiteStructureSheaf B S hS U W))
    (hN : N.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent
      (R := ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W)).ringCatSheaf)
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W))
        (chartOverObject B S hS U W).left.property).obj N) :=
  _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
    (associatedBigEtaleSite B) _ _ N hN

end Chart

section Descent

variable {X Y : AlgebraicSpaces B S hS}

/-- For a finite morphism of finite presentation `f : X ⟶ Y` of algebraic spaces, a quasi-coherent
`𝒪_X`-module `F` restricted to the base change `V ×_Y X` of an étale scheme chart `V` of `Y` is of
finite presentation exactly when the restriction of `f_*F` to `V` is. -/
theorem isFinitePresentation_over_baseChangeChart_iff (f : X ⟶ Y)
    (hf : IsFinite B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS Y.1) :
    (F.over (baseChangeChart B S hS f
        (relativelyRepresentable_hom_of_isFinite B S hS f hf) V)).IsFinitePresentation ↔
      (((smallBaseChangeModulePushforward B S hS f
        (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj F).over
          V).IsFinitePresentation := by
  set hrep := relativelyRepresentable_hom_of_isFinite B S hS f hf
  have hqcX : (F.over (baseChangeChart B S hS f hrep V)).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_iff_forall_over B S hS X.1 X.2 F).1 hqc _
  have hqcY : (((smallBaseChangeModulePushforward B S hS f hrep).obj F).over
      V).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_iff_forall_over B S hS Y.1 Y.2 _).1
      (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS f hf F hqc) V
  have hqcNX := (isQuasicoherentOnSite_chartSchemeModule_iff B S hS X
    (baseChangeChart B S hS f hrep V) _).1 hqcX
  have hqcNY := (isQuasicoherentOnSite_chartSchemeModule_iff B S hS Y V _).1 hqcY
  refine Iff.trans (isFinitePresentation_chartSchemeModule_iff B S hS X
    (baseChangeChart B S hS f hrep V) _) ?_
  refine Iff.trans ?_ (isFinitePresentation_chartSchemeModule_iff B S hS Y V _).symm
  refine Iff.trans (isFinitePresentation_restrictChartSchemeModule_iff B S hS X
    (baseChangeChart B S hS f hrep V) _ hqcNX).symm ?_
  refine Iff.trans ?_ (isFinitePresentation_restrictChartSchemeModule_iff B S hS Y V _ hqcNY)
  have := isQuasicoherent_restrictChartSchemeModule B S hS X
    (baseChangeChart B S hS f hrep V) _ hqcNX
  have := isFinite_baseChangeChartHom B S hS f hrep hf V
  have iso := (_root_.AlgebraicGeometry.SmallEtale.restrictModuleObjPushforwardIso
      (associatedBigEtaleSite B) (baseChangeChartHom B S hS f hrep V).left
      (chartSchemeSiteModule B S hS X (baseChangeChart B S hS f hrep V)
        (F.over (baseChangeChart B S hS f hrep V)))).symm ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS Y V))
      (chartOverObject B S hS Y V).left.property).mapIso
      ((chartSchemeSiteModulePushforwardIso B S hS f hrep V
        (F.over (baseChangeChart B S hS f hrep V))).symm ≪≫
        eqToIso (congrArg (chartSchemeSiteModule B S hS Y V)
          (over_smallBaseChangeModulePushforward_obj B S hS f hrep V F).symm))
  refine Iff.trans
    (_root_.AlgebraicGeometry.isFinitePresentation_iff_pushforward_isFinitePresentation _
      (finitePresentation_baseChangeChartHom B S hS f hrep hfp V) _) ?_
  exact ⟨Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso iso,
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso iso.symm⟩

/-- For a finite morphism `f : X ⟶ Y` of finite presentation of algebraic spaces a quasi-coherent
`𝒪_X`-module `F` is of finite presentation if and only if its direct image `f_*F` is. -/
@[stacks 0610]
theorem isFinitePresentation_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite
    (f : X ⟶ Y) (hf : IsFinite B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite) :
    F.IsFinitePresentation ↔
      ((smallBaseChangeModulePushforward B S hS f
        (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj F).IsFinitePresentation :=
  isFinitePresentation_iff_smallBaseChangePushforward B S hS f hf hfp F
    (isFinitePresentation_over_baseChangeChart_iff B S hS f hf hfp F hqc)

end Descent

end AlgebraicGeometry.Space

end

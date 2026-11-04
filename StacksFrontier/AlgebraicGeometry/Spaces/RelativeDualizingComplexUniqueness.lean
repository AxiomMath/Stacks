module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedHomGluingPullback

/-!
# Uniqueness of relative dualizing complexes of algebraic spaces

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation, and let
`(ω₁, τ₁)`, `(ω₂, τ₂)` be relative dualizing complexes (Stacks 0E5X). Granted that
`𝒪_X ⟶ R𝓗om(ω₁, ω₁)` is an isomorphism (the first half of Stacks 0E5Y), `R𝓗om(ω₁, ω₂)` lies in
`D^{≥ 0}`, since étale locally over affine charts of `Y` both complexes are `a'(𝒪_{Y'})`.

## Main results

* `AlgebraicGeometry.Space.isGE_smallEtaleDerivedModulePullback_obj_of_isEtale`: derived
  pullback along an étale morphism preserves `D^{≥ n}`.
* `AlgebraicGeometry.Space.RelativeDualizingComplex.isGE_smallEtaleDerivedSheafHom`:
  `R𝓗om(ω₁, ω₂)` lies in `D^{≥ 0}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Derived pullback along an étale morphism of algebraic spaces preserves `D^{≥ n}`: it is
étale restriction, an exact functor, on derived categories. -/
theorem isGE_smallEtaleDerivedModulePullback_obj_of_isEtale {X Y : AlgebraicSpaces B S hS}
    (a : X ⟶ Y) (ha : IsEtale B S hS a.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (hK : K.IsGE n) : ((smallEtaleDerivedModulePullback B S hS a).obj K).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro m hm
  have : (etaleModulePullback.{u, u} B S hS a ha).Additive :=
    etaleModulePullback_additive B S hS a ha
  have : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteLimits_etaleModulePullback B S hS a ha
  have : PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS a ha) :=
    preservesFiniteColimits_etaleModulePullback B S hS a ha
  let K' : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) := K
  have h₁ : IsZero ((etaleModulePullback.{u, u} B S hS a ha).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) m).obj K')) :=
    (etaleModulePullback.{u, u} B S hS a ha).map_isZero ((DerivedCategory.isGE_iff K n).1 hK m hm)
  exact (h₁.of_iso
    (((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategoryHomologyIso m).app K')).of_iso
    ((DerivedCategory.homologyFunctor _ m).mapIso
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K))

variable (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

namespace RelativeDualizingComplex

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hf : IsProper B S hS f.hom} {hfl : IsFlat B S hS f.hom}
  {hfp : IsFinitePresentation B S hS f.hom}

/-- **`R𝓗om(ω₁, ω₂)` lies in `D^{≥ 0}`** for relative dualizing complexes `ω₁`, `ω₂`, granted that
`𝒪_X ⟶ R𝓗om(ω₁, ω₁)` is an isomorphism. On a chart of `X` lying over an affine chart of `Y`
both complexes restrict to `a'(𝒪_{Y'})`, so there `R𝓗om(ω₁, ω₂)` is `R𝓗om(ω₁, ω₁)`, which is
`𝒪_X` in degree `0`. -/
theorem isGE_smallEtaleDerivedSheafHom (ω₁ ω₂ : RelativeDualizingComplex hZ f hf hfl hfp)
    (h₁ : IsIso (smallEtaleDerivedHomothety B S hS X ω₁.ω)) :
    (((smallEtaleDerivedSheafHom B S hS X).obj (op ω₁.ω)).obj ω₂.ω).IsGE 0 := by
  have h₁₁ : (((smallEtaleDerivedSheafHom B S hS X).obj (op ω₁.ω)).obj ω₁.ω).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso (asIso (smallEtaleDerivedHomothety B S hS X ω₁.ω)) 0
  refine isGE_of_isGE_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (coversTop_affineChartDiagramCharts B S hS f) _ 0 fun i => ?_
  obtain ⟨-, V, q, hq, hVaff⟩ := i.2
  let g := chartToSpace B S hS Y V
  have hY' : IsAffineSpace B S hS (chartSpace B S hS Y V).1 :=
    isAffineSpace_chartSpace B S hS Y V hVaff
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  obtain ⟨e₁, -⟩ := ω₁.isAffineBaseChangePair (pullback.snd f g) g (pullback.fst f g) sq hY'
  obtain ⟨e₂, -⟩ := ω₂.isAffineBaseChangePair (pullback.snd f g) g (pullback.fst f g) sq hY'
  have hfac : chartToSpace B S hS X i.1 ≫ f = chartSpaceMapOver B S hS q ≫ g :=
    (chartSpaceMapOver_comp_chartToSpace B S hS f q hq).symm
  let ψ : chartSpace B S hS X i.1 ⟶ pullback f g := pullback.lift _ _ hfac
  have hψ : ψ ≫ pullback.fst f g = chartToSpace B S hS X i.1 := pullback.lift_fst _ _ _
  let T : ∀ ω : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)),
      (smallEtaleDerivedModulePullback B S hS ψ).obj
          ((smallEtaleDerivedModulePullback B S hS (pullback.fst f g)).obj ω) ≅
        (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X i.1)).obj ω := fun ω =>
    (smallEtaleDerivedModulePullbackCompIso B S hS ψ (pullback.fst f g)).app ω ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS hψ).app ω
  let ι := (T ω₂.ω).symm ≪≫ (smallEtaleDerivedModulePullback B S hS ψ).mapIso (e₂ ≪≫ e₁.symm) ≪≫
    T ω₁.ω
  have hA := isGE_smallEtaleDerivedModulePullback_obj_of_isEtale
    (chartToSpace B S hS X i.1) (isEtale_chartToSpace B S hS X i.1) _ 0 h₁₁
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((smallEtaleDerivedSheafHomChartIso B S hS X i.1 ω₁.ω ω₁.ω ≪≫
      (((smallEtaleDerivedSheafHom B S hS (chartSpace B S hS X i.1)).obj _).mapIso ι).symm ≪≫
        (smallEtaleDerivedSheafHomChartIso B S hS X i.1 ω₁.ω ω₂.ω).symm)) 0

end RelativeDualizingComplex

end AlgebraicGeometry.Space

end

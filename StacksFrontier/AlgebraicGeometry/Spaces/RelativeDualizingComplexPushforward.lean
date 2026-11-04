module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedHomothety
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocalHigher
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMateIso

/-!
# The direct image of a relative dualizing complex is concentrated in nonpositive degrees

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation and
`(ω, τ)` a relative dualizing complex for `X/Y` (Stacks 0E5X). Étale locally on `Y` the pair is
`(a'(𝒪_{Y'}), Tr)` over an affine `Y'`, and direct image commutes with étale base change, so
`Rf_* ω` has vanishing cohomology sheaves in positive degrees as soon as every `Rf'_* a'(𝒪_{Y'})`
does. This is the second half of Stacks 0E5Y, reduced to Stacks 0E5V (2).

## Main results

* `AlgebraicGeometry.Space.RelativeDualizingComplex.isLE_derivedModulePushforward_of_affine`:
  `Rf_* ω` lies in `D^{≤ 0}`, granted that `Rf'_* a'(𝒪_{Y'})` does for every base change of `f`
  to an affine `Y'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

namespace RelativeDualizingComplex

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hf : IsProper B S hS f.hom} {hfl : IsFlat B S hS f.hom}
  {hfp : IsFinitePresentation B S hS f.hom}

/-- Over an affine étale chart of `Y`, the pullback of `ω` to the fibre product is the base change
object `a'(𝒪_{Y'})`. -/
private theorem nonempty_iso_pullback_chart (ω : RelativeDualizingComplex hZ f hf hfl hfp)
    (V : SmallEtale B S hS Y.1) (hV : IsAffineChart B S hS Y.1 V) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS
        (pullback.fst f (chartToSpace B S hS Y V))).obj ω.ω ≅
      ((affineBaseChangeRightAdjoint hZ (IsPullback.of_hasPullback f (chartToSpace B S hS Y V))
        hfp (isAffineSpace_chartSpace B S hS Y V hV)).obj
          (derivedStructureSheaf B S hS (chartSpace B S hS Y V).1
            (chartSpace B S hS Y V).2)).obj) :=
  let ⟨e, _⟩ := ω.isAffineBaseChangePair _ _ _ (IsPullback.of_hasPullback f _)
    (isAffineSpace_chartSpace B S hS Y V hV)
  ⟨e⟩

/-- **`Rf_* ω` lies in `D^{≤ 0}`, granted the affine case.** If `Rf'_* a'(𝒪_{Y'})` has vanishing
cohomology sheaves in positive degrees for every base change `f'` of `f` to an affine `Y'`, then
so does `Rf_* ω` for a relative dualizing complex `(ω, τ)`. -/
theorem isLE_derivedModulePushforward_of_affine (ω : RelativeDualizingComplex hZ f hf hfl hfp)
    (h : ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
      ((derivedModulePushforward B S hS f').obj
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj).IsLE 0) :
    ((derivedModulePushforward B S hS f).obj ω.ω).IsLE 0 := by
  refine isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS Y.1) _ 0 fun V => ?_
  let g := chartToSpace B S hS Y V.1
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  obtain ⟨e⟩ := nonempty_iso_pullback_chart ω V.1 V.2
  have := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f g (pullback.snd f g)
    (pullback.fst f g) sq (isEtale_chartToSpace B S hS Y V.1)
    (relativelyRepresentable_chartToSpace B S hS Y V.1) ω.ω
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((asIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g (pullback.snd f g) (pullback.fst f g)
      sq.w ω.ω) ≪≫ (derivedModulePushforward B S hS (pullback.snd f g)).mapIso e).symm) 0

omit hZ in
/-- The homothety map of an object isomorphic to `K` is invertible exactly when that of `K` is. -/
theorem isIso_smallEtaleDerivedHomothety_iff_of_iso {Z : AlgebraicSpaces B S hS}
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))}
    (e : K ≅ K') :
    IsIso (smallEtaleDerivedHomothety B S hS Z K) ↔
      IsIso (smallEtaleDerivedHomothety B S hS Z K') := by
  rw [isIso_smallEtaleDerivedHomothety_iff, isIso_smallEtaleDerivedHomothety_iff]
  exact RingedSite.isIso_derivedHomothety_iff_of_iso _
    ((smallEtaleModelDerivedEquivalence B S hS Z).functor.mapIso e)

omit hZ in
/-- If the homothety map of `K` on `X'` is invertible, so is the homothety map of the pullback
of `K` to any étale chart of `X'` along any morphism to `X` composed with which the chart map is
`a`. -/
theorem isIso_smallEtaleDerivedHomothety_chart_comp {X X' : AlgebraicSpaces B S hS}
    (A' : SmallEtale B S hS X'.1) (p : X' ⟶ X) (a : chartSpace B S hS X' A' ⟶ X)
    (ha : chartToSpace B S hS X' A' ≫ p = a)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (e : (smallEtaleDerivedModulePullback B S hS p).obj K ≅ K')
    (hK' : IsIso (smallEtaleDerivedHomothety B S hS X' K')) :
    IsIso (smallEtaleDerivedHomothety B S hS (chartSpace B S hS X' A')
      ((smallEtaleDerivedModulePullback B S hS a).obj K)) := by
  subst ha
  exact (isIso_smallEtaleDerivedHomothety_iff_of_iso
    (((smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS X' A') p).app K).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X' A')).mapIso e)).2
    ((isIso_map_smallEtaleDerivedHomothety_chartToSpace_iff B S hS X' A' K').1 inferInstance)

/-- **The homothety map of a relative dualizing complex is invertible, granted the affine
case.** If the homothety map `𝒪_{X'} ⟶ R𝓗om(a'(𝒪_{Y'}), a'(𝒪_{Y'}))` is invertible for every
base change `f'` of `f` to an affine `Y'`, then `𝒪_X ⟶ R𝓗om(ω, ω)` is invertible for a relative
dualizing complex `(ω, τ)`. -/
theorem isIso_smallEtaleDerivedHomothety_of_affine (ω : RelativeDualizingComplex hZ f hf hfl hfp)
    (h : ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
      IsIso (smallEtaleDerivedHomothety B S hS X'
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj)) :
    IsIso (smallEtaleDerivedHomothety B S hS X ω.ω) := by
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (coversTop_affineChartDiagramCharts B S hS f) _ fun i => ?_
  obtain ⟨-, V, q, hq, hVaff⟩ := i.2
  refine (isIso_map_smallEtaleDerivedHomothety_chartToSpace_iff B S hS X i.1 ω.ω).2 ?_
  let g := chartToSpace B S hS Y V
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  obtain ⟨e⟩ := nonempty_iso_pullback_chart ω V hVaff
  have hfac : chartToSpace B S hS X i.1 ≫ f = chartSpaceMapOver B S hS q ≫ g :=
    (chartSpaceMapOver_comp_chartToSpace B S hS f q hq).symm
  let ψ : chartSpace B S hS X i.1 ⟶ pullback f g := pullback.lift _ _ hfac
  have hψ : ψ ≫ pullback.fst f g = chartToSpace B S hS X i.1 := pullback.lift_fst _ _ _
  have hg' : IsEtale B S hS (pullback.fst f g).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ sq.flip (isEtale_chartToSpace B S hS Y V)
  let A' : SmallEtale B S hS (pullback f g).1 :=
    ⟨CostructuredArrow.mk ψ.hom, isEtaleChart_of_comp_etale B S hS _ hg' ψ.hom (by
      have h1 : ψ.hom ≫ (pullback.fst f g).hom = i.1.1.hom := congrArg InducedCategory.Hom.hom hψ
      exact h1 ▸ i.1.2)⟩
  exact isIso_smallEtaleDerivedHomothety_chart_comp A' (pullback.fst f g)
    (chartToSpace B S hS X i.1) hψ ω.ω _ e (h (pullback.snd f g) g (pullback.fst f g) sq
      (isAffineSpace_chartSpace B S hS Y V hVaff))

end RelativeDualizingComplex

end AlgebraicGeometry.Space

end

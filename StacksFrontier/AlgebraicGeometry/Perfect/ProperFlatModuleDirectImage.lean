module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.FlatOverModel
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.Descent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# The derived direct image of a flat module along a proper morphism

Let `f : X ⟶ S` be a proper morphism of finite presentation and `ℱ` an `𝒪_X`-module of finite
presentation, flat over `S`. This file proves the two halves of [Stacks, Tag 0B91] (2) for
`Rf_*ℱ`, with `ℱ` placed in degree zero, written out in terms of `derivedPushforward`,
`derivedPullback` and `DerivedCategory.singleFunctor`:

* `Rf_*ℱ` is a perfect object of `D(𝒪_S)`;
* for every cartesian square with `g : S' ⟶ S`, `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ`.

These are the inputs of the proof of [Stacks, Tag 0B9T] in
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatFibreEulerCharacteristic.lean`, which this file
sits below in the import graph; that is why the statements are written out rather than phrased
with the abbreviation `derivedPushforwardModule` of that file.

## Main results

All in the namespace `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic`.

* `nonempty_derivedPullback_derivedPushforward_singleFunctor_iso`:
  `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ` for `f` quasi-compact and quasi-separated and `ℱ` flat over `S` with
  `ℱ` and `(g')^*ℱ` quasi-coherent. The stalk check of the proof of [Stacks, Tag 0A1D] gives the
  pointwise condition of [Stacks, Tag 0DJ8] for `L(g')^*ℱ ⟶ (g')^*ℱ`, and
  [Stacks, Tag 0DJ9] turns it into the invertibility of `Lg^*Rf_*ℱ ⟶ Rf'_*(g')^*ℱ`.
* `isPerfect_derivedPushforward_singleFunctor_of_isAffine_of_baseChange`,
  `isPerfect_derivedPushforward_singleFunctor_of_baseChange`: the source's reduction of
  perfection to base change, through [Stacks, Tag 0A1H]. Perfectness is local on `S`
  ([Stacks, Tag 08CR]) and derived direct image commutes with restriction to an open of `S`
  ([Stacks, Tag 08FE]), so `S` may be taken affine; then `(f, ℱ)` is the base change of a proper
  flat family `(f₀, ℱ₀)` of finite presentation over a Noetherian `T`
  (`AlgebraicGeometry.ProperFlatPerfection.exists_noetherianModel`), `R(f₀)_*ℱ₀` is perfect
  (`AlgebraicGeometry.isPerfect_derivedPushforwardModules_single_of_isNoetherian`), its formation
  commutes with the base change `S ⟶ T`, and the derived pullback of a perfect object is perfect
  ([Stacks, Tag 09UA]). The base-change input is an explicit argument, so that it is visible which
  input the descent spends.
* `isPerfect_derivedPushforward_singleFunctor_of_isProper`: `Rf_*ℱ` is perfect, with the
  base-change input supplied by the previous item.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open AlgebraicGeometry.ProperFlatBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- **`Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ`** for a cartesian square with `f` quasi-compact and
quasi-separated and an `𝒪_X`-module `ℱ` flat over `S` such that `ℱ` and `(g')^*ℱ` are
quasi-coherent: the composite `Lg^*Rf_*ℱ ⟶ Rf'_*L(g')^*ℱ ⟶ Rf'_*(g')^*ℱ` is invertible by
[Stacks, Tag 0DJ9], its pointwise condition being the stalk check of [Stacks, Tag 0DJ8]. -/
theorem nonempty_derivedPullback_derivedPushforward_singleFunctor_iso {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) (hFq : F.IsQuasicoherent)
    (hF'q : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent)
    (hFflat : IsFlatOver f.toLRSHom.toShHom F) :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≅
      (derivedPushforward f'.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj ((Scheme.Modules.pullback g').obj F))) :=
  have h : IsIso (derivedBaseChangeComp f g f' g' hsq.w
      (DerivedCategory.Q.obj (singleDegreeComplex F))
      (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex F)))
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex F))) :=
    isIso_derivedBaseChangeComp_of_pointwiseBaseChange hsq _ _ _
    (isQuasicoherent_homology_of_iso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F).symm
      (isQuasicoherent_homology_singleFunctor F hFq))
    (isQuasicoherent_homology_of_iso (pullbackComplexSingleIso g' F)
      (isQuasicoherent_homology_singleFunctor _ hF'q))
    (fun x' n => isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver hsq hsq.w
      (singleDegreeComplex F) ⟨0, inferInstance⟩ (isFlatOver_singleDegreeComplex f F hFflat) x' n)
  ⟨(derivedPullback g.toLRSHom.toShHom).mapIso ((derivedPushforward f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F)) ≪≫
    @asIso _ _ _ _ _ h ≪≫
    (derivedPushforward f'.toLRSHom.toShHom).mapIso (pullbackComplexSingleIso g' F)⟩

/-- **The perfection half of [Stacks, Tag 0B91] (2) over an affine base, from its base-change
half.** For `V` affine, `f : X ⟶ V` proper of finite presentation and `ℱ` of finite presentation
and flat over `V`, `Rf_*ℱ` is perfect: it is the derived pullback of `R(f₀)_*ℱ₀` for a
Noetherian model `(f₀, ℱ₀)`, which is perfect. -/
theorem isPerfect_derivedPushforward_singleFunctor_of_isAffine_of_baseChange
    (hbc : ∀ {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
      IsPullback g' f' f g → FinitePresentation f → IsProper f →
      ∀ F : X.Modules, F.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom F →
        Nonempty ((derivedPullback g.toLRSHom.toShHom).obj
            ((derivedPushforward f.toLRSHom.toShHom).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≅
          (derivedPushforward f'.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor X'.Modules 0).obj
              ((Scheme.Modules.pullback g').obj F))))
    {X V : Scheme.{u}} [IsAffine V] (f : X ⟶ V)
    (hfp : FinitePresentation f) [IsProper f] (F : X.Modules) [F.IsFinitePresentation]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := V.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
  obtain ⟨T, X₀, _, g, f₀, g', F₀, hprop, hfp₀, hF₀, hfl₀, hsq, ⟨eF⟩⟩ :=
    ProperFlatPerfection.exists_noetherianModel f hfp F hF
  have := hF₀
  obtain ⟨ebc⟩ := hbc f₀ g f g' hsq hfp₀ hprop F₀ hF₀ hfl₀
  have h₀ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := T.toRingedSpace)
      ((derivedPushforward f₀.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X₀.Modules 0).obj F₀)) :=
    isPerfect_derivedPushforwardModules_single_of_isNoetherian f₀ F₀ hfl₀
  have h₁ := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback g.toLRSHom.toShHom _ h₀
  have e₂ : (derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pullback g').obj F₀)) ≅
      (derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
    (derivedPushforward f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctor X.Modules 0).mapIso eF.symm)
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} (ebc ≪≫ e₂) h₁

/-- **The perfection half of [Stacks, Tag 0B91] (2), from its base-change half.** Perfectness is
local on `S`, and on an affine open `V` the restriction of `Rf_*ℱ` is `R(f|_V)_*(ℱ|_{f⁻¹V})`. -/
theorem isPerfect_derivedPushforward_singleFunctor_of_baseChange
    (hbc : ∀ {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
      IsPullback g' f' f g → FinitePresentation f → IsProper f →
      ∀ F : X.Modules, F.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom F →
        Nonempty ((derivedPullback g.toLRSHom.toShHom).obj
            ((derivedPushforward f.toLRSHom.toShHom).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≅
          (derivedPushforward f'.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor X'.Modules 0).obj
              ((Scheme.Modules.pullback g').obj F))))
    {X S : Scheme.{u}} (f : X ⟶ S) (hfp : FinitePresentation f) (hprop : IsProper f)
    (F : X.Modules) (hFfp : F.IsFinitePresentation) (hFflat : IsFlatOver f.toLRSHom.toShHom F) :
    RingedSpace.IsPerfect.{u, u + 1} (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect.{u, u + 1} _
    fun s => ?_
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  refine ⟨V, hsV, ?_⟩
  have : IsAffine V.toScheme := hV
  have := hFfp
  have hfpV : FinitePresentation (f ∣_ V) :=
    FinitePresentation.of_isPullback (isPullback_morphismRestrict f V).flip hfp
  have : IsProper (f ∣_ V) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f V).flip hprop
  have : (F.restrict (f ⁻¹ᵁ V).ι).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_restrict (f ⁻¹ᵁ V).ι F
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation F
      hFfp).1
  have hflV : IsFlatOver (f ∣_ V).toLRSHom.toShHom (F.restrict (f ⁻¹ᵁ V).ι) :=
    (isFlatOver_iff_of_iso _
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F)).2
      (isFlatOver_restrict_of_flatOnPreimage f F V fun x _ => hFflat x)
  have hV' := isPerfect_derivedPushforward_singleFunctor_of_isAffine_of_baseChange hbc (f ∣_ V)
    hfpV (F.restrict (f ⁻¹ᵁ V).ι) hflV
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor S V).app _).symm ?_
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((schemeDerivedPushforwardRestrictOpensIso f V _).symm) ?_
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((schemeDerivedPushforward (f ∣_ V)).mapIso
      (((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).mapDerivedCategorySingleFunctor 0).app
        F).symm) hV'

/-- **[Stacks, Tag 0B91] (2), the perfection half, for a module placed in degree zero.** For
`f : X ⟶ S` proper of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation, flat
over `S`, the derived direct image `Rf_*ℱ` is a perfect object of `D(𝒪_S)`.

This is `isPerfect_derivedPushforward_singleFunctor_of_baseChange` with the base-change half
supplied by `nonempty_derivedPullback_derivedPushforward_singleFunctor_iso`. -/
theorem isPerfect_derivedPushforward_singleFunctor_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) (hproper : IsProper f) (F : X.Modules)
    (hfp : F.IsFinitePresentation) (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    RingedSpace.IsPerfect.{u, u + 1} (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :=
  isPerfect_derivedPushforward_singleFunctor_of_baseChange
    (fun _ _ _ g' hsq hf₀ hp₀ F₀ hF₀ hfl₀ =>
      have := hf₀.2.1
      have := hp₀
      have := hF₀
      nonempty_derivedPullback_derivedPushforward_singleFunctor_iso hsq F₀
        (Stacks.Modules.isQuasicoherent_of_isFinitePresentation F₀)
        (Stacks.Modules.isQuasicoherent_of_isFinitePresentation
          ((Scheme.Modules.pullback g').obj F₀)) hfl₀)
    f hf hproper F hfp hflat

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end

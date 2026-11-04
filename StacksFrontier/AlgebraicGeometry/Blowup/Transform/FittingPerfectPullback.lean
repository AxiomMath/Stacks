module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingProjectiveDimension
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexChartHomology
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic

/-!
# The pullback to the Fitting blowup is perfect of Tor dimension at most one

Let `ℱ` be a finitely presented module on a scheme `X` which is finite locally free of constant
rank `r` on a scheme-theoretically dense open `U`, and let `b : X' ⟶ X` be the blowup of `X` in
the `r`-th Fitting ideal of `ℱ`. This file proves that `b^*ℱ`, placed in degree zero, is a
perfect `𝒪_{X'}`-module of Tor amplitude in `[-1, 0]`, the half of part (4) of Stacks tag 0ESN
that concerns `b^*ℱ`.

## Main results

* `AlgebraicGeometry.exists_shortExact_finite_projective_of_hasProjectiveDimensionLE_one`: a
  finitely presented module of projective dimension at most one is the cokernel of an injection
  of finite projective modules.
* `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_restrict_of_shortExact_sections`: if the
  sections of a quasi-coherent module over an affine open are the cokernel of an injection of
  finite projective modules, the restriction of the module to that open is perfect of Tor
  amplitude in `[-1, 0]`.
* `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_modulePullback_fittingBlowUp`: **the half of
  Stacks 0ESN (4) about `b^*ℱ`**, on the blowup itself.

## References

* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
* [Stacks Project, Tag 0F7M](https://stacks.math.columbia.edu/tag/0F7M)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.CoherentTFAE (specModule restrictIsoSpecTilde)
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent (specModuleIsoSections)

/-! ### A resolution of length one by finite projective modules -/

/-- **A finitely presented module of projective dimension at most one is the cokernel of an
injection of finite projective modules.** -/
theorem exists_shortExact_finite_projective_of_hasProjectiveDimensionLE_one
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R) [Module.FinitePresentation R N]
    (h : HasProjectiveDimensionLE N 1) :
    ∃ T : ShortComplex (ModuleCat.{u} R), T.ShortExact ∧
      Module.Finite R T.X₁ ∧ Module.Projective R T.X₁ ∧
      Module.Finite R T.X₂ ∧ Module.Projective R T.X₂ ∧
      Nonempty (T.X₃ ≅ N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (N : Type u)
  have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
  have hX₂ : Projective f.shortComplexKer.X₂ :=
    (IsProjective.iff_projective (R := R) (Fin n → R)).1 inferInstance
  have hfin₁ : Module.Finite R f.shortComplexKer.X₁ :=
    Module.Finite.iff_fg.2 (Module.FinitePresentation.fg_ker f hf)
  have hlt : HasProjectiveDimensionLT f.shortComplexKer.X₁ 1 :=
    (hS.hasProjectiveDimensionLT_X₃_iff 0 hX₂).1 h
  have hproj₁ : Projective f.shortComplexKer.X₁ :=
    projective_iff_hasProjectiveDimensionLT_one.2 hlt
  exact ⟨f.shortComplexKer, hS, hfin₁, (IsProjective.iff_projective _).2 hproj₁,
    inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

/-! ### Perfectness and Tor amplitude over an affine open -/

/-- **A quasi-coherent module whose sections over an affine open are the cokernel of an injection
of finite projective modules is perfect of Tor dimension at most one there.** Its restriction
to `V`, placed in degree zero, is perfect of Tor amplitude in `[-1, 0]`. -/
theorem isPerfect_and_hasTorAmplitude_restrict_of_shortExact_sections {Y : Scheme.{u}}
    (M : Y.Modules) [M.IsQuasicoherent] (V : Y.affineOpens)
    (T : ShortComplex (ModuleCat.{u} Γ(Y, V.1))) (hT : T.ShortExact)
    [Module.Finite Γ(Y, V.1) T.X₁] [Module.Projective Γ(Y, V.1) T.X₁]
    [Module.Finite Γ(Y, V.1) T.X₂] [Module.Projective Γ(Y, V.1) T.X₂]
    (e : T.X₃ ≅ ModuleCat.of Γ(Y, V.1) Γ(M, V.1)) :
    IsPerfect.{u, u, u + 1} (X := V.1.toScheme.toRingedSpace)
        ((Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj M)) ∧
      HasTorAmplitude V.1.toScheme.toRingedSpace
        ((Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj M)) (-1) 0 := by
  let j := V.2.isoSpec.hom
  let N := (tilde.functor Γ(Y, V.1)).obj T.X₃
  obtain ⟨hperf, htor⟩ := isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution N
    (hasTwoTermFiniteLocallyFreeResolution_tilde T hT)
  let eM : (Scheme.Modules.restrictFunctor V.1.ι).obj M ≅
      (Scheme.Modules.restrictFunctor j).obj N :=
    restrictIsoSpecTilde M V.2 ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback j).app (tilde (specModule M V.2))).symm ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso
        ((tilde.functor Γ(Y, V.1)).mapIso (specModuleIsoSections M V ≪≫ e.symm))
  let eK : (Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj M) ≅
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (Spec Γ(Y, V.1)).Modules 0).obj N) :=
    ((Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor V.1.toScheme.Modules 0).mapIso eM ≪≫
      (((Scheme.Modules.restrictFunctor j).mapDerivedCategorySingleFunctor 0).app N).symm
  refine ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := V.1.toScheme.toRingedSpace) eK.symm
      (ComplexAndDivisorSituation.isPerfect_restrictFunctor_mapDerivedCategory j hperf), ?_⟩
  refine Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} ?_ eK
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1}
    (Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback
      j.toLRSHom.toShHom _ (-1) 0 htor)
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).app _)

/-! ### Stacks 0ESN (4) for the pullback, on the blowup -/

/-- **The half of Stacks Project, Tag 0ESN (4) that concerns `b^*ℱ`.** Let `ℱ` be a finitely
presented module on a scheme `X` which is finite locally free of constant rank `r` on a
scheme-theoretically dense open `U`. The pullback of `ℱ` to the blowup of `X` in the `r`-th
Fitting ideal of `ℱ` is a perfect `𝒪_{X'}`-module of Tor amplitude in `[-1, 0]`. -/
theorem isPerfect_and_hasTorAmplitude_modulePullback_fittingBlowUp {X : Scheme.{u}}
    (F : X.Modules) [F.IsFinitePresentation] (U : X.Opens) (r : ℕ)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    IsPerfect.{u, u, u + 1}
        ((DerivedCategory.singleFunctor (blowUp (fittingIdeal F (r : ℤ))).Modules 0).obj
          ((Scheme.Modules.pullback (blowUpToBase (fittingIdeal F (r : ℤ)))).obj F)) ∧
      HasTorAmplitude (blowUp (fittingIdeal F (r : ℤ))).toRingedSpace
        ((DerivedCategory.singleFunctor (blowUp (fittingIdeal F (r : ℤ))).Modules 0).obj
          ((Scheme.Modules.pullback (blowUpToBase (fittingIdeal F (r : ℤ)))).obj F)) (-1) 0 := by
  have hGfp : ((Scheme.Modules.pullback
      (blowUpToBase (fittingIdeal F (r : ℤ)))).obj F).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (blowUpToBase (fittingIdeal F (r : ℤ))).toLRSHom.toShHom F ‹_›
  have hGqc : ((Scheme.Modules.pullback
      (blowUpToBase (fittingIdeal F (r : ℤ)))).obj F).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation _
  refine isPerfect_and_hasTorAmplitude_of_forall_restrict _ (-1) 0 fun y => ?_
  obtain ⟨V, hV, hyV, g, hg, hspan, hpd, -, -, -, -⟩ :=
    exists_affineOpen_hasProjectiveDimensionLE_one_pullback_fittingBlowUp F U r hU hrank y
  have hpd' : HasProjectiveDimensionLE
      (ModuleCat.of Γ(blowUp (fittingIdeal F (r : ℤ)), V)
        Γ((Scheme.Modules.pullback (blowUpToBase (fittingIdeal F (r : ℤ)))).obj F, V)) 1 :=
    hasProjectiveDimensionLT_of_iso ULift.moduleEquiv.toModuleIso _
  have hfpV : Module.FinitePresentation Γ(blowUp (fittingIdeal F (r : ℤ)), V)
      Γ((Scheme.Modules.pullback (blowUpToBase (fittingIdeal F (r : ℤ)))).obj F, V) :=
    finitePresentation_sections_on_affine _ ⟨V, hV⟩
  obtain ⟨T, hT, h₁, h₂, h₃, h₄, ⟨e⟩⟩ :=
    exists_shortExact_finite_projective_of_hasProjectiveDimensionLE_one _ hpd'
  exact ⟨V, hyV, isPerfect_and_hasTorAmplitude_restrict_of_shortExact_sections _ ⟨V, hV⟩ T hT e⟩

end AlgebraicGeometry

end

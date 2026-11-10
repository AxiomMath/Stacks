module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeDimensionOneDerivedFibre
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.Perfect.Saturation

/-!
# `Rf_*𝒪_X` has Tor amplitude in `[0, 1]` in relative dimension at most one

Let `S` be any base scheme, `U` an object of the big fppf site over `S` with affine underlying
scheme, `Y = U` read as an algebraic space, and `f : X ⟶ Y` a proper, flat morphism of finite
presentation of algebraic spaces with relative dimension at most one. Then `Rf_*𝒪_X` has Tor
amplitude in `[0, 1]`; in particular `Hⁱ(Rf_*𝒪_X ⊗^L K) = 0` for every `𝒪_Y`-module `K` and every
`i ≥ 2`. This is the core of the vanishing of the obstruction groups `H²(X_{T'}, 𝓘)` of the
Picard stack in the proof of Stacks 0DPJ.

## Proof

`Rf_*𝒪_X` is perfect (Stacks 0CTM, part (1)) and lies in `D_QCoh`, so it is `Φ(M)` for
`M = RΓ(U, Rf_*𝒪_X)`, a perfect object of `D(A)`, `A = Γ(U, 𝒪)`; and `Φ(M)` has Tor amplitude in
`[0, 1]` exactly when `M` has. By Stacks 068V it suffices that `Hⁱ(M ⊗^L_A κ(𝔭)) = 0` for every
prime `𝔭` and every `i ∉ [0, 1]`, which is
`isZero_homology_residueField_derivedSections_of_hasRelativeDimensionLE_one`.

## Main results

All in the namespace `AlgebraicGeometry.Space`:

* `hasTorAmplitude_derivedModulePushforward_structureModule_of_hasRelativeDimensionLE_one`:
  `Rf_*𝒪_X` has Tor amplitude in `[0, 1]`.
* Its consequence `Hⁱ(Rf_*𝒪_X ⊗^L K) = 0` for every `𝒪_Y`-module `K` and every `i ≥ 2`, the
  theorem whose name prefixes `_of_hasRelativeDimensionLE_one` with
  `isZero_homology_derivedTensor_derivedModulePushforward_structureModule`.

## Implementation notes

No declaration here carries a `stacks` attribute: these are steps of the proof of Stacks 0DPJ.
The derived categories are those of the standard model, fixed by `letI` inside the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [-instance] SheafOfModules.hasBinBiprod

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`RΓ(U, Rf_*𝒪_X)` has Tor amplitude in `[0, 1]`** over `A = Γ(U, 𝒪)`, for `f : X ⟶ U` proper,
flat, of finite presentation and of relative dimension at most one, `U` affine (Stacks 068V
applied to the derived fibres). -/
theorem
    hasTorAmplitudeCanonical_derivedSections_derivedModulePushforward_of_hasRelativeDimensionLE_one
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))) 0 1 := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
  let E := (derivedModulePushforward B S hS f).obj
    ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))
  let M := (representedAffineDerivedSections B S hS U).obj E
  have hE := (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp _
    (isPerfect_unit X)).1
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M :=
    StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
      (isPerfect_representedAffineDerivedSections_obj B S hS U E hE)
  have h068V := (StacksDraft.Perfect.isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u}
    M hM 0 1).1
  have hprime : ∀ q : PrimeSpectrum Γ((BigFppfOver.toScheme B S hS).obj U, ⊤), ∀ i : ℤ,
      i < 0 ∨ 1 < i → StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} q.asIdeal M i :=
    fun q i hi => (StacksDraft.Perfect.fibreCohomologyVanishes_iff_isZero_homology.{u, u}
      q.asIdeal M hM i).2
      (isZero_homology_residueField_derivedSections_of_hasRelativeDimensionLE_one U f hf hfl hfp
        hd q.asIdeal i hi)
  exact (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ M 0 1).2
    (h068V.2 hprime).2.1

/-- **`Rf_*𝒪_X` has Tor amplitude in `[0, 1]`** for `f : X ⟶ Y` proper, flat, of finite
presentation and of relative dimension at most one, with `Y` represented by an affine scheme. -/
theorem hasTorAmplitude_derivedModulePushforward_structureModule_of_hasRelativeDimensionLE_one
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))) 0 1 := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
  let E := (derivedModulePushforward B S hS f).obj
    ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))
  let M := (representedAffineDerivedSections B S hS U).obj E
  have hcounit : IsIso ((representedAffineDerivedAdjunction B S hS U).counit.app E) :=
    isIso_representedAffineDerivedAdjunction_counit_app B S hS U E
      (qcohDerived_derivedModulePushforward_structureModule B S hS U f hfp.2.1 hfp.2.2)
  have hΦ := (hasTorAmplitude_representedAffineDerivedAssociated_iff B S hS U M 0 1).2
    (hasTorAmplitudeCanonical_derivedSections_derivedModulePushforward_of_hasRelativeDimensionLE_one
      U f hf hfl hfp hd)
  intro F i hi
  exact (hΦ F i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).mapIso
      (@asIso _ _ _ _ _ hcounit).symm).app ((DerivedCategory.singleFunctor _ 0).obj F)))

/-- **`Hⁱ(Rf_*𝒪_X ⊗^L K) = 0` for `i ≥ 2`** and every `𝒪_Y`-module `K`, for `f : X ⟶ Y` proper,
flat, of finite presentation and of relative dimension at most one, with `Y` represented by an
affine scheme. -/
theorem isZero_homology_derivedTensor_pushforward_structureModule_of_hasRelativeDimensionLE_one
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hd : HasRelativeDimensionLE 1 B S hS f.hom)
    (K : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) (i : ℤ)
    (hi : 2 ≤ i) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
    IsZero ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) i).obj
      (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
          ((derivedModulePushforward B S hS f).obj
            ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))).obj
        ((DerivedCategory.singleFunctor _ 0).obj K))) :=
  hasTorAmplitude_derivedModulePushforward_structureModule_of_hasRelativeDimensionLE_one U f hf hfl
    hfp hd K i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega)

end AlgebraicGeometry.Space

end

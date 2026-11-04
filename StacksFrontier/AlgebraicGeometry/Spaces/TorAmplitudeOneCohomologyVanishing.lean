module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseHigherDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBasePushforwardInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverDerivedTensorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedModulePushforwardTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage

/-!
# Tor amplitude in `[-1, ∞)` of `Rf_*𝒪_X` kills cohomology in degrees `≥ 2` of pullbacks

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and flat morphism of algebraic spaces with
`Y` affine, and suppose that `Rf_*𝒪_X ⊗^L K[0]` has no cohomology in degrees `≥ 2` for every
quasi-coherent `𝒪_Y`-module `K`.  Then `H^q(X, f^*K) = 0` for every quasi-coherent `K` and every
`q ≥ 2`.  This is a step of the proof of Stacks 0DPJ.

By the projection formula (Stacks 08IN) and flatness of `f`,
`Rf_*𝒪_X ⊗^L K[0] ≅ Rf_*(𝒪_X[0] ⊗^L Lf^*K[0]) ≅ Rf_*((f^*K)[0])`, whose cohomology in degree
`q` is `R^qf_*(f^*K)`.  Over the affine base the Leray spectral sequence collapses
(Stacks 08EX and 072Z), so `H^q(X, f^*K) = Γ(Y, R^qf_*(f^*K)) = 0`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_modulePullback_of_torAmplitude`:
  `R^qf_*(f^*K) = 0` for `q ≥ 2`.
* `Space.isZero_rightDerived_globalSections_modulePullback_of_isAffineSpace_of_torAmplitude`
  and, over an affine `U` of the big fppf site,
  `AlgebraicGeometry.Space.isZero_rightDerived_globalSections_modulePullback_of_torAmplitude`:
  `H^q(X, f^*K) = 0` for `q ≥ 2`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Tor amplitude of `Rf_*𝒪_X` against quasi-coherent modules kills the higher direct images of
pullbacks.**  For a quasi-compact, quasi-separated, flat `f : X ⟶ Y` such that
`Rf_*𝒪_X ⊗^L K[0]` has no cohomology in degrees `≥ 2` for quasi-coherent `K`, the higher direct
images `R^qf_*(f^*K)` vanish for `q ≥ 2`. -/
theorem isZero_rightDerived_modulePushforward_modulePullback_of_torAmplitude
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hfl : IsFlat B S hS f.hom)
    (hT : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
      letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
      letI := HasDerivedCategory.standard
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      ∀ (K : Modules.{u, u} B S hS Y.1 Y.2), K.IsQuasicoherentOnSite → ∀ i : ℤ, 2 ≤ i →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (((smallEtaleDerivedTensor B S hS Y).obj ((derivedModulePushforward B S hS f).obj
            ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))).obj
              ((DerivedCategory.singleFunctor _ 0).obj K))))
    (K : Modules.{u, u} B S hS Y.1 Y.2) (hK : K.IsQuasicoherentOnSite) (q : ℕ) (hq : 2 ≤ q) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((modulePushforward B S hS f).rightDerived q).obj
      ((modulePullback B S hS f).obj K)) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have hKq : QcohDerived B S hS Y ((DerivedCategory.singleFunctor _ 0).obj K) :=
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _) K hK).2
  have hOq : QcohDerived B S hS X ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)) :=
    qcohDerived_singleFunctor_structureModule
  have hiso := isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs _ hOq _ hKq
  have hG : ∀ x, IsFlatOverAtGeometricPoint B S hS f (structureModule X) x :=
    (isFlat_iff_forall_isFlatOverAtGeometricPoint_structureSheafModule B S hS f).1 hfl
  let e₁ := @asIso _ _ _ _ (smallEtaleProjectionFormulaMap B S hS f
    ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))
    ((DerivedCategory.singleFunctor _ 0).obj K)) hiso
  let e₂ := (derivedModulePushforward B S hS f).mapIso
    (smallEtaleDerivedTensorPullbackSingleIso f (structureModule X) hG K)
  let e₃ := (derivedModulePushforward B S hS f).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
    (Stacks.unitSheafTensorIso _ ≪≫ (pullbackModulesIsoModulePullback B S hS f).app K))
  let e₄ := ((totalRightDerivedModulePushforwardIso B S hS f).app
    ((DerivedCategory.singleFunctor _ 0).obj ((modulePullback B S hS f).obj K))).symm
  let e := (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄) ≪≫
    homologyDerivedModulePushforwardSingleIso B S hS f ((modulePullback B S hS f).obj K) 0 q q
      (by simp)
  exact (hT K hK q (by exact_mod_cast hq)).of_iso e.symm

/-- **Tor amplitude of `Rf_*𝒪_X` against quasi-coherent modules kills the cohomology of
pullbacks over an affine base.**  For a quasi-compact, quasi-separated, flat `f : X ⟶ Y` with `Y`
an affine algebraic space such that `Rf_*𝒪_X ⊗^L K[0]` has no cohomology in degrees `≥ 2` for
quasi-coherent `K`, the cohomology `H^q(X, f^*K)` vanishes for `q ≥ 2`: it is
`Γ(Y, R^qf_*(f^*K))` by Stacks 08EX over an affine base. -/
theorem isZero_rightDerived_globalSections_modulePullback_of_isAffineSpace_of_torAmplitude
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hY : IsAffineSpace B S hS Y.1)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hfl : IsFlat B S hS f.hom)
    (hT : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
      letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
      letI := HasDerivedCategory.standard
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      ∀ (K : Modules.{u, u} B S hS Y.1 Y.2), K.IsQuasicoherentOnSite → ∀ i : ℤ, 2 ≤ i →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (((smallEtaleDerivedTensor B S hS Y).obj ((derivedModulePushforward B S hS f).obj
            ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))).obj
              ((DerivedCategory.singleFunctor _ 0).obj K))))
    (K : Modules.{u, u} B S hS Y.1 Y.2) (hK : K.IsQuasicoherentOnSite) (q : ℕ) (hq : 2 ≤ q) :
    have : HasInjectiveResolutions (SheafOfModules.{u} (structureRingSheaf B S hS X)) :=
      hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).rightDerived q).obj ((modulePullback B S hS f).obj K)) := by
  have : HasInjectiveResolutions (SheafOfModules.{u} (structureRingSheaf B S hS X)) :=
    hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have : ((modulePullback B S hS f).obj K).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f K hK
  have h₁ := isZero_rightDerived_modulePushforward_modulePullback_of_torAmplitude B S hS f hfqc
    hfqs hfl hT K hK q hq
  have h₂ := (Functor.map_isZero
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (structureRingSheaf B S hS Y)) h₁).of_iso
    (globalSectionsRightDerivedIsoOfIsAffineSpace B S hS f hY hfqc hfqs
      ((modulePullback B S hS f).obj K) (acyclicPushforwardOfInjective_of_isAffineSpace B S hS f hY)
      q)
  have h₃ := h₂.of_iso ((derivedGlobalSectionsPushforwardIso B S hS f q).app
    ((modulePullback B S hS f).obj K)).symm
  have h₄ := ModuleCat.isZero_iff_subsingleton.mp h₃
  exact ModuleCat.isZero_iff_subsingleton.mpr h₄

/-- **Tor amplitude of `Rf_*𝒪_X` against quasi-coherent modules kills the cohomology of
pullbacks**, over an affine scheme `U` of the big fppf site.  For a quasi-compact,
quasi-separated, flat `f : X ⟶ U` such that `Rf_*𝒪_X ⊗^L K[0]` has no cohomology in degrees
`≥ 2` for quasi-coherent `K` on `U`, `H^q(X, f^*K) = 0` for every quasi-coherent `K` and every
`q ≥ 2`.  A step of the proof of Stacks 0DPJ. -/
theorem isZero_rightDerived_globalSections_modulePullback_of_torAmplitude
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace U)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hfl : IsFlat B S hS f.hom)
    (hT : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
      letI := HasDerivedCategory.standard
        (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        (schemeSpace U)))
      ∀ (K : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)),
        K.IsQuasicoherentOnSite → ∀ i : ℤ, 2 ≤ i →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj
            ((derivedModulePushforward B S hS f).obj
              ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))).obj
                ((DerivedCategory.singleFunctor _ 0).obj K))))
    (K : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hK : K.IsQuasicoherentOnSite) (q : ℕ) (hq : 2 ≤ q) :
    have : HasInjectiveResolutions (SheafOfModules.{u} (structureRingSheaf B S hS X)) :=
      hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).rightDerived q).obj ((modulePullback B S hS f).obj K)) :=
  isZero_rightDerived_globalSections_modulePullback_of_isAffineSpace_of_torAmplitude B S hS f
    (isAffineSpace_yoneda B S hS U hU) hfqc hfqs hfl hT K hK q hq

end AlgebraicGeometry.Space

end

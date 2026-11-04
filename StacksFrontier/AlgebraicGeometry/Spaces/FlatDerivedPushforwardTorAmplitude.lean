module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverDerivedTensorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeQuasiCoherentDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMateIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposFlatModule

/-!
# Tor amplitude of the direct image of the structure sheaf along a flat morphism

Let `f : X ⟶ Y` be a flat, quasi-compact and quasi-separated morphism of algebraic spaces with `Y`
quasi-compact and quasi-separated. Then `Rf_*𝒪_X` has Tor amplitude in `[0, N]` for some `N`:
for a quasi-coherent `𝒪_Y`-module `ℱ` the projection formula (Stacks 08IN) gives
`Rf_*𝒪_X ⊗^L ℱ = Rf_*(f^*ℱ)`, because `𝒪_X` is flat over `Y`, and `Rf_*` carries the
quasi-coherent module `f^*ℱ` into degrees `[0, N]` with `N` independent of `ℱ`; Stacks 08IL
concludes.

## Main results

* `AlgebraicGeometry.Space.exists_hasTorAmplitude_derivedModulePushforward_structureSheaf`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_*𝒪_X` has Tor amplitude in `[0, N]`** for a flat, quasi-compact and quasi-separated
morphism `f : X ⟶ Y` to a quasi-compact and quasi-separated algebraic space `Y`. -/
theorem exists_hasTorAmplitude_derivedModulePushforward_structureSheaf
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hfl : IsFlat B S hS f.hom)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) :
    ∃ N : ℤ, Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (smallEtaleDerivedTensorProduct B S hS Y) ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))) 0 N := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedModulePushforward_obj f hfqc hfqs hYqc
  let OX := (DerivedCategory.singleFunctor (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS X)) 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))
  have hOX : QcohDerived B S hS X OX := (derivedStructureSheaf B S hS X.1 X.2).property
  refine ⟨N, (hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent_standardModel hZ Y hYqs _ _
    (qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs OX hOX) 0 N).2
      fun F hF i hi => ?_⟩
  have hFq : QcohDerived B S hS Y ((DerivedCategory.singleFunctor _ 0).obj F) :=
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _) F hF).2
  let LF := (smallEtaleDerivedModulePullback B S hS f).obj
    ((DerivedCategory.singleFunctor _ 0).obj F)
  let M := ((smallEtaleDerivedTensor B S hS X).obj OX).obj LF
  have hMq : QcohDerived B S hS X M := qcohDerived_smallEtaleDerivedTensor X OX LF hOX
    ((quasicoherentDerivedModulePullback f).obj ⟨_, hFq⟩).property
  let eM : M ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((tensorPullbackFunctor f (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))).obj
        F) :=
    smallEtaleDerivedTensorPullbackSingleIso f _
      ((isFlat_iff_forall_isFlatOverAtGeometricPoint_structureSheafModule B S hS f).1 hfl) F
  have keyGE : ∀ A : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X),
      ((DerivedCategory.singleFunctor _ 0).obj A).IsGE 0 := fun A => inferInstance
  have keyLE : ∀ A : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X),
      ((DerivedCategory.singleFunctor _ 0).obj A).IsLE 0 := fun A => inferInstance
  have hMge : M.IsGE 0 := by
    have := keyGE ((tensorPullbackFunctor f
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))).obj F)
    exact DerivedCategory.TStructure.t.isGE_of_iso eM.symm 0
  have hMle : M.IsLE 0 := by
    have := keyLE ((tensorPullbackFunctor f
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))).obj F)
    exact DerivedCategory.TStructure.t.isLE_of_iso eM.symm 0
  let e := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).mapIso
    (@asIso _ _ _ _ (smallEtaleProjectionFormulaMap B S hS f OX
      ((DerivedCategory.singleFunctor _ 0).obj F))
      (isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs OX hOX _ hFq))
  obtain h | h : i < 0 ∨ N < i := by simpa only [Set.mem_Icc, not_and_or, not_le] using hi
  · exact ((DerivedCategory.isGE_iff _ 0).1 (isGE_rightDerived_modulePushforward_obj B S hS f _
      (derivedModulePushforwardUnit B S hS f) M 0 hMge) i h).of_iso e
  · exact ((DerivedCategory.isLE_iff _ (0 + N)).1 (hN M hMq 0 hMle) i (by omega)).of_iso e

end AlgebraicGeometry.Space

end

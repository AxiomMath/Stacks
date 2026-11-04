module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRelativeDualizingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDerivedPushforwardTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineHomToStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper

/-!
# The right adjoint of `Rf_*` at the structure sheaf over an affine base

Let `Y` be an affine algebraic space and `f : X ⟶ Y` a proper, flat morphism of finite
presentation, with right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55). This
file proves part (2) of Stacks 0E5V: `Rf_* a(𝒪_Y)` has vanishing cohomology sheaves in positive
degrees.

For `q > 0`, `Hom(𝒪_Y, Rf_* a(𝒪_Y)[q]) = Hom(Lf^*𝒪_Y[-q], a(𝒪_Y)) = Hom(Rf_*𝒪_X[-q], 𝒪_Y)`,
and the last group vanishes because `Rf_*𝒪_X` is perfect (Stacks 0CTM) with Tor amplitude in
`[0, N]` (flatness of `f`), hence represented by finite projective modules in degrees `[0, N]`
over the affine `Y`. Since `𝒪_Y` detects the cohomology sheaves of `D_QCoh(𝒪_Y)` on an affine
algebraic space, `H^q(Rf_* a(𝒪_Y)) = 0`.

## Main results

* `AlgebraicGeometry.Space.isLE_derivedModulePushforward_affineRightAdjoint`: Stacks 0E5V (2).
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

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **Stacks 0E5V (2).** For `Y` affine and `f : X ⟶ Y` proper, flat and of finite
presentation, `Rf_* a(𝒪_Y)` has vanishing cohomology sheaves in positive degrees. -/
@[stacks 0E5V "(2)"]
theorem isLE_derivedModulePushforward_affineRightAdjoint (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) :
    ((derivedModulePushforward B S hS f).obj
      ((affineRightAdjoint hZ f hfp hY).obj
        (derivedStructureSheaf B S hS Y.1 Y.2)).obj).IsLE 0 := by
  let R := derivedModulePushforward B S hS f
  let OY := derivedStructureSheaf B S hS Y.1 Y.2
  let ω := (affineRightAdjoint hZ f hfp hY).obj OY
  let OX : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
    (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)
  have hOX : QcohDerived B S hS X OX := (derivedStructureSheaf B S hS X.1 X.2).property
  let adj := quasicoherentDerivedRightAdjointAdjunction hZ f
    (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hfp.2.1 hfp.2.2
  obtain ⟨N, hN⟩ := exists_hasTorAmplitude_derivedModulePushforward_structureSheaf hZ f hfl
    hfp.2.1 hfp.2.2 hY.isQuasiCompactSpace
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY)
  have hP := (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp OX
    (isPerfect_unit X)).1
  have hK : QcohDerived B S hS Y (R.obj ω.obj) :=
    ((quasicoherentDerivedPushforward B S hS f hfp.2.1 hfp.2.2).obj ω).property
  rw [DerivedCategory.isLE_iff]
  intro q hq
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := id hY
  refine isZero_homology_of_forall_homFromUnit_eq_zero (X := Y.1) (hX := Y.2)
    (chartOfIso B S hS T₀ i) (isTerminalChartOfIso T₀ i) hT₀ _ hK q fun g => ?_
  let M : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
    ⟨OX⟦-q⟧, qcohDerived_shift OX (-q) hOX⟩
  let e : ((DerivedCategory.singleFunctor _ 0).obj (structureModule Y) ⟶ (R.obj ω.obj)⟦q⟧) ≃
      (R.obj OX ⟶ (DerivedCategory.singleFunctor _ (-q)).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))) :=
    (Iso.homCongr (Iso.refl _) ((R.commShiftIso q).app ω.obj).symm).trans <|
    ((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm.trans <|
    (Iso.homCongr (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) f)
      (Iso.refl _)).trans <|
    ((shiftEquiv' _ (-q) q (by omega)).toAdjunction.homEquiv OX ω.obj).symm.trans <|
    ((ObjectProperty.fullyFaithfulι _).homEquiv (X := M) (Y := ω)).symm.trans <|
    (adj.homEquiv M OY).symm.trans <|
    ((ObjectProperty.fullyFaithfulι _).homEquiv (X := (quasicoherentDerivedPushforward B S hS f
      hfp.2.1 hfp.2.2).obj M) (Y := OY)).trans <|
    (Iso.homCongr ((R.commShiftIso (-q)).app OX) (Iso.refl _)).trans <|
    ((shiftEquiv' _ (-q) q (by omega)).toAdjunction.homEquiv (R.obj OX) OY.obj).trans <|
    Iso.homCongr (Iso.refl _) (((DerivedCategory.singleFunctors _).shiftIso q (-q) 0
      (by omega)).app _)
  have h0 := hom_singleFunctor_structureModule_eq_zero_of_hasTorAmplitude B S hS Y hY _ hP 0 N hN
    (-q) (by omega)
  have : Subsingleton (R.obj OX ⟶ (DerivedCategory.singleFunctor _ (-q)).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))) :=
    ⟨fun t₁ t₂ => (h0 t₁).trans (h0 t₂).symm⟩
  have := e.subsingleton
  exact Subsingleton.elim _ _

end AlgebraicGeometry.Space

end

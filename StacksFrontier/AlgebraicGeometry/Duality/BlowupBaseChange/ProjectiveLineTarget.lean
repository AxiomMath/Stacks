module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.ComparisonIso
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonAffine
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence

/-!
# Two inputs for the projective line in [Stacks, Example 0AAC]

This file proves two facts used in [Stacks, Example 0AAC].

* For an arbitrary morphism of schemes `h : Z ⟶ W`, derived pullback carries `𝒪_W[0]` to
  `𝒪_Z[0]`: the complex `𝒪_W[0]` is K-flat, because `𝒪_W` is flat over itself, so `Lh^*` is
  computed on it degreewise, and `h^*𝒪_W ≅ 𝒪_Z`.
* For `p : ℙⁿ_R ⟶ Spec R` with `n ≥ 1` and `R ≠ 0`, the twisted inverse image `p^×(𝒪_{Spec R})`
  is not in `D^{≥ 0}`. Indeed `p^×(𝒪_{Spec R}) ≅ (𝒪(-n-1) ⊗ p^*𝒪)[n]` lies in `D^{≤ -n}`, so if it
  were in `D^{≥ 0}` it would vanish; but then `𝒪_{Spec R} ≅ Rp_*((𝒪(-n-1) ⊗ p^*𝒪)[n])` would
  vanish as well, which is false since `R ≠ 0`.

## References

* [Stacks Project, Example 0AAC](https://stacks.math.columbia.edu/tag/0AAC)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality

section StructureSheafPullback

/-- The structure sheaf of `W` in degree zero, as a cochain complex. -/
abbrev unitComplexScheme (W : Scheme.{u}) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) ℤ :=
  (CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) 0).obj
    (SheafOfModules.unit (structureSheafRing W.toRingedSpace))

/-- The structure sheaf of `W` in degree zero, as an object of the homotopy category. -/
abbrev unitHomotopyScheme (W : Scheme.{u}) :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing W.toRingedSpace))
      (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (unitComplexScheme W)

/-- The complex `𝒪_W[0]` is K-flat, since `𝒪_W` is a flat `𝒪_W`-module. -/
theorem kFlat_unitComplexScheme (W : Scheme.{u}) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex W.toRingedSpace
      (unitComplexScheme W) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat W.toRingedSpace.sheaf _
    (Stacks.Cohomology.DerivedPullbackUnit.isFlat_unit.{u} W.toRingedSpace) 0

/-- `𝒪_W[0]` is the object of the derived category represented by `unitComplexScheme W`. -/
def singleUnitIsoQhScheme (W : Scheme.{u}) :
    (DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf) ≅
      DerivedCategory.Qh.obj (unitHomotopyScheme W) :=
  (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) 0).app _ ≪≫
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace))).app (unitComplexScheme W)).symm

variable {Z W : Scheme.{u}} (h : Z ⟶ W)

/-- The comparison from derived pullback to degreewise pullback is invertible at `𝒪_W[0]`,
which is K-flat. -/
theorem isIso_derivedPullbackComparison_unitHomotopyScheme :
    IsIso ((derivedPullbackComparison h.toLRSHom.toShHom).app (unitHomotopyScheme W)) :=
  Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    h.toLRSHom.toShHom (unitComplexScheme W) (kFlat_unitComplexScheme W)

/-- Degreewise pullback of `𝒪_W[0]`, read in `D(𝒪_Z)`, is `𝒪_Z[0]`. -/
def pullbackOnHomotopyUnitIsoScheme :
    (pullbackOnHomotopy h.toLRSHom.toShHom).obj (unitHomotopyScheme W) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).obj
        (SheafOfModules.unit (structureSheafRing Z.toRingedSpace)) :=
  DerivedCategory.Qh.mapIso (((modulePullback h.toLRSHom.toShHom).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app (unitComplexScheme W)) ≪≫
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback h.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app _) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) 0).mapIso
      (modulePullbackObjUnitIso h.toLRSHom.toShHom)

/-- **`Lh^*(𝒪_W[0]) ≅ 𝒪_Z[0]`** for an arbitrary morphism of schemes `h : Z ⟶ W`: the complex
`𝒪_W[0]` is K-flat, so the derived pullback is the degreewise pullback, and `h^*𝒪_W ≅ 𝒪_Z`. -/
def derivedPullbackStructureSheafIsoScheme :
    (derivedPullback h).obj
        ((DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor Z.Modules 0).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).mapIso
      (singleUnitIsoQhScheme W) ≪≫
    @asIso _ _ _ _ ((derivedPullbackComparison h.toLRSHom.toShHom).app (unitHomotopyScheme W))
      (isIso_derivedPullbackComparison_unitHomotopyScheme h) ≪≫
    pullbackOnHomotopyUnitIsoScheme h

end StructureSheafPullback

/-- Derived pullback carries the structure sheaf to the structure sheaf. -/
theorem nonempty_quasiCoherentDerivedPullback_derivedStructureSheaf_iso {Z W : Scheme.{u}}
    (h : Z ⟶ W) :
    Nonempty ((quasiCoherentDerivedPullback' h).obj (DerivedPushforward.derivedStructureSheaf W) ≅
      DerivedPushforward.derivedStructureSheaf Z) :=
  ⟨ObjectProperty.isoMk _ (derivedPullbackStructureSheafIsoScheme h)⟩

/-- For `p : 𝐏ⁿ_R ⟶ Spec R` with `n ≥ 1` and `R ≠ 0`, `p^×(𝒪)` is not in `D^{≥ 0}`. -/
theorem not_isGE_twistedInverseImage_projToSpecCoeff_derivedStructureSheaf (R : Type u)
    [CommRing R] [Nontrivial R] (n : ℕ) (hn : 1 ≤ n) :
    ¬ ((twistedInverseImage (projToSpecCoeff R n)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (projToSpecCoeff R n))).obj
          (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of R)))).obj.IsGE 0 := by
  intro hGE
  let M : ModuleCat.{u} R := ModuleCat.of R R
  let e₁ : DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of R)) ≅
      ProjCoeff.Mqc R M :=
    derivedStructureSheafIsoDerivedTilde (CommRingCat.of R)
  let e₂ : (twistedInverseImage (projToSpecCoeff R n)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (projToSpecCoeff R n))).obj
          (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of R))) ≅
      ProjCoeff.Gqc R n M :=
    (Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec R n).mapIso e₁ ≪≫
      ProjCoeff.twistedInverseImageIso R n M
  let e₃ : ((twistedInverseImage (projToSpecCoeff R n)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (projToSpecCoeff R n))).obj
          (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of R)))).obj ≅
      (ProjCoeff.Gqc R n M).obj :=
    (ObjectProperty.ι _).mapIso e₂
  have hG : (ProjCoeff.Gqc R n M).obj.IsGE 0 :=
    have := hGE
    DerivedCategory.TStructure.t.isGE_of_iso e₃ 0
  have hL0 : (ProjCoeff.Gsingle R n M).IsLE 0 := inferInstance
  have hLn : (ProjCoeff.Gqc R n M).obj.IsLE (-(n : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_shift (ProjCoeff.Gsingle R n M) 0 (n : ℤ) (-(n : ℤ))
      (by omega)
  have hL : (ProjCoeff.Gqc R n M).obj.IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_of_le _ (-(n : ℤ)) (-1) (by omega)
  have hGobj : IsZero (ProjCoeff.Gqc R n M).obj :=
    (IsZero.iff_id_eq_zero _).2
      (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (-1) 0 (by omega) hL hG)
  have hGz : IsZero (ProjCoeff.Gqc R n M) :=
    ProjCoeff.isZero_of_faithful (ObjectProperty.ι _) hGobj
  have hMz : IsZero (ProjCoeff.Mqc R M) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    have key : (ProjCoeff.traceIso R n M).hom = 0 :=
      ((ProjCoeff.adjq R n).homEquiv _ _).injective (hGz.eq_of_src _ _)
    rw [← (ProjCoeff.traceIso R n M).inv_hom_id, key, comp_zero]
  have : (derivedTilde (CommRingCat.of R)).IsEquivalence :=
    AlgebraicGeometry.derivedTilde_isEquivalence _
  have hD : IsZero ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) :=
    ProjCoeff.isZero_of_faithful (derivedTilde (CommRingCat.of R)) hMz
  have hR : IsZero M := ProjCoeff.isZero_of_faithful _ hD
  rw [ModuleCat.isZero_iff_subsingleton] at hR
  exact not_subsingleton R hR

end Stacks.Duality

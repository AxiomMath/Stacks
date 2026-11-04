module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.CoefficientCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.ProjectiveMorphism
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# The derived direct image of the structure sheaf of projective space

Let `R` be a commutative ring, `n ≥ 0` and `p : ℙⁿ_R ⟶ Spec R` the structure morphism. This file
proves, in the locally small model of the derived categories, that `Lp^*(𝒪[0]) ≅ 𝒪[0]` and that
the unit `𝒪_{Spec R}[0] ⟶ Rp_*Lp^*(𝒪_{Spec R}[0])` of the derived adjunction is an isomorphism, so
`Rp_*𝒪_{ℙⁿ_R} = 𝒪_{Spec R}`.

## Main definitions

* `Stacks.Duality.ProjCoeff.derivedPullbackStructureSheafIso`: `Lp^*(𝒪_{Spec R}[0]) ≅ 𝒪_{ℙⁿ_R}[0]`.

## Main results

* `Stacks.Duality.ProjCoeff.isIso_derivedAdjunction_unit_structureSheaf`: the unit
  `𝒪_{Spec R}[0] ⟶ Rp_*Lp^*(𝒪_{Spec R}[0])` is an isomorphism.
* `Stacks.Duality.ProjCoeff.isZero_rightDerived_pushforward_unit`: `R^q p_*𝒪_{ℙⁿ_R} = 0` for
  `q > 0`.
* `Stacks.Duality.ProjCoeff.isIso_c_projToSpecCoeff`: `𝒪_{Spec R} = p_*𝒪_{ℙⁿ_R}`.

## Implementation notes

The derived categories are the locally small ones of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, found by instance search; the twisted
inverse image of `p` exists only there. The base identifications of the derived pullback of the
structure sheaf are stated at `HasDerivedCategory.standard`, so the argument is repeated here
from its model-free inputs.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.AffineBase

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The morphism of ringed spaces underlying `p`. -/
abbrev unitStructPR : (P R n).toRingedSpace ⟶ (Spec (CommRingCat.of R)).toRingedSpace :=
  (projToSpecCoeff R n).toLRSHom.toShHom

/-- The complex `𝒪_{Spec R}[0]` is K-flat, because `𝒪_{Spec R}` is flat over itself. -/
theorem kFlat_single_unit :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex (Spec (CommRingCat.of R)).toRingedSpace
      ((CochainComplex.singleFunctor (SheafOfModules.{u}
        (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace)) 0).obj
        (SheafOfModules.unit (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace))) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat
    (Spec (CommRingCat.of R)).toRingedSpace.sheaf _
    (Stacks.Cohomology.DerivedPullbackUnit.isFlat_unit.{u}
      (Spec (CommRingCat.of R)).toRingedSpace) 0

/-- The structure sheaf of `Spec R` in degree zero, as a cochain complex. -/
abbrev unitComplex : CochainComplex (SheafOfModules.{u}
    (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace)) ℤ :=
  (CochainComplex.singleFunctor (SheafOfModules.{u}
    (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace)) 0).obj
    (SheafOfModules.unit (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace))

/-- The structure sheaf of `Spec R` in degree zero, as an object of the homotopy category. -/
abbrev unitHomotopy : HomotopyCategory (SheafOfModules.{u}
    (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace)) (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (unitComplex R)

/-- `𝒪_{Spec R}[0]` is the object of the derived category represented by `unitComplex`. -/
def singleUnitIsoQh :
    (DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of R)).ringCatSheaf) ≅
      DerivedCategory.Qh.obj (unitHomotopy R) :=
  (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace)) 0).app _ ≪≫
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace))).app (unitComplex R)).symm

/-- The comparison from the degreewise pullback to the derived pullback is invertible at
`𝒪_{Spec R}[0]`, since that complex is K-flat. -/
theorem isIso_derivedPullbackComparison_unitHomotopy :
    IsIso ((derivedPullbackComparison (unitStructPR R n)).app (unitHomotopy R)) :=
  Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    (unitStructPR R n) (unitComplex R) (kFlat_single_unit R)

/-- Degreewise pullback of `𝒪_{Spec R}[0]`, read in `D(𝒪_{ℙⁿ_R})`, is `𝒪_{ℙⁿ_R}[0]`. -/
def pullbackOnHomotopyUnitIso :
    (pullbackOnHomotopy (unitStructPR R n)).obj (unitHomotopy R) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (P R n).toRingedSpace)) 0).obj
        (SheafOfModules.unit (structureSheafRing (P R n).toRingedSpace)) :=
  DerivedCategory.Qh.mapIso (((modulePullback (unitStructPR R n)).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app (unitComplex R)) ≪≫
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing (P R n).toRingedSpace))).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback (unitStructPR R n)) (ComplexShape.up ℤ) 0).app _) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (structureSheafRing (P R n).toRingedSpace)) 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (P R n).toRingedSpace)) 0).mapIso
      (modulePullbackObjUnitIso (unitStructPR R n))

/-- **`Lp^*(𝒪_{Spec R}[0]) ≅ 𝒪_{ℙⁿ_R}[0]`**, in the locally small model. The complex `𝒪[0]` is
K-flat because `𝒪` is flat over itself, so the derived pullback is the degreewise pullback, and
`p^*𝒪_{Spec R} ≅ 𝒪_{ℙⁿ_R}`. -/
def derivedPullbackStructureSheafIso :
    (Stacks.Duality.derivedPullback (projToSpecCoeff R n)).obj
        ((DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor (P R n).Modules 0).obj
        (SheafOfModules.unit (P R n).ringCatSheaf) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (unitStructPR R n)).mapIso
      (singleUnitIsoQh R) ≪≫
    @asIso _ _ _ _ ((derivedPullbackComparison (unitStructPR R n)).app (unitHomotopy R))
      (isIso_derivedPullbackComparison_unitHomotopy R n) ≪≫
    pullbackOnHomotopyUnitIso R n

/-! ### The underived inputs -/

/-- The structure morphism of `ℙⁿ_R`, as a morphism of schemes. -/
abbrev unitStructP : P R n ⟶ Spec (CommRingCat.of R) := projToSpecCoeff R n

/-- **`H^q(ℙⁿ_R, 𝒪) = 0` for `q > 0`** ([Stacks, Tag 01XT]). -/
theorem isZero_H_unit (q : ℕ) (hq : 0 < q) :
    IsZero ((H R n q).obj (SheafOfModules.unit (P R n).ringCatSheaf)) := by
  have h : IsZero ((H R n q).obj (O R n 0)) :=
    (isZero_H_O_iff R n 0 q).2 (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology R n 0 q
      (by omega))
  exact h.of_iso ((H R n q).mapIso
    (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading R n))).symm

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`R^q p_*𝒪_{ℙⁿ_R} = 0` for `q > 0`**: the base is affine, so the higher direct images of a
quasi-coherent module are the sheaves associated to its cohomology, which vanishes. -/
theorem isZero_rightDerived_pushforward_unit (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward (unitStructP R n)).rightDerived q).obj
      (SheafOfModules.unit (P R n).ringCatSheaf)) := by
  have hc : IsZero (((moduleGlobalSections (P R n)).rightDerivedPlus (q : ℤ)).obj
      (SheafOfModules.unit (P R n).ringCatSheaf)) :=
    (isZero_H_unit R n q hq).of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections (P R n)) q).app _).symm
  have : QuasiCompact (unitStructP R n) := inferInstanceAs (QuasiCompact (W R n).hom)
  have : QuasiSeparated (unitStructP R n) := inferInstanceAs (QuasiSeparated (W R n).hom)
  exact
    (AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
      (unitStructP R n) (q : ℤ) _ hc).of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (unitStructP R n)) q).app _)

end Standard

/-- **`𝒪_{Spec R} = p_*𝒪_{ℙⁿ_R}`** as sheaves of rings: the comparison with the base-change model
`ℙⁿ_{Spec R}` of projective space is an isomorphism over `Spec R`, and for that model the
statement is [Stacks, Tag 01XW]. -/
theorem isIso_c_projToSpecCoeff : IsIso (unitStructP R n).c := by
  have hq :=
    AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isIso_c_structureMorphism_projectiveSpaceOver
      n (Spec (CommRingCat.of R))
  have he : unitStructP R n = projCompare R n ≫
      (projectiveSpaceOver n (Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) := by
    rw [← Stacks.ProjCoherentCohomologyFinite.projCompare_inv_comp_projToSpecCoeff R n]
    simp
  refine (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_app (unitStructP R n)).2
    fun U => ?_
  have h := (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_app _).1 hq U
  have hc : IsIso (projCompare R n).c := PresheafedSpace.c_isIso_of_iso (projCompare R n).toPshHom
  have h' := (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_app _).1 hc
    ((projectiveSpaceOver n (Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) ⁻¹ᵁ U)
  rw [he, Scheme.Hom.comp_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h h'

/-- The unit `𝒪_{Spec R} ⟶ p_*p^*𝒪_{Spec R}` of the adjunction `p^* ⊣ p_*` is invertible. -/
theorem isIso_adjunction_unit_unit :
    IsIso ((modulePullbackPushforwardAdjunction (unitStructPR R n)).unit.app
      (SheafOfModules.unit (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace))) := by
  have hc := isIso_c_projToSpecCoeff R n
  have hu : IsIso (SheafOfModules.unitToPushforwardObjUnit (unitStructP R n).toRingCatSheafHom) :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      (unitStructP R n)).1 hc
  have heq : (modulePullbackPushforwardAdjunction (unitStructPR R n)).homEquiv _ _
      (modulePullbackObjUnitIso (unitStructPR R n)).hom =
      SheafOfModules.unitToPushforwardObjUnit (unitStructP R n).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [Adjunction.homEquiv_unit] at heq
  have : IsIso ((modulePullbackPushforwardAdjunction (unitStructPR R n)).unit.app
      (SheafOfModules.unit (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace)) ≫
        (modulePushforward (unitStructPR R n)).map
          (modulePullbackObjUnitIso (unitStructPR R n)).hom) := by
    rw [heq]; exact hu
  exact IsIso.of_isIso_comp_right _
    ((modulePushforward (unitStructPR R n)).map (modulePullbackObjUnitIso (unitStructPR R n)).hom)

/-! ### The derived unit -/

/-- The unit of `K(p^*) ⊣ K(p_*)` at `𝒪_{Spec R}[0]` becomes invertible in the derived category:
it is the class of the degreewise unit, which is invertible in degree `0` and between zero
objects elsewhere. -/
theorem isIso_Qh_map_homotopyUnit :
    IsIso (DerivedCategory.Qh.map
      ((homotopyPullbackPushforwardAdjunction (unitStructPR R n)).unit.app (unitHomotopy R))) := by
  have hu := isIso_adjunction_unit_unit R n
  have hcomp : ∀ i : ℤ, IsIso ((modulePullbackPushforwardAdjunction (unitStructPR R n)).unit.app
      ((unitComplex R).X i)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact (NatTrans.isIso_app_iff_of_iso _
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _)).2 hu
    · have hz : IsZero ((unitComplex R).X i) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i hi
      exact isIso_of_source_target_iso_zero _ hz.isoZero
        (((modulePushforward (unitStructPR R n)).map_isZero
          ((modulePullback (unitStructPR R n)).map_isZero hz)).isoZero)
  rw [Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient]
  have hK : IsIso ((Adjunction.mapHomologicalComplexAdjunction
      (modulePullbackPushforwardAdjunction (unitStructPR R n)) (ComplexShape.up ℤ)).unit.app
        (unitComplex R)) := by
    have : ∀ i : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
        (modulePullbackPushforwardAdjunction (unitStructPR R n)) (ComplexShape.up ℤ)).unit.app
          (unitComplex R)).f i) := hcomp
    exact HomologicalComplex.Hom.isIso_of_components _
  have hQ : IsIso ((HomotopyCategory.quotient (SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace)) (ComplexShape.up ℤ)).map
        ((Adjunction.mapHomologicalComplexAdjunction
          (modulePullbackPushforwardAdjunction (unitStructPR R n)) (ComplexShape.up ℤ)).unit.app
          (unitComplex R))) := @Functor.map_isIso _ _ _ _ _ _ _ _ hK
  exact @Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Qh _ hQ

/-- The derived direct image along `p`, on the ringed-space spelling of the module categories. -/
abbrev derivedPushforwardP :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (P R n).toRingedSpace)) ⥤
    DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of R)).toRingedSpace)) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward (unitStructPR R n)

/-- The comparison `p_* ⟶ Rp_*`, on the ringed-space spelling. -/
abbrev derivedPushforwardUnitP :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit (unitStructPR R n)

/-- `Rp_*` commutes with the shift. -/
abbrev commShiftDerivedPushforwardP : (derivedPushforwardP R n).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (derivedPushforwardP R n) (derivedPushforwardUnitP R n)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing (P R n).toRingedSpace))
      (ComplexShape.up ℤ)) ℤ

attribute [local instance] commShiftDerivedPushforwardP

/-- `Rp_*` is a triangulated functor. -/
theorem isTriangulatedDerivedPushforwardP : (derivedPushforwardP R n).IsTriangulated := by
  have := SheafOfModules.isGrothendieckAbelianU (structureSheafRing (P R n).toRingedSpace)
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated (modulePushforward (unitStructPR R n))
    (derivedPushforwardP R n) (derivedPushforwardUnitP R n)

attribute [local instance] isTriangulatedDerivedPushforwardP

/-- The canonical comparison `p_*(-)[0] ⟶ Rp_*(-[0])` at `𝒪_{ℙⁿ_R}` is invertible: `𝒪_{ℙⁿ_R}`
has no higher direct images, and `R⁰p_* = p_*` because `p_*` is left exact. -/
theorem isIso_singleUnit_unit :
    IsIso ((Stacks.DerivedFunctor.singleUnit (modulePushforward (unitStructPR R n))
      (derivedPushforwardP R n) (derivedPushforwardUnitP R n)).app
      (SheafOfModules.unit (structureSheafRing (P R n).toRingedSpace))) := by
  have := SheafOfModules.isGrothendieckAbelianU (structureSheafRing (P R n).toRingedSpace)
  have hpf : PreservesFiniteLimits (modulePushforward (unitStructPR R n)) :=
    have : PreservesLimitsOfSize.{0, 0} (modulePushforward (unitStructPR R n)) :=
      (modulePullbackPushforwardAdjunction (unitStructPR R n)).rightAdjoint_preservesLimits
    inferInstance
  exact Stacks.DerivedFunctor.isIso_singleUnit_app (modulePushforward (unitStructPR R n))
    (derivedPushforwardP R n) (derivedPushforwardUnitP R n)
    (fun X => Stacks.DerivedFunctor.isGE_totalRightDerived_obj
      (modulePushforward (unitStructPR R n))
      ((DerivedCategory.singleFunctor _ 0).obj X) 0)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective _) _
    (fun q hq => isZero_rightDerived_pushforward_unit R n q hq)

/-- The comparison `p_* ⟶ Rp_*` is invertible at `𝒪_{ℙⁿ_R}[0]` in the homotopy category. -/
theorem isIso_αp_app_single :
    IsIso ((derivedPushforwardUnitP R n).app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (P R n).toRingedSpace)) 0).obj
        (SheafOfModules.unit (structureSheafRing (P R n).toRingedSpace)))) := by
  have h := isIso_singleUnit_unit R n
  simp only [Stacks.DerivedFunctor.singleUnit, NatTrans.comp_app] at h
  have h' := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h'

/-- Degreewise pullback of `𝒪_{Spec R}[0]` is `𝒪_{ℙⁿ_R}[0]`, in the homotopy category. -/
def pullbackHomotopyUnitIso :
    ((modulePullback (unitStructPR R n)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (unitHomotopy R) ≅
      (HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (P R n).toRingedSpace)) 0).obj
        (SheafOfModules.unit (structureSheafRing (P R n).toRingedSpace)) :=
  ((modulePullback (unitStructPR R n)).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
      (unitComplex R) ≪≫
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      (((HomologicalComplex.singleMapHomologicalComplex (modulePullback (unitStructPR R n))
        (ComplexShape.up ℤ) 0).app _) ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso (modulePullbackObjUnitIso (unitStructPR R n))) ≪≫
    ((HomotopyCategory.singleFunctorPostcompQuotientIso _ 0).app _).symm

/-- **`Rp_*𝒪_{ℙⁿ_R} = 𝒪_{Spec R}`, through the unit.** For `p : ℙⁿ_R ⟶ Spec R`, the unit
`𝒪_{Spec R}[0] ⟶ Rp_*Lp^*(𝒪_{Spec R}[0])` of the derived adjunction `Lp^* ⊣ Rp_*` is an
isomorphism, in the locally small model.

`𝒪_{Spec R}[0]` is K-flat, so `Lp^*` is computed degreewise and the derived unit factors as the
class of the degreewise unit followed by the comparison `p_* ⟶ Rp_*` at `𝒪_{ℙⁿ_R}[0]`
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac`). The degreewise
unit is invertible because `p_*𝒪_{ℙⁿ_R} = 𝒪_{Spec R}`, and the comparison because
`R^q p_*𝒪_{ℙⁿ_R} = 0` for `q > 0` ([Stacks, Tag 01XT]) while `R⁰p_* = p_*`. -/
theorem isIso_derivedAdjunction_unit_structureSheaf :
    IsIso ((Stacks.Duality.derivedAdjunction (projToSpecCoeff R n)).unit.app
      ((DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of R)).ringCatSheaf))) := by
  refine (NatTrans.isIso_app_iff_of_iso
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction (unitStructPR R n)).unit
    (singleUnitIsoQh R)).2 ?_
  have hfac := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac
    (unitStructPR R n) (unitHomotopy R)
  have h1 := isIso_Qh_map_homotopyUnit R n
  have h2 : IsIso ((derivedPushforwardUnitP R n).app
      (((modulePullback (unitStructPR R n)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (unitHomotopy R))) :=
    (NatTrans.isIso_app_iff_of_iso (derivedPushforwardUnitP R n) (pullbackHomotopyUnitIso R n)).2
      (isIso_αp_app_single R n)
  have h3 := isIso_derivedPullbackComparison_unitHomotopy R n
  have h4 : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      (unitStructPR R n)).unit.app (DerivedCategory.Qh.obj (unitHomotopy R)) ≫
        (derivedPushforwardP R n).map
          ((derivedPullbackComparison (unitStructPR R n)).app (unitHomotopy R))) := by
    rw [hfac]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ (derivedPushforwardP R n) _ h3) h4

end Stacks.Duality.ProjCoeff

end

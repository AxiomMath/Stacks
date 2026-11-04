module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian

/-!
# `R⁰f_* = f_*` for a morphism of ringed spaces

For a morphism of ringed spaces `f : X ⟶ Y` and an `𝒪_X`-module `P`, the comparison
`f_*P ⟶ Rf_*(P[0])` from the degreewise pushforward to the derived pushforward is invertible on
degree-zero cohomology, `f_*` being left exact.

## Main results

* `Stacks.Cohomology.DerivedStructureUnit.isIso_homology_derivedPushforwardUnit_app_single`:
  `f_*P ⟶ Rf_*(P[0])` is invertible on degree-zero cohomology.
* `HomologicalComplex.isIso_homologyMap_zero_iff`: a map of complexes concentrated in degree zero
  is invertible on degree-zero cohomology exactly when its degree-zero component is invertible.
* `Stacks.Cohomology.DerivedStructureUnit.isIso_homology_Qh_map_unit_app_single_iff`: the
  degreewise unit of `f^* ⊣ f_*` at `P[0]` is invertible in degree zero exactly when the unit at
  `P` is.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- For an adjunction `L ⊣ R` with unit `η`, an isomorphism `s : A ≅ A'` and a factorisation
`η_{A'} ≫ R(c) = w` with `c` invertible, `η_A ≫ R(ν) = s ≫ w ≫ R(c⁻¹ ≫ L(s⁻¹) ≫ ν)`. -/
theorem _root_.CategoryTheory.Adjunction.unit_app_comp_map_eq_of_iso {C D : Type*} [Category C]
    [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A A' : C} (s : A ≅ A') {P : D}
    (c : L.obj A' ⟶ P) [IsIso c] {w : A' ⟶ R.obj P} (hw : adj.unit.app A' ≫ R.map c = w)
    {B : D} (ν : L.obj A ⟶ B) :
    adj.unit.app A ≫ R.map ν = s.hom ≫ w ≫ R.map (inv c ≫ L.map s.inv ≫ ν) := by
  rw [← hw, Category.assoc, ← R.map_comp, IsIso.hom_inv_id_assoc, ← adj.unit_naturality_assoc]
  simp

namespace Stacks.Cohomology.DerivedStructureUnit

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **`R⁰f_* = f_*`**: the comparison `f_* P ⟶ Rf_*(P[0])` of the derived direct image of a
morphism of ringed spaces is invertible on degree-zero cohomology, `f_*` being left exact. -/
theorem isIso_homology_derivedPushforwardUnit_app_single
    (P : SheafOfModules.{u} (structureSheafRing X)) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
      ((derivedPushforwardUnit f).app
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
          P))) := by
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X)
  have hpf : Limits.PreservesFiniteLimits (modulePushforward f) := by
    have : Limits.PreservesLimitsOfSize.{0, 0} (modulePushforward f) :=
      (modulePullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
    infer_instance
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (modulePushforward f) _
      (derivedPushforwardUnit f)
  exact Stacks.DerivedFunctor.isIso_singleUnitHomology_app (modulePushforward f)
    (derivedPushforward f) (derivedPushforwardUnit f)
    (fun Z ↦ Stacks.SmallDerivedCategory.isGE_obj_of_isGE (modulePushforward f)
      (derivedPushforward f) (derivedPushforwardUnit f)
      (isIso_derivedPushforwardUnit_app_of_isKInjective f) _ 0 inferInstance)
    (fun I hI ↦ Stacks.DerivedFunctor.isIso_unit_app_single_of_injective (modulePushforward f)
      (derivedPushforward f) (derivedPushforwardUnit f) (exists_quasiIso_isKInjective X) I hI) P

/-- **Degree-zero cohomology of a map of complexes concentrated in degree zero.** For complexes
whose terms vanish outside degree `0`, the map induced on degree-zero cohomology is invertible
exactly when the degree-zero component is. -/
theorem _root_.HomologicalComplex.isIso_homologyMap_zero_iff {C : Type*} [Category C]
    [Abelian C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (hK : ∀ n : ℤ, n ≠ 0 → Limits.IsZero (K.X n)) (hL : ∀ n : ℤ, n ≠ 0 → Limits.IsZero (L.X n)) :
    IsIso (HomologicalComplex.homologyMap φ 0) ↔ IsIso (φ.f 0) := by
  have key : ∀ M : CochainComplex C ℤ, (∀ n : ℤ, n ≠ 0 → Limits.IsZero (M.X n)) →
      IsIso (M.iCycles 0) ∧ IsIso (M.homologyπ 0) := fun M hM =>
    ⟨M.isIso_iCycles 0 1 (by simp) ((hM 1 (by omega)).eq_of_tgt _ _),
      M.isIso_homologyπ (-1) 0 (by simp) ((hM (-1) (by omega)).eq_of_src _ _)⟩
  obtain ⟨_, _⟩ := key K hK
  obtain ⟨_, _⟩ := key L hL
  rw [← isIso_comp_left_iff (K.homologyπ 0), HomologicalComplex.homologyπ_naturality φ 0,
    isIso_comp_right_iff, ← isIso_comp_left_iff (K.iCycles 0) (φ.f 0),
    ← HomologicalComplex.cyclesMap_i φ 0, isIso_comp_right_iff]

/-- The degreewise unit of `f^* ⊣ f_*` at `P[0]` is invertible on degree-zero cohomology exactly
when the unit at `P` is invertible. -/
theorem isIso_homology_Qh_map_unit_app_single_iff (P : SheafOfModules.{u} (structureSheafRing Y)) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map
        (DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app
          ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
            P)))) ↔
      IsIso ((modulePullbackPushforwardAdjunction f).unit.app
        P) := by
  let K := (CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj P
  let φ := (Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction f)
    (ComplexShape.up ℤ)).unit.app K
  have heq : DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj P)) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map φ := rfl
  have hK : ∀ n : ℤ, n ≠ 0 → Limits.IsZero (K.X n) := fun n hn =>
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn
  rw [heq]
  change IsIso (((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
    DerivedCategory.homologyFunctor _ 0).map φ) ↔ _
  rw [NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) _ ≪≫
        DerivedCategory.homologyFunctorFactors _ 0),
    HomologicalComplex.homologyFunctor_map]
  refine (HomologicalComplex.isIso_homologyMap_zero_iff φ hK fun n hn =>
    (modulePushforward f).map_isZero ((modulePullback f).map_isZero (hK n hn))).trans ?_
  exact NatTrans.isIso_app_iff_of_iso (modulePullbackPushforwardAdjunction f).unit
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _)

end Stacks.Cohomology.DerivedStructureUnit

end

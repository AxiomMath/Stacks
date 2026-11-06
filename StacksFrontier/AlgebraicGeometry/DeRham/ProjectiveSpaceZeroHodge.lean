module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeChernPowers
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions

/-!
# Projective space `ℙⁿ_A` indexed by every `n ≥ 0`, and the Hodge cohomology of `ℙ⁰_A`

Let `A` be a commutative ring, `n ≥ 0` and `ℙⁿ_A = Proj A[T₀, …, Tₙ]` with its structure morphism
`ℙⁿ_A ⟶ Spec A`. This file defines the Hodge cohomology `H^q(ℙⁿ_A, Ωᵖ)` for every `n ≥ 0`, agreeing
by definition at `n = m + 1` with that of
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology`
(`projectiveHodgeCohomology_succ`), and proves:

* `Ωᵖ_{ℙⁿ_A/A} = 0` for `p > n`, for every `n ≥ 0` (`isZero_projectiveForms_of_lt`);
* `H^q(ℙ⁰_A, Ωᵖ) = 0` unless `p = q = 0` (`isZero_projectiveHodgeCohomology_zero`,
  `isZero_hypercohomology_projectiveForms_zero`);
* the unit section `1` is a basis of the free rank-one `A`-module `H⁰(ℙⁿ_A, Ω⁰)`, for every
  `n ≥ 0` (`exists_basis_sectionClass_projectiveUnitForm`,
  `exists_basis_projectiveHodgeCohomology_unitForm`).

Each is stated in both readings of cohomology the library uses: right derived functors of global
sections, and hypercohomology of the sheaf placed in degree zero, related by
`projectiveHodgeCohomologyIso`.

It also records, for every `n ≥ 0`, the invertibility of `𝒪(1)`, its class in `Pic(ℙⁿ_A)` and its
Hodge first Chern class `c₁^{Hodge}(𝒪(1))` of [Stacks, Tag 0FLE], which at `n = m + 1` are those of
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology` by definition
(`projectiveHodgeFirstChernClass_succ`).

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveSpace`: `ℙⁿ_A`, for every `n ≥ 0`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveForms`: `Ωᵖ_{ℙⁿ_A/A}`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveHodgeCohomology`: the `A`-module
  `H^q(ℙⁿ_A, Ωᵖ)`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveHodgeCohomologyIso`: its comparison with
  hypercohomology.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveUnitForm`: the unit section of `Ω⁰`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveHodgeFirstChernClass` and
  `projectiveHodgeFirstChernClassModule`: `c₁^{Hodge}(𝒪(1)) ∈ H¹(ℙⁿ_A, Ω)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isZero_projectiveForms_of_lt`:
  `Ωᵖ_{ℙⁿ_A/A} = 0` for `p > n`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isZero_projectiveHodgeCohomology_zero`:
  `H^q(ℙ⁰_A, Ωᵖ) = 0` unless `p = q = 0`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.exists_basis_projectiveHodgeCohomology_unitForm`:
  `1` is a basis of `H⁰(ℙⁿ_A, Ω⁰)`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isInvertible_projectiveTwistingSheafOne`: `𝒪(1)`
  is invertible on `ℙⁿ_A`, for every `n ≥ 0`.

## References

* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.Hypercohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.ProjectiveSpace.Cohomology

variable (A : Type u) [CommRing A] (n : ℕ)

/-! ### Projective space, its differential forms and their cohomology, for every `n ≥ 0` -/

section Setting

/-- `ℙⁿ_A = Proj A[T₀, …, Tₙ]`, for every `n ≥ 0`. At `n = m + 1` it is `projSpace A m`. -/
abbrev projectiveSpace : Scheme.{u} := AlgebraicGeometry.Proj (polyGrading A n)

/-- The sheaf `Ωᵖ_{ℙⁿ_A/A}` of relative differential `p`-forms of `ℙⁿ_A ⟶ Spec A`. At `n = m + 1`
it is `forms A m p`. -/
abbrev projectiveForms (p : ℕ) : (projectiveSpace A n).Modules :=
  Scheme.Hom.relativeDifferentialForms (projToSpecCoeff A n) (p : ℤ)

/-- **The `A`-module `H^q(ℙⁿ_A, Ωᵖ)`**, the coefficients acting through the structure morphism
`ℙⁿ_A ⟶ Spec A`, as in `Stacks.ProjectiveSpace.Cohomology.twistCohomology`. At `n = m + 1` it is
`hodgeCohomology A m p q`. -/
abbrev projectiveHodgeCohomology (p q : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A n)).obj
    (((Stacks.Cohomology.sectionsFunctor (projectiveSpace A n) ⊤).rightDerived q).obj
      (projectiveForms A n p))

/-- At `n = m + 1` the Hodge cohomology of `ℙⁿ_A` is the one of
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology`, by definition. -/
theorem projectiveHodgeCohomology_succ (m p q : ℕ) :
    projectiveHodgeCohomology A (m + 1) p q = hodgeCohomology A m p q :=
  rfl

/-- The cohomology `H^q(ℙⁿ_A, Ωᵖ)` computed by right derived functors is the hypercohomology of
`Ωᵖ` placed in degree zero, as `A`-modules. -/
def projectiveHodgeCohomologyIso (p q : ℕ) :
    projectiveHodgeCohomology A n p q ≅ (ModuleCat.restrictScalars.{u} (coeffScalar A n)).obj
      (hypercohomology (projectiveSpace A n).sheaf
        (singlePlus (projectiveSpace A n).sheaf (projectiveForms A n p) 0) q) :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A n)).mapIso
    (rightDerivedIsoHypercohomology (projectiveSpace A n) (projectiveForms A n p) q)

end Setting

/-! ### Čech cohomology computes the cohomology of the sheaves involved -/

section CechComputes

/-- Čech cohomology computes the cohomology of `Ωᵖ` on `ℙⁿ_A`. -/
theorem cechComputesSheaf_projectiveForms (p : ℕ) :
    CechComputesSheaf (projectiveSpace A n).sheaf (projectiveForms A n p) :=
  have : SheafOfModules.IsQuasicoherent.{u, u, u} (R := (projectiveSpace A n).ringCatSheaf)
      (projectiveForms A n p) :=
    (inferInstance : (Scheme.Modules.exteriorPower (X := projectiveSpace A n)
      (Scheme.Hom.relativeDifferentials (projToSpecCoeff A n)) (p : ℤ)).IsQuasicoherent)
  cechComputesSheaf_of_isQuasicoherent (projectiveSpace A n) (projectiveForms A n p)

/-- Čech cohomology computes the cohomology of `Ω` on `ℙⁿ_A`. -/
theorem cechComputesSheaf_projDifferentials :
    CechComputesSheaf (projectiveSpace A n).sheaf (projDifferentials A n) :=
  cechComputesSheaf_of_isQuasicoherent (projectiveSpace A n) (projDifferentials A n)

/-- Čech cohomology computes the cohomology of `𝒪` on `ℙⁿ_A`. -/
theorem cechComputesSheaf_projectiveUnit :
    CechComputesSheaf (projectiveSpace A n).sheaf
      (SheafOfModules.unit (ringSheaf (projectiveSpace A n).sheaf)) :=
  cechComputesSheaf_of_isQuasicoherent (projectiveSpace A n) (SheafOfModules.unit _)

/-- The unit section `1` of `Ω⁰_{ℙⁿ_A/A} = 𝒪`. -/
def projectiveUnitForm : (projectiveForms A n 0).val.obj (op ⊤) :=
  (Scheme.Hom.relativeDifferentialFormsZeroIso (projToSpecCoeff A n)).inv.val.app (op ⊤)
    (1 : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n)).obj.obj (op ⊤))

end CechComputes

/-! ### `𝒪(1)` and its Hodge first Chern class, for every `n ≥ 0` -/

section ChernClass

/-- **`𝒪(1)` is an invertible sheaf on `ℙⁿ_A`**, for every `n ≥ 0` [Stacks, Tag 01MT]. -/
theorem isInvertible_projectiveTwistingSheafOne :
    Stacks.SheafOfModules.IsInvertible (projectiveSpace A n).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf (projectiveSpace A n).toRingedSpace)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) 1) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
    (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf
      (polyGrading A n) (Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading A n) 1)

/-- **The class of `𝒪(1)` in `Pic(ℙⁿ_A)`**, for every `n ≥ 0`. -/
def projectiveTwistingSheafOnePicardClass : Stacks.Picard.ofScheme (projectiveSpace A n) :=
  Stacks.SheafOfModules.picardClass (projectiveSpace A n).toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf (projectiveSpace A n).toRingedSpace)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) 1)
    (isInvertible_projectiveTwistingSheafOne A n)

/-- **The Hodge first Chern class `c₁^{Hodge}(𝒪(1)) ∈ H¹(ℙⁿ_A, Ω)`** of [Stacks, Tag 0FLE], read
in sheaves of abelian groups, for every `n ≥ 0`. -/
@[sga "7 XI 1.0" "special case"]
abbrev projectiveHodgeFirstChernClass :
    AlgebraicGeometry.Scheme.Hom.hodgeCohomologyOne (projToSpecCoeff A n) :=
  AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass (projToSpecCoeff A n)
    (projectiveTwistingSheafOnePicardClass A n)

/-- **The Hodge first Chern class of `𝒪(1)`, as a class of the sheaf of modules `Ω_{ℙⁿ_A/A}`**:
its image under the identification of first cohomology of [Stacks, Tag 03FD]. -/
@[sga "7 XI 1.0" "special case", sga "7 XI 1.5" "special case"]
abbrev projectiveHodgeFirstChernClassModule :
    hypercohomology (projectiveSpace A n).sheaf
      (singlePlus (projectiveSpace A n).sheaf (projDifferentials A n) 0) 1 :=
  abelianToModuleH1 (projDifferentials A n) (projectiveHodgeFirstChernClass A n)

/-- At `n = m + 1` the Hodge first Chern class of `𝒪(1)` is the one of
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology`, by definition. -/
theorem projectiveHodgeFirstChernClass_succ (m : ℕ) :
    projectiveHodgeFirstChernClass A (m + 1) = hodgeFirstChernClassTwistingSheafOne A m :=
  rfl

end ChernClass

/-! ### Degree zero, and `ℙ⁰_A` -/

section DegreeZero

/-- **`Ωᵖ_{ℙⁿ_A/A} = 0` for `p > n`**, for every `n ≥ 0`. -/
theorem isZero_projectiveForms_of_lt {p : ℕ} (hp : n < p) : IsZero (projectiveForms A n p) := by
  rcases n with _ | m
  · rw [IsZero.iff_id_eq_zero]
    refine Stacks.SheafOfModules.TopWedge.id_eq_zero_of_subsingleton_stalk _ fun x ↦ ?_
    obtain ⟨i, hxi⟩ : ∃ i : Fin (0 + 1),
        x ∈ ProjectiveSpectrum.basicOpen (polyGrading A 0) (MvPolynomial.X i) :=
      TopologicalSpace.Opens.mem_iSup.mp (show x ∈ ⨆ i : Fin (0 + 1),
          Proj.basicOpen (polyGrading A 0) (MvPolynomial.X i) by
        rw [iSup_basicOpen_X_eq_top]; trivial)
    have hcard : Nat.card {j : Fin (0 + 1) // j ≠ i} < p := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
        Fintype.card_subtype_eq]
      omega
    exact @Equiv.subsingleton _ _
      (SheafOfModules.exteriorPowerStalkEquiv
        (Scheme.Hom.relativeDifferentialFormsAlgebra (projToSpecCoeff A 0))
        (Scheme.Modules.exteriorGenerator
          (Scheme.Hom.relativeDifferentials (projToSpecCoeff A 0)))
        (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) p x).toEquiv
      (@exteriorPower.subsingleton_of_span_eq_top_of_card_lt
        (projStalk A 0 x) _ _ _ (moduleStalkProjDifferentials A 0 x)
        {j : Fin (0 + 1) // j ≠ i} _
        (fun j ↦ chartDiffGerm A 0 x i hxi j.1)
        (span_range_chartDiffGerm_eq_top A 0 x i hxi hxi) p hcard)
  · exact Stacks.AlgebraicGeometry.ProjectiveSpaceForms.isZero_relativeDifferentialForms_of_lt m p
      hp

/-- `Ω⁰_{ℙⁿ_A/A} = 𝒪 = 𝒪(0)`, for every `n ≥ 0`. -/
def projectiveFormsZeroIso :
    projectiveForms A n 0 ≅ ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) 0 :=
  Scheme.Hom.relativeDifferentialFormsZeroIso (projToSpecCoeff A n) ≪≫
    (twistingSheafZeroIsoUnit (polyGrading A n)).symm

/-- **`H^q(ℙⁿ_A, Ω⁰) ≅ H^q(ℙⁿ_A, 𝒪(0))`**, for every `n ≥ 0` and `q`. -/
def projectiveHodgeCohomologyZeroIso (q : ℕ) :
    projectiveHodgeCohomology A n 0 q ≅ twistCohomology A n 0 q :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A n)).mapIso
    (((Stacks.Cohomology.sectionsFunctor (projectiveSpace A n) ⊤).rightDerived q).mapIso
      (projectiveFormsZeroIso A n))

/-- **`H^q(ℙ⁰_A, Ωᵖ) = 0` unless `p = q = 0`**, in the cohomology computed by right derived
functors. -/
theorem isZero_projectiveHodgeCohomology_zero (p q : ℕ) (hpq : p ≠ q ∨ 0 < p) :
    IsZero (projectiveHodgeCohomology A 0 p q) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact (isZero_twistCohomology A 0 0 q (by omega)).of_iso
      (projectiveHodgeCohomologyZeroIso A 0 q)
  · exact (ModuleCat.restrictScalars.{u} (coeffScalar A 0)).map_isZero
      (((Stacks.Cohomology.sectionsFunctor (projectiveSpace A 0) ⊤).rightDerived q).map_isZero
        (isZero_projectiveForms_of_lt A 0 hp))

/-- **`H^q(ℙ⁰_A, Ωᵖ) = 0` unless `p = q = 0`**, in the cohomology computed by
hypercohomology. -/
theorem isZero_hypercohomology_projectiveForms_zero (p q : ℕ) (hpq : p ≠ q ∨ 0 < p) :
    IsZero (hypercohomology (projectiveSpace A 0).sheaf
      (singlePlus (projectiveSpace A 0).sheaf (projectiveForms A 0 p) 0) q) :=
  ((isZero_restrictScalars_iff (coeffScalar A 0) _).mp
    (isZero_projectiveHodgeCohomology_zero A p q hpq)).of_iso
      (rightDerivedIsoHypercohomology (projectiveSpace A 0) (projectiveForms A 0 p) q).symm

/-- `H⁰(ℙⁿ_A, Ω⁰) ≅ A`, in the cohomology computed by hypercohomology, for every `n ≥ 0`. -/
def projectiveHypercohomologyFormsZeroEquiv :
    (ModuleCat.restrictScalars.{u} (coeffScalar A n)).obj
        (hypercohomology (projectiveSpace A n).sheaf
          (singlePlus (projectiveSpace A n).sheaf (projectiveForms A n 0) 0) ((0 : ℕ) : ℤ)) ≃ₗ[A]
      A :=
  ((projectiveHodgeCohomologyIso A n 0 0).symm ≪≫ projectiveHodgeCohomologyZeroIso A n 0 ≪≫
    twistCohomologyZeroIsoCoeff A n).toLinearEquiv

/-- `H⁰(ℙⁿ_A, 𝒪) ≅ H⁰(ℙⁿ_A, Ω⁰)`, induced by `𝒪 ≅ Ω⁰`. -/
def projectiveHypercohomologyUnitEquivForms :
    (ModuleCat.restrictScalars.{u} (coeffScalar A n)).obj
        (hypercohomology (projectiveSpace A n).sheaf
          (singlePlus (projectiveSpace A n).sheaf
            (SheafOfModules.unit (ringSheaf (projectiveSpace A n).sheaf)) 0) 0) ≃ₗ[A]
      (ModuleCat.restrictScalars.{u} (coeffScalar A n)).obj
        (hypercohomology (projectiveSpace A n).sheaf
          (singlePlus (projectiveSpace A n).sheaf (projectiveForms A n 0) 0) ((0 : ℕ) : ℤ)) :=
  ((ModuleCat.restrictScalars.{u} (coeffScalar A n)).mapIso
    (hypercohomologySingleIso (projectiveSpace A n).sheaf
      (Scheme.Hom.relativeDifferentialFormsZeroIso (projToSpecCoeff A n)).symm 0)).toLinearEquiv

/-- **The unit section `1` is a basis of `H⁰(ℙⁿ_A, Ω⁰)`**, for every `n ≥ 0`, in the
cohomology computed by hypercohomology. -/
theorem exists_basis_sectionClass_projectiveUnitForm :
    ∃ b : Module.Basis (Fin 1) A ((ModuleCat.restrictScalars.{u} (coeffScalar A n)).obj
      (hypercohomology (projectiveSpace A n).sheaf
        (singlePlus (projectiveSpace A n).sheaf (projectiveForms A n 0) 0) ((0 : ℕ) : ℤ))),
      b 0 = sectionClass (projectiveForms A n 0) (projectiveUnitForm A n) := by
  obtain ⟨b, hb⟩ := exists_basis_of_rightUnit A
    ((projectiveHypercohomologyUnitEquivForms A n).trans
      (projectiveHypercohomologyFormsZeroEquiv A n))
    (sectionClass (unitSheaf (projectiveSpace A n).sheaf)
      (oneSection (projectiveSpace A n).sheaf))
    (fun g g' ↦ cup (projectiveSpace A n).sheaf (cechComputesSheaf_projectiveUnit A n)
      (cechComputesSheaf_projectiveUnit A n)
      (scalarPairing (projectiveSpace A n).sheaf (unitSheaf _)) 0 0 0 (add_zero 0) g g')
    (fun g ↦ cup_scalarPairing_sectionClass_one _ (cechComputesSheaf_projectiveUnit A n)
      (cechComputesSheaf_projectiveUnit A n) 0 g)
    (fun g g' a ↦ cup_smul_right (projectiveSpace A n).sheaf _ _ _ 0 0 0 (add_zero 0) g g'
      (coeffScalar A n a))
  refine ⟨b.map (projectiveHypercohomologyUnitEquivForms A n), ?_⟩
  rw [Module.Basis.map_apply, hb]
  exact hypercohomologyMap_sectionClass _ _

/-- **The unit section `1` is a basis of `H⁰(ℙⁿ_A, Ω⁰)`**, for every `n ≥ 0`, in the
cohomology computed by right derived functors. -/
theorem exists_basis_projectiveHodgeCohomology_unitForm :
    ∃ b : Module.Basis (Fin 1) A ↥(projectiveHodgeCohomology A n 0 0),
      b 0 = (projectiveHodgeCohomologyIso A n 0 0).inv
        (sectionClass (projectiveForms A n 0) (projectiveUnitForm A n)) := by
  obtain ⟨b, hb⟩ := exists_basis_sectionClass_projectiveUnitForm A n
  refine ⟨b.map (projectiveHodgeCohomologyIso A n 0 0).toLinearEquiv.symm, ?_⟩
  rw [Module.Basis.map_apply, hb]
  rfl

end DegreeZero

end Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

end

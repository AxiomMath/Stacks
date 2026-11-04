module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceZeroHodge
public import StacksFrontier.AlgebraicGeometry.DeRham.VanishingDifferentialsDeRham

/-!
# The de Rham cohomology of `ℙⁿ_A`, for every `n ≥ 0`

Let `A` be a commutative ring, `n ≥ 0` and `ℙⁿ_A = Proj A[T₀, …, Tₙ]` with its structure morphism
`ℙⁿ_A ⟶ Spec A`. This file states [Stacks, Tag 0FMJ] for every `n ≥ 0`, as one declaration
(`exists_basis_and_isZero_projectiveDeRhamCohomology`):

* for `0 ≤ i ≤ n` the `A`-module `H^{2i}_dR(ℙⁿ_A/A)` is free of rank one with basis element
  `c₁^{dR}(𝒪(1))^i`, the `i`-th cup power of the de Rham first Chern class of `𝒪(1)`;
* in every other degree `H^k_dR(ℙⁿ_A/A)` vanishes.

For `n = m + 1 ≥ 1` the objects here are those of
`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamCohomology` by definition
(`projectiveDeRhamCohomology_succ`, `projectiveDeRhamChernPow_succ`; there `projSpace A m` is
`Proj A[T₀, …, T_{m+1}] = ℙ^{m+1}_A`), and both assertions are the ones proved there. For `n = 0`
the relative differentials of `ℙ⁰_A` vanish (`isZero_projectiveForms_of_lt`), so the
Hodge-to-de Rham spectral sequence of the source's proof degenerates to
`H^k_dR(ℙ⁰_A/A) = H^k(ℙ⁰_A, 𝒪)` (`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyEquivFormsZero`);
this vanishes for `k ≠ 0` by [Stacks, Tag 0FMI] at `n = 0`, and in degree zero it carries
`c₁^{dR}(𝒪(1))⁰ = 1` to the unit section, which is a basis of `H⁰(ℙ⁰_A, 𝒪) = A`.

## Main definitions

* `projectiveDeRhamCohomology`: the `A`-module `H^i_dR(ℙⁿ_A/A)`.
* `projectiveDeRhamChernPow`: the cup powers `c₁^{dR}(𝒪(1))^i ∈ H^{2i}_dR(ℙⁿ_A/A)`.

## Main results

* `exists_basis_and_isZero_projectiveDeRhamCohomology`: [Stacks, Tag 0FMJ], for every `n ≥ 0`.

## References

* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
* [Stacks Project, Tag 0FMI](https://stacks.math.columbia.edu/tag/0FMI)
* [Stacks Project, Section 0FM6](https://stacks.math.columbia.edu/tag/0FM6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cech.Hypercohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge
open Stacks.ProjectiveSpace.Cohomology (coeffScalar)

variable (A : Type u) [CommRing A] (n : ℕ)

/-! ### The setting, for every `n ≥ 0` -/

section Setting

/-- **The `A`-module `H^i_dR(ℙⁿ_A/A)`**, for every `n ≥ 0`: relative de Rham cohomology of
`ℙⁿ_A ⟶ Spec A`, a module over `Γ(Spec A, 𝒪)` by [Stacks, Tag 0FL6], read over `A` along
`A ≅ Γ(Spec A, 𝒪)`. -/
abbrev projectiveDeRhamCohomology (i : ℤ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).obj
    (Scheme.Hom.deRhamCohomologyBaseModule (projToSpecCoeff A n) i)

/-- At `n = m + 1` it is the de Rham cohomology of `deRhamCohomology`, by definition. -/
theorem projectiveDeRhamCohomology_succ (m : ℕ) (i : ℤ) :
    projectiveDeRhamCohomology A (m + 1) i = deRhamCohomology A m i :=
  rfl

/-- **The powers `c₁^{dR}(𝒪(1))^i ∈ H^{2i}_dR(ℙⁿ_A/A)`**, for every `n ≥ 0`: the cup powers, for
the cup product of [Stacks, Section 0FM3], of the de Rham first Chern class of `𝒪(1)` of
[Stacks, Section 0FLE]; `c⁰ = 1` and `c^{i+1} = cⁱ ∪ c₁^{dR}(𝒪(1))`
(`AlgebraicGeometry.Scheme.Hom.deRhamChernPow_zero`, `deRhamChernPow_succ`). -/
abbrev projectiveDeRhamChernPow (i : ℕ) : ↥(projectiveDeRhamCohomology A n (2 * (i : ℤ))) :=
  Scheme.Hom.deRhamChernPow (projToSpecCoeff A n)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) 1)
    (isInvertible_projectiveTwistingSheafOne A n) i

/-- At `n = m + 1` the powers are `chernPow`, by definition. -/
theorem projectiveDeRhamChernPow_succ (m i : ℕ) :
    projectiveDeRhamChernPow A (m + 1) i = chernPow A m i :=
  rfl

end Setting

/-! ### `ℙ⁰_A` -/

section Zero

/-- `Ωᵏ_{ℙ⁰_A/A} = 0` for `k ≥ 1`. -/
theorem isZero_relativeDifferentialForms_projectiveZero (k : ℕ) (hk : 0 < k) :
    IsZero (Scheme.Hom.relativeDifferentialForms (projToSpecCoeff A 0) (k : ℤ)) :=
  isZero_projectiveForms_of_lt A 0 hk

/-- The coefficients of `H^*_dR(ℙ⁰_A/A)` act on `Γ(ℙ⁰_A, 𝒪)` as the coefficients `A`. -/
theorem underlyingRingHom_inverseImageGlobalSections_projectiveZero (a : A) :
    ((AlgebraicGeometry.SheafOfModules.underlyingRingHom
        (φ := inverseImageStructureMap (projToSpecCoeff A 0))).hom.app (op ⊤)).hom
        ((Scheme.Hom.inverseImageGlobalSections (projToSpecCoeff A 0)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) =
      coeffScalar A 0 a :=
  congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (Scheme.Hom.inverseImageGlobalSections_comp_inverseImageStructureMap_app
      (projToSpecCoeff A 0))

/-- **`H⁰_dR(ℙ⁰_A/A) ≅ H⁰(ℙ⁰_A, Ω⁰)` as `A`-modules**: the relative differentials of `ℙ⁰_A`
vanish, so its de Rham complex is `𝒪` in degree zero. -/
def projectiveDeRhamCohomologyZeroEquiv :
    ↥(projectiveDeRhamCohomology A 0 ((0 : ℕ) : ℤ)) ≃ₗ[A]
      ↥((ModuleCat.restrictScalars.{u} (coeffScalar A 0)).obj
        (hypercohomology (projectiveSpace A 0).sheaf
          (singlePlus (projectiveSpace A 0).sheaf (projectiveForms A 0 0) 0) ((0 : ℕ) : ℤ))) where
  __ := Scheme.Hom.deRhamCohomologyEquivFormsZero (projToSpecCoeff A 0)
    (isZero_relativeDifferentialForms_projectiveZero A) 0
  map_smul' a x := by
    refine (Scheme.Hom.deRhamCohomologyEquivFormsZero_smul (projToSpecCoeff A 0)
      (isZero_relativeDifferentialForms_projectiveZero A) 0 _ x).trans ?_
    exact congrArg (fun r => r • Scheme.Hom.deRhamCohomologyEquivFormsZero (projToSpecCoeff A 0)
      (isZero_relativeDifferentialForms_projectiveZero A) 0 x)
      (underlyingRingHom_inverseImageGlobalSections_projectiveZero A a)

/-- **[Stacks, Tag 0FMJ] for `n = 0`, the basis**: `1 = c₁^{dR}(𝒪(1))⁰` is a basis of
`H⁰_dR(ℙ⁰_A/A)`. -/
theorem exists_basis_projectiveDeRhamChernPow_zero :
    ∃ b : Module.Basis (Fin 1) A ↥(projectiveDeRhamCohomology A 0 (2 * ((0 : ℕ) : ℤ))),
      b 0 = projectiveDeRhamChernPow A 0 0 := by
  obtain ⟨b, hb⟩ := exists_basis_sectionClass_projectiveUnitForm A 0
  refine ⟨b.map (projectiveDeRhamCohomologyZeroEquiv A).symm, ?_⟩
  rw [Module.Basis.map_apply, hb]
  exact (projectiveDeRhamCohomologyZeroEquiv A).symm_apply_eq.mpr
    (Scheme.Hom.deRhamCohomologyEquivFormsZero_deRhamUnit (projToSpecCoeff A 0)
      (isZero_relativeDifferentialForms_projectiveZero A)).symm

/-- **[Stacks, Tag 0FMJ] for `n = 0`, the vanishing**: `H^k_dR(ℙ⁰_A/A) = 0` for `k ≠ 0`. -/
theorem isZero_projectiveDeRhamCohomology_zero (k : ℤ) (hk : k ≠ 0) :
    IsZero (projectiveDeRhamCohomology A 0 k) := by
  refine (isZero_restrictScalars_iff _ _).mpr ?_
  rcases lt_or_gt_of_ne hk with hk | hk
  · exact Scheme.Hom.isZero_deRhamCohomologyBaseModule_of_neg _ k hk
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
    exact Scheme.Hom.isZero_deRhamCohomologyBaseModule_of_isZero (projToSpecCoeff A 0)
      (isZero_relativeDifferentialForms_projectiveZero A) q
      (isZero_hypercohomology_projectiveForms_zero A 0 q (Or.inl (by omega)))

end Zero

/-! ### [Stacks, Tag 0FMJ], for every `n ≥ 0` -/

/-- **[Stacks, Tag 0FMJ].** For every `n ≥ 0`: for `0 ≤ i ≤ n` the `A`-module
`H^{2i}_dR(ℙⁿ_A/A)` is free of rank one with basis element `c₁^{dR}(𝒪(1))^i`, and in every
other degree `k` the de Rham cohomology `H^k_dR(ℙⁿ_A/A)` vanishes.

For `n ≥ 1` both parts are `exists_basis_chernPow` and `isZero_deRhamCohomology`. For `n = 0`
they are `exists_basis_projectiveDeRhamChernPow_zero` and
`isZero_projectiveDeRhamCohomology_zero`. -/
@[stacks 0FMJ "for 0 ≤ i ≤ n the A-module H^{2i}_dR(ℙⁿ_A/A) is free of rank one with basis
c₁^dR(𝒪(1))^i, and every other degree vanishes, for every n ≥ 0"]
theorem exists_basis_and_isZero_projectiveDeRhamCohomology :
    (∀ i : ℕ, i ≤ n → ∃ b : Module.Basis (Fin 1) A ↥(projectiveDeRhamCohomology A n (2 * (i : ℤ))),
      b 0 = projectiveDeRhamChernPow A n i) ∧
    ∀ k : ℤ, (∀ i : ℕ, i ≤ n → k ≠ 2 * i) → IsZero (projectiveDeRhamCohomology A n k) := by
  rcases n with _ | m
  · refine ⟨fun i hi => ?_, fun k hk => isZero_projectiveDeRhamCohomology_zero A k
      (by simpa using hk 0 le_rfl)⟩
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact exists_basis_projectiveDeRhamChernPow_zero A
  · exact ⟨fun i hi => exists_basis_chernPow i hi, fun k hk => isZero_deRhamCohomology k hk⟩

end Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham

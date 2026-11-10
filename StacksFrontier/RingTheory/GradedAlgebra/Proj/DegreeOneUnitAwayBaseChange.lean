module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.DegreeOneUnitAway
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The localization of a graded module at a product of consecutive degrees is a base change

Let `A` be a graded ring, `g = cb` with `c ∈ A_{m+1}` and `b ∈ A_m`, and `u = c² / g` the unit of
degree one of `A[1/g]` (`Stacks.DegreeOneUnitAway.chartUnit`). The powers `uʲ` form a basis of
`A[1/g]` over `A₍g₎`, and for a graded `A`-module `M` they span `M[1/g]` over `M₍g₎` with no
relations. Consequently `M[1/g]` is the base change of `M₍g₎` along `A₍g₎ → A[1/g]`:

`A[1/g] ⊗_{A₍g₎} M₍g₎ ≅ M[1/g]`.

## Main results

* `Stacks.DegreeOneUnitAway.isBaseChange_degreeZero`: `M[1/g]` is the base change of `M₍g₎` along
  `A₍g₎ → A[1/g]`, for `g = cb` with `c`, `b` homogeneous of consecutive degrees.
-/

@[expose] public noncomputable section

namespace Stacks.DegreeOneUnitAway

open HomogeneousLocalization Stacks.GradedLocalization TensorProduct

universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {M : Type v} [AddCommGroup M] [Module A M] {τ : Type*} [SetLike τ M]
  [AddSubgroupClass τ M] {𝓜 : ℤ → τ} [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]
  {c b g : A} {m : ℕ}

/-- The action of the degree-zero localization of the ring on the localized module. -/
local instance moduleAwayBC (g : A) : Module (Away 𝒜 g) (LocalizedModule.Away (R := A) g M) :=
  Module.compHom (R := Localization.Away g) (LocalizedModule.Away (R := A) g M)
    (algebraMap (Away 𝒜 g) (Localization.Away g))

/-- The actions of `A₍g₎` and of `A[1/g]` on `M[1/g]` form a scalar tower. -/
local instance isScalarTowerAwayBC (g : A) :
    IsScalarTower (Away 𝒜 g) (Localization.Away g) (LocalizedModule.Away (R := A) g M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **`M[1/g]` is the base change of `M₍g₎` along `A₍g₎ → A[1/g]`** for `g = cb` a product of
homogeneous elements of consecutive degrees. -/
theorem isBaseChange_degreeZero (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    IsBaseChange (Localization.Away g) (GradedModuleDegreeZeroLocalization 𝒜 𝓜 g).subtype := by
  classical
  set N := GradedModuleDegreeZeroLocalization 𝒜 𝓜 g with hN
  set φ : Localization.Away g ⊗[Away 𝒜 g] N →ₗ[Localization.Away g]
      LocalizedModule.Away (R := A) g M :=
    AlgebraTensorModule.lift
      { toFun := fun a =>
          { toFun := fun z => a • (z : LocalizedModule.Away (R := A) g M)
            map_add' := fun z z' => by rw [Submodule.coe_add, smul_add]
            map_smul' := fun r z => by
              rw [Submodule.coe_smul, RingHom.id_apply, smul_comm] }
        map_add' := fun a a' => LinearMap.ext fun z => add_smul a a' _
        map_smul' := fun r a => LinearMap.ext fun z => by
          change (r • a) • (z : LocalizedModule.Away (R := A) g M) =
            r • (a • (z : LocalizedModule.Away (R := A) g M))
          rw [smul_assoc] } with hφ
  have hφ_tmul : ∀ (a : Localization.Away g) (z : N), φ (a ⊗ₜ z) = a • (z : _) := fun _ _ => rfl
  have hφ_one : ∀ z : N, φ (1 ⊗ₜ z) = (z : LocalizedModule.Away (R := A) g M) := fun z => by
    rw [hφ_tmul, one_smul]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff,
      ← span_degreeZero_eq_top (𝓜 := 𝓜) hc hb hcb, Submodule.span_le]
    intro z hz
    exact ⟨1 ⊗ₜ ⟨z, hz⟩, hφ_one ⟨z, hz⟩⟩
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    set ℬ := basisChartUnit hc hb hcb
    obtain ⟨w, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.surjective x
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum, map_sum] at hx
    simp only [hφ_tmul, ℬ, basisChartUnit_apply] at hx
    have hw0 : w = 0 := Finsupp.ext fun j => by_contra fun hj => hj <|
      eq_zero_of_sum_chartUnit_zpow_smul_eq_zero hc hb hcb w.support (fun j => w j) hx
        (Finsupp.mem_support_iff.mpr hj)
    rw [hw0, map_zero]
    exact Submodule.zero_mem _
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩) hφ_one

end Stacks.DegreeOneUnitAway

end

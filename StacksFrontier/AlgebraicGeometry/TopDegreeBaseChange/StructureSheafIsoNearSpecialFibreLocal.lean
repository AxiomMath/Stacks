module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# A local criterion for injectivity of a surjection onto a flat module

Let `R → A` be a local homomorphism of local rings, `M` an `A`-module, `B` an `A`-module flat
over `R`, and `u : M → B` a surjective `A`-linear map with finitely generated kernel. If `u` is
injective modulo `𝔪_R` then `u` is injective.

## Main results

* `injective_of_surjective_of_flat_of_fg_ker`: the criterion.
* `mem_smul_top_of_injective_baseChange`: injectivity modulo an ideal `I` of `R` follows from
  injectivity after extension of scalars along a surjection `A → C` whose kernel is `I A`.

## Implementation notes

The finiteness of the kernel replaces the Noetherian hypothesis of [Stacks, Tag 00ME]: the
flatness of `B` gives `K/𝔪_R K ↪ M/𝔪_R M` for the kernel `K`, so that `K = 𝔪_R K` and
Nakayama's lemma applies.

## References

* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 00ME](https://stacks.math.columbia.edu/tag/00ME)
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- `1 ⊗ x` vanishes in `R/I ⊗[R] M` exactly when `x ∈ I M`. -/
private theorem one_tmul_eq_zero_iff_mem_smul_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) (x : M) :
    Ideal.Quotient.mk I 1 ⊗ₜ[R] x = 0 ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]

/-- Let `R → A` be a local homomorphism of local rings, `M` an `A`-module, `B` an `A`-module flat
over `R`, and `u : M → B` a surjective `A`-linear map with finitely generated kernel. If every
`a : M` with `u a ∈ 𝔪_R B` lies in `𝔪_R M`, then `u` is injective. -/
theorem injective_of_surjective_of_flat_of_fg_ker
    {R A B : Type*} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    {M : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup B] [Module A B] [Module R B] [IsScalarTower R A B] [Module.Flat R B]
    (u : M →ₗ[A] B) (hu : Function.Surjective u) (hK : (LinearMap.ker u).FG)
    (hbar : ∀ a : M, u a ∈ maximalIdeal R • (⊤ : Submodule R B) →
      a ∈ maximalIdeal R • (⊤ : Submodule R M)) :
    Function.Injective u := by
  set I := maximalIdeal R
  set K := LinearMap.ker u
  let g : K.restrictScalars R →ₗ[R] M := (K.restrictScalars R).subtype
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat (u.restrictScalars R) hu g
    (Submodule.injective_subtype _) (fun a => ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨k, hk⟩ => hk ▸ k.2⟩)
    (R ⧸ I)
  have hle : ∀ k : K.restrictScalars R, k ∈ I • (⊤ : Submodule R (K.restrictScalars R)) := by
    intro k
    have hk : (k : M) ∈ I • (⊤ : Submodule R M) := hbar _ (by
      rw [show u (k : M) = 0 from k.2]
      exact Submodule.zero_mem _)
    have h2 : g.lTensor (R ⧸ I) (Ideal.Quotient.mk I 1 ⊗ₜ[R] k) = 0 := by
      rw [LinearMap.lTensor_tmul]
      exact (one_tmul_eq_zero_iff_mem_smul_top I _).2 hk
    exact (one_tmul_eq_zero_iff_mem_smul_top I _).1 (hinj (by rw [h2, map_zero]))
  have hmap : I.map (algebraMap R A) ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact (mem_maximalIdeal _).2 fun h =>
      (mem_maximalIdeal _).1 hr (isUnit_of_map_unit (algebraMap R A) r h)
  have hKle : K ≤ maximalIdeal A • K := by
    intro a ha
    have h1 : a ∈ (I • (⊤ : Submodule R (K.restrictScalars R))).map g :=
      ⟨⟨a, ha⟩, hle ⟨a, ha⟩, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
      ← Ideal.smul_restrictScalars] at h1
    exact Submodule.smul_mono_left hmap h1
  exact LinearMap.ker_eq_bot.mp <|
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) K hK hKle
      (IsLocalRing.maximalIdeal_le_jacobson _)

/-- Let `A → C` be a surjection whose kernel is `I A` for an ideal `I` of `R`. If `u : M → B` is
`A`-linear and `C ⊗[A] u` is injective, then every `a : M` with `u a ∈ I B` lies in `I M`. -/
theorem mem_smul_top_of_injective_baseChange
    {R A C M B : Type*} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra A C] (hsurj : Function.Surjective (algebraMap A C)) (I : Ideal R)
    (hker : RingHom.ker (algebraMap A C) = I.map (algebraMap R A))
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup B] [Module A B] [Module R B] [IsScalarTower R A B]
    (u : M →ₗ[A] B) (hinj : Function.Injective (u.baseChange C))
    (a : M) (ha : u a ∈ I • (⊤ : Submodule R B)) :
    a ∈ I • (⊤ : Submodule R M) := by
  have h1 : ((1 : C) ⊗ₜ[A] u a) = 0 := by
    refine Submodule.smul_induction_on ha (fun r hr b _ => ?_) (fun x y hx hy => ?_)
    · rw [← algebraMap_smul A r b, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      have : algebraMap A C (algebraMap R A r) = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact Ideal.mem_map_of_mem _ hr
      rw [this, TensorProduct.zero_tmul]
    · rw [TensorProduct.tmul_add, hx, hy, add_zero]
  have h2 : ((1 : C) ⊗ₜ[A] a) = 0 := hinj (by rw [LinearMap.baseChange_tmul, h1, map_zero])
  set J := RingHom.ker (algebraMap A C)
  let e : (A ⧸ J) ≃ₗ[A] C :=
    (Ideal.quotientKerAlgEquivOfSurjective (R₁ := A) (f := Algebra.ofId A C) hsurj).toLinearEquiv
  have h3 := congrArg (TensorProduct.congr e.symm (LinearEquiv.refl A M)) h2
  simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, map_zero] at h3
  have he : e.symm 1 = Ideal.Quotient.mk J 1 := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (map_one (algebraMap A C)).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective_mk (f := Algebra.ofId A C) hsurj 1).symm
  rw [he, one_tmul_eq_zero_iff_mem_smul_top, hker] at h3
  have h4 := (Submodule.restrictScalars_mem R _ a).mpr h3
  rwa [Ideal.smul_restrictScalars] at h4

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

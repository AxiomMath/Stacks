module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit
public import StacksFrontier.Homology.Tor.Presentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor is strictly pro-zero

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a finite `A`-module. For every `p > 0`
there is `c > 0` such that for all `n ≥ c` the map `Tor_p^A(M, A/I^n) → Tor_p^A(M, A/I^{n-c})`
induced by the canonical surjection `A/I^n ↠ A/I^{n-c}` is zero.

`A`-modules are objects of `ModuleCat A`, and `((Tor (ModuleCat A) p).obj M).obj N` is
`Tor_p^A(M, N)`, the `p`-th left derived functor of `M ⊗_A -` applied to `N`.

## Main definitions

* `torProZeroQuot I n`: the quotient module `A / I^n` as an object of `ModuleCat A`.
* `torProZeroTransition I h`: the canonical surjection `A / I^n → A / I^m` for `h : m ≤ n`.

## Main results

* `tor_one_map_eq_zero_of_inf_le_smul`: for a finite free presentation `0 → K → Aᵗ → M → 0`,
  the map on `Tor₁(M, -)` induced by `A/I^n ↠ A/I^m` vanishes when `K ⊓ I^n Aᵗ ≤ I^m K`.
* `tor_pro_zero_one`: the statement for `p = 1`.
* `tor_pro_zero_succ`: the statement in degree `q + 1` for every finite module implies it in
  degree `q + 2`.
* `tor_pro_zero`: the statement for every `p > 0`.

## References

* [Stacks Project, Tag 0911](https://stacks.math.columbia.edu/tag/0911)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The quotient `A`-module `A / I^n`, viewed as an object of `ModuleCat A`.
With the convention `I^0 = A`, this is the zero module for `n = 0`. -/
@[ega "III 7.5.1"]
noncomputable def torProZeroQuot (n : ℕ) : ModuleCat A :=
  ModuleCat.of A (A ⧸ I ^ n)

/-- The canonical surjection `π_{n,m} : A / I^n → A / I^m`, `a + I^n ↦ a + I^m`, for `m ≤ n`,
as a morphism in `ModuleCat A`. -/
noncomputable def torProZeroTransition {m n : ℕ} (h : m ≤ n) :
    torProZeroQuot I n ⟶ torProZeroQuot I m :=
  ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right h))

/-- The transition map `π_{n,n} : A / I^n → A / I^n` is the identity. -/
@[simp]
theorem torProZeroTransition_refl (n : ℕ) :
    torProZeroTransition I (le_refl n) = 𝟙 (torProZeroQuot I n) :=
  ModuleCat.hom_ext (LinearMap.ext fun x => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl)

/-- The transition maps compose: `π_{m,k} ∘ π_{n,m} = π_{n,k}` for `k ≤ m ≤ n`. -/
@[simp]
theorem torProZeroTransition_comp {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    torProZeroTransition I hmn ≫ torProZeroTransition I hkm
      = torProZeroTransition I (hkm.trans hmn) :=
  ModuleCat.hom_ext
    (Submodule.factor_comp (Ideal.pow_le_pow_right hmn) (Ideal.pow_le_pow_right hkm))

/-- The transition map `π_{n,m} : A / I^n → A / I^m` is an epimorphism. -/
instance epi_torProZeroTransition {m n : ℕ} (h : m ≤ n) : Epi (torProZeroTransition I h) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.factor_surjective (Ideal.pow_le_pow_right h))

/-- If `K ∩ I^n·P ≤ I^m·K`, the transition `A/I^n → A/I^m` kills the
kernel of `K ⊗ A/I^n → P ⊗ A/I^n`. -/
theorem lTensor_factor_eq_zero_of_rTensor_subtype_eq_zero
    {P : Type*} [AddCommGroup P] [Module A P] (K : Submodule A P) {m n : ℕ} (h : m ≤ n)
    (hAR : K ⊓ (I ^ n • ⊤ : Submodule A P) ≤ (I ^ m • K : Submodule A P))
    {w : K ⊗[A] (A ⧸ I ^ n)}
    (hw : LinearMap.rTensor (A ⧸ I ^ n) K.subtype w = 0) :
    LinearMap.lTensor (↥K) (Submodule.factor (Ideal.pow_le_pow_right h)) w = 0 := by
  obtain ⟨x, rfl⟩ : ∃ x : K, w = x ⊗ₜ[A] (1 : A ⧸ I ^ n) := by
    obtain ⟨q, rfl⟩ := (TensorProduct.tensorQuotEquivQuotSMul (↥K) (I ^ n)).symm.surjective w
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨x, by rw [TensorProduct.tensorQuotEquivQuotSMul_symm_mk]⟩
  rw [LinearMap.rTensor_tmul] at hw
  have hxn : (x : P) ∈ (I ^ n • ⊤ : Submodule A P) := by
    have hco := congrArg (TensorProduct.tensorQuotEquivQuotSMul P (I ^ n)) hw
    rw [map_zero] at hco
    have h1 : (1 : A ⧸ I ^ n) = (Ideal.Quotient.mk (I ^ n)) 1 := rfl
    rw [K.subtype_apply, h1, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul] at hco
    rwa [Submodule.Quotient.mk_eq_zero] at hco
  have hxm : (x : P) ∈ (I ^ m • K : Submodule A P) := hAR ⟨x.2, hxn⟩
  have hxmK : x ∈ (I ^ m • ⊤ : Submodule A (↥K)) := by
    have hmap : (I ^ m • ⊤ : Submodule A (↥K)).map K.subtype = (I ^ m • K : Submodule A P) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    rw [← hmap] at hxm
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hxm
    rwa [K.injective_subtype hyx] at hy
  rw [← LinearEquiv.map_eq_zero_iff (TensorProduct.tensorQuotEquivQuotSMul (↥K) (I ^ m)),
    LinearMap.lTensor_tmul]
  have hf1 : (Submodule.factor (Ideal.pow_le_pow_right h)) (1 : A ⧸ I ^ n)
      = (Ideal.Quotient.mk (I ^ m)) 1 := rfl
  rwa [hf1, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
    Submodule.Quotient.mk_eq_zero]

/-- For `K = LinearMap.ker φ` with `K ⊓ I^n • Aᵗ ≤ I^m • K`, the map induced on the kernel of
`K ⊗ - → Aᵗ ⊗ -` by the transition `A/I^n ↠ A/I^m` (for `m ≤ n`) is zero. -/
theorem torBaseNT_kernel_map_eq_zero (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    {m n : ℕ} (h : m ≤ n)
    (hAR : LinearMap.ker φ ⊓ (I ^ n • ⊤ : Submodule A (Fin t → A))
      ≤ (I ^ m • LinearMap.ker φ : Submodule A (Fin t → A))) :
    (kernel (torBaseNT M φ)).map (torProZeroTransition I h) = 0 := by
  have hcomp (N : ModuleCat A) : (torKerPointwise M φ N).hom ≫ kernel.ι ((torBaseNT M φ).app N)
      = (kernel.ι (torBaseNT M φ)).app N := by
    rw [torKerPointwise, PreservesKernel.iso_hom]
    exact kernelComparison_comp_ι (torBaseNT M φ) ((evaluation (ModuleCat A) (ModuleCat A)).obj N)
  have hmono : Mono ((kernel.ι (torBaseNT M φ)).app (torProZeroQuot I m)) := by
    rw [← hcomp]
    infer_instance
  rw [← cancel_mono ((kernel.ι (torBaseNT M φ)).app (torProZeroQuot I m)), Limits.zero_comp,
    (kernel.ι (torBaseNT M φ)).naturality (torProZeroTransition I h), ← hcomp, Category.assoc]
  suffices hkey : kernel.ι ((torBaseNT M φ).app (torProZeroQuot I n))
      ≫ ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
          (ModuleCat.of A (LinearMap.ker φ))).map (torProZeroTransition I h) = 0 by
    rw [hkey, Limits.comp_zero]
  set u : ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
        (ModuleCat.of A (LinearMap.ker φ))).obj (torProZeroQuot I n) ⟶
      ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
        (ModuleCat.of A (Fin t → A))).obj (torProZeroQuot I n) :=
    (torBaseNT M φ).app (torProZeroQuot I n)
  rw [← cancel_epi (ModuleCat.kernelIsoKer u).inv, Limits.comp_zero, ← Category.assoc,
    ModuleCat.kernelIsoKer_inv_kernel_ι]
  exact ModuleCat.hom_ext (LinearMap.ext fun ⟨w, hw⟩ =>
    lTensor_factor_eq_zero_of_rTensor_subtype_eq_zero I (LinearMap.ker φ) h hAR hw)

/-- Given a finite free presentation `0 → K → Aᵗ → M → 0` (here `Aᵗ = Fin t → A`,
`φ : Aᵗ ↠ M` surjective and `K := LinearMap.ker φ`), the map on `Tor₁(M, -)` induced
by the transition `A/I^n ↠ A/I^m` (for `m ≤ n`) is zero as soon as the Artin–Rees
inclusion `K ⊓ I^n • Aᵗ ≤ I^m • K` holds (all as submodules of `Aᵗ`). -/
theorem tor_one_map_eq_zero_of_inf_le_smul (M : ModuleCat A) {t : ℕ}
    (φ : (Fin t → A) →ₗ[A] M) (hφ : Function.Surjective φ) {m n : ℕ} (h : m ≤ n)
    (hAR : LinearMap.ker φ ⊓ (I ^ n • ⊤ : Submodule A (Fin t → A))
      ≤ (I ^ m • LinearMap.ker φ : Submodule A (Fin t → A))) :
    ((Tor (ModuleCat A) 1).obj M).map (torProZeroTransition I h) = 0 := by
  set α := torOneTensorKernelNatIso M φ hφ
  exact zero_of_comp_mono (α.hom.app (torProZeroQuot I m)) (by
    rw [α.hom.naturality, torBaseNT_kernel_map_eq_zero I M φ h hAR, Limits.comp_zero])

/-- For a Noetherian ring `A`, an ideal `I ⊆ A` and a finite `A`-module `M`, there exists
`c > 0` such that, for all `n ≥ c`, the map `Tor_1^A(M, A/I^n) → Tor_1^A(M, A/I^{n-c})`
induced by the canonical surjection `A/I^n ↠ A/I^{n-c}` is zero. -/
theorem tor_pro_zero_one [IsNoetherianRing A] (M : ModuleCat A) [Module.Finite A M] :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor (ModuleCat A) 1).obj M).map (torProZeroTransition I (Nat.sub_le n c)) = 0 := by
  obtain ⟨t, φ, hφ⟩ := Module.Finite.exists_fin' A M
  obtain ⟨c₀, hc₀⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.ker φ)
  refine ⟨max c₀ 1, by positivity, fun n hn => ?_⟩
  set c := max c₀ 1
  have hARincl : LinearMap.ker φ ⊓ (I ^ n • ⊤ : Submodule A (Fin t → A))
      ≤ (I ^ (n - c) • LinearMap.ker φ : Submodule A (Fin t → A)) := by
    rw [inf_comm, hc₀ n ((le_max_left _ _).trans hn)]
    calc I ^ (n - c₀) • (I ^ c₀ • ⊤ ⊓ LinearMap.ker φ)
        ≤ I ^ (n - c₀) • LinearMap.ker φ := Submodule.smul_mono le_rfl inf_le_right
      _ ≤ I ^ (n - c) • LinearMap.ker φ :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  exact tor_one_map_eq_zero_of_inf_le_smul I M φ hφ (Nat.sub_le n c) hARincl

/-- If for every finite `A`-module the maps `Tor_{q+1}(-, A/I^n) → Tor_{q+1}(-, A/I^{n-c})`
vanish for some `c > 0` and all `n ≥ c`, then the same holds in degree `q + 2` for `M`. -/
theorem tor_pro_zero_succ [IsNoetherianRing A] (q : ℕ)
    (ih : ∀ (M : ModuleCat A) [Module.Finite A M], ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor (ModuleCat A) (q + 1)).obj M).map (torProZeroTransition I (Nat.sub_le n c)) = 0)
    (M : ModuleCat A) [Module.Finite A M] :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor (ModuleCat A) (q + 2)).obj M).map (torProZeroTransition I (Nat.sub_le n c)) = 0 := by
  obtain ⟨t, φ, hφ⟩ := Module.Finite.exists_fin' A M
  set K : ModuleCat A := ModuleCat.of A (LinearMap.ker φ)
  have hKfin : Module.Finite A K :=
    inferInstanceAs (Module.Finite A (LinearMap.ker φ))
  obtain ⟨c, hcpos, hcK⟩ := ih K
  refine ⟨c, hcpos, fun n hn => ?_⟩
  exact zero_of_comp_mono (torShiftIsoApp q M φ hφ (torProZeroQuot I (n - c))).hom (by
    rw [torShiftIsoApp_naturality, hcK n hn, Limits.comp_zero])

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal, and `M` a finite `A`-module. Then for every
`p > 0` there exists `c > 0` such that, for all `n ≥ c`, the map
`Tor_p^A(M, A/I^n) → Tor_p^A(M, A/I^{n-c})` induced by the canonical surjection
`A/I^n ↠ A/I^{n-c}` is the zero map. -/
@[stacks 0911]
theorem tor_pro_zero
    [IsNoetherianRing A]
    (M : ModuleCat A) [Module.Finite A M]
    {p : ℕ} (hp : 0 < p) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor (ModuleCat A) p).obj M).map
        (torProZeroTransition I (Nat.sub_le n c)) = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  clear hp
  induction q generalizing M with
  | zero => exact tor_pro_zero_one I M
  | succ q ih => exact tor_pro_zero_succ I q ih M

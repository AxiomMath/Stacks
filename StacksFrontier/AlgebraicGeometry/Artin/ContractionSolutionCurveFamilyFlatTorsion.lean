module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness from a compatible system of maps into an adically complete ring

Let `Γ` be a Dedekind domain, let `R` be a Noetherian local `Γ`-algebra and let `A` be a
`Γ`-algebra which is complete for an ideal `I` and on which no nonzero element of `Γ` is a zero
divisor. Suppose given `Γ`-algebra maps `ρₙ : R → A ⧸ Iⁿ⁺¹`, compatible in `n`, whose kernels lie
in the powers `𝔪ⁿ⁺¹` of the maximal ideal of `R`. Then `R` is torsion free, hence flat, over `Γ`,
and so flat over every localization of `Γ` it is an algebra over.

This is the algebraic core of the flatness of the contraction in Stacks 0D5E: there `R` is a
local ring of an étale chart at a point of the contracted locus, and the `ρₙ` come from the
identification of the completion with the completion of `Spec A` at its closed point.

## Main results

* `AlgebraicGeometry.Artin.eq_zero_of_smul_eq_zero_of_algHom_quotient_pow`: the torsion
  freeness.
* `AlgebraicGeometry.Artin.flat_of_algHom_quotient_pow`: the flatness over a localization of
  `Γ`.
-/

@[expose] public section

open IsLocalRing

namespace AlgebraicGeometry.Artin

variable {Γ R A : Type*} [CommRing Γ] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Algebra Γ R] [CommRing A] [Algebra Γ A] {I : Ideal A}

/-- A submodule power of an ideal, acting on the ring itself, is that power of the ideal. -/
private theorem pow_smul_top_eq (I : Ideal A) (n : ℕ) :
    (I ^ n • ⊤ : Submodule A A) = I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- Let `A` be `I`-adically complete with no nonzero element of `Γ` a zero divisor on it, and let
`ρₙ : R → A ⧸ Iⁿ⁺¹` be compatible `Γ`-algebra maps from a Noetherian local `Γ`-algebra `R` whose
kernels lie in the powers `𝔪ⁿ⁺¹` of the maximal ideal of `R`. Then no nonzero element of `Γ` kills
a nonzero element of `R`: the images of a killed element form a Cauchy sequence whose limit is
killed in `A`, hence zero, so the element lies in every power of the maximal ideal. -/
theorem eq_zero_of_smul_eq_zero_of_algHom_quotient_pow [IsAdicComplete I A]
    (hAt : ∀ r : Γ, r ≠ 0 → IsSMulRegular A r) (ρ : ∀ n : ℕ, R →ₐ[Γ] A ⧸ I ^ (n + 1))
    (hρ : ∀ m n (h : m ≤ n) (y : R),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) (ρ n y) = ρ m y)
    (hker : ∀ n (y : R), ρ n y = 0 → y ∈ maximalIdeal R ^ (n + 1))
    {r : Γ} (hr : r ≠ 0) {y : R} (hy : r • y = 0) : y = 0 := by
  choose f hf using fun n => Ideal.Quotient.mk_surjective (ρ n y)
  have hsucc : ∀ {m n : ℕ}, m ≤ n → f m - f n ∈ I ^ (m + 1) := by
    intro m n hmn
    rw [← Ideal.Quotient.eq, hf m, ← hρ m n hmn, ← hf n, Ideal.Quotient.factor_mk]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    rw [SModEq.sub_mem, pow_smul_top_eq]
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (hsucc hmn)
  obtain ⟨b, hb⟩ := IsPrecomplete.prec (I := I) inferInstance hcauchy
  have hrb : r • b = 0 := by
    refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
    have h1 : r • f n ≡ r • b [SMOD (I ^ n • ⊤ : Submodule A A)] := by
      simpa only [algebraMap_smul] using (hb n).smul (algebraMap Γ A r)
    have h2 : r • f n ≡ 0 [SMOD (I ^ n • ⊤ : Submodule A A)] := by
      rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
      refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def, map_mul, hf n,
        Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def, ← map_smul, hy, map_zero]
    exact h1.symm.trans h2
  have hb0 : b = 0 := hAt r hr (show r • b = r • 0 by rw [hrb, smul_zero])
  have hy' : y ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by
    refine Submodule.mem_iInf _ |>.2 fun n => ?_
    refine Ideal.pow_le_pow_right (Nat.le_succ n) (hker n y ?_)
    have h := hb (n + 1)
    rw [hb0, SModEq.sub_mem, sub_zero, pow_smul_top_eq] at h
    have h' : f n ∈ I ^ (n + 1) := by
      simpa using Ideal.add_mem _ (hsucc (Nat.le_succ n)) h
    rw [← hf n, Ideal.Quotient.eq_zero_iff_mem]
    exact h'
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hy'

/-- **Flatness from a compatible system of maps into an adically complete ring.** Let `Γ` be a
Dedekind domain, `L` a localization of `Γ`, and `R` a Noetherian local `L`-algebra. If `A` is
`I`-adically complete with no nonzero element of `Γ` a zero divisor on it, and
`ρₙ : R → A ⧸ Iⁿ⁺¹` are compatible `Γ`-algebra maps whose kernels lie in the powers `𝔪ⁿ⁺¹` of
the maximal ideal of `R`, then `R` is flat over `L`: it is torsion free, hence flat, over the
Dedekind domain `Γ`, and flatness over `Γ` and over its localization `L` agree. -/
theorem flat_of_algHom_quotient_pow [IsDomain Γ] [IsDedekindDomain Γ] {L : Type*} [CommRing L]
    [Algebra Γ L] (M : Submonoid Γ) [IsLocalization M L] [Algebra L R] [IsScalarTower Γ L R]
    [IsAdicComplete I A] (hAt : ∀ r : Γ, r ≠ 0 → IsSMulRegular A r)
    (ρ : ∀ n : ℕ, R →ₐ[Γ] A ⧸ I ^ (n + 1))
    (hρ : ∀ m n (h : m ≤ n) (y : R),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) (ρ n y) = ρ m y)
    (hker : ∀ n (y : R), ρ n y = 0 → y ∈ maximalIdeal R ^ (n + 1)) :
    Module.Flat L R := by
  rw [Module.flat_iff_of_isLocalization L M, IsDedekindDomain.flat_iff_torsion_eq_bot,
    Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨⟨r, hr⟩, hry⟩ := (Submodule.mem_torsion_iff y).1 hy
  exact eq_zero_of_smul_eq_zero_of_algHom_quotient_pow hAt ρ hρ hker
    (nonZeroDivisors.ne_zero hr) hry

end AlgebraicGeometry.Artin

end

module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerAlgebra
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient

/-!
# The standard tamely ramified algebra is integrally closed in its localization

Let `A` be a Noetherian ring, `φ ∈ A` a nonzerodivisor with `A / φA` regular and `e ≥ 1`. The
standard tamely ramified algebra `C = A[x]/(x^e - φ)` of [Stacks, Tag 0EYF] is integrally closed
in `C_φ = C[1/x]`. This is the step "the integral closure of `A` in `A_f[x]/(x^e - f)` is
`A[x]/(x^e - f)`" of the proof of [Stacks, Tag 0EYH], where the source argues that the
localizations of `C` at primes containing `x` are regular.

## Main results

* `AlgebraicGeometry.TameCovers.root_mem_nonZeroDivisors_of_mem_nonZeroDivisors`: the root `x` is
  a nonzerodivisor of `C` as soon as `φ` is a nonzerodivisor of `A`.
* `AlgebraicGeometry.TameCovers.isRegularLocalRing_localization_of_root_mem`: the localization of
  `C` at a prime containing `x` is a regular local ring ([Stacks, Tag 00NU]).
* `AlgebraicGeometry.TameCovers.isIntegrallyClosedIn_localizationAway`: `C` is integrally
  closed in `C_φ`.

## References

* [Stacks Project, Tag 0EYH](https://stacks.math.columbia.edu/tag/0EYH)
* [Stacks Project, Tag 0EYF](https://stacks.math.columbia.edu/tag/0EYF)
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u

namespace AlgebraicGeometry.TameCovers

variable {A : Type u} [CommRing A] {φ : A} {e : ℕ}

/-- The standard tamely ramified algebra is a free module over the base. -/
instance standardTamelyRamifiedAlgebra_free [NeZero e] :
    Module.Free A (standardTamelyRamifiedAlgebra A φ e) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_X_pow_sub_C φ (NeZero.ne e))).basis

/-- **The root is a nonzerodivisor** of `A[x]/(x^e - φ)` when `φ` is a nonzerodivisor of `A`:
`x c = 0` gives `φ c = x^(e-1) (x c) = 0`, and `φ` acts injectively on the free module `C`. -/
theorem root_mem_nonZeroDivisors_of_mem_nonZeroDivisors [NeZero e] (hφ : φ ∈ nonZeroDivisors A) :
    Abhyankar.root A φ e ∈ nonZeroDivisors (standardTamelyRamifiedAlgebra A φ e) := by
  have hreg : IsSMulRegular (standardTamelyRamifiedAlgebra A φ e) φ :=
    Module.Flat.isSMulRegular_of_isRegular (isRegular_iff_mem_nonZeroDivisors.mpr hφ)
  rw [mem_nonZeroDivisors_iff_right]
  intro c hc
  apply hreg
  change φ • c = φ • (0 : standardTamelyRamifiedAlgebra A φ e)
  rw [smul_zero, Algebra.smul_def, ← Abhyankar.root_pow A φ e,
    ← pow_sub_one_mul (NeZero.ne e) (Abhyankar.root A φ e), mul_assoc, mul_comm _ c, hc, mul_zero]

variable (A φ e) in
/-- The image of `φ` in `A[x]/(x^e - φ)` is the `e`-th power of the root. -/
lemma algebraMap_eq_root_pow :
    algebraMap A (standardTamelyRamifiedAlgebra A φ e) φ = Abhyankar.root A φ e ^ e :=
  (Abhyankar.root_pow A φ e).symm

/-- **The localizations at primes containing the root are regular** ([Stacks, Tag 00NU]): the
root is a nonzerodivisor there, with quotient a localization of `A / φA`. -/
theorem isRegularLocalRing_localization_of_root_mem [IsNoetherianRing A] [NeZero e]
    (hφ : φ ∈ nonZeroDivisors A) [IsRegularRing (A ⧸ Ideal.span {φ})]
    (P : Ideal (standardTamelyRamifiedAlgebra A φ e)) [P.IsPrime]
    (hP : Abhyankar.root A φ e ∈ P) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  set C := standardTamelyRamifiedAlgebra A φ e
  set x := Abhyankar.root A φ e
  let J : Ideal C := Ideal.span {x}
  have hJP : J ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hP)
  have : IsRegularRing (C ⧸ J) := IsRegularRing.of_ringEquiv (Abhyankar.quotRootEquiv A φ e).symm
  let Q : Ideal (C ⧸ J) := P.map (Ideal.Quotient.mk J)
  have hQc : Q.comap (Ideal.Quotient.mk J) = P := Ideal.comap_map_mk hJP
  have : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  have := isLocalization_atPrime_quotient P (Localization.AtPrime P) J Q hQc
  let σ : Localization.AtPrime Q ≃+* (Localization.AtPrime P ⧸ J.map
      (algebraMap C (Localization.AtPrime P))) :=
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) _).toRingEquiv
  have hx : algebraMap C (Localization.AtPrime P) x ∈ nonZeroDivisors (Localization.AtPrime P) :=
    IsLocalization.nonZeroDivisors_le_comap P.primeCompl (Localization.AtPrime P)
      (root_mem_nonZeroDivisors_of_mem_nonZeroDivisors hφ)
  have hspan : J.map (algebraMap C (Localization.AtPrime P)) =
      Ideal.span {algebraMap C (Localization.AtPrime P) x} := by
    rw [Ideal.map_span, Set.image_singleton]
  exact isRegularLocalRing_of_nonZeroDivisor _ _ hx (hspan ▸ IsRegularLocalRing.of_ringEquiv σ)

/-- **Key step.** If `c / x` is integral over `C` in `C_φ`, then `c ∈ x C`. The membership is
checked at every maximal ideal `P`: if `x ∉ P` it is clear; if `x ∈ P` the localization `C_P` is
regular, hence an integrally closed domain, and `c / x` lies in it. -/
theorem mem_span_root_of_isIntegral [IsNoetherianRing A] [NeZero e]
    (hφ : φ ∈ nonZeroDivisors A) [IsRegularRing (A ⧸ Ideal.span {φ})]
    (c : standardTamelyRamifiedAlgebra A φ e)
    (v : Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ e) φ))
    (hv : algebraMap _ _ (Abhyankar.root A φ e) * v = 1)
    (hc : _root_.IsIntegral (standardTamelyRamifiedAlgebra A φ e)
      (algebraMap _ (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ e) φ)) c *
        v)) :
    c ∈ Ideal.span {Abhyankar.root A φ e} := by
  let C := standardTamelyRamifiedAlgebra A φ e
  let x := Abhyankar.root A φ e
  let L := Localization.Away (algebraMap A C φ)
  refine Ideal.mem_of_localization_maximal fun P hPmax => ?_
  by_cases hxP : x ∈ P
  · have hreg := isRegularLocalRing_localization_of_root_mem hφ P hxP
    have := IsRegularLocalRing.isDomain (Localization.AtPrime P)
    have := isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime P)
    let Cp := Localization.AtPrime P
    let K := FractionRing Cp
    let ψ : C →+* K := algebraMap C K
    have hψ : ∀ y : C, ψ y = algebraMap Cp K (algebraMap C Cp y) :=
      IsScalarTower.algebraMap_apply C Cp K
    have hxnz : algebraMap C Cp x ∈ nonZeroDivisors Cp :=
      IsLocalization.nonZeroDivisors_le_comap P.primeCompl Cp
        (root_mem_nonZeroDivisors_of_mem_nonZeroDivisors hφ)
    have hxK : IsUnit (ψ x) :=
      IsUnit.mk0 _ (by rw [hψ]; exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hxnz)
    have hφK : IsUnit (ψ (algebraMap A C φ)) := by
      rw [algebraMap_eq_root_pow, map_pow]
      exact hxK.pow e
    let τ₀ : L →+* K := IsLocalization.Away.lift (algebraMap A C φ) hφK
    have hτ₀ : ∀ y : C, τ₀ (algebraMap C L y) = ψ y :=
      IsLocalization.Away.lift_eq (algebraMap A C φ) hφK
    let τ : L →ₐ[C] K := { τ₀ with commutes' := hτ₀ }
    have hτc : _root_.IsIntegral Cp (τ (algebraMap C L c * v)) := (hc.map τ).tower_top
    obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hτc
    have hτv : τ v * ψ x = 1 := by
      rw [mul_comm, ← hτ₀, ← AlgHom.coe_toRingHom]
      change τ₀ (algebraMap C L x) * τ₀ v = 1
      rw [← map_mul, hv, map_one]
    have hcd : algebraMap C Cp c = algebraMap C Cp x * d := by
      apply IsFractionRing.injective Cp K
      rw [map_mul, hd, ← hψ, ← hψ, map_mul]
      change ψ c = ψ x * (τ₀ (algebraMap C L c) * τ v)
      rw [hτ₀, mul_comm (ψ c), ← mul_assoc, mul_comm (ψ x), hτv, one_mul]
    rw [Ideal.map_span, Set.image_singleton, hcd]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · have hu : IsUnit (algebraMap C (Localization.AtPrime P) x) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P x).mpr hxP
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top.mpr hu]
    exact Submodule.mem_top

/-- **`A[x]/(x^e - φ)` is integrally closed in its localization away from `φ`**, for `A`
Noetherian, `φ` a nonzerodivisor of `A` and `A / φA` regular. -/
theorem isIntegrallyClosedIn_localizationAway [IsNoetherianRing A] [NeZero e]
    (hφ : φ ∈ nonZeroDivisors A) [IsRegularRing (A ⧸ Ideal.span {φ})] :
    IsIntegrallyClosedIn (standardTamelyRamifiedAlgebra A φ e)
      (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ e) φ)) := by
  set C := standardTamelyRamifiedAlgebra A φ e
  set x := Abhyankar.root A φ e
  set L := Localization.Away (algebraMap A C φ)
  have hxnz := root_mem_nonZeroDivisors_of_mem_nonZeroDivisors (e := e) hφ
  have hφC : algebraMap A C φ ∈ nonZeroDivisors C := by
    rw [algebraMap_eq_root_pow]
    exact pow_mem hxnz e
  have hφL : IsUnit (algebraMap C L (algebraMap A C φ)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hφx : algebraMap C L (algebraMap A C φ) = algebraMap C L x ^ e := by
    rw [← map_pow, ← algebraMap_eq_root_pow]
  have hxL : IsUnit (algebraMap C L x) := (isUnit_pow_iff (NeZero.ne e)).mp (by rwa [hφx] at hφL)
  set v : L := ↑hxL.unit⁻¹
  have hv : algebraMap C L x * v = 1 := hxL.mul_val_inv
  have key : ∀ m : ℕ, ∀ c : C, _root_.IsIntegral C (algebraMap C L c * v ^ m) →
      ∃ y, algebraMap C L y = algebraMap C L c * v ^ m := by
    intro m
    induction m with
    | zero => exact fun c _ => ⟨c, by simp⟩
    | succ m ih =>
      intro c hc
      have hpow : (algebraMap C L x * v) ^ m = 1 := by rw [hv, one_pow]
      have hcv : _root_.IsIntegral C (algebraMap C L c * v) := by
        have := hc.mul (isIntegral_algebraMap (R := C) (A := L) (x := x ^ m))
        have heq : algebraMap C L c * v ^ (m + 1) * algebraMap C L (x ^ m) =
            algebraMap C L c * v := by
          rw [map_pow]
          linear_combination (algebraMap C L c * v) * hpow
        rwa [heq] at this
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp (mem_span_root_of_isIntegral hφ c v hv hcv)
      have hdv : algebraMap C L (d * x) * v ^ (m + 1) = algebraMap C L d * v ^ m := by
        rw [map_mul]
        linear_combination (algebraMap C L d * v ^ m) * hv
      obtain ⟨y, hy⟩ := ih d (by rwa [← hdv])
      exact ⟨y, hy.trans hdv.symm⟩
  refine isIntegrallyClosedIn_iff.mpr ⟨IsLocalization.injective L
    ((Submonoid.powers_le).mpr hφC), fun {b} hb => ?_⟩
  obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (algebraMap A C φ)) b
  have hb' : IsLocalization.mk' L c (⟨algebraMap A C φ ^ k, k, rfl⟩ :
      Submonoid.powers (algebraMap A C φ)) = algebraMap C L c * v ^ (e * k) := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, map_pow, hφx, ← pow_mul,
      mul_assoc, ← mul_pow, mul_comm v, hv, one_pow, mul_one]
  change _root_.IsIntegral C (IsLocalization.mk' L c (⟨algebraMap A C φ ^ k, k, rfl⟩ :
      Submonoid.powers (algebraMap A C φ))) at hb
  change ∃ y, algebraMap C L y = IsLocalization.mk' L c (⟨algebraMap A C φ ^ k, k, rfl⟩ :
      Submonoid.powers (algebraMap A C φ))
  rw [hb'] at hb ⊢
  exact key _ c hb

end AlgebraicGeometry.TameCovers

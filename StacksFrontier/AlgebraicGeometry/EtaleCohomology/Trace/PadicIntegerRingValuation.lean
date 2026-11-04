module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRing
public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure
public import StacksFrontier.RingTheory.Henselian.Criteria

/-!
# The ring of integers of a finite extension of `ℚ_ℓ` is a discrete valuation ring

Let `E'` be a finite extension of `ℚ_ℓ` and `O' = integralClosure ℤ_ℓ E'` the integral closure of
`ℤ_ℓ` in `E'` (for the `ℤ_ℓ`-algebra structure `Stacks.EtaleCohomology.padicIntAlgebraOfRat`). The
spectral norm `‖·‖` of `E'/ℚ_ℓ` is a multiplicative nonarchimedean norm extending the `ℓ`-adic
norm, and an element of `E'` is integral over `ℤ_ℓ` exactly when its spectral norm is at most one
(`Stacks.EtaleCohomology.mem_padicIntegerRing_iff_spectralNorm_le_one`): the spectral norm of `x`
is computed from the coefficients of the minimal polynomial of `x` over `ℚ_ℓ`, which has
coefficients in `ℤ_ℓ` exactly when `x` is integral, `ℤ_ℓ` being integrally closed. Hence for
`a, b ∈ O'` with `‖b‖ ≤ ‖a‖` and `a ≠ 0` the quotient `b / a` lies in `O'`
(`Stacks.EtaleCohomology.dvd_of_spectralNorm_le_padicIntegerRing`), and every nonzero `d ∈ O'`
divides a power of `ℓ`, as `‖ℓ‖ = ℓ⁻¹ < 1`; integers prime to `ℓ` have norm one and are units. The
ring `O'` is a discrete valuation ring (`ℤ_ℓ` is complete, hence henselian:
`Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure`), hence also a
Noetherian valuation ring. Its quotients `O' / ℓⁿ` are finite, `O'` being a finite `ℤ_ℓ`-module
(`Stacks.EtaleCohomology.finite_padicIntegerRing`).

These are the coefficient rings of the finite levels `O' / ℓᴺ⁺¹` used in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), where absolute irreducibility is tested over
the finite extensions `E'` of the field of coefficients.

## Main results

* `Stacks.EtaleCohomology.mem_padicIntegerRing_iff_spectralNorm_le_one`: `O'` is the closed unit
  ball of the spectral norm.
* `Stacks.EtaleCohomology.spectralNorm_natCast_self`: the spectral norm of `ℓ` is `ℓ⁻¹`.
* `Stacks.EtaleCohomology.dvd_of_spectralNorm_le_padicIntegerRing`: for `a ≠ 0` in `O'`,
  `‖b‖ ≤ ‖a‖` implies `a ∣ b`.
* `Stacks.EtaleCohomology.exists_dvd_natCast_pow_padicIntegerRing`: every nonzero element of `O'`
  divides a power of `ℓ`.
* `Stacks.EtaleCohomology.not_isUnit_natCast_padicIntegerRing`,
  `Stacks.EtaleCohomology.natCast_ne_zero_padicIntegerRing`: `ℓ` is a nonzero nonunit of `O'`.
* `Stacks.EtaleCohomology.isUnit_natCast_padicIntegerRing_of_coprime`: an integer prime to `ℓ` is
  a unit of `O'`.
* `Stacks.EtaleCohomology.natCast_mem_span_pow_padicIntegerRing_iff`: an integer lies in `ℓⁿ O'`
  exactly when `ℓⁿ` divides it.
* `Stacks.EtaleCohomology.isDiscreteValuationRing_padicIntegerRing`,
  `Stacks.EtaleCohomology.finite_padicIntegerRing_quotient_pow`,
  `Stacks.EtaleCohomology.charP_padicIntegerRing_quotient_pow` (instances): `O'` is a discrete
  valuation ring, and `O' / ℓⁿ` is finite of characteristic `ℓⁿ`.
* `Stacks.EtaleCohomology.finiteDimensional_padic_intermediateField` (instance): a finite
  subextension of an extension of a finite extension of `ℚ_ℓ` is finite over `ℚ_ℓ`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.EtaleCohomology

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {E' : Type} [Field E'] [Algebra ℚ_[ℓ] E']
  [FiniteDimensional ℚ_[ℓ] E']

attribute [local instance] padicIntAlgebraOfRat

/-- **The integral closure of `ℤ_ℓ` in a finite extension `E'` of `ℚ_ℓ` is the closed unit ball
of the spectral norm.** -/
theorem mem_padicIntegerRing_iff_spectralNorm_le_one (x : E') :
    x ∈ integralClosure ℤ_[ℓ] E' ↔ spectralNorm ℚ_[ℓ] E' x ≤ 1 := by
  have hxK : IsIntegral ℚ_[ℓ] x := Algebra.IsIntegral.isIntegral x
  rw [mem_integralClosure_iff, spectralNorm, spectralValue_le_one_iff (minpoly.monic hxK)]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[ℓ] hx, coeff_map,
      PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one _
  · intro h
    have hlifts : minpoly ℚ_[ℓ] x ∈ lifts (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
      rw [lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlifts (minpoly.monic hxK)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[ℓ], hq, minpoly.aeval]

omit [FiniteDimensional ℚ_[ℓ] E'] in
/-- The spectral norm of `ℓ` is `ℓ⁻¹`. -/
theorem spectralNorm_natCast_self : spectralNorm ℚ_[ℓ] E' (ℓ : E') = (ℓ : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[ℓ] E'), spectralNorm_extends, Padic.norm_p]

/-- The spectral norm is multiplicative on a finite extension of `ℚ_ℓ`. -/
private theorem spectralNorm_mul_eq (x y : E') :
    spectralNorm ℚ_[ℓ] E' (x * y) = spectralNorm ℚ_[ℓ] E' x * spectralNorm ℚ_[ℓ] E' y :=
  spectralAlgNorm_mul _ _

/-- `ℓ⁻¹ < 1` in `ℝ`. -/
private theorem inv_natCast_lt_one : (ℓ : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt)

private theorem spectralNorm_natCast_pow (k : ℕ) :
    spectralNorm ℚ_[ℓ] E' ((ℓ : E') ^ k) = (ℓ : ℝ)⁻¹ ^ k := by
  induction k with
  | zero => simpa using (spectralNorm_one (K := ℚ_[ℓ]) (L := E'))
  | succ k ih =>
    rw [pow_succ, spectralNorm_mul_eq, ih, spectralNorm_natCast_self, pow_succ]

/-- **Divisibility in `O'` is comparison of spectral norms**: if `a ≠ 0` and `‖b‖ ≤ ‖a‖` then
`a ∣ b`. -/
theorem dvd_of_spectralNorm_le_padicIntegerRing {a b : integralClosure ℤ_[ℓ] E'} (ha : a ≠ 0)
    (hab : spectralNorm ℚ_[ℓ] E' (b : E') ≤ spectralNorm ℚ_[ℓ] E' (a : E')) : a ∣ b := by
  have ha' : (a : E') ≠ 0 := fun h => ha (Subtype.ext h)
  have hpos : 0 < spectralNorm ℚ_[ℓ] E' (a : E') :=
    spectralNorm_zero_lt ha' (Algebra.IsAlgebraic.isAlgebraic _)
  have hmem : (b : E') / a ∈ integralClosure ℤ_[ℓ] E' := by
    rw [mem_padicIntegerRing_iff_spectralNorm_le_one]
    have h := spectralNorm_mul_eq ℓ ((b : E') / a) a
    rw [div_mul_cancel₀ _ ha'] at h
    by_contra! hlt
    exact hab.not_gt (h ▸ lt_mul_of_one_lt_left hpos hlt)
  exact ⟨⟨_, hmem⟩, Subtype.ext (by simp [mul_div_cancel₀ _ ha'])⟩

/-- **Every nonzero element of `O'` divides a power of `ℓ`.** -/
theorem exists_dvd_natCast_pow_padicIntegerRing {d : integralClosure ℤ_[ℓ] E'} (hd : d ≠ 0) :
    ∃ c : ℕ, d ∣ (ℓ : integralClosure ℤ_[ℓ] E') ^ c := by
  have hd' : (d : E') ≠ 0 := fun h => hd (Subtype.ext h)
  have hpos : 0 < spectralNorm ℚ_[ℓ] E' (d : E') :=
    spectralNorm_zero_lt hd' (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨c, hc⟩ := exists_pow_lt_of_lt_one hpos (inv_natCast_lt_one ℓ)
  refine ⟨c, dvd_of_spectralNorm_le_padicIntegerRing ℓ hd ?_⟩
  push_cast
  rw [spectralNorm_natCast_pow]
  exact hc.le

/-- **`ℓ` is not a unit of `O'`.** -/
theorem not_isUnit_natCast_padicIntegerRing : ¬IsUnit (ℓ : integralClosure ℤ_[ℓ] E') := by
  rintro ⟨u, hu⟩
  have h := congrArg (fun y : integralClosure ℤ_[ℓ] E' => spectralNorm ℚ_[ℓ] E' (y : E'))
    u.mul_inv
  simp only [Subalgebra.coe_mul, Subalgebra.coe_one, spectralNorm_mul_eq, spectralNorm_one] at h
  rw [hu] at h
  push_cast at h
  rw [spectralNorm_natCast_self] at h
  have h1 : spectralNorm ℚ_[ℓ] E' ((u⁻¹ : (integralClosure ℤ_[ℓ] E')ˣ) : E') ≤ 1 :=
    (mem_padicIntegerRing_iff_spectralNorm_le_one ℓ _).1 (u⁻¹ : (integralClosure ℤ_[ℓ] E')ˣ).1.2
  have : (ℓ : ℝ)⁻¹ * spectralNorm ℚ_[ℓ] E' ((u⁻¹ : (integralClosure ℤ_[ℓ] E')ˣ) : E') < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) h1) (inv_natCast_lt_one ℓ)
  exact absurd h this.ne

/-- A nonzero natural number stays nonzero in the integral closure of `ℤ_ℓ`. -/
private theorem natCast_ne_zero_integralClosure {F : Type} [Field F] [Algebra ℚ_[ℓ] F] {m : ℕ}
    (hm : m ≠ 0) : (m : integralClosure ℤ_[ℓ] F) ≠ 0 := fun h => by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] F).injective
  exact hm (by exact_mod_cast congrArg Subtype.val h)

omit [FiniteDimensional ℚ_[ℓ] E'] in
/-- `ℓ ≠ 0` in `O'`. -/
theorem natCast_ne_zero_padicIntegerRing : (ℓ : integralClosure ℤ_[ℓ] E') ≠ 0 :=
  natCast_ne_zero_integralClosure ℓ hℓ.out.ne_zero

/-- **An integer prime to `ℓ` is a unit of `O'`.** -/
theorem isUnit_natCast_padicIntegerRing_of_coprime {m : ℕ} (hm : m.Coprime ℓ) :
    IsUnit (m : integralClosure ℤ_[ℓ] E') := by
  have hnorm : spectralNorm ℚ_[ℓ] E' (m : E') = 1 := by
    rw [← map_natCast (algebraMap ℚ_[ℓ] E'), spectralNorm_extends, Padic.norm_natCast_eq_one_iff]
    exact hm.symm
  have hm0 : (m : integralClosure ℤ_[ℓ] E') ≠ 0 := natCast_ne_zero_integralClosure ℓ fun h =>
    hℓ.out.ne_one ((Nat.coprime_zero_left _).1 (h ▸ hm))
  obtain ⟨t, ht⟩ := dvd_of_spectralNorm_le_padicIntegerRing ℓ hm0 (b := 1) (by
    push_cast
    rw [hnorm, spectralNorm_one])
  exact IsUnit.of_mul_eq_one t ht.symm

/-- **An integer lies in `ℓⁿ O'` exactly when `ℓⁿ` divides it.** -/
theorem natCast_mem_span_pow_padicIntegerRing_iff (k n : ℕ) :
    (k : integralClosure ℤ_[ℓ] E') ∈ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E') ^ n} ↔
      ℓ ^ n ∣ k := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
    have h1 := congrArg (fun z : integralClosure ℤ_[ℓ] E' => spectralNorm ℚ_[ℓ] E' (z : E')) hy
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow] at h1
    push_cast at h1
    rw [spectralNorm_mul_eq, spectralNorm_natCast_pow, ← map_natCast (algebraMap ℚ_[ℓ] E') k,
      spectralNorm_extends] at h1
    have hy1 : spectralNorm ℚ_[ℓ] E' (y : E') ≤ 1 :=
      (mem_padicIntegerRing_iff_spectralNorm_le_one ℓ _).1 y.2
    have hk : ‖((k : ℤ) : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := by
      rw [Int.cast_natCast, ← h1, zpow_neg, zpow_natCast, inv_pow]
      exact mul_le_of_le_one_left (by positivity) hy1
    rw [Padic.norm_int_le_pow_iff_dvd] at hk
    exact_mod_cast hk
  · rintro ⟨j, rfl⟩
    exact Ideal.mem_span_singleton'.2 ⟨j, by push_cast; ring⟩

/-- **The integral closure of `ℤ_ℓ` in a finite extension of `ℚ_ℓ` is a discrete valuation
ring.** -/
instance isDiscreteValuationRing_padicIntegerRing :
    IsDiscreteValuationRing (integralClosure ℤ_[ℓ] E') :=
  haveI := henselianLocalRing_of_isAdicComplete_maximalIdeal ℤ_[ℓ]
  Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure
    ℤ_[ℓ] ℚ_[ℓ] E'

/-- **The finite levels `O' / ℓⁿ` are finite.** -/
instance finite_padicIntegerRing_quotient_pow (n : ℕ) :
    Finite (integralClosure ℤ_[ℓ] E' ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E') ^ n}) := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' ℤ_[ℓ] (integralClosure ℤ_[ℓ] E')
  let g : (Fin k → ZMod (ℓ ^ n)) →
      integralClosure ℤ_[ℓ] E' ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E') ^ n} :=
    fun v => Ideal.Quotient.mk _ (f fun i => ((v i).val : ℤ_[ℓ]))
  refine Finite.of_surjective g fun q => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨a, rfl⟩ := hf y
  refine ⟨fun i => PadicInt.toZModPow n (a i), ?_⟩
  simp only [g]
  rw [Ideal.Quotient.eq]
  have hker : ∀ i, ((PadicInt.toZModPow n (a i)).val : ℤ_[ℓ]) - a i ∈
      Ideal.span {(ℓ : ℤ_[ℓ]) ^ n} := by
    intro i
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  choose w hw using fun i => Ideal.mem_span_singleton'.1 (hker i)
  have : (fun i => ((PadicInt.toZModPow n (a i)).val : ℤ_[ℓ])) - a =
      (ℓ : ℤ_[ℓ]) ^ n • w := by
    funext i
    simp [hw i, mul_comm]
  rw [← map_sub, this, map_smul, Ideal.mem_span_singleton']
  refine ⟨f w, ?_⟩
  rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]

/-- **The finite levels `O' / ℓⁿ` have characteristic `ℓⁿ`.** -/
instance charP_padicIntegerRing_quotient_pow (n : ℕ) :
    CharP (integralClosure ℤ_[ℓ] E' ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E') ^ n}) (ℓ ^ n) :=
  ⟨fun k => by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
      natCast_mem_span_pow_padicIntegerRing_iff]⟩

omit [FiniteDimensional ℚ_[ℓ] E'] in
/-- **A finite subextension of an extension of a finite extension `E` of `ℚ_ℓ` is finite over
`ℚ_ℓ`.** -/
instance finiteDimensional_padic_intermediateField {E L : Type*} [Field E] [Field L]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra E L] [Algebra ℚ_[ℓ] L]
    [IsScalarTower ℚ_[ℓ] E L] (E'' : IntermediateField E L) [FiniteDimensional E E''] :
    FiniteDimensional ℚ_[ℓ] E'' :=
  Module.Finite.trans E E''

end Stacks.EtaleCohomology

end

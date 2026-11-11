module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.LevelNumerator
public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.GaloisDegree

/-!
# A Galois, totally ramified extension of degree `p` in mixed characteristic

Let `A` be a discrete valuation ring with fraction field `K` of characteristic zero and
uniformizer `π`, and let `p` be a prime with `p = u π ^ ((p - 1) r)` in `A` for a unit `u` and
some `r > 0`. (This holds when `A` has mixed characteristic `(0, p)` and some weakly unramified
extension of `A` contains a primitive `p`-th root of unity.) We construct a finite Galois
extension `K₁ / K` of degree `p`, totally ramified with respect to `A`, containing an element
`t` with `t ^ p = π V` for a unit `V` of the integral closure of `A` in `K₁`.

The extension `K(π ^ (1 / p))` is totally ramified of degree `p` but is Galois only when `K`
contains the `p`-th roots of unity. Instead, over `K' = K(ζ)` with Galois group `Δ` acting on
`ζ` through the cyclotomic character `χ`, put `x = (1 - ζ) / π ^ r` (a unit) and
`β = ∏_{σ ∈ Δ} (1 + π σ(x)) ^ {n_σ}` with `n_σ ≡ χ(σ)⁻¹ / |Δ| (mod p)`. Then `σ(β)` is `β ^ χ(σ)`
up to a `p`-th power, `β = 1 + π c` with `c ≡ x` a unit, so `N = K'(β ^ (1 / p))` is a degree
`p` Kummer extension of `K'`. The lifts `φ_σ` of the elements of `Δ` normalizing the Kummer
generator form a subgroup `H ≅ Δ` of `Aut(N / K)` commuting with the Kummer automorphism, and
`K₁ = N ^ H` is the required extension: it has degree `p`, it is Galois because the Kummer
automorphism restricts to an automorphism of order `p`, and the norm to `K₁` of `θ - 1`
(`θ ^ p = β`) has `p`-th power `π ^ |Δ|` times a unit, which forces every ramification index to
be divisible by `p`.

## Main results

* `Stacks.DegreePExtensionLevel.GaloisTotallyRamified.exists_isGalois_totallyRamified`: the
  extension `K₁ / K` above.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.DegreePExtensionLevel.GaloisTotallyRamified

/-! ### Elementary lemmas -/

/-- Expansion of a product of powers of `1 + π aᵢ` to first order in `π`. -/
theorem exists_prod_one_add_mul_pow {R ι : Type*} [CommRing R] (s : Finset ι) (π : R)
    (a : ι → R) (n : ι → ℕ) :
    ∃ r : R, ∏ i ∈ s, (1 + π * a i) ^ n i = 1 + π * (∑ i ∈ s, (n i : R) * a i + π * r) := by
  classical
  have hpow : ∀ (b : R) (k : ℕ), ∃ r : R, (1 + π * b) ^ k = 1 + π * ((k : R) * b + π * r) := by
    intro b k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r + (k : R) * b * b + π * r * b, by rw [pow_succ, hr]; push_cast; ring⟩
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := hpow (a j) (n j)
    refine ⟨r' + r + ((n j : R) * a j + π * r') * (∑ i ∈ s, (n i : R) * a i + π * r), ?_⟩
    rw [Finset.prod_insert hj, Finset.sum_insert hj, hr, hr']
    ring

/-- A unit plus an element of the Jacobson radical is a unit. -/
theorem isUnit_add_of_mem_jacobson {R : Type*} [CommRing R] {a b : R} (ha : IsUnit a)
    (hb : b ∈ Ideal.jacobson (⊥ : Ideal R)) : IsUnit (a + b) := by
  obtain ⟨u, rfl⟩ := ha
  have h := Ideal.mem_jacobson_bot.mp hb (↑u⁻¹)
  have he : (u : R) + b = (b * ↑u⁻¹ + 1) * u := by
    rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, add_comm]
  rw [he]
  exact h.mul u.isUnit

/-- The Jacobson radical is a radical ideal. -/
theorem mem_jacobson_of_pow_mem {R : Type*} [CommRing R] {a : R} {n : ℕ}
    (h : a ^ n ∈ Ideal.jacobson (⊥ : Ideal R)) : a ∈ Ideal.jacobson (⊥ : Ideal R) := by
  have hrad : a ∈ (Ideal.jacobson (⊥ : Ideal R)).radical := ⟨n, h⟩
  have h2 := Ideal.radical_le_jacobson (I := Ideal.jacobson (⊥ : Ideal R)) hrad
  rwa [Ideal.jacobson_idem] at h2

/-- In an integral extension of a local ring, the maximal ideal of the base maps into the
Jacobson radical. -/
theorem algebraMap_mem_jacobson (A R : Type*) [CommRing A] [IsLocalRing A] [CommRing R]
    [Algebra A R] [Algebra.IsIntegral A R] {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    algebraMap A R a ∈ Ideal.jacobson (⊥ : Ideal R) := by
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  have : M.IsMaximal := hM
  have hc : M.comap (algebraMap A R) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) M)
  rw [← Ideal.mem_comap, hc]
  exact ha

/-- The inverse of a unit of the integral closure is integral. -/
theorem isIntegral_inv_of_isUnit {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    {u : integralClosure A F} (hu : IsUnit u) : IsIntegral A (u : F)⁻¹ := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h : (u : F) * (v : F) = 1 := by
    have := congrArg (fun z : integralClosure A F => (z : F)) hv
    simpa using this
  rw [inv_eq_of_mul_eq_one_right h]
  exact (mem_integralClosure_iff A F).mp v.2

/-- An element which is integral, with integral inverse, is a unit of the integral closure. -/
theorem isUnit_of_isIntegral_inv {A F : Type*} [CommRing A] [Field F] [Algebra A F] {u : F}
    (hu : IsIntegral A u) (hu' : IsIntegral A u⁻¹) (h0 : u ≠ 0) :
    IsUnit (⟨u, (mem_integralClosure_iff A F).mpr hu⟩ : integralClosure A F) :=
  IsUnit.of_mul_eq_one ⟨u⁻¹, (mem_integralClosure_iff A F).mpr hu'⟩
    (Subtype.ext (by simp [h0]))

/-- **The `p`-th power of `t` from `(1 + t) ^ p = 1 + π c`.** If `t` is integral, `c` is a unit of
the integral closure, `π` lies in the maximal ideal and `p ∈ (π)`, then `t ^ p = π u` for a unit
`u` of the integral closure. -/
theorem exists_pow_eq_mul_of_one_add_pow (A F : Type*) [CommRing A] [IsLocalRing A] [Field F]
    [Algebra A F] (p : ℕ) (hp : p.Prime) (π q : A) (hπ : π ∈ IsLocalRing.maximalIdeal A)
    (hpq : (p : A) = π * q) (t c : F) (ht : IsIntegral A t) (hc : IsIntegral A c)
    (hc' : IsIntegral A c⁻¹) (hc0 : c ≠ 0) (h : (1 + t) ^ p = 1 + algebraMap A F π * c) :
    ∃ u : F, t ^ p = algebraMap A F π * u ∧ IsIntegral A u ∧ IsIntegral A u⁻¹ ∧ u ≠ 0 := by
  let R := integralClosure A F
  let tR : R := ⟨t, (mem_integralClosure_iff A F).mpr ht⟩
  let cR : R := ⟨c, (mem_integralClosure_iff A F).mpr hc⟩
  have hcR : IsUnit cR := isUnit_of_isIntegral_inv hc hc' hc0
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : R) tR
  have hπJ := algebraMap_mem_jacobson A R hπ
  have heqR : (1 + tR) ^ p = 1 + algebraMap A R π * cR := Subtype.ext (by simpa using h)
  have hpR : (p : R) = algebraMap A R π * algebraMap A R q := by
    rw [← map_mul, ← hpq, map_natCast]
  have htp : tR ^ p = algebraMap A R π * (cR - algebraMap A R q * tR * r) := by
    rw [one_pow] at hr
    linear_combination heqR - hr - tR * r * hpR
  have htJ : tR ∈ Ideal.jacobson (⊥ : Ideal R) := by
    refine mem_jacobson_of_pow_mem (n := p) ?_
    rw [htp]
    exact Ideal.mul_mem_right _ _ hπJ
  have hu : IsUnit (cR - algebraMap A R q * tR * r) := by
    rw [sub_eq_add_neg]
    exact isUnit_add_of_mem_jacobson hcR
      (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ htJ)))
  refine ⟨((cR - algebraMap A R q * tR * r : R) : F), ?_, ?_, isIntegral_inv_of_isUnit hu, ?_⟩
  · have := congrArg (fun z : R => (z : F)) htp
    simpa using this
  · exact (mem_integralClosure_iff A F).mp (cR - algebraMap A R q * tR * r).2
  · intro h0
    exact hu.ne_zero (Subtype.ext (by simpa using h0))

/-- **Ramification from `s ^ p = π ^ d V`.** If `s ^ p = π ^ d V` in a finite separable extension
`E / K`, with `V` a unit of the integral closure and `d` prime to `p`, then `p` divides the
ramification index of every maximal ideal above the maximal ideal of `A`. -/
theorem dvd_ramificationIdx_of_pow_eq
    (A K E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (p d : ℕ) (hpd : p.Coprime d) (π : A) (hπ : Irreducible π) (s V : E)
    (hV : IsIntegral A V) (hV' : IsIntegral A V⁻¹) (hV0 : V ≠ 0)
    (h : s ^ p = algebraMap A E π ^ d * V)
    (m : Ideal (integralClosure A E)) (hm : m.IsMaximal)
    [hOver : m.LiesOver (IsLocalRing.maximalIdeal A)] :
    p ∣ Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m := by
  let B := integralClosure A E
  let mA := IsLocalRing.maximalIdeal A
  let : m.IsPrime := hm.isPrime
  have hAB : Function.Injective (algebraMap A B) := by
    apply Function.Injective.of_comp (f := algebraMap B E)
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  let : Module.Finite A B := IsIntegralClosure.finite A K E B
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K E
  let : IsFractionRing B E := IsIntegralClosure.isFractionRing_of_finite_extension A K E B
  let vA : IsDedekindDomain.HeightOneSpectrum A :=
    ⟨mA, (IsLocalRing.maximalIdeal.isMaximal A).isPrime, IsDiscreteValuationRing.not_a_field A⟩
  have hm0 : m ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) m
  let vB : IsDedekindDomain.HeightOneSpectrum B := ⟨m, hm.isPrime, hm0⟩
  let : vB.asIdeal.LiesOver vA.asIdeal := hOver
  have hvπ : vA.intValuation π = WithZero.exp (-1 : ℤ) :=
    vA.intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq
  have hvπB : vB.valuation E (algebraMap A E π) =
      WithZero.exp (-((mA.ramificationIdx' m : ℕ) : ℤ)) := by
    rw [IsScalarTower.algebraMap_apply A K E,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver E vA vB,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hvπ, ← WithZero.exp_nsmul,
      Ideal.ramificationIdx'_eq_ramificationIdx mA m (IsDiscreteValuationRing.not_a_field A)]
    congr 1
    simp [vA, vB, mA]
  have hle : ∀ y : E, IsIntegral A y → vB.valuation E y ≤ 1 := by
    intro y hy
    have hy' : y = algebraMap B E ⟨y, (mem_integralClosure_iff A E).mpr hy⟩ := rfl
    rw [hy', IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact vB.intValuation_le_one _
  have hvV : vB.valuation E V = 1 := by
    have h1 := hle V hV
    have h2 := hle V⁻¹ hV'
    rw [map_inv₀] at h2
    have hne : vB.valuation E V ≠ 0 := (Valuation.ne_zero_iff _).mpr hV0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hne)).mp h2)
  have hval : vB.valuation E s ^ p =
      WithZero.exp (-(((mA.ramificationIdx' m * d : ℕ)) : ℤ)) := by
    rw [← map_pow, h, map_mul, map_pow, hvπB, hvV, mul_one, ← WithZero.exp_nsmul]
    congr 1
    push_cast
    simp only [nsmul_eq_mul]
    ring
  have hlog := congrArg WithZero.log hval
  rw [WithZero.log_pow, WithZero.log_exp] at hlog
  have hdvd : (p : ℤ) ∣ ((mA.ramificationIdx' m * d : ℕ) : ℤ) :=
    ⟨-(vB.valuation E s).log, by simp only [nsmul_eq_mul] at hlog; linear_combination hlog⟩
  have hdvd' : p ∣ mA.ramificationIdx' m * d := by exact_mod_cast hdvd
  exact hpd.dvd_of_dvd_mul_right hdvd'

/-- `(ζ - 1) ^ (p - 1)` is associated to `p` for a primitive `p`-th root of unity `ζ` in a
domain. -/
theorem associated_sub_one_pow_prime {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    [hp : Fact p.Prime] {ζ : R} (hζ : IsPrimitiveRoot ζ p) :
    Associated ((ζ - 1) ^ (p - 1)) (p : R) := by
  classical
  rw [← eval_one_cyclotomic_prime (R := R) (p := p), cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
    eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hp.out, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη ↦ ?_
  have hη' : IsPrimitiveRoot η p := (mem_primitiveRoots hp.out.pos).mp hη
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨i, -, hi, rfl⟩ := hζ.isPrimitiveRoot_iff.mp hη'
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right

/-! ### Exponent bookkeeping over the cyclotomic Galois group -/

section Exponents

variable {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] (χ : G →* (ZMod p)ˣ)

/-- The exponent `m_σ`, the natural-number representative of `χ(σ)`. -/
def mExp (σ : G) : ℕ := ((χ σ : (ZMod p)ˣ) : ZMod p).val

/-- The exponent `n_σ`, the natural-number representative of `χ(σ)⁻¹ / |G|`. -/
def nExp (σ : G) : ℕ :=
  (((χ σ)⁻¹ : (ZMod p)ˣ) * ((Fintype.card G : ℕ) : ZMod p)⁻¹ : ZMod p).val

/-- The correction exponent `k_{σ, ρ} = (n_{σ⁻¹ ρ} - m_σ n_ρ) / p`. -/
def kExp (σ ρ : G) : ℤ := ((nExp p χ (σ⁻¹ * ρ) : ℤ) - mExp p χ σ * nExp p χ ρ) / p

theorem nExp_inv_mul_cast (σ ρ : G) :
    ((nExp p χ (σ⁻¹ * ρ) : ℕ) : ZMod p) = (mExp p χ σ : ZMod p) * (nExp p χ ρ : ZMod p) := by
  simp only [nExp, mExp, ZMod.natCast_val, ZMod.cast_id', id, map_mul, map_inv, inv_inv,
    mul_inv_rev, Units.val_mul]
  ring

theorem p_mul_kExp (σ ρ : G) :
    (p : ℤ) * kExp p χ σ ρ = (nExp p χ (σ⁻¹ * ρ) : ℤ) - mExp p χ σ * nExp p χ ρ := by
  apply Int.mul_ediv_cancel'
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  push_cast
  rw [nExp_inv_mul_cast, sub_self]

omit [Fintype G] in
theorem mExp_one : mExp p χ 1 = 1 := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  simp [mExp, ZMod.val_one]

theorem kExp_one (ρ : G) : kExp p χ 1 ρ = 0 := by
  have h := p_mul_kExp p χ 1 ρ
  rw [inv_one, one_mul, mExp_one] at h
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h' : (p : ℤ) * kExp p χ 1 ρ = 0 := by rw [h]; simp
  exact (mul_eq_zero.mp h').resolve_left hp

omit [Fintype G] in
theorem mExp_mul (σ τ : G) :
    mExp p χ σ * mExp p χ τ = mExp p χ (σ * τ) + p * (mExp p χ σ * mExp p χ τ / p) := by
  have h : mExp p χ (σ * τ) = mExp p χ σ * mExp p χ τ % p := by
    simp only [mExp, map_mul, Units.val_mul, ZMod.val_mul]
  rw [h, Nat.mod_add_div]

theorem card_lt (hχ : Function.Injective χ) : Fintype.card G < p := by
  have h := Fintype.card_le_of_injective χ hχ
  rw [ZMod.card_units] at h
  have := (Fact.out : p.Prime).one_lt
  omega

theorem sum_nExp_mul_mExp (hχ : Function.Injective χ) :
    ((∑ σ : G, nExp p χ σ * mExp p χ σ : ℕ) : ZMod p) = 1 := by
  have hcard : ((Fintype.card G : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact absurd (Nat.le_of_dvd Fintype.card_pos hdvd) (not_le.mpr (card_lt p χ hχ))
  push_cast
  simp only [nExp, mExp, ZMod.natCast_val, ZMod.cast_id', id]
  have hterm : ∀ σ : G, (((χ σ)⁻¹ : (ZMod p)ˣ) : ZMod p) * ((Fintype.card G : ℕ) : ZMod p)⁻¹ *
      ((χ σ : (ZMod p)ˣ) : ZMod p) = ((Fintype.card G : ℕ) : ZMod p)⁻¹ := by
    intro σ
    rw [mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_inv_cancel₀ hcard]

end Exponents

/-! ### The cocycle identities -/

section Cocycle

variable {G F : Type*} [Group G] [Fintype G] [Field F] (p : ℕ) [Fact p.Prime]
  (χ : G →* (ZMod p)ˣ) (b : G → F)

/-- The Kummer parameter `β = ∏_ρ b_ρ ^ {n_ρ}`. -/
def betaElt : F := ∏ ρ : G, b ρ ^ nExp p χ ρ

/-- The correction factor `γ_σ = ∏_ρ b_ρ ^ {k_{σ, ρ}}`. -/
def gammaElt (σ : G) : F := ∏ ρ : G, b ρ ^ kExp p χ σ ρ

theorem gammaElt_one : gammaElt p χ b 1 = 1 := by
  simp [gammaElt, kExp_one]

theorem betaElt_eq_prod_zpow :
    betaElt p χ b = ∏ ρ : G, b ρ ^ ((nExp p χ ρ : ℕ) : ℤ) := by
  simp [betaElt, zpow_natCast]

omit [Fact p.Prime] in
/-- `∏_ρ b_{σρ} ^ {e_ρ} = ∏_ρ b_ρ ^ {e_{σ⁻¹ρ}}`. -/
theorem prod_mul_left_zpow (σ : G) (e : G → ℤ) :
    ∏ ρ : G, b (σ * ρ) ^ e ρ = ∏ ρ : G, b ρ ^ e (σ⁻¹ * ρ) :=
  Fintype.prod_equiv (Equiv.mulLeft σ) _ _ (fun ρ => by simp)

omit [Fact p.Prime] [Group G] in
theorem prod_zpow_mul_prod_zpow (hb0 : ∀ ρ, b ρ ≠ 0) (e e' : G → ℤ) :
    (∏ ρ : G, b ρ ^ e ρ) * ∏ ρ : G, b ρ ^ e' ρ = ∏ ρ : G, b ρ ^ (e ρ + e' ρ) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun ρ _ => (zpow_add₀ (hb0 ρ) _ _).symm

omit [Fact p.Prime] [Group G] in
theorem prod_zpow_zpow (e : G → ℤ) (k : ℤ) :
    (∏ ρ : G, b ρ ^ e ρ) ^ k = ∏ ρ : G, b ρ ^ (k * e ρ) := by
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun ρ _ => by rw [← zpow_mul, mul_comm]

/-- **The eigen-relation `σ(β) = β ^ {m_σ} γ_σ ^ p`**, for an action with `σ(β)` the product of
the translates `b_{σρ}`. -/
theorem act_betaElt (hb0 : ∀ ρ, b ρ ≠ 0) (σ : G) (y : F)
    (hact : ∏ ρ : G, b (σ * ρ) ^ ((nExp p χ ρ : ℕ) : ℤ) = y) :
    y = betaElt p χ b ^ mExp p χ σ * gammaElt p χ b σ ^ p := by
  rw [← hact, prod_mul_left_zpow, ← zpow_natCast (betaElt p χ b),
    ← zpow_natCast (gammaElt p χ b σ), betaElt_eq_prod_zpow, gammaElt, prod_zpow_zpow,
    prod_zpow_zpow, prod_zpow_mul_prod_zpow b hb0]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  congr 1
  have := p_mul_kExp p χ σ ρ
  linear_combination -this

/-- **The cocycle relation for the correction factors.** -/
theorem gammaElt_mul (hb0 : ∀ ρ, b ρ ≠ 0) (σ τ : G) (y : F)
    (hact : ∏ ρ : G, b (σ * ρ) ^ kExp p χ τ ρ = y) :
    betaElt p χ b ^ (mExp p χ σ * mExp p χ τ / p) * gammaElt p χ b σ ^ mExp p χ τ * y =
      gammaElt p χ b (σ * τ) := by
  rw [← hact, prod_mul_left_zpow, ← zpow_natCast (betaElt p χ b),
    ← zpow_natCast (gammaElt p χ b σ), betaElt_eq_prod_zpow, gammaElt, gammaElt,
    prod_zpow_zpow, prod_zpow_zpow, prod_zpow_mul_prod_zpow b hb0,
    prod_zpow_mul_prod_zpow b hb0]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  congr 1
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hp
  have h1 := p_mul_kExp p χ σ ρ
  have h2 := p_mul_kExp p χ τ (σ⁻¹ * ρ)
  have h3 := p_mul_kExp p χ (σ * τ) ρ
  have h4 := mExp_mul p χ σ τ
  have h4' : ((mExp p χ σ : ℤ) * mExp p χ τ) =
      mExp p χ (σ * τ) + p * ((mExp p χ σ * mExp p χ τ / p : ℕ) : ℤ) := by exact_mod_cast h4
  have h3' : (p : ℤ) * kExp p χ (σ * τ) ρ =
      (nExp p χ (τ⁻¹ * (σ⁻¹ * ρ)) : ℤ) - mExp p χ (σ * τ) * nExp p χ ρ := by
    rw [← mul_assoc, ← mul_inv_rev]
    exact h3
  linear_combination (mExp p χ τ : ℤ) * h1 + h2 - h3' - (nExp p χ ρ : ℤ) * h4'

end Cocycle

/-! ### The degree-`p` subfield `K` cannot contain a `p`-th root with prime-to-`p` pole -/

/-- In `K` itself there is no `s` with `s ^ p = π ^ d V`, `V` a unit and `d` prime to `p`. -/
theorem false_of_pow_eq_pow_mul (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (p d : ℕ) (hp : p.Prime) (hpd : p.Coprime d) (π : A) (hπ : Irreducible π) (s V : K)
    (hV : IsIntegral A V) (hV' : IsIntegral A V⁻¹) (hV0 : V ≠ 0)
    (h : s ^ p = algebraMap A K π ^ d * V) : False := by
  let B := integralClosure A K
  let mA := IsLocalRing.maximalIdeal A
  have hAB : Function.Injective (algebraMap A B) := by
    apply Function.Injective.of_comp (f := algebraMap B K)
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact IsFractionRing.injective A K
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  let : Module.Finite A B := IsIntegralClosure.finite A K K B
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K K
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A K
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  have hOver : m.LiesOver mA := ⟨((IsLocalRing.isMaximal_iff A).mp
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m)).symm⟩
  let := hOver
  have hdvd := dvd_ramificationIdx_of_pow_eq A K K p d hpd π hπ s V hV hV' hV0 h m hm
  have he : 0 < mA.ramificationIdx' m :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m
        (IsDiscreteValuationRing.not_a_field A))
  have hle : mA.ramificationIdx' m ≤ 1 := by
    have h1 := (IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_le_finrank
      A K K m hm).1
    rw [Module.finrank_self] at h1
    rwa [Ideal.ramificationIdx'_eq_ramificationIdx mA m (IsDiscreteValuationRing.not_a_field A)]
  have he1 : mA.ramificationIdx' m = 1 := by omega
  rw [he1] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)

/-! ### The construction -/

section Construction

variable (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]

local notation "𝕂" => CyclotomicField p K

/-- **The fixed field of the normalized lifts in a Kummer extension.** Let `F / K` be a finite
Galois extension with group `G` acting faithfully on a primitive `p`-th root of unity `ζ ∈ F`
through `χ`, and let `b : G → F` be a family permuted by `G`, `σ (b ρ) = b (σ ρ)`, with
`β = ∏_ρ b_ρ ^ {n_ρ} = 1 + π c` for a unit `c` of the integral closure and `X ^ p - β`
irreducible. Then the fixed field in `F(β ^ (1 / p))` of the lifts of `G` normalizing the Kummer
generator is a Galois, totally ramified extension of `K` of degree `p`, containing `t` with
`t ^ p = π V` for a unit `V`. -/
theorem exists_isGalois_totallyRamified_of_kummer
    (F : Type u) [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (χ : Gal(F/K) →* (ZMod p)ˣ) (hχ : Function.Injective χ) (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (hχspec : ∀ σ : Gal(F/K), σ ζ = ζ ^ mExp p χ σ)
    (b : Gal(F/K) → F) (hb0 : ∀ σ, b σ ≠ 0) (hbact : ∀ σ ρ : Gal(F/K), σ (b ρ) = b (σ * ρ))
    (πA : A) (hπ : Irreducible πA) (q : A) (hpq : (p : A) = πA * q)
    (c : F) (hcint : IsIntegral A c) (hcinv : IsIntegral A c⁻¹) (hc0 : c ≠ 0)
    (hβc : betaElt p χ b = 1 + algebraMap A F πA * c)
    (f : F[X]) (hf : f = X ^ p - C (betaElt p χ b)) (hirr : Irreducible f) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : FiniteDimensional K K₁),
      IsGalois K K₁ ∧ Module.finrank K K₁ = p ∧
        IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁ ∧
        ∃ t V : K₁, t ^ p = algebraMap A K₁ πA * V ∧ IsIntegral A V ∧ IsIntegral A V⁻¹ ∧
          V ≠ 0 := by
  classical
  have hp' := hp.out
  have : Fact (Irreducible f) := ⟨hirr⟩
  set β := betaElt p χ b with hβ
  have hdpos : 0 < Fintype.card Gal(F/K) := Fintype.card_pos
  have hdlt : Fintype.card Gal(F/K) < p := card_lt p χ hχ
  have hcop : p.Coprime (Fintype.card Gal(F/K)) := Nat.coprime_of_lt_prime hdpos.ne' hdlt hp'
  have hdfin : Fintype.card Gal(F/K) = Module.finrank K F := by
    rw [← Nat.card_eq_fintype_card]
    exact IsGalois.card_aut_eq_finrank K F
  have hπmem : πA ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
  have hβint : IsIntegral A β := by
    rw [hβc]
    exact isIntegral_one.add (isIntegral_algebraMap.mul hcint)
  have hβ0 : β ≠ 0 := by
    rw [hβ, betaElt]
    exact Finset.prod_ne_zero_iff.mpr fun ρ _ => pow_ne_zero _ (hb0 ρ)
  have hkey : ∀ σ : Gal(F/K), σ β = β ^ mExp p χ σ * gammaElt p χ b σ ^ p := by
    intro σ
    refine act_betaElt p χ b hb0 σ (σ β) ?_
    rw [hβ, betaElt, map_prod]
    exact Finset.prod_congr rfl fun ρ _ => by rw [map_pow, hbact, zpow_natCast]
  have hgact : ∀ σ τ : Gal(F/K), ∏ ρ, b (σ * ρ) ^ kExp p χ τ ρ = σ (gammaElt p χ b τ) := by
    intro σ τ
    rw [gammaElt, map_prod]
    exact Finset.prod_congr rfl fun ρ _ => by rw [map_zpow₀, hbact]
  have hev : ∀ {T : Type u} [CommRing T] (i : F →+* T) (y : T), y ^ p = i β →
      eval₂ i y f = 0 := by
    intro T _ i y hy
    rw [hf, eval₂_sub, eval₂_X_pow, eval₂_C, hy, sub_self]
  have hf0 : f ≠ 0 := hirr.ne_zero
  have : FiniteDimensional F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hfrankN : Module.finrank F (AdjoinRoot f) = p := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hf,
      natDegree_X_pow_sub_C]
  have : FiniteDimensional K (AdjoinRoot f) := FiniteDimensional.trans K F (AdjoinRoot f)
  let ι : F →ₐ[K] AdjoinRoot f := IsScalarTower.toAlgHom K F (AdjoinRoot f)
  have hιof : ∀ y : F, AdjoinRoot.of f y = ι y := fun y => by
    simp [ι, AdjoinRoot.algebraMap_eq]
  have hιinj : Function.Injective ι := ι.toRingHom.injective
  let θ : AdjoinRoot f := AdjoinRoot.root f
  have hθ : θ ^ p = ι β := by
    have h2 : eval₂ (AdjoinRoot.of f) θ (X ^ p - C β) = 0 := by
      rw [← hf]
      exact AdjoinRoot.eval₂_root f
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, hιof] at h2
    exact h2
  have hθ0 : θ ≠ 0 := by
    intro h
    apply hβ0
    apply hιinj
    rw [← hθ, h, zero_pow hp'.ne_zero, map_zero]
  -- the normalized lifts `φ_σ`
  let φ : Gal(F/K) → (AdjoinRoot f →ₐ[K] AdjoinRoot f) := fun σ =>
    AdjoinRoot.liftAlgHom f (ι.comp σ.toAlgHom) (θ ^ mExp p χ σ * ι (gammaElt p χ b σ))
      (hev _ _ (by
        rw [mul_pow, ← pow_mul, mul_comm (mExp p χ σ) p, pow_mul, hθ, ← map_pow, ← map_pow,
          ← map_mul, ← hkey σ]
        rfl))
  have hφof : ∀ σ y, φ σ (ι y) = ι (σ y) := by
    intro σ y
    rw [← hιof]
    simp [φ]
  have hφθ : ∀ σ, φ σ θ = θ ^ mExp p χ σ * ι (gammaElt p χ b σ) := by
    intro σ
    simp [φ, θ]
  have hext : ∀ g₁ g₂ : AdjoinRoot f →ₐ[K] AdjoinRoot f, (∀ y, g₁ (ι y) = g₂ (ι y)) →
      g₁ θ = g₂ θ → g₁ = g₂ := by
    intro g₁ g₂ h1 h2
    apply AlgHom.coe_ringHom_injective
    apply AdjoinRoot.ringHom_ext
    · ext y
      simpa [hιof] using h1 y
    · exact h2
  have hφ1 : φ 1 = AlgHom.id K _ := hext _ _ (fun y => by rw [hφof]; rfl)
    (by rw [hφθ, mExp_one, gammaElt_one, map_one, pow_one, mul_one]; rfl)
  have hφmul : ∀ σ τ, (φ σ).comp (φ τ) = φ (σ * τ) := by
    intro σ τ
    refine hext _ _ (fun y => by simp only [AlgHom.comp_apply, hφof, AlgEquiv.mul_apply]) ?_
    have hθpow : θ ^ (mExp p χ σ * mExp p χ τ) =
        θ ^ mExp p χ (σ * τ) * ι β ^ (mExp p χ σ * mExp p χ τ / p) := by
      conv_lhs => rw [mExp_mul p χ σ τ]
      rw [pow_add, pow_mul, hθ]
    rw [AlgHom.comp_apply, hφθ, map_mul, map_pow, hφθ, hφof, hφθ,
      ← gammaElt_mul p χ b hb0 σ τ _ (hgact σ τ), mul_pow, ← pow_mul, hθpow]
    simp only [map_mul, map_pow]
    ring
  have hbij : ∀ g : AdjoinRoot f →ₐ[K] AdjoinRoot f, Function.Bijective g :=
    fun g => AlgHom.bijective g
  let Φfun : Gal(F/K) → Gal(AdjoinRoot f/K) := fun σ => AlgEquiv.ofBijective (φ σ) (hbij _)
  have hΦapply : ∀ σ y, Φfun σ y = φ σ y := fun _ _ => rfl
  let Φ : Gal(F/K) →* Gal(AdjoinRoot f/K) := MonoidHom.mk' Φfun (fun σ τ => by
    ext y
    rw [AlgEquiv.mul_apply, hΦapply, hΦapply, hΦapply, ← hφmul]
    rfl)
  have hΦapply' : ∀ σ y, Φ σ y = φ σ y := fun _ _ => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    ext y
    apply hιinj
    have := congrArg (fun g : Gal(AdjoinRoot f/K) => g (ι y)) hσ
    simp only [hΦapply', hφof, AlgEquiv.one_apply] at this
    simpa using this
  -- the Kummer automorphism `g : θ ↦ ζ θ`
  let g : AdjoinRoot f →ₐ[K] AdjoinRoot f := AdjoinRoot.liftAlgHom f ι (ι ζ * θ)
    (hev _ _ (by rw [mul_pow, hθ, ← map_pow, hζ.pow_eq_one, map_one, one_mul]; rfl))
  have hgof : ∀ y, g (ι y) = ι y := fun y => by
    rw [← hιof, show g (AdjoinRoot.of f y) = ι y by simp [g]]
    exact hιof y
  have hgθ : g θ = ι ζ * θ := by simp [g, θ]
  have hgφ : ∀ σ, (φ σ).comp g = g.comp (φ σ) := by
    intro σ
    refine hext _ _ (fun y => by simp only [AlgHom.comp_apply, hgof, hφof]) ?_
    simp only [AlgHom.comp_apply, hgθ, hφθ, map_mul, map_pow, hφof, hgof, hχspec]
    ring
  let gE : Gal(AdjoinRoot f/K) := AlgEquiv.ofBijective g (hbij g)
  have hgE : ∀ y, gE y = g y := fun _ => rfl
  have hgEpow : ∀ i : ℕ, (gE ^ i) θ = ι ζ ^ i * θ ∧ ∀ y, (gE ^ i) (ι y) = ι y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      refine ⟨?_, fun y => ?_⟩
      · rw [pow_succ', AlgEquiv.mul_apply, ih.1, hgE, map_mul, map_pow, hgof, hgθ]
        ring
      · rw [pow_succ', AlgEquiv.mul_apply, ih.2, hgE, hgof]
  have hgEp : gE ^ p = 1 := by
    have h := hext (gE ^ p).toAlgHom (AlgHom.id K _) (fun y => (hgEpow p).2 y) (by
      change (gE ^ p) θ = θ
      rw [(hgEpow p).1, ← map_pow, hζ.pow_eq_one, map_one, one_mul])
    ext y
    exact congrArg (fun φ' : AdjoinRoot f →ₐ[K] AdjoinRoot f => φ' y) h
  -- the fixed field `K₁ = N ^ H`
  set H : Subgroup Gal(AdjoinRoot f/K) := Φ.range with hH
  set K₁ : IntermediateField K (AdjoinRoot f) := IntermediateField.fixedField H with hK₁
  have hcardH : Nat.card H = Fintype.card Gal(F/K) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv.symm
  have hK₁N : Module.finrank K₁ (AdjoinRoot f) = Fintype.card Gal(F/K) := by
    rw [hK₁, IntermediateField.finrank_fixedField_eq_card, hcardH]
  have hKN : Module.finrank K (AdjoinRoot f) = Fintype.card Gal(F/K) * p := by
    rw [← Module.finrank_mul_finrank K F (AdjoinRoot f), hfrankN, hdfin]
  have hfinK₁ : Module.finrank K K₁ = p := by
    have h := Module.finrank_mul_finrank K K₁ (AdjoinRoot f)
    rw [hK₁N, hKN, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left hdpos h
  -- `g` restricts to an automorphism of order `p` of `K₁`
  have hgK₁ : ∀ y ∈ K₁, g y ∈ K₁ := by
    intro y hy
    rw [hK₁, IntermediateField.mem_fixedField_iff] at hy ⊢
    rintro _ ⟨σ, rfl⟩
    have := hy (Φ σ) ⟨σ, rfl⟩
    rw [hΦapply'] at this ⊢
    rw [← AlgHom.comp_apply, hgφ, AlgHom.comp_apply, this]
  let gK : K₁ →ₐ[K] K₁ :=
    { toFun := fun y => ⟨g y, hgK₁ y y.2⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun y z => Subtype.ext (map_mul g (y : AdjoinRoot f) z)
      map_zero' := Subtype.ext (map_zero g)
      map_add' := fun y z => Subtype.ext (map_add g (y : AdjoinRoot f) z)
      commutes' := fun k => Subtype.ext (g.commutes k) }
  let gKE : Gal(K₁/K) := AlgEquiv.ofBijective gK (AlgHom.bijective gK)
  have hgKpow : ∀ (i : ℕ) (y : K₁), ((gKE ^ i) y : AdjoinRoot f) = (gE ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [pow_succ', AlgEquiv.mul_apply, pow_succ', AlgEquiv.mul_apply, ← ih]
      rfl
  have hgKp : gKE ^ p = 1 := by
    ext y
    rw [hgKpow, hgEp]
    rfl
  have hgK1 : gKE ≠ 1 := by
    intro h
    have hfix : gE ∈ IntermediateField.fixingSubgroup K₁ := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have := congrArg (fun φ' : Gal(K₁/K) => ((φ' ⟨y, hy⟩ : K₁) : AdjoinRoot f)) h
      exact this
    rw [hK₁, IntermediateField.fixingSubgroup_fixedField] at hfix
    obtain ⟨σ, hσ⟩ := hfix
    have hσ1 : σ = 1 := by
      ext y
      apply hιinj
      have := congrArg (fun φ' : Gal(AdjoinRoot f/K) => φ' (ι y)) hσ
      simp only [hΦapply', hφof, hgE, hgof] at this
      simpa using this
    subst hσ1
    have := congrArg (fun φ' : Gal(AdjoinRoot f/K) => φ' θ) hσ
    simp only [hΦapply', hφ1, hgE, hgθ, AlgHom.id_apply] at this
    have hζ1 : ι ζ = 1 := by
      have h2 : (ι ζ - 1) * θ = 0 := by rw [sub_mul, ← this, one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hθ0)
    exact hζ.ne_one hp'.one_lt (hιinj (by rw [hζ1, map_one]))
  have horder : orderOf gKE = p := orderOf_eq_prime hgKp hgK1
  have hGal : IsGalois K K₁ := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [Nat.card_eq_fintype_card, hfinK₁]
    refine le_antisymm (hfinK₁ ▸ AlgEquiv.card_le) ?_
    rw [← horder]
    exact orderOf_le_card_univ
  -- the norm of `θ - 1`
  have hθint : IsIntegral A θ :=
    IsIntegral.of_pow hp'.pos (by rw [hθ]; exact hβint.map (ι.restrictScalars A))
  have hιA : ∀ a : A, ι (algebraMap A F a) = algebraMap A (AdjoinRoot f) a :=
    fun a => (ι.restrictScalars A).commutes a
  obtain ⟨u, hu, huint, huinv, hu0⟩ := exists_pow_eq_mul_of_one_add_pow A (AdjoinRoot f) p hp'
    πA q hπmem hpq (θ - 1) (ι c) (hθint.sub isIntegral_one) (hcint.map (ι.restrictScalars A))
    (by rw [← map_inv₀]; exact hcinv.map (ι.restrictScalars A))
    ((map_ne_zero_iff _ hιinj).mpr hc0)
    (by rw [add_sub_cancel, hθ, hβc, map_add, map_one, map_mul, hιA])
  have hσint : ∀ (σ : Gal(AdjoinRoot f/K)) (y : AdjoinRoot f), IsIntegral A y →
      IsIntegral A (σ y) := fun σ y hy => hy.map (σ.toAlgHom.restrictScalars A)
  have hσA : ∀ (σ : Gal(AdjoinRoot f/K)) (a : A),
      σ (algebraMap A (AdjoinRoot f) a) = algebraMap A (AdjoinRoot f) a := by
    intro σ a
    rw [IsScalarTower.algebraMap_apply A K (AdjoinRoot f), AlgEquiv.commutes]
  have hprodfix : ∀ y : AdjoinRoot f, (∏ h : H, (h : Gal(AdjoinRoot f/K)) y) ∈ K₁ := by
    intro y
    rw [hK₁, IntermediateField.mem_fixedField_iff]
    intro φ' hφ'
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨φ', hφ'⟩ : H)) _ _
      (fun h => by simp [AlgEquiv.mul_apply])
  let s₁ : K₁ := ⟨_, hprodfix (θ - 1)⟩
  let U₁ : K₁ := ⟨_, hprodfix u⟩
  have hcardH' : Fintype.card H = Fintype.card Gal(F/K) := by
    rw [← Nat.card_eq_fintype_card, hcardH]
  have hs₁ : s₁ ^ p = algebraMap A K₁ πA ^ Fintype.card Gal(F/K) * U₁ := by
    apply Subtype.ext
    change (∏ h : H, (h : Gal(AdjoinRoot f/K)) (θ - 1)) ^ p =
      algebraMap A (AdjoinRoot f) πA ^ Fintype.card Gal(F/K) * ∏ h : H, (h : Gal(AdjoinRoot f/K)) u
    rw [← Finset.prod_pow, Finset.prod_congr rfl fun h _ => by rw [← map_pow, hu, map_mul, hσA],
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcardH']
  have hK₁int : ∀ y : K₁, IsIntegral A (y : AdjoinRoot f) → IsIntegral A y := fun y hy =>
    (isIntegral_algHom_iff (K₁.val.restrictScalars A) Subtype.val_injective).mp hy
  have hUint : IsIntegral A U₁ :=
    hK₁int _ (IsIntegral.prod _ fun h _ => hσint _ u huint)
  have hUinv : IsIntegral A U₁⁻¹ := by
    refine hK₁int _ ?_
    rw [IntermediateField.coe_inv]
    change IsIntegral A (∏ h : H, (h : Gal(AdjoinRoot f/K)) u)⁻¹
    rw [← Finset.prod_inv_distrib]
    exact IsIntegral.prod _ fun h _ => by rw [← map_inv₀]; exact hσint _ _ huinv
  have hU0 : U₁ ≠ 0 := by
    intro h
    have h' : (∏ h : H, (h : Gal(AdjoinRoot f/K)) u) = 0 := congrArg Subtype.val h
    rw [Finset.prod_eq_zero_iff] at h'
    obtain ⟨h, -, hh⟩ := h'
    exact hu0 ((map_eq_zero_iff _ (h : Gal(AdjoinRoot f/K)).injective).mp hh)
  have : Algebra.IsSeparable K K₁ := Algebra.IsSeparable.of_integral _ _
  have htot : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁ :=
    Stacks.DiscreteValuationRing.EppLevelInduction.isTotallyRamified_of_dvd_ramificationIdx A K K₁
      p hp'.pos hfinK₁.le (fun m hm hlies => dvd_ramificationIdx_of_pow_eq A K K₁ p _ hcop πA hπ
        s₁ U₁ hUint hUinv hU0 hs₁ m hm (hOver := hlies))
  -- a root of `π V`
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm hp'.one_lt
  obtain ⟨bb, hda⟩ : ∃ bb, Fintype.card Gal(F/K) * a = 1 + p * bb := by
    refine ⟨Fintype.card Gal(F/K) * a / p, ?_⟩
    have := Nat.mod_add_div (Fintype.card Gal(F/K) * a) p
    rw [ha] at this
    omega
  have hπK₁ : algebraMap A K₁ πA ≠ 0 := by
    intro h
    have h' : algebraMap A (AdjoinRoot f) πA = 0 := congrArg Subtype.val h
    rw [IsScalarTower.algebraMap_apply A K (AdjoinRoot f)] at h'
    exact hπ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective A K)).mp
      ((map_eq_zero_iff _ (algebraMap K (AdjoinRoot f)).injective).mp h'))
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hGal,
    hfinK₁, htot, s₁ ^ a / algebraMap A K₁ πA ^ bb, U₁ ^ a, ?_,
    hUint.pow a, by rw [← inv_pow]; exact hUinv.pow a, pow_ne_zero _ hU0⟩
  rw [div_pow, div_eq_iff (pow_ne_zero _ (pow_ne_zero _ hπK₁)), ← pow_mul, mul_comm a p, pow_mul,
    hs₁, mul_pow, ← pow_mul, hda]
  ring

/-- **A Galois, totally ramified extension of degree `p`.** Let `A` be a discrete valuation ring
with fraction field `K` of characteristic zero and uniformizer `π`, and suppose
`p = u π ^ ((p - 1) r)` in `A` with `u` a unit and `r > 0`. Then there is a finite Galois
extension `K₁ / K` of degree `p`, totally ramified with respect to `A`, together with `t ∈ K₁`
and a unit `V` of the integral closure of `A` in `K₁` such that `t ^ p = π V`. -/
theorem exists_isGalois_totallyRamified
    (πA : A) (hπ : Irreducible πA) (r : ℕ) (hr : 0 < r) (uA : Aˣ)
    (hpu : (p : A) = uA * πA ^ ((p - 1) * r)) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : FiniteDimensional K K₁),
      IsGalois K K₁ ∧ Module.finrank K K₁ = p ∧
        IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁ ∧
        ∃ t V : K₁, t ^ p = algebraMap A K₁ πA * V ∧ IsIntegral A V ∧ IsIntegral A V⁻¹ ∧
          V ≠ 0 := by
  classical
  have hp' := hp.out
  have : NeZero p := ⟨hp'.ne_zero⟩
  have : FiniteDimensional K 𝕂 := IsCyclotomicExtension.finiteDimensional {p} K 𝕂
  have : IsGalois K 𝕂 := IsCyclotomicExtension.isGalois {p} K 𝕂
  -- the cyclotomic data
  obtain ⟨ζ, hζ⟩ : ∃ ζ : 𝕂, IsPrimitiveRoot ζ p := ⟨_, IsCyclotomicExtension.zeta_spec p K 𝕂⟩
  let χ : Gal(𝕂/K) →* (ZMod p)ˣ := hζ.autToPow K
  have hχ : Function.Injective χ := hζ.autToPow_injective K
  have hχspec : ∀ σ : Gal(𝕂/K), σ ζ = ζ ^ mExp p χ σ := fun σ => (hζ.autToPow_spec K σ).symm
  have hdpos : 0 < Fintype.card Gal(𝕂/K) := Fintype.card_pos
  have hdlt : Fintype.card Gal(𝕂/K) < p := card_lt p χ hχ
  have hcop : p.Coprime (Fintype.card Gal(𝕂/K)) := Nat.coprime_of_lt_prime hdpos.ne' hdlt hp'
  have hdfin : Fintype.card Gal(𝕂/K) = Module.finrank K 𝕂 := by
    rw [← Nat.card_eq_fintype_card]
    exact IsGalois.card_aut_eq_finrank K 𝕂
  -- the uniformizer and the prime
  let π' : 𝕂 := algebraMap A 𝕂 πA
  have hπmem : πA ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
  have hπ'0 : π' ≠ 0 := by
    change algebraMap A 𝕂 πA ≠ 0
    rw [IsScalarTower.algebraMap_apply A K 𝕂]
    exact (map_ne_zero_iff _ (algebraMap K 𝕂).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hπ.ne_zero)
  have hpr : 1 ≤ (p - 1) * r := by
    have := hp'.two_le
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hr.ne')
  obtain ⟨n', hn'⟩ : ∃ n', (p - 1) * r = n' + 1 := ⟨(p - 1) * r - 1, by omega⟩
  let q : A := uA * πA ^ n'
  have hpq : (p : A) = πA * q := by rw [hpu, hn', pow_succ]; ring
  -- the integral closure of `A` in `K(ζ)`
  let R' := integralClosure A 𝕂
  let J : Ideal R' := Ideal.jacobson ⊥
  have hRint : ∀ y : R', IsIntegral A (y : 𝕂) := fun y => (mem_integralClosure_iff A 𝕂).mp y.2
  let πR : R' := algebraMap A R' πA
  have hπR : (πR : 𝕂) = π' := rfl
  have hπJ : πR ∈ J := algebraMap_mem_jacobson A R' hπmem
  have hpJ : (p : R') ∈ J := by
    rw [← map_natCast (algebraMap A R'), hpq, map_mul]
    exact Ideal.mul_mem_right _ _ hπJ
  have hζint : IsIntegral A ζ :=
    IsIntegral.of_pow hp'.pos (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  let ζR : R' := ⟨ζ, (mem_integralClosure_iff A 𝕂).mpr hζint⟩
  have hζR : IsPrimitiveRoot ζR p :=
    IsPrimitiveRoot.of_map_of_injective (f := (integralClosure A 𝕂).val) hζ Subtype.val_injective
  obtain ⟨ε, hε⟩ := associated_sub_one_pow_prime hζR
  -- the unit `x = (1 - ζ) / π ^ r`
  let x : 𝕂 := (1 - ζ) / π' ^ r
  have hxw : 1 - ζ = π' ^ r * x := by
    simp only [x]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hπ'0)]
  have hx1 : x ^ (p - 1) * ((ε : R') : 𝕂) = (-1) ^ (p - 1) * algebraMap A 𝕂 uA := by
    have h1 : (ζ - 1) ^ (p - 1) * ((ε : R') : 𝕂) = (p : 𝕂) := by
      have := congrArg (fun z : R' => (z : 𝕂)) hε
      simpa [ζR] using this
    have h2 : (p : 𝕂) = algebraMap A 𝕂 uA * π' ^ ((p - 1) * r) := by
      rw [← map_natCast (algebraMap A 𝕂), hpu, map_mul, map_pow]
    have hneg : (1 - ζ) ^ (p - 1) = (-1) ^ (p - 1) * (ζ - 1) ^ (p - 1) := by
      rw [← neg_pow, neg_sub]
    simp only [x]
    rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ (pow_ne_zero _ hπ'0))]
    linear_combination ((ε : R') : 𝕂) * hneg + (-1) ^ (p - 1) * h1 + (-1) ^ (p - 1) * h2
  have hxint : IsIntegral A x := by
    have hx2 : x ^ (p - 1) =
        (-1) ^ (p - 1) * algebraMap A 𝕂 uA * (((ε⁻¹ : R'ˣ) : R') : 𝕂) := by
      rw [← hx1, mul_assoc, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, mul_one]
    refine IsIntegral.of_pow (n := p - 1) (by have := hp'.two_le; omega) ?_
    rw [hx2]
    exact ((isIntegral_one.neg.pow _).mul isIntegral_algebraMap).mul (hRint _)
  let xR : R' := ⟨x, (mem_integralClosure_iff A 𝕂).mpr hxint⟩
  have hxR : IsUnit xR := by
    have h : xR ^ (p - 1) * (ε : R') = (-1) ^ (p - 1) * algebraMap A R' uA :=
      Subtype.ext (by simpa [xR] using hx1)
    have hu : IsUnit ((-1) ^ (p - 1) * algebraMap A R' uA) :=
      ((isUnit_one.neg).pow _).mul (uA.isUnit.map _)
    rw [← h] at hu
    exact (isUnit_pow_iff (by have := hp'.two_le; omega)).mp (isUnit_of_mul_isUnit_left hu)
  have hwJ : 1 - ζR ∈ J := by
    have h : 1 - ζR = πR ^ r * xR := Subtype.ext (by simpa [ζR, xR, πR] using hxw)
    rw [h]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [pow_succ, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hπJ)
  -- the conjugates of `x`
  have hσint : ∀ (σ : Gal(𝕂/K)) (y : 𝕂), IsIntegral A y → IsIntegral A (σ y) := fun σ y hy =>
    hy.map (σ.toAlgHom.restrictScalars A)
  have hσπ : ∀ σ : Gal(𝕂/K), σ π' = π' := by
    intro σ
    simp only [π', IsScalarTower.algebraMap_apply A K 𝕂, AlgEquiv.commutes]
  let aR : Gal(𝕂/K) → R' := fun σ => ⟨σ x, (mem_integralClosure_iff A 𝕂).mpr (hσint σ x hxint)⟩
  let gR : Gal(𝕂/K) → R' := fun σ => ∑ i ∈ Finset.range (mExp p χ σ), ζR ^ i
  have haR : ∀ σ, aR σ = xR * gR σ := by
    intro σ
    apply Subtype.ext
    have h1 : σ (1 - ζ) = (1 - ζ) * ∑ i ∈ Finset.range (mExp p χ σ), ζ ^ i := by
      rw [map_sub, map_one, hχspec, mul_neg_geom_sum]
    have h2 : σ x = x * ∑ i ∈ Finset.range (mExp p χ σ), ζ ^ i := by
      have h3 : σ (1 - ζ) = σ (π' ^ r) * σ x := by rw [← map_mul, ← hxw]
      rw [map_pow, hσπ, h1, hxw] at h3
      exact mul_left_cancel₀ (pow_ne_zero _ hπ'0) (by rw [← h3]; ring)
    simpa [aR, xR, gR, ζR] using h2
  -- the Kummer parameter `β = 1 + π c`
  obtain ⟨rem, hrem⟩ := exists_prod_one_add_mul_pow Finset.univ πR aR (nExp p χ)
  let cR : R' := ∑ σ, (nExp p χ σ : R') * aR σ + πR * rem
  have hcR : IsUnit cR := by
    have hsumJ : (∑ σ, (nExp p χ σ : R') * gR σ) - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hζQ : Ideal.Quotient.mk J ζR = 1 := by
        rw [← map_one (Ideal.Quotient.mk J)]
        exact (Ideal.Quotient.eq.mpr (by rw [← neg_sub]; exact J.neg_mem hwJ))
      have hpQ : ((p : ℕ) : R' ⧸ J) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
        exact hpJ
      have hN := sum_nExp_mul_mExp p χ hχ
      set N₀ := ∑ σ : Gal(𝕂/K), nExp p χ σ * mExp p χ σ with hN₀
      have hmod : N₀ % p = 1 := by
        have := (ZMod.natCast_eq_natCast_iff' N₀ 1 p).mp (by simpa using hN)
        rwa [Nat.mod_eq_of_lt hp'.one_lt] at this
      have hNQ : ((N₀ : ℕ) : R' ⧸ J) = 1 := by
        rw [← Nat.mod_add_div N₀ p, hmod]
        push_cast
        rw [hpQ, zero_mul, add_zero]
      simp only [gR, map_sub, map_sum, map_mul, map_natCast, map_one, map_pow, hζQ, one_pow,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [sub_eq_zero, ← hNQ, hN₀]
      push_cast
      rfl
    have hc : cR = xR + (xR * ((∑ σ, (nExp p χ σ : R') * gR σ) - 1) + πR * rem) := by
      simp only [cR, haR]
      rw [mul_sub, Finset.mul_sum]
      simp only [mul_one]
      rw [show ∑ σ, (nExp p χ σ : R') * (xR * gR σ) = ∑ σ, xR * ((nExp p χ σ : R') * gR σ) from
        Finset.sum_congr rfl fun σ _ => by ring]
      ring
    rw [hc]
    exact isUnit_add_of_mem_jacobson hxR
      (J.add_mem (J.mul_mem_left _ hsumJ) (J.mul_mem_right _ hπJ))
  let c' : 𝕂 := cR
  have hc'int : IsIntegral A c' := hRint cR
  have hc'inv : IsIntegral A c'⁻¹ := isIntegral_inv_of_isUnit hcR
  have hc'0 : c' ≠ 0 := fun h => hcR.ne_zero (Subtype.ext h)
  obtain ⟨b, hb⟩ : ∃ b : Gal(𝕂/K) → 𝕂, ∀ σ, b σ = 1 + π' * σ x := ⟨_, fun _ => rfl⟩
  have hbR : ∀ σ, b σ = ((1 + πR * aR σ : R') : 𝕂) := fun σ => by simp [hb, aR, πR, π']
  have hb0 : ∀ σ, b σ ≠ 0 := by
    intro σ h
    have hu : IsUnit (1 + πR * aR σ) :=
      isUnit_add_of_mem_jacobson isUnit_one (J.mul_mem_right _ hπJ)
    exact hu.ne_zero (Subtype.ext (by rw [← hbR]; simpa using h))
  have hbact : ∀ σ ρ : Gal(𝕂/K), σ (b ρ) = b (σ * ρ) := by
    intro σ ρ
    rw [hb, hb, map_add, map_one, map_mul, hσπ, AlgEquiv.mul_apply]
  obtain ⟨β', hβ'⟩ : ∃ β' : 𝕂, β' = betaElt p χ b := ⟨_, rfl⟩
  have hβc : β' = 1 + π' * c' := by
    have h1 : β' = ((∏ σ, (1 + πR * aR σ) ^ nExp p χ σ : R') : 𝕂) := by
      rw [hβ', betaElt]
      simp_rw [hbR]
      push_cast
      rfl
    rw [h1, hrem]
    change ((1 + πR * cR : R') : 𝕂) = 1 + π' * c'
    push_cast
    rfl
  have hβint : IsIntegral A β' := by
    rw [hβc]
    exact isIntegral_one.add ((isIntegral_algebraMap).mul hc'int)
  -- `β` is not a `p`-th power in `K(ζ)`
  have hirr : Irreducible (X ^ p - C β' : 𝕂[X]) := by
    apply X_pow_sub_C_irreducible_of_prime hp'
    intro γ hγ
    have hγint : IsIntegral A γ := IsIntegral.of_pow hp'.pos (by rw [hγ]; exact hβint)
    obtain ⟨u, hu, huint, huinv, hu0⟩ := exists_pow_eq_mul_of_one_add_pow A 𝕂 p hp' πA q
      hπmem hpq (γ - 1) c' (hγint.sub isIntegral_one) hc'int hc'inv hc'0
      (by rw [add_sub_cancel, hγ, hβc])
    let s : 𝕂 := ∏ σ : Gal(𝕂/K), σ (γ - 1)
    let U : 𝕂 := ∏ σ : Gal(𝕂/K), σ u
    have hfix : ∀ y : 𝕂, (∀ τ : Gal(𝕂/K), τ y = y) → ∃ y₀ : K, algebraMap K 𝕂 y₀ = y := by
      intro y hy
      exact IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed y).mpr hy)
    have hprodfix : ∀ y : 𝕂, ∀ τ : Gal(𝕂/K), τ (∏ σ : Gal(𝕂/K), σ y) = ∏ σ : Gal(𝕂/K), σ y := by
      intro y τ
      rw [map_prod]
      exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => by simp [AlgEquiv.mul_apply])
    obtain ⟨s₀, hs₀⟩ := hfix s (hprodfix _)
    obtain ⟨U₀, hU₀⟩ := hfix U (hprodfix _)
    have hs : s ^ p = π' ^ Fintype.card Gal(𝕂/K) * U := by
      simp only [s, U]
      rw [← Finset.prod_pow, Finset.prod_congr rfl fun σ _ => by rw [← map_pow, hu, map_mul,
        hσπ], Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have hs₀ : s₀ ^ p = algebraMap A K πA ^ Fintype.card Gal(𝕂/K) * U₀ := by
      apply (algebraMap K 𝕂).injective
      rw [map_pow, hs₀, map_mul, map_pow, hU₀, ← IsScalarTower.algebraMap_apply]
      exact hs
    have hUint : IsIntegral A U := by
      simp only [U]
      exact IsIntegral.prod _ fun σ _ => hσint σ u huint
    have hUinv : IsIntegral A U⁻¹ := by
      simp only [U]
      rw [← Finset.prod_inv_distrib]
      exact IsIntegral.prod _ fun σ _ => by rw [← map_inv₀]; exact hσint σ _ huinv
    have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun σ _ => by simpa using hu0
    have hinj : ∀ y : K, IsIntegral A (algebraMap K 𝕂 y) ↔ IsIntegral A y := fun y =>
      isIntegral_algHom_iff (IsScalarTower.toAlgHom A K 𝕂) (algebraMap K 𝕂).injective
    refine false_of_pow_eq_pow_mul A K p _ hp' hcop πA hπ s₀ U₀ ?_ ?_ ?_ hs₀
    · exact (hinj U₀).mp (by rw [hU₀]; exact hUint)
    · exact (hinj U₀⁻¹).mp (by rw [map_inv₀, hU₀]; exact hUinv)
    · rintro rfl
      exact hU0 (by rw [← hU₀, map_zero])
  exact exists_isGalois_totallyRamified_of_kummer A K p 𝕂 χ hχ ζ hζ hχspec b hb0 hbact πA hπ q
    hpq c' hc'int hc'inv hc'0 (by rw [← hβ']; exact hβc) _ rfl (hβ' ▸ hirr)

end Construction

end Stacks.DegreePExtensionLevel.GaloisTotallyRamified

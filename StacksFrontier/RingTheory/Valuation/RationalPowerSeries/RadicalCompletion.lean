module

public import StacksFrontier.RingTheory.Valuation.RationalPowerSeries.ValuationRing
import Mathlib.Algebra.MonoidAlgebra.Ideal

/-!
# Power series with nonnegative rational exponents: completing at the radical of `(t)`

The monoid algebra `κ[t^(ℚ≥0)] = ⋃ₙ κ[t^(1/n)]` also shows that completing at an ideal and
completing at its radical are different operations. The radical `J` of `(t)` is the maximal
ideal of polynomials without constant term and satisfies `J ^ 2 = J`, so the `J`-adic
completion is just `κ`, whereas the `(t)`-adic completion is the large ring `A` above; the
comparison map between them is not even injective.

## Main definitions

* `RationalPowerSeries.polynomialConstantCoeff`: the constant coefficient of a polynomial
  with nonnegative rational exponents, as a ring homomorphism `κ[t^(ℚ≥0)] → κ`.
* `RationalPowerSeries.radicalQuotientEquiv`,
  `RationalPowerSeries.radicalAdicCompletionEquiv`: the residue field of `κ[t^(ℚ≥0)]` at the
  radical of `(t)`, and the completion of `κ[t^(ℚ≥0)]` at that radical, both equal to `κ`.

## Main results

* `RationalPowerSeries.mem_radical_polynomialTIdeal_iff`,
  `RationalPowerSeries.isMaximal_radical_polynomialTIdeal`: the radical of `(t)` in
  `κ[t^(ℚ≥0)]` is the maximal ideal of polynomials with vanishing constant coefficient.
* `RationalPowerSeries.radical_polynomialTIdeal_sq`,
  `RationalPowerSeries.radical_polynomialTIdeal_pow`: that radical is idempotent.
* `RationalPowerSeries.injective_of_rationalPolynomial`: `κ[t^(ℚ≥0)]` is a subring of its
  `(t)`-adic completion.
* `RationalPowerSeries.not_injective_compareAlgHom_radical`,
  `RationalPowerSeries.not_bijective_compareAlgHom_radical`,
  `RationalPowerSeries.isEmpty_ringEquiv_adicCompletion_radical`: the comparison map from the
  `(t)`-adic completion to the completion at the radical of `(t)` is not injective, hence not
  a ring isomorphism, and in fact the two completions are not isomorphic at all.

## Implementation notes

The constant coefficient of a polynomial is a ring homomorphism `κ[t^(ℚ≥0)] → κ` because a
sum of nonnegative rationals vanishes only when both summands do; its kernel is the radical
of `(t)`, which gives both the maximal ideal and the residue field in one step. The
comparison map between the two completions is `AdicCompletion.compareAlgHom` along the
inclusion `(t) ≤ √(t)`.

## References

* [Stacks Project, Tag 0CKX](https://stacks.math.columbia.edu/tag/0CKX)
-/

@[expose] public noncomputable section

namespace RationalPowerSeries

/-! ### The radical of `(t)` and the two completions of the monoid algebra -/

/-- The character of `ℚ≥0` with value `1` at the exponent `0` and `0` at every positive
exponent; it is multiplicative because a sum of nonnegative rationals vanishes only when both
summands do. -/
def polynomialConstantChar (k : Type*) [CommRing k] : Multiplicative ℚ≥0 →* k where
  toFun q := if q.toAdd = 0 then 1 else 0
  map_one' := by simp
  map_mul' q r := by
    by_cases hq : q.toAdd = 0 <;> by_cases hr : r.toAdd = 0 <;> simp [hq, hr]

/-- The constant coefficient of a polynomial with nonnegative rational exponents, as a ring
homomorphism `k[t^(ℚ≥0)] → k`. -/
def polynomialConstantCoeff (k : Type*) [CommRing k] : rationalPolynomial k →+* k :=
  (AddMonoidAlgebra.lift k k ℚ≥0 (polynomialConstantChar k)).toRingHom

/-- The constant-coefficient homomorphism reads off the coefficient of exponent zero. -/
theorem polynomialConstantCoeff_apply {k : Type*} [CommRing k]
    (p : rationalPolynomial k) : polynomialConstantCoeff k p = p.coeff 0 := by
  change AddMonoidAlgebra.lift k k ℚ≥0 (polynomialConstantChar k) p = _
  rw [AddMonoidAlgebra.lift_apply,
    Finsupp.sum_eq_single 0 (fun b _ hb => by simp [polynomialConstantChar, hb])
      (fun _ => by simp)]
  simp [polynomialConstantChar]

/-- The constant coefficient of a monomial is its coefficient if the exponent is zero and
zero otherwise. -/
theorem polynomialConstantCoeff_single {k : Type*} [CommRing k] (c : ℚ≥0) (a : k) :
    polynomialConstantCoeff k (AddMonoidAlgebra.single c a) = if c = 0 then a else 0 := by
  rw [polynomialConstantCoeff_apply]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Every element of `k` is the constant coefficient of a constant polynomial. -/
theorem polynomialConstantCoeff_surjective (k : Type*) [CommRing k] :
    Function.Surjective (polynomialConstantCoeff k) := fun a =>
  ⟨AddMonoidAlgebra.single 0 a, by rw [polynomialConstantCoeff_single]; simp⟩

/-- A monomial whose exponent is at least one lies in the ideal `(t)`. -/
private theorem single_mem_polynomialTIdeal {k : Type*} [CommRing k] {c : ℚ≥0} (hc : 1 ≤ c) :
    AddMonoidAlgebra.single c (1 : k) ∈ polynomialTIdeal k := by
  refine Ideal.mem_span_singleton.2 ⟨AddMonoidAlgebra.single (c - 1) 1, ?_⟩
  rw [polynomialT, AddMonoidAlgebra.single_mul_single, one_mul, add_tsub_cancel_of_le hc]

/-- A polynomial all of whose exponents are at least `c` is divisible by the monomial of
exponent `c`. -/
private theorem mem_span_single_of_forall_le {k : Type*} [CommRing k]
    {p : rationalPolynomial k} {c : ℚ≥0} (hc : ∀ q ∈ p.coeff.support, c ≤ q) :
    p ∈ Ideal.span ({AddMonoidAlgebra.single c (1 : k)} : Set (rationalPolynomial k)) := by
  have hp : p ∈ Ideal.span (AddMonoidAlgebra.of' k ℚ≥0 '' ({c} : Set ℚ≥0)) := by
    refine AddMonoidAlgebra.mem_ideal_span_of'_image.2 fun q hq =>
      ⟨c, Set.mem_singleton _, q - c, ?_⟩
    rw [tsub_add_cancel_of_le (hc q hq)]
  simpa only [Set.image_singleton, AddMonoidAlgebra.of'_apply] using hp

/-- Powers of a monomial are the monomials of the multiplied exponent. -/
private theorem single_pow {k : Type*} [CommRing k] (c : ℚ≥0) (n : ℕ) :
    AddMonoidAlgebra.single c (1 : k) ^ n = AddMonoidAlgebra.single (n • c) 1 := by
  induction n with
  | zero => simpa using AddMonoidAlgebra.one_def
  | succ n ih => rw [pow_succ, ih, AddMonoidAlgebra.single_mul_single, succ_nsmul, one_mul]

/-- The support of a nonzero polynomial is nonempty. -/
private theorem support_nonempty_of_ne_zero {k : Type*} [CommRing k]
    {p : rationalPolynomial k} (hp : p ≠ 0) : p.coeff.support.Nonempty := by
  rw [Finsupp.support_nonempty_iff]
  intro hc
  exact hp (by ext q; simp [hc])

/-- A nonzero polynomial with vanishing constant coefficient is divisible by a monomial of
positive exponent: the one at its least exponent. -/
private theorem exists_ne_zero_mem_span_single {k : Type*} [CommRing k]
    {p : rationalPolynomial k} (hp : p ≠ 0) (h0 : p.coeff 0 = 0) :
    ∃ c : ℚ≥0, c ≠ 0 ∧
      p ∈ Ideal.span ({AddMonoidAlgebra.single c (1 : k)} : Set (rationalPolynomial k)) := by
  have hsupp := support_nonempty_of_ne_zero hp
  have hcmem := p.coeff.support.min'_mem hsupp
  exact ⟨_, fun hc0 => (Finsupp.mem_support_iff.1 (hc0 ▸ hcmem)) h0,
    mem_span_single_of_forall_le fun q hq => p.coeff.support.min'_le q hq⟩

/-- **Stacks 0CKX.** The radical of `(t)` in `k[t^(ℚ≥0)]` is the ideal of polynomials with
vanishing constant coefficient: a positive exponent becomes at least one after enough
multiplications. -/
@[stacks 0CKX "the radical of (t) in the monoid algebra"]
theorem mem_radical_polynomialTIdeal_iff (k : Type*) [Field k] (p : rationalPolynomial k) :
    p ∈ (polynomialTIdeal k).radical ↔ p.coeff 0 = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 hn
    have h : p.coeff 0 ^ n = 0 := by
      have hc := congrArg (polynomialConstantCoeff k) hr
      rw [map_pow, map_mul, polynomialConstantCoeff_apply,
        polynomialConstantCoeff_apply (polynomialT k)] at hc
      simpa [polynomialT, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] using hc
    rcases n with _ | n
    · simp at h
    · exact (pow_eq_zero_iff (Nat.succ_ne_zero n)).1 h
  · intro h0
    rcases eq_or_ne p 0 with rfl | hp
    · exact Ideal.zero_mem _
    obtain ⟨c, hcne, hcmem⟩ := exists_ne_zero_mem_span_single hp h0
    have hcpos : 0 < c := lt_of_le_of_ne bot_le (Ne.symm hcne)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / c)
    have hnc : 1 ≤ n • c := by
      rw [nsmul_eq_mul]
      exact le_of_lt ((div_lt_iff₀ hcpos).1 hn)
    refine ⟨n, ?_⟩
    have hpow := Ideal.pow_mem_pow hcmem n
    rw [Ideal.span_singleton_pow, single_pow] at hpow
    refine (Ideal.span_le.2 ?_) hpow
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ single_mem_polynomialTIdeal hnc

/-- The radical of `(t)` is the kernel of the constant-coefficient homomorphism. -/
theorem ker_polynomialConstantCoeff (k : Type*) [Field k] :
    RingHom.ker (polynomialConstantCoeff k) = (polynomialTIdeal k).radical := by
  ext p
  rw [RingHom.mem_ker, polynomialConstantCoeff_apply, mem_radical_polynomialTIdeal_iff]

/-- **Stacks 0CKX.** The radical of `(t)` is a maximal ideal of `k[t^(ℚ≥0)]`, being the
kernel of the constant-coefficient map onto the field `k`. -/
@[stacks 0CKX "the radical of (t) is the maximal ideal"]
theorem isMaximal_radical_polynomialTIdeal (k : Type*) [Field k] :
    ((polynomialTIdeal k).radical).IsMaximal := by
  rw [← ker_polynomialConstantCoeff k]
  exact RingHom.ker_isMaximal_of_surjective _ (polynomialConstantCoeff_surjective k)

/-- **Stacks 0CKX.** The residue field of `k[t^(ℚ≥0)]` at the radical of `(t)` is `k`. -/
@[stacks 0CKX "the residue field at the radical of (t)"]
def radicalQuotientEquiv (k : Type*) [Field k] :
    rationalPolynomial k ⧸ (polynomialTIdeal k).radical ≃+* k :=
  (Ideal.quotEquivOfEq (ker_polynomialConstantCoeff k).symm).trans
    (RingHom.quotientKerEquivOfSurjective (polynomialConstantCoeff_surjective k))

/-- **Stacks 0CKX.** The radical of `(t)` is idempotent: a monomial of positive exponent is
the square of the monomial of half that exponent. -/
@[stacks 0CKX "J ^ 2 = J for J the radical of (t)"]
theorem radical_polynomialTIdeal_sq (k : Type*) [Field k] :
    (polynomialTIdeal k).radical ^ 2 = (polynomialTIdeal k).radical := by
  refine le_antisymm (Ideal.pow_le_self two_ne_zero) fun p hp => ?_
  rw [mem_radical_polynomialTIdeal_iff] at hp
  rcases eq_or_ne p 0 with rfl | hp0
  · exact Ideal.zero_mem _
  obtain ⟨c, hcne, hcspan⟩ := exists_ne_zero_mem_span_single hp0 hp
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 hcspan
  have hhalf : AddMonoidAlgebra.single (c / 2) (1 : k) *
      AddMonoidAlgebra.single (c / 2) (1 : k) = AddMonoidAlgebra.single c 1 := by
    rw [AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1
    rw [← two_mul]
    field_simp
  have hhalfne : c / 2 ≠ 0 := by simpa using hcne
  have h1 : AddMonoidAlgebra.single (c / 2) (1 : k) ∈ (polynomialTIdeal k).radical := by
    rw [mem_radical_polynomialTIdeal_iff, ← polynomialConstantCoeff_apply,
      polynomialConstantCoeff_single]
    simp [hhalfne]
  have h2 : AddMonoidAlgebra.single (c / 2) (1 : k) * r ∈ (polynomialTIdeal k).radical := by
    rw [mem_radical_polynomialTIdeal_iff, ← polynomialConstantCoeff_apply, map_mul,
      polynomialConstantCoeff_single]
    simp [hhalfne]
  have hfactor : p = AddMonoidAlgebra.single (c / 2) (1 : k) *
      (AddMonoidAlgebra.single (c / 2) (1 : k) * r) := by rw [← mul_assoc, hhalf, hr]
  rw [hfactor, sq]
  exact Ideal.mul_mem_mul h1 h2

/-- **Stacks 0CKX.** Every positive power of the radical of `(t)` equals it, so the tower
defining its adic completion is constant. -/
@[stacks 0CKX "J ^ n = J for J the radical of (t)"]
theorem radical_polynomialTIdeal_pow (k : Type*) [Field k] {n : ℕ} (hn : n ≠ 0) :
    (polynomialTIdeal k).radical ^ n = (polynomialTIdeal k).radical := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · rw [pow_succ, ih hn0, ← sq, radical_polynomialTIdeal_sq]

/-- Reduction modulo two equal ideals is injective on the quotients. -/
private theorem factor_injective_of_eq {R : Type*} [CommRing R] {I J : Ideal R} (hle : I ≤ J)
    (heq : I = J) : Function.Injective (Ideal.Quotient.factor hle) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at hab
  rw [Ideal.Quotient.eq, heq]
  exact hab

/-- For an ideal all of whose positive powers agree, the adic completion is its first
quotient: the tower defining the completion is constant. -/
theorem bijective_evalOneₐ_of_pow_eq {R : Type*} [CommRing R] {I : Ideal R}
    (h : ∀ n : ℕ, n ≠ 0 → I ^ n = I) : Function.Bijective (AdicCompletion.evalOneₐ I) := by
  constructor
  · intro x y hxy
    have hone : AdicCompletion.evalₐ I 1 x = AdicCompletion.evalₐ I 1 y := by
      refine factor_injective_of_eq (show I ^ 1 ≤ I by simp) (by simp) ?_
      rw [AdicCompletion.factorₐ_evalₐ_one, AdicCompletion.factorₐ_evalₐ_one, hxy]
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · have : Subsingleton (R ⧸ I ^ 0) :=
        Ideal.Quotient.subsingleton_iff.2 ((pow_zero I).trans Ideal.one_eq_top)
      exact Subsingleton.elim _ _
    · have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
      refine factor_injective_of_eq (Ideal.pow_le_pow_right h1) ?_ ?_
      · rw [h n hn, pow_one]
      · rw [AdicCompletion.factor_evalₐ I h1 x, AdicCompletion.factor_evalₐ I h1 y, hone]
  · intro c
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨AdicCompletion.of I _ r, AdicCompletion.evalOneₐ_of I r⟩

/-- **Stacks 0CKX.** The completion of `k[t^(ℚ≥0)]` at the radical of `(t)` is `k` itself,
because that radical is idempotent. -/
@[stacks 0CKX "the radical-adic completion of the monoid algebra is k"]
def radicalAdicCompletionEquiv (k : Type*) [Field k] :
    AdicCompletion (polynomialTIdeal k).radical (rationalPolynomial k) ≃+* k :=
  (RingEquiv.ofBijective (AdicCompletion.evalOneₐ (polynomialTIdeal k).radical).toRingHom
    (bijective_evalOneₐ_of_pow_eq fun _ hn => radical_polynomialTIdeal_pow k hn)).trans
      (radicalQuotientEquiv k)

/-- The ideal `(t)` is contained in its own radical, the inclusion along which the two adic
completions are compared. -/
theorem polynomialTIdeal_pow_one_le_radical (k : Type*) [CommRing k] :
    polynomialTIdeal k ^ 1 ≤ (polynomialTIdeal k).radical := by
  simpa using Ideal.le_radical

/-- **Stacks 0CKX.** The monoid algebra is contained in its `(t)`-adic completion: a
polynomial whose class vanishes modulo every power of `(t)` has all coefficients zero. -/
@[stacks 0CKX "the monoid algebra sits inside its (t)-adic completion"]
theorem injective_of_rationalPolynomial (k : Type*) [CommRing k] :
    Function.Injective
      (AdicCompletion.of (polynomialTIdeal k) (rationalPolynomial k)) := by
  intro p r hpr
  have hmem : ∀ n : ℕ, p - r ∈ (polynomialTIdeal k) ^ n := by
    intro n
    have h := congrArg (AdicCompletion.evalₐ (polynomialTIdeal k) n) hpr
    rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.Quotient.eq] at h
    exact h
  ext q
  have hq : q < (Nat.ceil q + 1 : ℕ) :=
    lt_of_le_of_lt (Nat.le_ceil q) (by exact_mod_cast Nat.lt_succ_self (Nat.ceil q))
  have hzero := (polynomial_mem_pow_iff_coeff_eq_zero (p - r) (Nat.ceil q + 1)).1
    (hmem (Nat.ceil q + 1)) q hq
  change p.coeff q - r.coeff q = 0 at hzero
  exact sub_eq_zero.1 hzero

/-- The image of `t` in the completion at the radical of `(t)` vanishes, since `t` lies in
every power of that radical. -/
private theorem of_radical_polynomialT_eq_zero (k : Type*) [Field k] :
    AdicCompletion.of (polynomialTIdeal k).radical (rationalPolynomial k)
      (polynomialT k) = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [AdicCompletion.evalₐ_of, _root_.map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [radical_polynomialTIdeal_pow k hn]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)

/-- **Stacks 0CKX.** The comparison map from the `(t)`-adic completion of `k[t^(ℚ≥0)]` to the
completion at the radical of `(t)` is not injective: it kills the nonzero element `t`. -/
@[stacks 0CKX "the comparison map is not injective"]
theorem not_injective_compareAlgHom_radical (k : Type*) [Field k] :
    ¬ Function.Injective
      (AdicCompletion.compareAlgHom k (polynomialTIdeal_pow_one_le_radical k)) := by
  intro hinj
  refine t_ne_zero k (hinj ?_)
  rw [_root_.map_zero, t, AdicCompletion.compareAlgHom_of, of_radical_polynomialT_eq_zero]

/-- **Stacks 0CKX.** The natural map from the `I`-adic completion to the `√I`-adic completion
of a ring can fail to be an isomorphism: for `I = (t)` in `k[t^(ℚ≥0)]` it is not bijective. -/
@[stacks 0CKX "the comparison map is not a ring isomorphism"]
theorem not_bijective_compareAlgHom_radical (k : Type*) [Field k] :
    ¬ Function.Bijective
      (AdicCompletion.compareAlgHom k (polynomialTIdeal_pow_one_le_radical k)) := fun h =>
  not_injective_compareAlgHom_radical k h.1

/-- **Stacks 0CKX.** The two completions are not isomorphic by any ring map at all: the
completion at the radical is the field `k`, while `t` is a nonzero non-unit of the `(t)`-adic
completion. -/
@[stacks 0CKX "the two completions are not isomorphic"]
theorem isEmpty_ringEquiv_adicCompletion_radical (k : Type*) [Field k] :
    IsEmpty (rationalPowerSeries k ≃+*
      AdicCompletion (polynomialTIdeal k).radical (rationalPolynomial k)) := by
  refine ⟨fun e => ?_⟩
  have he : rationalPowerSeries k ≃+* k := e.trans (radicalAdicCompletionEquiv k)
  have htu : IsUnit (t k) := by
    have h0 : he (t k) ≠ 0 := fun h => t_ne_zero k (by simpa using congrArg he.symm h)
    simpa using he.symm.toRingHom.isUnit_map (isUnit_iff_ne_zero.2 h0)
  have hmem := t_mem_maximalIdeal k
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
  exact hmem htu

end RationalPowerSeries

end

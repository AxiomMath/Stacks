module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.Basic
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.PlacesOver
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.RiemannRoch

/-!
# A character of the divisor group at a principal divisor, prime by prime

Let `K` be a function field over a finite field `k`, `y ∈ K` transcendental over `k`, `A = k[y]`
and `B` the integral closure of `A` in `K`. The zeros of `y` are the places of `K` at the primes
`P` of `B` above the prime `(y)` of `A`, and the order of `y` at such a place is the ramification
index `e(P | (y))`. Hence for a character `d` of the divisor group,
`∏_{ord_v y > 0} d_v ^ ord_v y = ∏_{P | (y)} d_P ^ e(P | (y))`
(`Stacks.Adeles.GlobalFunctionField.finsuppProd_sup_zero_principalDivisor`). The poles of `y` are
the zeros of `y⁻¹`, so the value of `d` at the principal divisor of `y` is the quotient of the
products for `y` and for `y⁻¹` (`Stacks.Adeles.GlobalFunctionField.finsuppProd_principalDivisor`).
This is the form in which the transfer computation of
`Stacks.Adeles.GlobalFunctionField.transfer_eq_finprod_frob_pow_ramificationIdx` enters the proof
of unramified reciprocity, with `y = η` and `y = η⁻¹`.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.placeValue` — `d` evaluated at the place of a nonzero prime.

## Main results

* `Stacks.Adeles.Place.ofHeightOneSpectrum_injective`.
* `Stacks.Adeles.GlobalFunctionField.finsuppProd_sup_zero_principalDivisor`.
* `Stacks.Adeles.GlobalFunctionField.finsuppProd_principalDivisor`.
-/

@[expose] public noncomputable section

open IsDedekindDomain Polynomial IntermediateField

universe u

namespace Stacks.Adeles

namespace Place

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [IsDedekindDomain B] [Algebra B K]
  [IsFractionRing B K]

/-- **Distinct height-one primes give distinct places.** -/
public theorem ofHeightOneSpectrum_injective :
    Function.Injective (ofHeightOneSpectrum (K := K) (B := B)) := by
  intro P P' h
  have hv : (P.valuation K).IsEquiv (P'.valuation K) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2 (congrArg Subtype.val h)
  ext b
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K),
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hv.lt_one_iff_lt_one]

end Place

namespace GlobalFunctionField

variable {K : Type u} [Field K] {𝒜 : Type*} [CommGroup 𝒜]

open Classical in
/-- The value of `d : Place K → 𝒜` at the place of a nonzero prime `P` of a Dedekind domain `B`
with fraction field `K`, and `1` at the other ideals. -/
public def placeValue {B : Type u} [CommRing B] [IsDedekindDomain B] [Algebra B K]
    [IsFractionRing B K] (d : Place K → 𝒜) (P : Ideal B) : 𝒜 :=
  if h : P.IsPrime ∧ P ≠ ⊥ then d (Place.ofHeightOneSpectrum ⟨P, h.1, h.2⟩) else 1

public theorem placeValue_of_heightOneSpectrum {B : Type u} [CommRing B] [IsDedekindDomain B]
    [Algebra B K] [IsFractionRing B K] (d : Place K → 𝒜) (P : HeightOneSpectrum B) :
    placeValue d P.asIdeal = d (Place.ofHeightOneSpectrum P) := by
  rw [placeValue, dif_pos ⟨P.isPrime, P.ne_bot⟩]

variable {k : Type u} [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- `y` as an element of `k[y]`. -/
public abbrev polyGen (y : K) : polySubalg k y := ⟨y, Algebra.self_mem_adjoin_singleton k y⟩

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] in
/-- For transcendental `y`, `y` is a prime element of `k[y]`. -/
public theorem prime_polyGen {y : K} (hy : Transcendental k y) : Prime (polyGen (k := k) y) := by
  have h := (MulEquiv.prime_iff (polySubalgEquiv hy).toMulEquiv).2 Polynomial.prime_X
  have hX : (polySubalgEquiv hy).toMulEquiv X = polyGen (k := k) y := by
    apply Subtype.ext
    simp
  rwa [hX] at h

/-- For transcendental `y`, the image of `y` in the integral closure of `k[y]` is nonzero. -/
private theorem algebraMap_polyGen_ne_zero {F : Type u} [Field F] [Algebra F K] {y : K}
    (hy : Transcendental F y) :
    algebraMap (polySubalg F y) (intClosure F y) (polyGen (k := F) y) ≠ 0 := fun h =>
  hy.ne_zero (by
    rw [← show algebraMap (intClosure F y) K (algebraMap (polySubalg F y) (intClosure F y)
      (polyGen (k := F) y)) = y from rfl, h, map_zero])

/-- The order of `y` at the place of a prime `Q` of the integral closure of `F[y]` is the
multiplicity of `Q` in `(y)`. -/
private theorem ord_ofHeightOneSpectrum_eq_multiplicity {F : Type u} [Field F] [Algebra F K]
    {y : K} (hy : Transcendental F y) [FiniteDimensional F⟮y⟯ K]
    (Q : HeightOneSpectrum (intClosure F y)) :
    (Place.ofHeightOneSpectrum (K := K) Q).ord y =
      multiplicity Q.asIdeal (Ideal.span {algebraMap (polySubalg F y) (intClosure F y)
        (polyGen (k := F) y)}) :=
  Place.ord_ofHeightOneSpectrum Q (algebraMap_polyGen_ne_zero hy)

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] in
variable (k) in
/-- At a prime of the integral closure of `k[y]` above `(y)`, the order of `y` is the
ramification index. -/
public theorem ord_ofHeightOneSpectrum_eq_ramificationIdx {y : K} (hy : Transcendental k y)
    [FiniteDimensional k⟮y⟯ K] (Q : HeightOneSpectrum (intClosure k y))
    (hQ : Q.asIdeal ∈ (Ideal.span {polyGen (k := k) y}).primesOver (intClosure k y)) :
    (Place.ofHeightOneSpectrum (K := K) Q).ord y =
      Q.asIdeal.ramificationIdx (polySubalg k y) := by
  set p : Ideal (polySubalg k y) := Ideal.span {polyGen (k := k) y}
  have hb0 := algebraMap_polyGen_ne_zero hy
  have hmapne : Ideal.map (algebraMap (polySubalg k y) (intClosure k y)) p ≠ ⊥ := by
    rwa [Ideal.map_span, Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot]
  have : Q.asIdeal.LiesOver p := hQ.2
  rw [ord_ofHeightOneSpectrum_eq_multiplicity hy Q,
    Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p _ hmapne,
    Ideal.map_span, Set.image_singleton,
    UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).irreducible
      (mt Ideal.span_singleton_eq_bot.1 hb0), normalize_eq]

variable (k) in
/-- Every zero of a transcendental `y` is the place of a prime of the integral closure of `k[y]`
above `(y)`. -/
public theorem exists_primesOver_of_ord_pos {y : K} (hy : Transcendental k y)
    [FiniteDimensional k⟮y⟯ K] (v : Place K) (hv : 0 < v.ord y) :
    ∃ Q : HeightOneSpectrum (intClosure k y),
      Q.asIdeal ∈ (Ideal.span {polyGen (k := k) y}).primesOver (intClosure k y) ∧
        Place.ofHeightOneSpectrum Q = v := by
  set A := polySubalg k y
  set B := intClosure k y
  set p : Ideal A := Ideal.span {polyGen (k := k) y}
  have hprime := prime_polyGen (k := k) hy
  have hpmax : p.IsMaximal := ((Ideal.span_singleton_prime hprime.ne_zero).2 hprime).isMaximal
    (by simpa [p] using hprime.ne_zero)
  obtain ⟨Q, rfl, -⟩ := exists_eq_ofHeightOneSpectrum_intClosure k y v
    ((Place.ord_nonneg_iff (isDiscrete k v) hy.ne_zero).1 hv.le)
  have hbQ : algebraMap A B (polyGen (k := k) y) ∈ Q.asIdeal := by
    rw [ord_ofHeightOneSpectrum_eq_multiplicity hy Q] at hv
    have h1 := (Int.natCast_pos.1 hv).ne'
    rwa [Ne, multiplicity_eq_zero, not_not, Ideal.dvd_span_singleton] at h1
  refine ⟨Q, ⟨Q.isPrime, ⟨?_⟩⟩, rfl⟩
  exact hpmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
    (by rwa [Ideal.span_le, Set.singleton_subset_iff])

variable (k) in
/-- **The zero part of `div y`, prime by prime.** For transcendental `y`,
`∏_{ord_v y > 0} d_v ^ ord_v y = ∏_{P | (y)} d_P ^ e(P | (y))`, `P` running over the primes of the
integral closure `B` of `A = k[y]` above `(y)`. -/
public theorem finsuppProd_sup_zero_principalDivisor {y : K} (hy : Transcendental k y)
    [FiniteDimensional k⟮y⟯ K] (d : Place K → 𝒜) :
    ((principalDivisor k K y ⊔ 0).prod fun v n => d v ^ n) =
      ∏ᶠ P ∈ (Ideal.span {polyGen (k := k) y}).primesOver (intClosure k y),
        placeValue d P ^ P.ramificationIdx (polySubalg k y) := by
  classical
  set A := polySubalg k y
  set B := intClosure k y
  set p : Ideal A := Ideal.span {polyGen (k := k) y}
  have hpbot : p ≠ ⊥ := by simpa [p] using (prime_polyGen (k := k) hy).ne_zero
  have hne : ∀ P ∈ p.primesOver B, P ≠ ⊥ := by
    rintro P ⟨-, hPp⟩ rfl
    apply hpbot
    rw [hPp.over, Ideal.under_def, ← RingHom.ker_eq_comap_bot, RingHom.ker_eq_bot_iff_eq_zero]
    exact fun a ha => Subtype.ext (congrArg (fun x : B => (x : K)) ha)
  have hval : ∀ Q : HeightOneSpectrum B, Q.asIdeal ∈ p.primesOver B →
      (principalDivisor k K y ⊔ 0) (Place.ofHeightOneSpectrum Q) = Q.asIdeal.ramificationIdx A := by
    intro Q hQ
    rw [Finsupp.sup_apply, Finsupp.coe_zero, Pi.zero_apply, principalDivisor_apply,
      ord_ofHeightOneSpectrum_eq_ramificationIdx k hy Q hQ]
    exact max_eq_left (Int.natCast_nonneg _)
  rw [Finsupp.prod, ← finprod_mem_coe_finset]
  symm
  -- First pass from ideals to height-one primes, then to places.
  have step1 : (∏ᶠ P ∈ p.primesOver B, placeValue d P ^ P.ramificationIdx A) =
      ∏ᶠ Q ∈ {Q : HeightOneSpectrum B | Q.asIdeal ∈ p.primesOver B},
        placeValue d Q.asIdeal ^ Q.asIdeal.ramificationIdx A :=
    (finprod_mem_eq_of_bijOn HeightOneSpectrum.asIdeal ⟨fun Q hQ => hQ,
      fun _ _ _ _ h => HeightOneSpectrum.ext h, fun P hP => ⟨⟨P, hP.1, hne P hP⟩, hP, rfl⟩⟩
      fun _ _ => rfl).symm
  rw [step1]
  refine finprod_mem_eq_of_bijOn (Place.ofHeightOneSpectrum (K := K)) ⟨?_,
    fun _ _ _ _ h => Place.ofHeightOneSpectrum_injective (K := K) (B := B) h, ?_⟩ ?_
  · -- Primes above `(y)` are zeros of `y`.
    intro Q hQ
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hval Q hQ, Nat.cast_ne_zero]
    have : Q.asIdeal.LiesOver p := hQ.2
    exact (Ideal.ramificationIdx_pos (S := B) Q.asIdeal A).ne'
  · -- Every zero of `y` is the place of a prime above `(y)`.
    intro v hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sup_apply, Finsupp.coe_zero,
      Pi.zero_apply, principalDivisor_apply] at hv
    exact exists_primesOver_of_ord_pos k hy v (by omega)
  · intro Q hQ
    rw [placeValue_of_heightOneSpectrum, hval Q hQ, zpow_natCast]

variable (k) in
/-- **A character of the divisor group at a principal divisor, prime by prime.** For `y`
transcendental over `k`, `∏_v d_v ^ ord_v y` is the quotient of
`∏_{P | (y)} d_P ^ e(P | (y))` (over the integral closure of `k[y]`) by
`∏_{P | (y⁻¹)} d_P ^ e(P | (y⁻¹))` (over the integral closure of `k[y⁻¹]`). -/
public theorem finsuppProd_principalDivisor {y : K} (hy : Transcendental k y)
    [FiniteDimensional k⟮y⟯ K] [FiniteDimensional k⟮y⁻¹⟯ K] (d : Place K → 𝒜) :
    ((principalDivisor k K y).prod fun v n => d v ^ n) =
      (∏ᶠ P ∈ (Ideal.span {polyGen (k := k) y}).primesOver (intClosure k y),
        placeValue d P ^ P.ramificationIdx (polySubalg k y)) /
      ∏ᶠ P ∈ (Ideal.span {polyGen (k := k) y⁻¹}).primesOver (intClosure k y⁻¹),
        placeValue d P ^ P.ramificationIdx (polySubalg k y⁻¹) := by
  have hy' : Transcendental k y⁻¹ := fun h => hy (IsAlgebraic.inv_iff.1 h)
  rw [← finsuppProd_sup_zero_principalDivisor k hy d,
    ← finsuppProd_sup_zero_principalDivisor k hy' d, eq_div_iff_mul_eq',
    ← Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  congr 1
  ext v
  rw [principalDivisor_inv k hy.ne_zero]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.sup_apply, Finsupp.coe_neg, Pi.neg_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  omega

end GlobalFunctionField

end Stacks.Adeles

end

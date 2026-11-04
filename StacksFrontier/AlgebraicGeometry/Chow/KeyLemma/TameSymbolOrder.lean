module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Defs
public import StacksFrontier.RingTheory.Lattice.Defs
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal

/-!
# The order of the tame symbol at a height-one prime

Let `(A, 𝔪)` be a two-dimensional Noetherian local ring and `a, b ∈ A` nonzerodivisors. For a
height-one prime `𝔮` of `A` the localization `A_𝔮` is a one-dimensional Noetherian local ring,
so it carries a tame symbol `∂_{A_𝔮}` in the sense of Stacks 0EAH — the data of
`Stacks.Chow.RegularTameSymbol` — and the quotient `A / 𝔮` is a one-dimensional Noetherian ring
whose fraction field is the residue field of `A_𝔮`. The summand of the reciprocity relation
Stacks 0EAW is therefore defined:

`ord_{A/𝔮}(∂_{A_𝔮}(a, b)) ∈ ℤ`.

This file defines that summand, proves that only finitely many height-one primes contribute to
it — which is the finiteness assertion of Stacks 0EAW — and establishes the arithmetic of the
summand that the proof of the reciprocity relation uses: it is additive in each argument, it is
skew, it vanishes on the diagonal, and at a prime where the two elements admit a simultaneous
power factorization `a = u π ^ e`, `b = v π ^ f` it is

`m (f ord_{A/𝔮}(ū) - e ord_{A/𝔮}(v̄))`,  `m = length_{A_𝔮}(A_𝔮 / π A_𝔮)`.

The source obtains that last formula from the construction of the symbol; here the symbol is
carried as data satisfying the four conditions Stacks 0EAL, 0EAM, 0EAN and 0EAP, and the formula
is derived from those four conditions alone, in
`Stacks.Chow.RegularTameSymbol.apply_eq_of_factorization`.

## Main definitions

* `Stacks.Chow.HeightOnePrime` — the height-one primes of a ring.
* `Stacks.Chow.heightOnePrimeEquivIdeal` — those primes read as points of the prime spectrum of
  height one and as prime ideals of height one.
* `Stacks.Chow.heightOneOrd` — the integer order of vanishing along `A / 𝔮` of a unit of the
  residue field of `A_𝔮`.
* `Stacks.Chow.tameSymbolOrderAt` — the summand `ord_{A/𝔮}(∂_{A_𝔮}(a, b))` of Stacks 0EAW.

## Main results

* `Stacks.Chow.RegularTameSymbol.apply_eq_of_factorization` — the value of a tame symbol on a
  simultaneous power factorization.
* `Stacks.Chow.finite_tameSymbolOrderAt_support` — the finiteness assertion of Stacks 0EAW.
* `Stacks.Chow.tameSymbolOrderAt_mul_left`, `Stacks.Chow.tameSymbolOrderAt_mul_right`,
  `Stacks.Chow.tameSymbolOrderAt_add_swap` — bilinearity and skewness of the summand.
* `Stacks.Chow.tameSymbolOrderAt_finsum_self_eq_zero` — the reciprocity relation on the
  diagonal.
* `Stacks.Chow.tameSymbolOrderAt_eq_of_factorization` — the summand at a prepared prime.

## Implementation notes

The nonzerodivisors of `A` are handled as the submonoid `nonZeroDivisors A`, matching
`Stacks.Chow.RegularTameSymbol`. The order of vanishing is Mathlib's `Ring.ordFrac`, taken
through the integer-valued `ordInt`; the two instances it needs, that `A / 𝔮` has Krull
dimension at most one and that the residue field of `A_𝔮` is a fraction field of `A / 𝔮`, come
from `Stacks.Chow.krullDimLE_quotient_of_height_eq_one` and from Mathlib. Because those
instances are produced from the dimension hypothesis rather than inferred, the order is
packaged as `Stacks.Chow.heightOneOrd`, whose arithmetic is then available without carrying
them.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Chow

section Symbol

variable {A : Type u} [CommRing A] [IsLocalRing A] (symb : RegularTameSymbol A)

/-- The symbol is multiplicative in the first argument, hence takes powers to powers. -/
theorem RegularTameSymbol.pow_left (a b : nonZeroDivisors A) (n : ℕ) :
    symb (a ^ n) b = symb a b ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, symb.map_mul_left, ih, pow_succ]

/-- The symbol is multiplicative in the second argument, hence takes powers to powers. -/
theorem RegularTameSymbol.pow_right (a b : nonZeroDivisors A) (n : ℕ) :
    symb a (b ^ n) = symb a b ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, symb.map_mul_right, ih, pow_succ]

omit [IsLocalRing A] in
/-- A unit has order of vanishing zero: the quotient by the unit ideal is trivial. -/
theorem ord_eq_zero_of_isUnit {x : A} (hx : IsUnit x) : Ring.ord A x = 0 := by
  rw [Ring.ord, Ideal.span_singleton_eq_top.mpr hx]
  simp [Module.length_eq_zero]

/-- **The tame symbol of two units is trivial.** By Stacks 0EAN the symbol of a unit against
`b` is the residue of that unit raised to `length_A(A / bA)`, and a unit has vanishing order. -/
theorem RegularTameSymbol.eq_one_of_isUnit {a b : nonZeroDivisors A}
    (ha : IsUnit (a : A)) (hb : IsUnit (b : A)) : symb a b = 1 := by
  rw [symb.unit_left a b ha.unit ha.unit_spec.symm, ord_eq_zero_of_isUnit hb]
  simp

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- **The tame symbol of a simultaneous power factorization.** If `a = u π ^ e` and
`b = v π ^ f` with `u`, `v` units of `A` and `π` a nonzerodivisor, then

`∂_A(a, b) = ((-1) ^ (e f) ū ^ f v̄ ^ (-e)) ^ m`,  `m = length_A(A / π A)`,

which is the value the proof of Stacks 0EAW uses at each contributing prime. In the source this
is read off the construction of the symbol; here the symbol is carried as data satisfying
Stacks 0EAL, 0EAM, 0EAN and 0EAP, and the formula is a consequence of those four properties
alone: bimultiplicativity expands the symbol into the four symbols of `u`, `v` and `π`, the
unit condition evaluates three of them, and the diagonal condition the fourth. -/
theorem RegularTameSymbol.apply_eq_of_factorization (p a b : nonZeroDivisors A) (u v : Aˣ)
    (e f : ℕ) (ha : (a : A) = u * (p : A) ^ e) (hb : (b : A) = v * (p : A) ^ f) :
    symb a b =
      ((-1) ^ (e * f) * Units.map (residue A).toMonoidHom u ^ f *
        (Units.map (residue A).toMonoidHom v)⁻¹ ^ e) ^ (Ring.ord A (p : A)).toNat := by
  set U : nonZeroDivisors A := ⟨(u : A), u.isUnit.mem_nonZeroDivisors⟩ with hU
  set V : nonZeroDivisors A := ⟨(v : A), v.isUnit.mem_nonZeroDivisors⟩ with hV
  have hA : a = U * p ^ e := Subtype.ext (by simpa [hU] using ha)
  have hB : b = V * p ^ f := Subtype.ext (by simpa [hV] using hb)
  have hUV : symb U V = 1 := symb.eq_one_of_isUnit u.isUnit v.isUnit
  have hUp : symb U p = Units.map (residue A).toMonoidHom u ^ (Ring.ord A (p : A)).toNat :=
    symb.unit_left U p u (by simp [hU])
  have hVp : symb V p = Units.map (residue A).toMonoidHom v ^ (Ring.ord A (p : A)).toNat :=
    symb.unit_left V p v (by simp [hV])
  have hpV : symb p V =
      (Units.map (residue A).toMonoidHom v ^ (Ring.ord A (p : A)).toNat)⁻¹ := by
    rw [symb.symm_eq_inv, hVp]
  rw [hA, hB, symb.map_mul_left, symb.map_mul_right, symb.map_mul_right,
    symb.pow_left, symb.pow_right, symb.pow_right, symb.pow_left, hUV, hUp, hpV, symb.self p]
  simp only [mul_pow, ← pow_mul, ← inv_pow, one_mul]
  simp only [mul_comm, mul_left_comm, mul_assoc]

end Symbol

section HeightOne

variable {A : Type u} [CommRing A]

/-- The height-one primes of a commutative ring. -/
abbrev HeightOnePrime (A : Type u) [CommRing A] :=
  {p : PrimeSpectrum A // p.asIdeal.height = 1}

/-- The height-one primes of a commutative ring `A`, described as points of `Spec A` of height
one and as prime ideals of `A` of height one. -/
def heightOnePrimeEquivIdeal :
    HeightOnePrime A ≃ {q : Ideal A // q.IsPrime ∧ q.height = 1} where
  toFun p := ⟨p.1.asIdeal, p.1.isPrime, p.2⟩
  invFun q := ⟨⟨q.1, q.2.1⟩, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Only finitely many height-one primes contain a fixed nonzerodivisor: such a prime is a
minimal prime of the principal ideal the element generates. -/
theorem finite_setOf_height_eq_one_mem [IsNoetherianRing A] {t : A}
    (ht : t ∈ nonZeroDivisors A) :
    {p : Ideal A | p.IsPrime ∧ p.height = 1 ∧ t ∈ p}.Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {t})).subset
    fun p hp => ?_
  have : p.IsPrime := hp.1
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).mpr hp.2.2) ?_
  rw [hp.2.1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors ht

/-- Only finitely many height-one primes, as points of the prime spectrum, contain a fixed
nonzerodivisor. -/
theorem finite_heightOnePrime_mem [IsNoetherianRing A] {t : A} (ht : t ∈ nonZeroDivisors A) :
    {p : HeightOnePrime A | t ∈ p.1.asIdeal}.Finite := by
  refine Set.Finite.of_finite_image ((finite_setOf_height_eq_one_mem ht).subset ?_)
    fun p _ q _ hpq => Subtype.ext (PrimeSpectrum.ext hpq)
  rintro I ⟨p, hp, rfl⟩
  exact ⟨p.1.isPrime, p.2, hp⟩

/-- The localization of a Noetherian ring at a height-one prime has Krull dimension at most
one, which is what a tame symbol in the sense of Stacks 0EAH requires of it. -/
theorem krullDimLE_localization_of_height_eq_one [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    Ring.KrullDimLE 1 (Localization.AtPrime p) := by
  rw [Ring.krullDimLE_iff,
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp]
  rfl

/-- The quotient of a two-dimensional ring by a height-one prime has Krull dimension at most
one, which is what the order of vanishing along it requires: the height and the coheight of a
prime add to at most the Krull dimension, and the coheight is the dimension of the quotient. -/
theorem krullDimLE_quotient_of_height_eq_one (hdim : ringKrullDim A = 2)
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    Ring.KrullDimLE 1 (A ⧸ p) := by
  let P : PrimeSpectrum A := ⟨p, inferInstance⟩
  rw [Ring.krullDimLE_iff, ← coheight_eq_ringKrullDim_quotient P]
  have h : (Order.height P : WithBot ℕ∞) + (Order.coheight P : WithBot ℕ∞) ≤
      (2 : WithBot ℕ∞) := by
    calc
      _ ≤ ringKrullDim A := by
        have : Nonempty (PrimeSpectrum A) := ⟨P⟩
        rw [← WithBot.coe_add, ringKrullDim,
          Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
        exact WithBot.coe_le_coe.mpr
          (le_iSup (fun x : PrimeSpectrum A => Order.height x + Order.coheight x) P)
      _ = 2 := hdim
  rw [← PrimeSpectrum.height_eq_orderHeight] at h
  change ((p.height : WithBot ℕ∞) + _ ≤ _) at h
  rw [hp, ← WithBot.coe_add] at h
  have h' : (1 : ℕ∞) + Order.coheight P ≤ 1 + 1 := by
    rw [one_add_one_eq_two]
    exact WithBot.coe_le_coe.mp h
  exact WithBot.coe_le_coe.mpr
    ((ENat.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp h')

/-- A nonzerodivisor stays a nonzerodivisor in a localization. -/
def toLocalizationNonZeroDivisor (p : Ideal A) [p.IsPrime] (a : nonZeroDivisors A) :
    nonZeroDivisors (Localization.AtPrime p) :=
  ⟨algebraMap A (Localization.AtPrime p) (a : A),
    IsLocalization.nonZeroDivisors_le_comap (M := p.primeCompl)
      (S := Localization.AtPrime p) a.2⟩

/-- The map to the localization sends a product to the product of the images. -/
private theorem toLocalizationNonZeroDivisor_mul (p : Ideal A) [p.IsPrime]
    (a a' : nonZeroDivisors A) :
    toLocalizationNonZeroDivisor p (a * a') =
      toLocalizationNonZeroDivisor p a * toLocalizationNonZeroDivisor p a' :=
  Subtype.ext (by simp [toLocalizationNonZeroDivisor])

/-- The map to the localization sends `1` to `1`. -/
private theorem toLocalizationNonZeroDivisor_one (p : Ideal A) [p.IsPrime] :
    toLocalizationNonZeroDivisor p 1 = 1 :=
  Subtype.ext (by simp [toLocalizationNonZeroDivisor])

/-- A nonzerodivisor outside a prime becomes a unit in the localization there. -/
theorem isUnit_toLocalizationNonZeroDivisor (p : Ideal A) [p.IsPrime]
    (a : nonZeroDivisors A) (ha : (a : A) ∉ p) :
    IsUnit ((toLocalizationNonZeroDivisor p a : Localization.AtPrime p)) :=
  IsLocalization.map_units (Localization.AtPrime p) (⟨(a : A), ha⟩ : p.primeCompl)

variable [IsNoetherianRing A]

/-- **The order of vanishing along a height-one prime** of a unit of the residue field of the
localization there. For a two-dimensional Noetherian ring `A` and a height-one prime `𝔮`, the
residue field of `A_𝔮` is a fraction field of the one-dimensional ring `A / 𝔮`, so Mathlib's
order of vanishing is defined on it; this is its integer value. -/
noncomputable def heightOneOrd (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (x : (ResidueField (Localization.AtPrime p.1.asIdeal))ˣ) : ℤ :=
  let _ : Ring.KrullDimLE 1 (A ⧸ p.1.asIdeal) :=
    krullDimLE_quotient_of_height_eq_one hdim p.1.asIdeal p.2
  ordInt (A ⧸ p.1.asIdeal) (x : ResidueField (Localization.AtPrime p.1.asIdeal)) x.ne_zero

/-- The order of vanishing along a height-one prime is additive: the order of `x * y` is the
sum of the orders of `x` and `y`. -/
theorem heightOneOrd_mul (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (x y : (ResidueField (Localization.AtPrime p.1.asIdeal))ˣ) :
    heightOneOrd hdim p (x * y) = heightOneOrd hdim p x + heightOneOrd hdim p y := by
  let _ : Ring.KrullDimLE 1 (A ⧸ p.1.asIdeal) :=
    krullDimLE_quotient_of_height_eq_one hdim p.1.asIdeal p.2
  exact ordInt_mul (A ⧸ p.1.asIdeal) (x : ResidueField (Localization.AtPrime p.1.asIdeal))
    (y : ResidueField (Localization.AtPrime p.1.asIdeal)) x.ne_zero y.ne_zero

/-- The order of vanishing of `1` is zero. -/
@[simp]
theorem heightOneOrd_one (hdim : ringKrullDim A = 2) (p : HeightOnePrime A) :
    heightOneOrd hdim p 1 = 0 := by
  have h := heightOneOrd_mul hdim p 1 1
  rw [one_mul] at h
  linarith

/-- The order of vanishing of `x⁻¹` is the negative of the order of vanishing of `x`. -/
theorem heightOneOrd_inv (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (x : (ResidueField (Localization.AtPrime p.1.asIdeal))ˣ) :
    heightOneOrd hdim p x⁻¹ = - heightOneOrd hdim p x := by
  have h := heightOneOrd_mul hdim p x x⁻¹
  rw [mul_inv_cancel, heightOneOrd_one] at h
  linarith

/-- The order of vanishing of `x ^ n` is `n` times the order of vanishing of `x`. -/
theorem heightOneOrd_pow (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (x : (ResidueField (Localization.AtPrime p.1.asIdeal))ˣ) (n : ℕ) :
    heightOneOrd hdim p (x ^ n) = n * heightOneOrd hdim p x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, heightOneOrd_mul, ih]
    push_cast
    ring

/-- The order of vanishing of `-1` is zero: it is a root of unity. -/
@[simp]
theorem heightOneOrd_neg_one (hdim : ringKrullDim A = 2) (p : HeightOnePrime A) :
    heightOneOrd hdim p (-1) = 0 := by
  have h := heightOneOrd_mul hdim p (-1) (-1)
  rw [neg_mul_neg, one_mul, heightOneOrd_one] at h
  linarith

/-- **The summand of Stacks 0EAW.** For a two-dimensional Noetherian ring `A`, a height-one
prime `𝔮` and a tame symbol `∂_{A_𝔮}` on the localization `A_𝔮`, this is the order of vanishing
along `A / 𝔮` of `∂_{A_𝔮}(a, b)`: an element of the residue field of `A_𝔮`, which is a fraction
field of the one-dimensional ring `A / 𝔮`. -/
noncomputable def tameSymbolOrderAt (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) : ℤ :=
  heightOneOrd hdim p
    (symb (toLocalizationNonZeroDivisor p.1.asIdeal a)
      (toLocalizationNonZeroDivisor p.1.asIdeal b))

/-- **At a height-one prime avoiding both arguments the summand vanishes.** The two
nonzerodivisors become units of `A_𝔮`, so the tame symbol is `1` there. -/
theorem tameSymbolOrderAt_eq_zero (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) (a b : nonZeroDivisors A)
    (ha : (a : A) ∉ p.1.asIdeal) (hb : (b : A) ∉ p.1.asIdeal) :
    tameSymbolOrderAt hdim p symb a b = 0 := by
  rw [tameSymbolOrderAt,
    symb.eq_one_of_isUnit (isUnit_toLocalizationNonZeroDivisor p.1.asIdeal a ha)
      (isUnit_toLocalizationNonZeroDivisor p.1.asIdeal b hb),
    heightOneOrd_one]

/-- **Stacks 0EAW, finiteness of the sum.** For two nonzerodivisors of a two-dimensional
Noetherian ring, only finitely many height-one primes contribute a nonzero tame-symbol order:
away from the finitely many height-one primes containing `a` or `b`, both become units of the
localization and the symbol is trivial. -/
theorem finite_tameSymbolOrderAt_support (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) :
    {p : HeightOnePrime A | tameSymbolOrderAt hdim p (symb p) a b ≠ 0}.Finite :=
  ((finite_heightOnePrime_mem a.2).union (finite_heightOnePrime_mem b.2)).subset
    fun p hp => by_contra fun hmem => hp (tameSymbolOrderAt_eq_zero hdim p (symb p) a b
      (hmem ∘ Or.inl) (hmem ∘ Or.inr))

/-- The summand of Stacks 0EAW is additive in its first argument, by Stacks 0EAL. -/
theorem tameSymbolOrderAt_mul_left (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a a' b : nonZeroDivisors A) :
    tameSymbolOrderAt hdim p symb (a * a') b =
      tameSymbolOrderAt hdim p symb a b + tameSymbolOrderAt hdim p symb a' b := by
  rw [tameSymbolOrderAt, tameSymbolOrderAt, tameSymbolOrderAt,
    toLocalizationNonZeroDivisor_mul, symb.map_mul_left, heightOneOrd_mul]

/-- The summand of Stacks 0EAW is additive in its second argument, by Stacks 0EAL. -/
theorem tameSymbolOrderAt_mul_right (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b b' : nonZeroDivisors A) :
    tameSymbolOrderAt hdim p symb a (b * b') =
      tameSymbolOrderAt hdim p symb a b + tameSymbolOrderAt hdim p symb a b' := by
  rw [tameSymbolOrderAt, tameSymbolOrderAt, tameSymbolOrderAt,
    toLocalizationNonZeroDivisor_mul, symb.map_mul_right, heightOneOrd_mul]

/-- The tame-symbol order vanishes when the first argument is `1`. -/
@[simp]
theorem tameSymbolOrderAt_one_left (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) (b : nonZeroDivisors A) :
    tameSymbolOrderAt hdim p symb 1 b = 0 := by
  rw [tameSymbolOrderAt,
    toLocalizationNonZeroDivisor_one,
    symb.one_left, heightOneOrd_one]

/-- The tame-symbol order vanishes when the second argument is `1`. -/
@[simp]
theorem tameSymbolOrderAt_one_right (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) (a : nonZeroDivisors A) :
    tameSymbolOrderAt hdim p symb a 1 = 0 := by
  rw [tameSymbolOrderAt,
    toLocalizationNonZeroDivisor_one,
    symb.one_right, heightOneOrd_one]

/-- **The summand of Stacks 0EAW is skew.** By Stacks 0EAJ the symbol satisfies
`∂(a, b) ∂(b, a) = 1`, so the two orders are opposite. -/
theorem tameSymbolOrderAt_add_swap (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) (a b : nonZeroDivisors A) :
    tameSymbolOrderAt hdim p symb a b + tameSymbolOrderAt hdim p symb b a = 0 := by
  let _ : Ring.KrullDimLE 1 (Localization.AtPrime p.1.asIdeal) :=
    krullDimLE_localization_of_height_eq_one p.1.asIdeal p.2
  rw [tameSymbolOrderAt, tameSymbolOrderAt, ← heightOneOrd_mul, symb.skew, heightOneOrd_one]

/-- **The diagonal summand of Stacks 0EAW vanishes.** By Stacks 0EAM the symbol of `a` with
itself is `(-1) ^ length(A_𝔮 / a A_𝔮)`, a root of unity. -/
theorem tameSymbolOrderAt_self (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal)) (a : nonZeroDivisors A) :
    tameSymbolOrderAt hdim p symb a a = 0 := by
  rw [tameSymbolOrderAt, symb.self, heightOneOrd_pow, heightOneOrd_neg_one, mul_zero]

/-- **The diagonal case of the vanishing sum of Stacks 0EAW**, unconditionally: the tame symbol
of a nonzerodivisor with itself has order zero at every height-one prime. -/
theorem tameSymbolOrderAt_finsum_self_eq_zero (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a : nonZeroDivisors A) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a a = 0 := by
  rw [finsum_congr (fun p => tameSymbolOrderAt_self hdim p (symb p) a), finsum_zero]

/-- **The summand of Stacks 0EAW at a prepared prime.** If in `A_𝔮` the two nonzerodivisors
factor simultaneously as `a = u π ^ e` and `b = v π ^ f`, with `u`, `v` units of `A_𝔮` and `π` a
nonzerodivisor, then

`ord_{A/𝔮}(∂_{A_𝔮}(a, b)) = m (f ord_{A/𝔮}(ū) - e ord_{A/𝔮}(v̄))`,
`m = length(A_𝔮 / π A_𝔮)`.

This is the evaluation the proof of Stacks 0EAW performs at each of the finitely many
contributing primes: the `(-1) ^ (e f)` factor is a root of unity and drops out, and what is
left is the order of the unit parts. -/
theorem tameSymbolOrderAt_eq_of_factorization (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (π : nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
    (u v : (Localization.AtPrime p.1.asIdeal)ˣ) (e f : ℕ)
    (ha : (toLocalizationNonZeroDivisor p.1.asIdeal a :
      Localization.AtPrime p.1.asIdeal) = u * (π : Localization.AtPrime p.1.asIdeal) ^ e)
    (hb : (toLocalizationNonZeroDivisor p.1.asIdeal b :
      Localization.AtPrime p.1.asIdeal) = v * (π : Localization.AtPrime p.1.asIdeal) ^ f) :
    tameSymbolOrderAt hdim p symb a b =
      (Ring.ord (Localization.AtPrime p.1.asIdeal)
          (π : Localization.AtPrime p.1.asIdeal)).toNat *
        (f * heightOneOrd hdim p
            (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom u) -
          e * heightOneOrd hdim p
            (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom v)) := by
  let _ : Ring.KrullDimLE 1 (Localization.AtPrime p.1.asIdeal) :=
    krullDimLE_localization_of_height_eq_one p.1.asIdeal p.2
  rw [tameSymbolOrderAt, symb.apply_eq_of_factorization π _ _ u v e f ha hb,
    heightOneOrd_pow, heightOneOrd_mul, heightOneOrd_mul, heightOneOrd_pow, heightOneOrd_pow,
    heightOneOrd_pow, heightOneOrd_neg_one, heightOneOrd_inv]
  ring

end HeightOne

end Stacks.Chow

end

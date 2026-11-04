module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.Vector
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.PolynomialUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable

/-!
# Divided powers after adjoining an even variable

Let `A` be a strictly graded-commutative graded `R`-algebra with a divided power structure `γ`
on its positive even part, and let `d > 0` be even. The algebra `A⟨T⟩` obtained by adjoining a
divided-power variable of degree `d` is built in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable`. This file develops the
arithmetic of the coefficients occurring in the divided powers of `A⟨T⟩` and the coefficientwise
description of its positive even part.

## Main definitions

* `DividedPowers.TateResolution.dividedPowerMonomialCoefficient` — the natural number
  `(n i)! / (n! (i!)ⁿ)` occurring in `γₙ(T⁽ⁱ⁾)`.
* `DividedPowers.TateResolution.EvenVariableAlgebra.monomialDividedPower` — the divided power
  `γₙ(x T⁽ⁱ⁾) = c(n, i) xⁿ T⁽ⁿⁱ⁾` of a single divided-power monomial.
* `DividedPowers.TateResolution.EvenVariableAlgebra.positivePolynomialDividedPower` — the
  explicit finite multinomial expansion of a divided power of a polynomial all of whose terms
  have positive variable exponent.

## Main results

* `DividedPowers.TateResolution.dividedPowerMonomialCoefficient_eq_uniformBell` identifies the
  coefficient with Mathlib's `Nat.uniformBell`, and
  `DividedPowers.TateResolution.dividedPowerMonomialCoefficient_mul_factorial` is the
  integrality statement that makes the coefficient a natural number.
* `DividedPowers.TateResolution.dividedPowerMonomialCoefficient_binomial` is the identity forced
  by the divided-power binomial axiom on a single monomial `x T⁽ⁱ⁾`, and
  `DividedPowers.TateResolution.dividedPowerMonomialCoefficient_comp` is the identity forced by
  the composition axiom.
* `DividedPowers.TateResolution.EvenVariableAlgebra.monomialDividedPower_add` and
  `DividedPowers.TateResolution.EvenVariableAlgebra.monomialDividedPower_comp` are those two
  identities transported into `A⟨T⟩`: the divided-power binomial formula and the composition
  formula for a single divided-power monomial.
* `DividedPowers.TateResolution.EvenVariableAlgebra.mem_positiveEvenPart_iff` describes the
  positive even part of `A⟨T⟩` coefficientwise: the constant coefficient is positive even and
  every other coefficient is even.

## Implementation notes

The second half of this file opens the construction of the divided power structure on
`A⟨T⟩`, which is completed in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers.Structure`: it
proves `DividedPowers.TateResolution.evenPart_pow_mem` and makes the even part of `A` a
commutative subalgebra, which together with the positive even part and `γ` is a divided power
ring in the sense of Tag 07GU. Those auxiliaries are private.

**Deviation from the source.** Tag 09PI states the rule `γₙ(T⁽ⁱ⁾) = T⁽ⁿⁱ⁾` for the divided
powers of the formal monomials. That printed rule contradicts the divided-power composition
axiom. Indeed `T⁽ⁱ⁾ = γᵢ(T)`, so the composition axiom
`γₙ(γᵢ(x)) = ((n i)! / (n! (i!)ⁿ)) γ_{n i}(x)` forces

```
γₙ(T⁽ⁱ⁾) = ((n i)! / (n! (i!)ⁿ)) · T⁽ⁿⁱ⁾,
```

whose coefficient is `1` only when `n ≤ 1` or `i ≤ 1`; already `γ₂(T⁽²⁾) = 3 T⁽⁴⁾`. The same
coefficients are missing from the source's displayed expansion
`γₙ(∑_{i>0} xᵢ T⁽ⁱ⁾) = ∑ ∏ xᵢ^{eᵢ} T^{(i eᵢ)}`. We formalize the axiom-consistent version
throughout, with the forced coefficient
`DividedPowers.TateResolution.dividedPowerMonomialCoefficient`, since the composition axiom is
load-bearing for every downstream use of the construction. The coefficient agrees with Mathlib's
`Nat.uniformBell` for positive `i`, which is also the coefficient already appearing in the
`dpow_dpow` field of
`DividedPowers.TateResolution.DividedPowerStructure`.

## References

* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

/-- The coefficient `(n i)! / (n! (i!)ⁿ)` forced on `γₙ(T⁽ⁱ⁾)` by the divided-power composition
axiom, in place of the source's printed coefficient `1`. -/
public abbrev dividedPowerMonomialCoefficient (n i : ℕ) : ℕ :=
  (n * i).factorial / (n.factorial * i.factorial ^ n)

/-- For a positive variable exponent the forced coefficient is Mathlib's `Nat.uniformBell`. -/
public theorem dividedPowerMonomialCoefficient_eq_uniformBell (n : ℕ) {i : ℕ} (hi : i ≠ 0) :
    dividedPowerMonomialCoefficient n i = Nat.uniformBell n i := by
  rw [Nat.uniformBell_eq_div n hi, dividedPowerMonomialCoefficient,
    mul_comm (Nat.factorial n) (Nat.factorial i ^ n)]

/-- Integrality of the forced coefficient: the displayed quotient is exact. This is what makes
`dividedPowerMonomialCoefficient` a natural number, and hence makes the divided powers of the
formal monomials definable over an arbitrary base ring. -/
public theorem dividedPowerMonomialCoefficient_mul_factorial (n : ℕ) {i : ℕ} (hi : i ≠ 0) :
    dividedPowerMonomialCoefficient n i * (n.factorial * i.factorial ^ n) =
      (n * i).factorial := by
  rw [dividedPowerMonomialCoefficient_eq_uniformBell n hi,
    mul_comm (Nat.factorial n) (Nat.factorial i ^ n), ← mul_assoc]
  exact Nat.uniformBell_mul_eq n hi

/-- The denominator of the forced coefficient divides its numerator. -/
public theorem factorial_mul_pow_dvd_factorial (n : ℕ) {i : ℕ} (hi : i ≠ 0) :
    n.factorial * i.factorial ^ n ∣ (n * i).factorial :=
  Dvd.intro_left _ (dividedPowerMonomialCoefficient_mul_factorial n hi)

/-- The forced coefficient `c(0, i)` equals `1`. -/
@[simp] public theorem dividedPowerMonomialCoefficient_zero_left (i : ℕ) :
    dividedPowerMonomialCoefficient 0 i = 1 := by
  simp [dividedPowerMonomialCoefficient]

/-- The forced coefficient `c(1, i)` equals `1`. -/
@[simp] public theorem dividedPowerMonomialCoefficient_one_left (i : ℕ) :
    dividedPowerMonomialCoefficient 1 i = 1 := by
  simp only [dividedPowerMonomialCoefficient, one_mul, Nat.factorial_one, pow_one]
  exact Nat.div_self (Nat.factorial_pos i)

/-- The forced coefficient `c(n, 1)` equals `1`. -/
@[simp] public theorem dividedPowerMonomialCoefficient_one_right (n : ℕ) :
    dividedPowerMonomialCoefficient n 1 = 1 := by
  simp only [dividedPowerMonomialCoefficient, mul_one, Nat.factorial_one, one_pow]
  exact Nat.div_self (Nat.factorial_pos n)

/-- The forced coefficient is positive for a positive variable exponent. -/
public theorem dividedPowerMonomialCoefficient_pos (n : ℕ) {i : ℕ} (hi : i ≠ 0) :
    0 < dividedPowerMonomialCoefficient n i := by
  rcases Nat.eq_zero_or_pos (dividedPowerMonomialCoefficient n i) with h | h
  · have := dividedPowerMonomialCoefficient_mul_factorial n hi
    rw [h, zero_mul] at this
    exact absurd this.symm (Nat.factorial_pos _).ne'
  · exact h

/-- The identity forced by the divided-power binomial axiom on a single monomial `x T⁽ⁱ⁾`:
expanding `γ_{a+b}((x + y) T⁽ⁱ⁾)` by the ordinary binomial theorem must agree with the
convolution `∑ γₐ(x T⁽ⁱ⁾) γ_b(y T⁽ⁱ⁾)`, whose `T`-monomials multiply with a binomial
coefficient of their own. -/
public theorem dividedPowerMonomialCoefficient_binomial {i : ℕ} (hi : i ≠ 0) (a b : ℕ) :
    dividedPowerMonomialCoefficient (a + b) i * Nat.choose (a + b) a =
      dividedPowerMonomialCoefficient a i * dividedPowerMonomialCoefficient b i *
        Nat.choose ((a + b) * i) (a * i) := by
  have hpos : 0 < a.factorial * b.factorial * i.factorial ^ (a + b) := by positivity
  have hchoose : Nat.choose (a + b) a * a.factorial * b.factorial = (a + b).factorial := by
    simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  have hchoose2 : Nat.choose ((a + b) * i) (a * i) * (a * i).factorial * (b * i).factorial =
      ((a + b) * i).factorial := by
    have hle : a * i ≤ (a + b) * i := Nat.mul_le_mul_right i (Nat.le_add_right a b)
    have hsub : (a + b) * i - a * i = b * i := by
      rw [Nat.add_mul]
      omega
    simpa [hsub] using Nat.choose_mul_factorial_mul_factorial hle
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc dividedPowerMonomialCoefficient (a + b) i * Nat.choose (a + b) a *
        (a.factorial * b.factorial * i.factorial ^ (a + b))
      = dividedPowerMonomialCoefficient (a + b) i *
          ((a + b).factorial * i.factorial ^ (a + b)) := by rw [← hchoose]; ring
    _ = ((a + b) * i).factorial := dividedPowerMonomialCoefficient_mul_factorial (a + b) hi
    _ = dividedPowerMonomialCoefficient a i * dividedPowerMonomialCoefficient b i *
          Nat.choose ((a + b) * i) (a * i) *
          (a.factorial * b.factorial * i.factorial ^ (a + b)) := by
        rw [← hchoose2, ← dividedPowerMonomialCoefficient_mul_factorial a hi,
          ← dividedPowerMonomialCoefficient_mul_factorial b hi]
        ring

/-- The identity forced by the divided-power composition axiom on the formal monomials:
`γₙ(γₘ(T⁽ⁱ⁾))` computed through `γₘ(T⁽ⁱ⁾) = c(m, i) T⁽ᵐⁱ⁾` must agree with
`c(n, m) γ_{nm}(T⁽ⁱ⁾)`. -/
public theorem dividedPowerMonomialCoefficient_comp {i m : ℕ} (hi : i ≠ 0) (hm : m ≠ 0)
    (n : ℕ) :
    dividedPowerMonomialCoefficient m i ^ n * dividedPowerMonomialCoefficient n (m * i) =
      dividedPowerMonomialCoefficient n m * dividedPowerMonomialCoefficient (n * m) i := by
  have hmi : m * i ≠ 0 := Nat.mul_ne_zero hm hi
  have hpos : 0 < n.factorial * m.factorial ^ n * i.factorial ^ (n * m) := by positivity
  have hpow : (dividedPowerMonomialCoefficient m i * (m.factorial * i.factorial ^ m)) ^ n =
      ((m * i).factorial) ^ n := by
    rw [dividedPowerMonomialCoefficient_mul_factorial m hi]
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc dividedPowerMonomialCoefficient m i ^ n * dividedPowerMonomialCoefficient n (m * i) *
        (n.factorial * m.factorial ^ n * i.factorial ^ (n * m))
      = dividedPowerMonomialCoefficient n (m * i) *
          (n.factorial * (m * i).factorial ^ n) := by
        rw [← hpow]
        ring
    _ = (n * (m * i)).factorial := dividedPowerMonomialCoefficient_mul_factorial n hmi
    _ = ((n * m) * i).factorial := by rw [mul_assoc]
    _ = dividedPowerMonomialCoefficient n m * dividedPowerMonomialCoefficient (n * m) i *
          (n.factorial * m.factorial ^ n * i.factorial ^ (n * m)) := by
        rw [← dividedPowerMonomialCoefficient_mul_factorial (n * m) hi,
          ← dividedPowerMonomialCoefficient_mul_factorial n hm]
        ring

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

namespace EvenVariableAlgebra

open scoped BigOperators

/-- Scaling a divided-power monomial by a natural number scales its coefficient. -/
@[simp] public theorem nsmul_monomial (k n : ℕ) (a : A) :
    k • monomial (A := A) n a = monomial n (k • a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, succ_nsmul, monomial_add]

/-- A natural number scalar can be pulled out of a power, since natural number scalars act
through the central image of `ℕ`. -/
public theorem nsmul_pow (c : ℕ) (y : A) (n : ℕ) : (c • y) ^ n = c ^ n • y ^ n := by
  simp only [nsmul_eq_mul, Nat.cast_pow]
  exact (Nat.cast_commute c y).mul_pow n

/-- The divided power `γₙ(x T⁽ⁱ⁾) = c(n, i) xⁿ T⁽ⁿⁱ⁾` of a single divided-power monomial, with
the coefficient `c` forced by the composition axiom. -/
public noncomputable def monomialDividedPower (n i : ℕ) (x : A) : EvenVariableAlgebra A :=
  monomial (n * i) (dividedPowerMonomialCoefficient n i • x ^ n)

/-- The zeroth divided power `γ₀(x T⁽ⁱ⁾)` is `1`. -/
@[simp] public theorem monomialDividedPower_zero_left (i : ℕ) (x : A) :
    monomialDividedPower 0 i x = 1 := by
  unfold monomialDividedPower
  simp only [zero_mul, dividedPowerMonomialCoefficient_zero_left, pow_zero, one_smul]
  rfl

/-- The first divided power `γ₁(x T⁽ⁱ⁾)` is the monomial `x T⁽ⁱ⁾` itself. -/
@[simp] public theorem monomialDividedPower_one_left (i : ℕ) (x : A) :
    monomialDividedPower 1 i x = monomial i x := by
  unfold monomialDividedPower
  simp only [one_mul, dividedPowerMonomialCoefficient_one_left, pow_one, one_smul]

/-- The product of two divided-power monomials of the same variable exponent. -/
public theorem monomialDividedPower_mul (i a b : ℕ) (x y : A) :
    monomialDividedPower a i x * monomialDividedPower b i y =
      monomial ((a + b) * i)
        ((Nat.choose ((a + b) * i) (a * i) * dividedPowerMonomialCoefficient a i *
            dividedPowerMonomialCoefficient b i) • (x ^ a * y ^ b)) := by
  unfold monomialDividedPower
  rw [monomial_mul_monomial, show a * i + b * i = (a + b) * i from by ring,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul]

/-- The divided-power binomial identity on a single divided-power monomial. This is the
monomial case of the `dpow_add` axiom, and it is exactly where the coefficient forced by the
composition axiom is needed: with the source's printed coefficient `1` the identity fails. -/
public theorem monomialDividedPower_add {i : ℕ} (hi : i ≠ 0) (n : ℕ) {x y : A}
    (h : Commute x y) :
    monomialDividedPower n i (x + y) =
      ∑ p ∈ Finset.antidiagonal n,
        monomialDividedPower p.1 i x * monomialDividedPower p.2 i y := by
  classical
  have hmono : ∀ f : ℕ × ℕ → A,
      monomial (A := A) (n * i) (∑ p ∈ Finset.antidiagonal n, f p) =
        ∑ p ∈ Finset.antidiagonal n, monomial (n * i) (f p) := fun f =>
    map_sum (show A →+ EvenVariableAlgebra A from
      { toFun := monomial (n * i), map_zero' := monomial_zero _,
        map_add' := monomial_add _ }) f (Finset.antidiagonal n)
  have hL : monomialDividedPower n i (x + y) =
      ∑ p ∈ Finset.antidiagonal n,
        monomial (n * i)
          ((dividedPowerMonomialCoefficient n i * Nat.choose n p.1) • (x ^ p.1 * y ^ p.2)) := by
    unfold monomialDividedPower
    rw [h.add_pow' n, Finset.smul_sum, hmono]
    exact Finset.sum_congr rfl fun p _ => by rw [smul_smul]
  rw [hL]
  refine Finset.sum_congr rfl fun ⟨a, b⟩ hp => ?_
  obtain rfl : a + b = n := Finset.mem_antidiagonal.mp hp
  rw [monomialDividedPower_mul]
  congr 1
  rw [dividedPowerMonomialCoefficient_binomial hi]
  congr 1
  ring

/-- The divided-power composition identity on a single divided-power monomial: applying the
`n`th divided power to `γₘ(x T⁽ⁱ⁾) = c(m, i) xᵐ T⁽ᵐⁱ⁾` produces `c(n, m) γ_{nm}(x T⁽ⁱ⁾)`. This
is the monomial case of the `dpow_dpow` axiom. -/
public theorem monomialDividedPower_comp {i m : ℕ} (hi : i ≠ 0) (hm : m ≠ 0) (n : ℕ) (x : A) :
    monomialDividedPower n (m * i) (dividedPowerMonomialCoefficient m i • x ^ m) =
      monomial (n * m * i)
        ((dividedPowerMonomialCoefficient n m *
          dividedPowerMonomialCoefficient (n * m) i) • x ^ (n * m)) := by
  have hc : dividedPowerMonomialCoefficient n (m * i) *
      dividedPowerMonomialCoefficient m i ^ n =
        dividedPowerMonomialCoefficient n m * dividedPowerMonomialCoefficient (n * m) i := by
    rw [mul_comm]
    exact dividedPowerMonomialCoefficient_comp hi hm n
  unfold monomialDividedPower
  rw [nsmul_pow, smul_smul, ← pow_mul, show n * (m * i) = n * m * i from by ring,
    show m * n = n * m from by ring, hc]

end EvenVariableAlgebra

section PositiveEvenPart

variable {𝒜 : ℕ → Submodule R A}

namespace EvenVariableAlgebra

/-- A divided-power monomial of positive variable exponent and even coefficient lies in the
positive even part of `A⟨T⟩`, because the new variable has positive even degree. -/
public theorem monomial_mem_positiveEvenPart {d : ℕ} (hdeven : Even d) (hd : 0 < d)
    {i : ℕ} (hi : 0 < i) {a : A} (ha : a ∈ evenPart 𝒜) :
    monomial i a ∈ positiveEvenPart (grade 𝒜 d) := by
  obtain ⟨d₀, hdd⟩ := hdeven
  have hd₀ : 0 < d₀ := by omega
  have hik : i * d = 2 * (i * d₀) := by rw [hdd]; ring
  have hposk : 0 < i * d₀ := Nat.mul_pos hi hd₀
  induction ha using Submodule.iSup_induction' with
  | mem e a ha =>
      refine mem_positiveEvenPart_of_mem_grade (grade 𝒜 d) (d := e + i * d₀) (by omega) ?_
      have h2 := monomial_mem_grade 𝒜 d i (2 * e) ha
      rwa [show 2 * e + i * d = 2 * (e + i * d₀) from by omega] at h2
  | zero => simp
  | add a a' _ _ ih ih' =>
      rw [monomial_add]
      exact Submodule.add_mem _ ih ih'

/-- A constant divided-power polynomial with positive even coefficient lies in the positive even
part of `A⟨T⟩`. -/
public theorem coeffEmbedding_mem_positiveEvenPart (d : ℕ) {a : A}
    (ha : a ∈ positiveEvenPart 𝒜) :
    coeffEmbedding a ∈ positiveEvenPart (grade 𝒜 d) := by
  induction ha using Submodule.iSup_induction' with
  | mem e a ha =>
      refine mem_positiveEvenPart_of_mem_grade (grade 𝒜 d) (d := e + 1) (by omega) ?_
      have h2 := monomial_mem_grade 𝒜 d 0 (2 * (e + 1)) ha
      rwa [show 2 * (e + 1) + 0 * d = 2 * (e + 1) from by ring] at h2
  | zero => simp
  | add a a' _ _ ih ih' =>
      rw [map_add]
      exact Submodule.add_mem _ ih ih'

/-- Every coefficient of an element of the positive even part of `A⟨T⟩` is even. -/
public theorem coeff_mem_evenPart_of_mem_positiveEvenPart {d : ℕ} (hdeven : Even d)
    {x : EvenVariableAlgebra A} (hx : x ∈ positiveEvenPart (grade 𝒜 d)) (i : ℕ) :
    x.coeff i ∈ evenPart 𝒜 := by
  obtain ⟨d₀, hdd⟩ := hdeven
  have hik : i * d = 2 * (i * d₀) := by rw [hdd]; ring
  induction hx using Submodule.iSup_induction' with
  | mem e y hy =>
      have h := (mem_grade_iff 𝒜 d (2 * (e + 1)) y).1 hy i
      by_cases hle : i * d ≤ 2 * (e + 1)
      · have hy' : y.coeff i ∈ 𝒜 (2 * (e + 1) - i * d) := by simpa [hle] using h
        refine Submodule.mem_iSup_of_mem ((e + 1) - i * d₀) ?_
        rwa [show 2 * ((e + 1) - i * d₀) = 2 * (e + 1) - i * d from by omega]
      · have hy' : y.coeff i = 0 := by simpa [hle] using h
        simp [hy']
  | zero => simp
  | add y z _ _ ih ih' =>
      rw [coeff_add, Finsupp.add_apply]
      exact Submodule.add_mem _ ih ih'

/-- The constant coefficient of an element of the positive even part of `A⟨T⟩` is positive
even. -/
public theorem coeff_zero_mem_positiveEvenPart {d : ℕ}
    {x : EvenVariableAlgebra A} (hx : x ∈ positiveEvenPart (grade 𝒜 d)) :
    x.coeff 0 ∈ positiveEvenPart 𝒜 := by
  induction hx using Submodule.iSup_induction' with
  | mem e y hy =>
      have h := (mem_grade_iff 𝒜 d (2 * (e + 1)) y).1 hy 0
      refine mem_positiveEvenPart_of_mem_grade 𝒜 (d := e + 1) (by omega) ?_
      simpa using h
  | zero => simp
  | add y z _ _ ih ih' =>
      rw [coeff_add, Finsupp.add_apply]
      exact Submodule.add_mem _ ih ih'

/-- The positive even part of `A⟨T⟩` described coefficientwise: a divided-power polynomial is
positive even exactly when its constant coefficient is positive even and all of its other
coefficients are even. This is the domain on which the source prescribes the divided powers,
by its two displayed formulas for `x₀ = 0` and for general `x₀`. -/
public theorem mem_positiveEvenPart_iff {d : ℕ} (hdeven : Even d) (hd : 0 < d)
    (x : EvenVariableAlgebra A) :
    x ∈ positiveEvenPart (grade 𝒜 d) ↔
      x.coeff 0 ∈ positiveEvenPart 𝒜 ∧ ∀ i, 0 < i → x.coeff i ∈ evenPart 𝒜 := by
  classical
  refine ⟨fun hx => ⟨coeff_zero_mem_positiveEvenPart hx, fun i _ =>
    coeff_mem_evenPart_of_mem_positiveEvenPart hdeven hx i⟩, fun hc => ?_⟩
  rw [← sum_monomial x]
  refine Submodule.sum_mem _ fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact coeffEmbedding_mem_positiveEvenPart d hc.1
  · exact monomial_mem_positiveEvenPart hdeven hd hi (hc.2 i hi)

end EvenVariableAlgebra

end PositiveEvenPart

section Structure

open scoped BigOperators

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

namespace EvenVariableAlgebra


/-- The finite multinomial expansion for divided powers of a polynomial with
only positive variable exponents. Its factors are multiplied in the
divided-power polynomial algebra, not coefficientwise. -/
public noncomputable def positivePolynomialDividedPower (n : ℕ)
    (x : EvenVariableAlgebra A) : EvenVariableAlgebra A := by
  classical
  exact ∑ e : (↥x.coeff.support → Fin (n + 1)),
    if (∑ i : ↥x.coeff.support, (e i).val) = n then
      ((Finset.univ : Finset ↥x.coeff.support).toList.map fun i ↦
        monomial (i.val * (e i).val)
          (dividedPowerMonomialCoefficient (e i).val i.val •
            x.coeff i.val ^ (e i).val)).prod
    else 0

end EvenVariableAlgebra

open EvenVariableAlgebra

private noncomputable def symmetricTupleAssignments {ι : Type*}
    [DecidableEq ι] [Fintype ι] (n : ℕ) :
    Sym ι n ≃ {e : ι → Fin (n + 1) // ∑ i, (e i).val = n} := by
  let eNat := Sym.equivNatSumOfFintype ι n
  let eBound : {f : ι → ℕ // ∑ i, f i = n} ≃
      {e : ι → Fin (n + 1) // ∑ i, (e i).val = n} := {
    toFun := fun f => ⟨fun i => ⟨f.1 i, Nat.lt_succ_of_le (by
      calc
        f.1 i ≤ ∑ j, f.1 j := by
          simpa using (Finset.single_le_sum (s := Finset.univ)
            (f := f.1) (fun j hj => Nat.zero_le _) (Finset.mem_univ i))
        _ = n := f.2)⟩, by simpa using f.2⟩
    invFun := fun e => ⟨fun i => (e.1 i).val, by simpa using e.2⟩
    left_inv := by intro f; apply Subtype.ext; funext i; rfl
    right_inv := by intro e; apply Subtype.ext; funext i; apply Fin.ext; rfl }
  exact eNat.trans eBound

private theorem sum_sym_count_eq_sum_assignments {ι : Type*}
    [DecidableEq ι] [Fintype ι] {M : Type*} [AddCommMonoid M]
    (n : ℕ) (F : (ι → ℕ) → M) :
    (∑ k ∈ (Finset.univ : Finset ι).sym n,
      F (fun i => Multiset.count i (k : Multiset ι))) =
    ∑ e : ι → Fin (n + 1),
      if (∑ i, (e i).val) = n then F (fun i => (e i).val) else 0 := by
  classical
  let E := symmetricTupleAssignments (ι := ι) n
  calc
    _ = ∑ k : Sym ι n, F (fun i => Multiset.count i (k : Multiset ι)) := by simp
    _ = ∑ e : {e : ι → Fin (n + 1) // ∑ i, (e i).val = n},
        F (fun i => (e.1 i).val) := by
      exact Fintype.sum_equiv E _ _ (by
        intro k
        simp [E, symmetricTupleAssignments, Sym.equivNatSumOfFintype])
    _ = _ := by
      let p : (ι → Fin (n + 1)) → Prop := fun e => (∑ i, (e i).val) = n
      let g : (ι → Fin (n + 1)) → M := fun e =>
        if p e then F (fun i => (e i).val) else 0
      have hsplit := Fintype.sum_subtype_add_sum_subtype p g
      have hp : (∑ e : {e : ι → Fin (n + 1) // p e}, g e.1) =
          ∑ e : {e : ι → Fin (n + 1) // p e}, F (fun i => (e.1 i).val) := by
        apply Finset.sum_congr rfl
        intro e he
        simp [g, p, e.2]
      have hnot : (∑ e : {e : ι → Fin (n + 1) // ¬ p e}, g e.1) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        simp [g, e.2]
      calc
        _ = ∑ e : {e : ι → Fin (n + 1) // p e}, g e.1 := hp.symm
        _ = (∑ e : {e : ι → Fin (n + 1) // p e}, g e.1) +
              ∑ e : {e : ι → Fin (n + 1) // ¬ p e}, g e.1 := by
                rw [hnot, add_zero]
        _ = ∑ e : ι → Fin (n + 1), g e := by rw [← hsplit]
        _ = _ := rfl

private theorem one_mem_evenPart
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : (1 : A) ∈ evenPart 𝒜 :=
  Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)

private theorem evenPart_mul_mem
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {x y : A} (hx : x ∈ evenPart 𝒜) (hy : y ∈ evenPart 𝒜) :
    x * y ∈ evenPart 𝒜 := by
  change x ∈ (⨆ d : ℕ, 𝒜 (2 * d)) at hx
  change y ∈ (⨆ d : ℕ, 𝒜 (2 * d)) at hy
  rw [Submodule.iSup_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨e, he⟩ := Set.mem_iUnion.mp hy
          exact Submodule.mem_iSup_of_mem (d + e) (by
            have hdeg : 2 * d + 2 * e = 2 * (d + e) := by omega
            simpa only [hdeg] using SetLike.mul_mem_graded hd he)
      | zero => simp
      | add y z hy hz ihy ihz =>
          simpa only [mul_add] using (evenPart 𝒜).add_mem ihy ihz
      | smul r y hy ih =>
          simpa only [mul_smul_comm] using (evenPart 𝒜).smul_mem r ih
  | zero => simp
  | add x z hx hz ihx ihz =>
      simpa only [add_mul] using (evenPart 𝒜).add_mem ihx ihz
  | smul r x hx ih =>
      simpa only [smul_mul_assoc] using (evenPart 𝒜).smul_mem r ih

/-- A power of an element of the even part of a graded algebra lies in the even part. -/
public theorem evenPart_pow_mem
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {x : A} (hx : x ∈ evenPart 𝒜) (n : ℕ) : x ^ n ∈ evenPart 𝒜 := by
  induction n with
  | zero => simpa using one_mem_evenPart 𝒜
  | succ n ih =>
      rw [pow_succ]
      exact evenPart_mul_mem 𝒜 ih hx

private def evenSubalgebra
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : Subalgebra R A where
  carrier := evenPart 𝒜
  add_mem' := (evenPart 𝒜).add_mem
  mul_mem' := evenPart_mul_mem 𝒜
  algebraMap_mem' r := by
    change algebraMap R A r ∈ evenPart 𝒜
    rw [Algebra.algebraMap_eq_smul_one]
    exact (evenPart 𝒜).smul_mem r (one_mem_evenPart 𝒜)

private instance evenSubalgebraCommRing
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] :
    CommRing (evenSubalgebra 𝒜) :=
  { (inferInstance : Ring (evenSubalgebra 𝒜)) with
    mul_comm := by
      intro x y
      apply Subtype.ext
      exact evenPart_mul_comm 𝒜 x.property (y : A) }

private def positiveEvenIdeal
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] :
    Ideal (evenSubalgebra 𝒜) where
  carrier := {x | (x : A) ∈ positiveEvenPart 𝒜}
  zero_mem' := (positiveEvenPart 𝒜).zero_mem
  add_mem' := fun hx hy ↦ (positiveEvenPart 𝒜).add_mem hx hy
  smul_mem' := fun a _x hx ↦ evenPart_mul_positiveEvenPart 𝒜 a.property hx

private theorem gamma_dpow_mem_evenPart
    (γ : DividedPowerStructure 𝒜) {n : ℕ} {x : A}
    (hx : x ∈ positiveEvenPart 𝒜) : γ.dpow n x ∈ evenPart 𝒜 := by
  by_cases hn : n = 0
  · subst n
    rw [γ.dpow_zero hx]
    exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒜)
  · exact positiveEvenPart_le_evenPart 𝒜 (γ.dpow_mem hn hx)


private def baseDividedPowers
    (γ : DividedPowerStructure 𝒜) :
  DividedPowers (positiveEvenIdeal 𝒜) where
  dpow n x := ⟨γ.dpow n (x : A), by
    by_cases hx : (x : A) ∈ positiveEvenPart 𝒜
    · exact dpow_mem_evenPart 𝒜 γ n hx
    · rw [γ.dpow_null hx]
      exact (evenSubalgebra 𝒜).zero_mem⟩
  dpow_null {n x} hx := by
    apply Subtype.ext
    exact γ.dpow_null hx
  dpow_zero {x} hx := by
    apply Subtype.ext
    exact γ.dpow_zero hx
  dpow_one {x} hx := by
    apply Subtype.ext
    exact γ.dpow_one hx
  dpow_mem {n x} hn hx := by
    change γ.dpow n (x : A) ∈ positiveEvenPart 𝒜
    exact γ.dpow_mem hn hx
  dpow_add {n} {x y} hx hy := by
    apply Subtype.ext
    change γ.dpow n ((x : A) + (y : A)) = _
    simpa using γ.dpow_add hx
      hy
  dpow_mul {n} {a x} hx := by
    apply Subtype.ext
    change γ.dpow n ((a : A) * (x : A)) = _
    by_cases hn : n = 0
    · subst n
      have hx' : (x : A) ∈ positiveEvenPart 𝒜 := hx
      have hax : (a : A) * (x : A) ∈ positiveEvenPart 𝒜 :=
        evenPart_mul_positiveEvenPart 𝒜 a.property hx'
      simp [γ.dpow_zero hx', γ.dpow_zero hax]
    · simpa [Algebra.smul_def] using
        γ.dpow_mul_even hn a.property hx
  mul_dpow {m n} {x} hx := by
    apply Subtype.ext
    change γ.dpow m (x : A) * γ.dpow n (x : A) = _
    simpa using γ.dpow_mul hx
  dpow_comp {m n x} hn hx := by
    -- `uniformBell m n` is the factorial quotient in the graded definition.
    have hcoeff : Nat.uniformBell m n = (m * n).factorial /
        (n.factorial ^ m * m.factorial) := by
      exact Nat.uniformBell_eq_div m hn
    by_cases hm : m = 0
    · subst m
      apply Subtype.ext
      change γ.dpow 0 (γ.dpow n (x : A)) = _
      have hx' : (x : A) ∈ positiveEvenPart 𝒜 := hx
      have hinner : γ.dpow n (x : A) ∈ positiveEvenPart 𝒜 := γ.dpow_mem hn hx'
      simp [γ.dpow_zero hx', γ.dpow_zero hinner, Nat.uniformBell_zero_left]
    · rw [hcoeff]
      apply Subtype.ext
      change γ.dpow m (γ.dpow n (x : A)) = _
      simpa [mul_comm, mul_left_comm, mul_assoc] using
      γ.dpow_dpow (m := n) (n := m) hn hm
          hx

end Structure

end DividedPowers.TateResolution

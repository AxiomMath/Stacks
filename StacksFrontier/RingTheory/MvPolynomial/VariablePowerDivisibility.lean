module

public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Divisibility by a power of a variable in a polynomial ring

Let `R` be a commutative ring and `A = R[Tᵤ]` a polynomial ring. Divisibility of `f ∈ A` by
`Tᵢ ^ k` is a condition on the support of `f`: every monomial of `f` must carry an exponent at
least `k` at the variable `Tᵢ`. Consequently two powers of *distinct* variables impose
independent conditions, and an equation

`f · Tⱼ ^ l = g · Tᵢ ^ k`  with `i ≠ j`

forces `Tᵢ ^ k` to divide `f` and `Tⱼ ^ l` to divide `g`, with one common cofactor:
`f = Tᵢ ^ k · w` and `g = Tⱼ ^ l · w`.

Read in the localizations, the last statement says that the subrings `A[1/Tᵢ]` and `A[1/Tⱼ]` of
`A[1/(Tᵢ Tⱼ)]` meet in `A`: a fraction whose denominator is a power of `Tᵢ` and also a power of
`Tⱼ` has no denominator. This is the algebraic form of the fact that a regular function on
`𝐀^{m+n}_S` defined away from a coordinate subspace cut out by at least two of the coordinates
extends across it.

## Main results

* `MvPolynomial.monomial_one_dvd_iff_forall_le` and `MvPolynomial.X_pow_dvd_iff_forall_le`:
  **divisibility by a monic monomial, and by a power of a variable, is a condition on the
  support.**
* `MvPolynomial.X_pow_mul_left_injective`: a power of a variable is a non-zero-divisor.
* `MvPolynomial.X_pow_dvd_of_mul_X_pow_eq_mul_X_pow`: **denominators at distinct variables are
  independent** — if `f · Tⱼ ^ l = g · Tᵢ ^ k` and `i ≠ j`, then `Tᵢ ^ k` divides `f`.
* `MvPolynomial.exists_eq_mul_X_pow_of_mul_X_pow_eq_mul_X_pow`: the same equation with both
  denominators cleared at once, by a single common cofactor.

## Implementation notes

The support criterion is read off Mathlib's monomial division `MvPolynomial.divMonomial` and
`MvPolynomial.modMonomial` through `MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero`, whose
two coefficient lemmas `MvPolynomial.coeff_modMonomial_of_le` and
`MvPolynomial.coeff_modMonomial_of_not_le` split exactly along the inequality the criterion
asserts.

Multiplying by `Tⱼ ^ l` translates the support by `Finsupp.single j l`, which leaves the exponent
at every variable other than `Tⱼ` unchanged; that is the whole content of the independence
statement, and it is why `i ≠ j` is needed and nothing else is.

No hypothesis is placed on `R`: the statements are about supports and about the translation
action of monomial multiplication on them, both of which are insensitive to zero divisors in `R`,
and over the zero ring every statement below is vacuous or trivial.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR), in the proof of whose
  first assertion a differential form on `𝐀^{m+n}_S` given off the coordinate subspace
  `y₁ = ⋯ = yₙ = 0` with `n ≥ 2` is extended across it
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} [CommRing R] {σ : Type v}

/-! ### The support criterion -/

/-- **Divisibility by a monic monomial is a condition on the support.** A polynomial is divisible
by `monomial d 1` exactly when every monomial of its support dominates `d`. -/
theorem monomial_one_dvd_iff_forall_le {d : σ →₀ ℕ} {f : MvPolynomial σ R} :
    monomial d (1 : R) ∣ f ↔ ∀ n ∈ f.support, d ≤ n := by
  rw [monomial_one_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h n hn
    by_contra hle
    exact mem_support_iff.mp hn (by rw [← coeff_modMonomial_of_not_le f hle, h, coeff_zero])
  · intro h
    ext n
    rw [coeff_zero]
    by_cases hle : d ≤ n
    · exact coeff_modMonomial_of_le f hle
    · rw [coeff_modMonomial_of_not_le f hle]
      exact notMem_support_iff.mp fun hn => hle (h n hn)

/-- **Divisibility by a power of a variable is a condition on the support.** A polynomial is
divisible by `Tᵢ ^ k` exactly when every monomial of its support has exponent at least `k` at the
variable `Tᵢ`. -/
theorem X_pow_dvd_iff_forall_le {i : σ} {k : ℕ} {f : MvPolynomial σ R} :
    (X i : MvPolynomial σ R) ^ k ∣ f ↔ ∀ n ∈ f.support, k ≤ n i := by
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_forall_le]
  exact forall₂_congr fun n _ => Finsupp.single_le_iff

/-- **A power of a variable is a non-zero-divisor**: multiplication by `Tᵢ ^ k` shifts the
exponent of `Tᵢ` in every monomial by `k`, hence is injective on coefficients. -/
theorem X_pow_mul_left_injective (i : σ) (k : ℕ) :
    Function.Injective fun f : MvPolynomial σ R => (X i : MvPolynomial σ R) ^ k * f := by
  intro f g h
  ext n
  simpa [X_pow_eq_monomial, coeff_monomial_mul] using congrArg (coeff (Finsupp.single i k + n)) h

/-! ### Denominators at distinct variables -/

/-- **Denominators at two distinct variables are independent.** If `f · Tⱼ ^ l = g · Tᵢ ^ k` with
`i ≠ j`, then `Tᵢ ^ k` divides `f`.

Multiplying by `Tⱼ ^ l` leaves the exponent at `Tᵢ` of every monomial unchanged, so the support
condition of `MvPolynomial.X_pow_dvd_iff_forall_le` for the right-hand side, which holds
trivially, transfers to `f`. -/
theorem X_pow_dvd_of_mul_X_pow_eq_mul_X_pow {i j : σ} (hij : i ≠ j)
    {f g : MvPolynomial σ R} {k l : ℕ} (h : f * X j ^ l = g * X i ^ k) :
    (X i : MvPolynomial σ R) ^ k ∣ f := by
  rw [X_pow_dvd_iff_forall_le]
  intro n hn
  have h1 : coeff (n + Finsupp.single j l) (f * X j ^ l) = coeff n f := by
    simp [X_pow_eq_monomial, coeff_mul_monomial]
  have h2 : coeff (n + Finsupp.single j l) (g * X i ^ k) ≠ 0 := by
    rwa [← h, h1, ← mem_support_iff]
  simpa [Finsupp.single_apply, hij] using X_pow_dvd_iff_forall_le.mp
    (dvd_mul_left ((X i : MvPolynomial σ R) ^ k) g) _ (mem_support_iff.mpr h2)

/-- **Two denominators at distinct variables are cleared by a single common cofactor.** If
`f · Tⱼ ^ l = g · Tᵢ ^ k` with `i ≠ j`, there is `w` with `f = Tᵢ ^ k · w` and `g = Tⱼ ^ l · w`.

In the localizations this says that `A[1/Tᵢ] ∩ A[1/Tⱼ] = A` inside `A[1/(Tᵢ Tⱼ)]`, the fraction
in question being `w`. -/
theorem exists_eq_mul_X_pow_of_mul_X_pow_eq_mul_X_pow {i j : σ} (hij : i ≠ j)
    {f g : MvPolynomial σ R} {k l : ℕ} (h : f * X j ^ l = g * X i ^ k) :
    ∃ w : MvPolynomial σ R, f = X i ^ k * w ∧ g = X j ^ l * w := by
  obtain ⟨w, hw⟩ := X_pow_dvd_of_mul_X_pow_eq_mul_X_pow hij h
  refine ⟨w, hw, X_pow_mul_left_injective i k ?_⟩
  show (X i : MvPolynomial σ R) ^ k * g = X i ^ k * (X j ^ l * w)
  rw [mul_comm ((X i : MvPolynomial σ R) ^ k) g, ← h, hw, mul_assoc,
    mul_comm w ((X j : MvPolynomial σ R) ^ l)]

/-- The companion divisibility of `MvPolynomial.X_pow_dvd_of_mul_X_pow_eq_mul_X_pow`: the
right-hand numerator is divisible by the left-hand denominator. -/
theorem X_pow_dvd_of_mul_X_pow_eq_mul_X_pow' {i j : σ} (hij : i ≠ j)
    {f g : MvPolynomial σ R} {k l : ℕ} (h : f * X j ^ l = g * X i ^ k) :
    (X j : MvPolynomial σ R) ^ l ∣ g :=
  let ⟨w, _, hg⟩ := exists_eq_mul_X_pow_of_mul_X_pow_eq_mul_X_pow hij h
  ⟨w, hg⟩

end MvPolynomial

end

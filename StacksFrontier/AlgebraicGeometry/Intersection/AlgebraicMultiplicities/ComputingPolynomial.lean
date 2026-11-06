module

public import StacksFrontier.AlgebraicGeometry.Intersection.AlgebraicMultiplicities.Defs
public import StacksFrontier.RingTheory.HilbertFunction
public import StacksFrontier.RingTheory.HilbertFunction.Numerical
public import StacksFrontier.RingTheory.HilbertSamuel.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Polynomials computing the Hilbert–Samuel function

The Hilbert–Samuel degree and multiplicity of a module are defined by reading off a
polynomial selected from the property of eventually computing the lengths
`length_R (M / I ^ (n + 1) M)`. This file names that property, proves that such a
polynomial exists whenever the radical of `I` is the maximal ideal, shows it is unique, and
converts both invariants into statements about an arbitrary computing polynomial rather than
about the chosen one.

## Main definitions

* `Ideal.ComputesHilbertSamuelPoly I M P` says that `P` eventually computes
  `length_R (M / I ^ (n + 1) M)` on the naturals.
* `Ideal.ComputesGeneralizedHilbertPoly I M P` is the unshifted variant, for
  `length_R (M / I ^ n M)`.

## Main results

* `Ideal.exists_computesHilbertSamuelPoly`: existence of a computing polynomial.
* `Ideal.ComputesHilbertSamuelPoly.unique`: uniqueness of a computing polynomial.
* `Ideal.hilbertSamuelDegree_eq_degree_of_computes`: the Hilbert–Samuel degree is the degree
  of any computing polynomial.
* `Ideal.hilbertSamuelMultiplicity_eq_factorial_mul_coeff`: the multiplicity in degree `d` is
  `d !` times the degree-`d` coefficient of any computing polynomial.

## Implementation notes

Both predicates are stated with the lengths and an explicit natural-number witness, rather
than through `HilbertSamuel.hilbertSamuelFunction`, because that is verbatim the condition on
which `Ideal.hilbertSamuelDegree` and `Ideal.hilbertSamuelMultiplicity` branch; it is
therefore what makes `dif_pos` applicable to them. They are `abbrev`s for the same reason.
`HilbertSamuel.IsHilbertSamuelPoly` is the same condition with the lengths pushed through
`ENat.toNat`, which discards the finiteness witness, so the two are kept apart.

## References

* [Stacks Project, Tag 0AZV](https://stacks.math.columbia.edu/tag/0AZV)
* [Stacks Project, Tag 0AZW](https://stacks.math.columbia.edu/tag/0AZW)
* [Stacks Project, Tag 0B00](https://stacks.math.columbia.edu/tag/0B00)
-/

@[expose] public section

open Filter Polynomial

namespace Ideal

variable {R : Type*} [CommRing R]

/-- `P` *computes the Hilbert–Samuel function* of `M` for `I` if, for all sufficiently large
`n`, the length of `M / I ^ (n + 1) M` is a natural number whose cast is `P.eval n`. -/
abbrev ComputesHilbertSamuelPoly (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    (P : ℚ[X]) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
    Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = p ∧ P.eval (n : ℚ) = (p : ℚ)

/-- `P` *computes the generalized Hilbert function* of `M` for `I` if, for all sufficiently
large `n`, the length of `M / I ^ n M` is a natural number whose cast is `P.eval n`. This is
the unshifted companion of `Ideal.ComputesHilbertSamuelPoly`. -/
abbrev ComputesGeneralizedHilbertPoly (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    (P : ℚ[X]) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
    Module.length R (M ⧸ (I ^ n • (⊤ : Submodule R M))) = p ∧ P.eval (n : ℚ) = (p : ℚ)

/-- For an ideal whose radical is the maximal ideal of a Noetherian local ring, the
Hilbert–Samuel function of a finite module is computed by a rational polynomial: the
binomial-basis presentation of the Hilbert function assembles one. -/
theorem exists_computesHilbertSamuelPoly [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I.radical = IsLocalRing.maximalIdeal R) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : ∃ P : ℚ[X], ComputesHilbertSamuelPoly I M P := by
  obtain ⟨r, _a, b, hab⟩ :=
    Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul I hI M
  refine ⟨∑ i ∈ Finset.range (r + 1), C (b i : ℚ) *
    Stacks.HilbertFunction.PolynomialQuotient.binomialPoly i,
    hab.mono fun n hn => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := hn.2
  refine ⟨q, hq1, ?_⟩
  simp only [eval_finsetSum, eval_mul, eval_C,
    Stacks.HilbertFunction.PolynomialQuotient.binomialPoly_eval,
    Ring.choose_natCast]
  rw [show ((q : ℚ)) = ((q : ℤ) : ℚ) by push_cast; ring, hq2]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Two polynomials that eventually both compute the same `ℕ∞`-valued sequence are equal. -/
private theorem eq_of_eventually_length_eq {P Q : ℚ[X]} (L : ℕ → ℕ∞)
    (hP : ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, L n = p ∧ P.eval (n : ℚ) = (p : ℚ))
    (hQ : ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, L n = p ∧ Q.eval (n : ℚ) = (p : ℚ)) : P = Q := by
  apply Polynomial.eq_of_eventually_eval_natCast_eq
  filter_upwards [hP, hQ] with n hn hm
  obtain ⟨p, hp, hp'⟩ := hn
  obtain ⟨q, hq, hq'⟩ := hm
  have hpq : p = q := by exact_mod_cast hp.symm.trans hq
  simp [hp', hq', hpq]

/-- A computing polynomial for the Hilbert–Samuel function is unique. -/
@[ega "0 16.2.1" "partial"]
theorem ComputesHilbertSamuelPoly.unique {M : Type*} [AddCommGroup M] [Module R M]
    {I : Ideal R} {P Q : ℚ[X]} (hP : ComputesHilbertSamuelPoly I M P)
    (hQ : ComputesHilbertSamuelPoly I M Q) : P = Q := by
  exact eq_of_eventually_length_eq _ hP hQ

/-- A computing polynomial for the generalized Hilbert function is unique. -/
theorem ComputesGeneralizedHilbertPoly.unique {M : Type*} [AddCommGroup M] [Module R M]
    {I : Ideal R} {P Q : ℚ[X]} (hP : ComputesGeneralizedHilbertPoly I M P)
    (hQ : ComputesGeneralizedHilbertPoly I M Q) : P = Q := by
  exact eq_of_eventually_length_eq _ hP hQ

/-- The Hilbert–Samuel degree of `M` for `I` is the degree of any polynomial computing the
Hilbert–Samuel function, not only of the one chosen in the definition. -/
theorem hilbertSamuelDegree_eq_degree_of_computes {M : Type*} [AddCommGroup M] [Module R M]
    {I : Ideal R} {P : ℚ[X]} (hP : ComputesHilbertSamuelPoly I M P) :
    I.hilbertSamuelDegree M = P.degree := by
  have hex : ∃ Q : ℚ[X], ComputesHilbertSamuelPoly I M Q := ⟨P, hP⟩
  rw [Ideal.hilbertSamuelDegree, dite_eq_left hex]
  exact congrArg Polynomial.degree (ComputesHilbertSamuelPoly.unique hex.choose_spec hP)

/-- The Hilbert–Samuel multiplicity in degree `d` is `d !` times the coefficient of degree
`d` of any polynomial computing the Hilbert–Samuel function. -/
theorem hilbertSamuelMultiplicity_eq_factorial_mul_coeff (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] {P : ℚ[X]} (hP : ComputesHilbertSamuelPoly I M P) (d : ℕ) :
    I.hilbertSamuelMultiplicity M d = (d.factorial : ℚ) * P.coeff d := by
  classical
  have hex : ∃ Q : ℚ[X], ComputesHilbertSamuelPoly I M Q := ⟨P, hP⟩
  rw [Ideal.hilbertSamuelMultiplicity, dite_eq_left hex]
  rw [ComputesHilbertSamuelPoly.unique hex.choose_spec hP]

end Ideal

module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MvPolynomial.VariablePowerDivisibility

/-!
# `ℚ[x, y]` with `deg x = 2`, `deg y = 3`, and the ideal `(y²)`

This is the ring of the last paragraph of Stacks tag 0BXK: `A = ℚ[x, y]` graded by
`deg x = 2` and `deg y = 3`, so that the least common multiple of the degrees of the generators
`x, y` of `A` over `A₀ = ℚ` is `d = 6`, together with the homogeneous ideal `I = (y²)`.

The two computations the source performs in this ring are carried out here:

* every homogeneous `f` with `6 ∣ deg(f · y)` is divisible by `y`, hence `f · y ∈ I`
  (`Stacks.WeightedProjSaturation.X_one_dvd_of_mem_grading`,
  `Stacks.WeightedProjSaturation.mul_X_one_mem_squareIdeal`) — equivalently, the degree-`6n` part
  of the ideal `(y)` lies in `I`
  (`Stacks.WeightedProjSaturation.mem_squareIdeal_of_mem_span_X_one`);
* `xⁿ · y ∉ I` for every `n`
  (`Stacks.WeightedProjSaturation.X_zero_pow_mul_X_one_notMem_squareIdeal`), so `y` is not in the
  saturation `(I : A₊^∞)` of `I`
  (`Stacks.WeightedProjSaturation.not_exists_irrelevant_pow_mul_X_one_mem`).

So `y` passes the degreewise test `(A y)_{6n} ⊆ I` of the source's general formula while lying
outside the saturation of `I`: the two sets the source compares are genuinely different, and `y`
separates them.

## What is *not* claimed here

The source concludes from the first computation that `y ∈ I(V₊(I))` and that
`I(V₊(I)) = (y)`. That conclusion is **false in this ring**, and nothing below asserts it. The
reason is visible in the computations of this file together with the charts of `Proj A`: the
degree-zero part of `A[1/x]` is `ℚ[y²/x³]`, and `(A[1/x])₃ = (y/1) · ℚ[y²/x³]` is free of rank
one *on the element `y/1` itself*; the same holds on `D₊(y)`, where `(A[1/y])₃ = (y/1) · ℚ[x³/y²]`.
So `𝒪(3)` is trivialized by the canonical section of `y` on both charts of `Proj A`, i.e. that
section is nowhere vanishing, while `V₊(y²)` is the nonempty reduced point `y²/x³ = 0` of
`D₊(x)`. A nowhere-vanishing section does not pull back to zero on a nonempty closed subscheme,
so `y ∉ I(V₊(I))`; in fact `I(V₊(I)) = (y²) = I`. What the computation of this file really
reflects is that the multiplication map `𝒪(3) ⊗ 𝒪(3) ⟶ 𝒪(6)` is, in the trivializations above,
multiplication by `y²/x³` — it vanishes exactly along `V₊(y²)` — and not that `y` vanishes there.

Accordingly the tag attributes below are attached to the two computations the source states, and
to nothing else.

## Implementation notes

The grading is Mathlib's `MvPolynomial.weightedHomogeneousSubmodule` at the weight function
`![2, 3]`, whose `GradedAlgebra` instance `MvPolynomial.weightedGradedAlgebra` is a `def` rather
than an `instance` upstream and is installed here.

Both computations are divisibility statements, and both are read off the support criterion
`MvPolynomial.X_pow_dvd_iff_forall_le`: divisibility of `f` by `y ^ k` says that every monomial
of `f` carries an exponent at least `k` at `y`. Weighted homogeneity of degree `m` says that
every monomial `x^a y^b` of `f` satisfies `2a + 3b = m`, so the arithmetic of each statement is a
single `omega` call on `2a + 3b = m` together with a congruence on `m` — the parity of `m`
forces the parity of `b`.

Note that the source's degree-one formula `{x | A_N x ⊆ I for some N}` is vacuous in this ring,
since `A₁ = 0` (`Stacks.WeightedProjSaturation.grading_one_eq_bot`); the saturation the last
paragraph of the tag compares against is therefore the `A₊`-power saturation `(I : A₊^∞)`, which
is what `not_exists_irrelevant_pow_mul_X_one_mem` refutes membership in.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

namespace Stacks.WeightedProjSaturation

open MvPolynomial

/-! ### The ring, its grading, and the ideal -/

/-- The weight function of Stacks tag 0BXK's last paragraph: `deg x = 2`, `deg y = 3`. -/
def weight : Fin 2 → ℕ := ![2, 3]

/-- `ℚ[x, y]` graded by `deg x = 2`, `deg y = 3`. -/
abbrev grading : ℕ → Submodule ℚ (MvPolynomial (Fin 2) ℚ) :=
  MvPolynomial.weightedHomogeneousSubmodule ℚ weight

instance : GradedAlgebra grading := MvPolynomial.weightedGradedAlgebra ℚ weight

/-- The ideal `I = (y²)`. -/
abbrev squareIdeal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ^ 2}

/-! ### Degrees -/

theorem weight_apply (d : Fin 2 →₀ ℕ) : Finsupp.weight weight d = 2 * d 0 + 3 * d 1 := by
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_two]
  simp only [weight, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul]
  ring

/-- A polynomial is homogeneous of degree `n` for the weights `(2, 3)` exactly when every
monomial `x^a y^b` occurring in it has `2a + 3b = n`. -/
theorem mem_grading_iff {n : ℕ} (f : MvPolynomial (Fin 2) ℚ) :
    f ∈ grading n ↔ ∀ d ∈ f.support, 2 * d 0 + 3 * d 1 = n := by
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine ⟨fun h d hd => ?_, fun h d hd => ?_⟩
  · rw [← weight_apply]
    exact h (MvPolynomial.mem_support_iff.mp hd)
  · rw [weight_apply]
    exact h d (MvPolynomial.mem_support_iff.mpr hd)

theorem X_zero_mem_grading : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ∈ grading 2 :=
  isWeightedHomogeneous_X ℚ weight 0

theorem X_one_mem_grading : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∈ grading 3 :=
  isWeightedHomogeneous_X ℚ weight 1

/-- **There is no element of degree one**: no monomial `x^a y^b` has `2a + 3b = 1`. So the
degree-one formula `{z | A_N z ⊆ I for some N}` of the earlier part of Stacks tag 0BXK is
satisfied by every `z` in this ring, at `N = 1`, and is not the notion its last paragraph
compares against. -/
theorem grading_one_eq_bot : grading 1 = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [Submodule.mem_bot]
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [MvPolynomial.coeff_zero]
  by_contra hc
  have h := (mem_grading_iff f).mp hf d (MvPolynomial.mem_support_iff.mpr hc)
  omega

/-! ### The source's first computation -/

/-- Divisibility by `y` means every monomial carries a positive exponent at `y`. -/
private theorem X_one_dvd_iff_forall_le (f : MvPolynomial (Fin 2) ℚ) :
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∣ f ↔ ∀ d ∈ f.support, 1 ≤ d 1 := by
  simpa using MvPolynomial.X_pow_dvd_iff_forall_le (i := (1 : Fin 2)) (k := 1) (f := f)

/-- **Stacks 0BXK, in the counterexample of its last paragraph: a homogeneous `f` with
`6 ∣ deg(f · y)` is divisible by `y`.** Every monomial `x^a y^b` of `f` has `2a + 3b = n` with
`n + 3` divisible by `6`, so `n` is odd, so `b` is odd and in particular nonzero. -/
@[stacks 0BXK "the counterexample of the last paragraph, `A = ℚ[x, y]` with `deg x = 2` and \
  `deg y = 3`: for homogeneous `f` with `6 ∣ deg (f y)` one has `y ∣ f`"]
theorem X_one_dvd_of_mem_grading (n : ℕ) (f : MvPolynomial (Fin 2) ℚ) (hf : f ∈ grading n)
    (h6 : 6 ∣ n + 3) : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∣ f := by
  obtain ⟨k, hk⟩ := h6
  refine (X_one_dvd_iff_forall_le f).mpr fun d hd => ?_
  have hw := (mem_grading_iff f).mp hf d hd
  omega

/-- **Stacks 0BXK, in the counterexample of its last paragraph: hence `f · y ∈ I = (y²)`.** -/
@[stacks 0BXK "the counterexample of the last paragraph: for homogeneous `f` with \
  `6 ∣ deg (f y)` one has `f y ∈ I = (y²)`"]
theorem mul_X_one_mem_squareIdeal (n : ℕ) (f : MvPolynomial (Fin 2) ℚ) (hf : f ∈ grading n)
    (h6 : 6 ∣ n + 3) :
    f * (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∈ squareIdeal := by
  obtain ⟨g, rfl⟩ := X_one_dvd_of_mem_grading n f hf h6
  rw [Ideal.mem_span_singleton]
  exact ⟨g, by ring⟩

/-- **The degreewise test of Stacks 0BXK's general formula, for `y` in this ring:
`(A · y)_{6n} ⊆ I` for every `n`.** An element of the ideal `(y)` that is homogeneous of a degree
divisible by `6` already lies in `(y²)`: divisibility by `y` makes the exponent `b` of `y` in
every monomial positive, and `2a + 3b = 6n` makes it even, so it is at least `2`. -/
@[stacks 0BXK "the counterexample of the last paragraph: `(A y)_{6n} ⊆ I` for `I = (y²)`, the \
  degreewise test `y` passes"]
theorem mem_squareIdeal_of_mem_span_X_one (n : ℕ) (z : MvPolynomial (Fin 2) ℚ)
    (hz : z ∈ Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ)})
    (hdeg : z ∈ grading (6 * n)) : z ∈ squareIdeal := by
  rw [Ideal.mem_span_singleton] at hz
  have h1 := (X_one_dvd_iff_forall_le z).mp hz
  rw [Ideal.mem_span_singleton]
  exact MvPolynomial.X_pow_dvd_iff_forall_le.mpr fun d hd => by
    have hw := (mem_grading_iff z).mp hdeg d hd
    have hb := h1 d hd
    omega

/-! ### The source's second computation -/

theorem X_zero_pow_mul_X_one_eq_monomial (n : ℕ) :
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ n * MvPolynomial.X 1 =
      MvPolynomial.monomial (Finsupp.single (0 : Fin 2) n + Finsupp.single (1 : Fin 2) 1) 1 := by
  rw [← pow_one (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ),
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    one_mul]

/-- **Stacks 0BXK, in the counterexample of its last paragraph: `xⁿ · y ∉ I` for every `n`.** The
only monomial of `xⁿ y` carries the exponent `1` at `y`, which is less than `2`. -/
@[stacks 0BXK "the counterexample of the last paragraph: `xⁿ y ∉ I` for every `n`, with \
  `I = (y²)`"]
theorem X_zero_pow_mul_X_one_notMem_squareIdeal (n : ℕ) :
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ n * MvPolynomial.X 1 ∉ squareIdeal := by
  intro h
  rw [Ideal.mem_span_singleton, MvPolynomial.X_pow_dvd_iff_forall_le] at h
  have hd : (Finsupp.single (0 : Fin 2) n + Finsupp.single (1 : Fin 2) 1) ∈
      ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ n * MvPolynomial.X 1).support := by
    rw [MvPolynomial.mem_support_iff, X_zero_pow_mul_X_one_eq_monomial n,
      MvPolynomial.coeff_monomial, if_pos rfl]
    exact one_ne_zero
  have hle := h _ hd
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by decide), Finsupp.single_eq_same] at hle
  omega

/-- **`y` is not in the saturation `(I : A₊^∞)` of `I = (y²)`.** The element `xⁿ` lies in the
`n`-th power of the irrelevant ideal, and `xⁿ y ∉ I`. -/
theorem not_exists_irrelevant_pow_mul_X_one_mem :
    ¬ ∃ N : ℕ, ∀ z : MvPolynomial (Fin 2) ℚ,
      z ∈ (HomogeneousIdeal.irrelevant grading).toIdeal ^ N →
        z * (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) ∈ squareIdeal := by
  rintro ⟨N, hN⟩
  refine X_zero_pow_mul_X_one_notMem_squareIdeal N (hN _ ?_)
  exact Ideal.pow_mem_pow
    (HomogeneousIdeal.mem_irrelevant_of_mem grading Nat.zero_lt_two X_zero_mem_grading) N

end Stacks.WeightedProjSaturation

end

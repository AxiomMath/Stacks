module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppFrobeniusNumerator

/-!
# `F_p`-combinations of Frobenius numerators

The all-perfect-core branch of Tag 09F9 needs to know that the subextensions of a joint splitting
field of base Artin--Schreier classes are not ferociously ramified, and the subextensions
correspond to `F_p`-combinations of the members' parameters. So the branch needs the members'
presentation to be **closed under `F_p`-combination**, and that is what this file supplies.

## Which presentation is closed, and which is not

Write, for a depth `N` and a length `n`,

    `Ξ_N(n) = { π⁻¹ ^ n * (∑_{j < n} α j ^ (p ^ N) * π ^ j) + b  |  α : ℕ → A,  b : A }`

the set of parameters presented at depth `N` with pole **bound** `n`. The distinction that decides
the question is between that and the *terminal* shape of
`Stacks.EppTheorem.exists_terminal_of_frobeniusNumerator`, which additionally carries
  `IsUnit (β 0)` and
`¬ p ∣ n'`. Those two pin `n'` to the pole **order** rather than a bound, and the pole order is not
stable under `F_p`-combination: leading terms cancel, so a combination of parameters of pole order
`n` can have pole order below `n`. On that shape the closure statement is **false**, and the
characteristic-`2` example in `EppFrobeniusNumerator.lean`'s module docstring — `π⁻³` and
`π⁻³ + π⁻²` both minimal of pole order `3`, their sum `π⁻²` of pole order `2` — is exactly a
witness.

On the bound shape `Ξ_N(n)` it is **true**, and the two lemmas below are the content: `Ξ_N` is
monotone in the length, and `Ξ_N(M)` is an `F_p`-subspace at the *same* depth `N`, with the
integral part of a combination exactly `∑ i, c i * b i`. No unit hypothesis on any leading
coefficient, no `¬ p ∣ n i`, no dependence on the size of the index set, and no side condition
relating `M` to `N` — the depth condition belongs to the reduction that consumes this, not to the
closure itself.

## Main results

* `Stacks.EppTheorem.exists_pad_sum_pow` — **padding**, `Ξ_N(m) ⊆ Ξ_N(n)` for `m ≤ n` in the form
  the
  algebra needs: multiplying a depth-`N` numerator of length `m` by `π ^ k` gives one of length
  `k + m`, by shifting the coefficients up and padding with `0`. Legal because `0 = 0 ^ (p ^ N)`,
  which is where `ExpChar` enters and the only thing it is used for.
* `Stacks.EppTheorem.sum_natCast_mul_sum_pow` — the coefficientwise form: an `F_p`-combination of
  numerators of one common length is the numerator whose `j`-th coefficient is the combination of
  the `j`-th coefficients. This is `sum_natCast_mul_pow_expChar_pow` applied under the sum, i.e.
  the iterated Frobenius being additive.
* `Stacks.EppTheorem.exists_frobeniusNumerator_of_sum` — **closure.** An `F_p`-combination of
  parameters in
  `Ξ_N(n i)` with `n i ≤ M` lies in `Ξ_N(M)`, with integral part exactly `∑ i, c i * b i`. The
  proof pads each member from `n i` up to `M`, which is what makes one common length available for
  the previous lemma.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
  Addendum 20
-/

@[expose] public section

namespace Stacks.EppTheorem

/-- **Padding a Frobenius numerator to a longer bound.**

A depth-`N` Frobenius numerator of length `m`, multiplied by `π ^ k`, is a depth-`N` Frobenius
numerator of length `k + m`: shift the coefficients up by `k` and pad the bottom `k` places with
`0`. The padding is legal because `0 = 0 ^ (p ^ N)`, so the padded coefficients are still
`p ^ N`-th powers — that is the whole role of `ExpChar A p` here.

This is `Ξ_N(m) ⊆ Ξ_N(n)` for `m ≤ n` in the form the algebra consumes, with `k = n - m`. -/
theorem exists_pad_sum_pow {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p] (N k m : ℕ)
    (π : A) (α : ℕ → A) :
    π ^ k * (∑ j ∈ Finset.range m, α j ^ (p ^ N) * π ^ j)
      = ∑ j ∈ Finset.range (k + m), (if k ≤ j then α (j - k) else 0) ^ (p ^ N) * π ^ j := by
  classical
  have hq : p ^ N ≠ 0 := (expChar_pow_pos A p N).ne'
  have h0 : (∑ j ∈ Finset.range k,
      (if k ≤ j then α (j - k) else (0 : A)) ^ (p ^ N) * π ^ j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hlt : ¬ k ≤ j := by simp only [Finset.mem_range] at hj; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hlt), zero_pow hq, zero_mul]
  rw [Finset.sum_range_add, h0, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.le_add_right k j)), Nat.add_sub_cancel_left,
    pow_add]
  ring

/-- **An `F_p`-combination of numerators of one common length, coefficientwise.**

The `j`-th coefficient of the combination is the combination of the `j`-th coefficients, and it is
again a `p ^ N`-th power because the iterated Frobenius is additive
(`sum_natCast_mul_pow_expChar_pow`). Cancellation between members is therefore invisible to the
shape: it happens inside a coefficient, not to the length. -/
theorem sum_natCast_mul_sum_pow {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p] (N M : ℕ)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (α : ι → ℕ → A) (π : A) :
    ∑ i ∈ s, (c i : A) * (∑ j ∈ Finset.range M, α i j ^ (p ^ N) * π ^ j)
      = ∑ j ∈ Finset.range M, (∑ i ∈ s, (c i : A) * α i j) ^ (p ^ N) * π ^ j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sum_natCast_mul_pow_expChar_pow p N s c (fun i => α i j), Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The bound shape is closed under `F_p`-combination.**

An `F_p`-linear combination of parameters presented at depth `N` with pole bounds `n i ≤ M` is
again presented at depth `N` with pole bound `M`, and its integral part is exactly
`∑ i, c i * b i`.

No unit hypothesis on any leading coefficient, no `¬ p ∣ n i`, no dependence on the size of the
index set, and no side condition relating `M` to `N`. That is the point of stating closure on the
*bound* shape: on the terminal shape, where `IsUnit (β 0)` and `¬ p ∣ n` pin the length to the pole
order, the statement is false, because pole order is not stable under combination.

The proof pads each member from its own `n i` up to the common `M` by `exists_pad_sum_pow` — which
is where `n i ≤ M` is used and the only place it is used — and then combines coefficientwise by
`sum_natCast_mul_sum_pow`. -/
theorem exists_frobeniusNumerator_of_sum {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (p : ℕ) [ExpChar A p] (N : ℕ) (π : A) (hπ : algebraMap A K π ≠ 0)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (n : ι → ℕ) (M : ℕ)
    (hn : ∀ i ∈ s, n i ≤ M) (α : ι → ℕ → A) (b : ι → A) (ξ : ι → K)
    (hξ : ∀ i ∈ s, ξ i = (algebraMap A K π)⁻¹ ^ (n i) *
      algebraMap A K (∑ j ∈ Finset.range (n i), α i j ^ (p ^ N) * π ^ j)
      + algebraMap A K (b i)) :
    ∃ β : ℕ → A, ∑ i ∈ s, (c i : K) * ξ i
      = (algebraMap A K π)⁻¹ ^ M *
          algebraMap A K (∑ j ∈ Finset.range M, β j ^ (p ^ N) * π ^ j)
        + algebraMap A K (∑ i ∈ s, (c i : A) * b i) := by
  classical
  set T := algebraMap A K π with hT
  set pad : ι → ℕ → A := fun i j => if M - n i ≤ j then α i (j - (M - n i)) else 0 with hpad
  refine ⟨fun j => ∑ i ∈ s, (c i : A) * pad i j, ?_⟩
  have key : ∀ i ∈ s, (c i : K) * ξ i
      = T⁻¹ ^ M * algebraMap A K ((c i : A) *
          ∑ j ∈ Finset.range M, pad i j ^ (p ^ N) * π ^ j)
        + algebraMap A K ((c i : A) * b i) := by
    intro i hi
    have hle := hn i hi
    have h2 : T⁻¹ ^ (M - n i) * T ^ (M - n i) = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hπ)]
    have hMn : T⁻¹ ^ (n i) = T⁻¹ ^ M * algebraMap A K (π ^ (M - n i)) := by
      have h1 : T⁻¹ ^ M = T⁻¹ ^ (n i) * T⁻¹ ^ (M - n i) := by
        rw [← pow_add]; congr 1; omega
      rw [map_pow, ← hT, h1, mul_assoc, h2, mul_one]
    have hp := exists_pad_sum_pow p N (M - n i) (n i) π (α i)
    rw [show M - n i + n i = M from by omega] at hp
    rw [hξ i hi, hMn, hpad, ← hp]
    simp only [map_mul, map_natCast, map_pow, ← hT]
    ring
  have hA : (∑ i ∈ s, algebraMap A K ((c i : A) *
        ∑ j ∈ Finset.range M, pad i j ^ (p ^ N) * π ^ j))
      = algebraMap A K
        (∑ j ∈ Finset.range M, (∑ i ∈ s, (c i : A) * pad i j) ^ (p ^ N) * π ^ j) := by
    rw [← map_sum]
    exact congrArg (algebraMap A K) (sum_natCast_mul_sum_pow p N M s c pad π)
  have hB : (∑ i ∈ s, algebraMap A K ((c i : A) * b i))
      = algebraMap A K (∑ i ∈ s, (c i : A) * b i) := (map_sum _ _ _).symm
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB]

end Stacks.EppTheorem

end

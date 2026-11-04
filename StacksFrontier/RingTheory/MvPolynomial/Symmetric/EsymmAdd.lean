module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Elementary symmetric functions of sums and of pairwise sums

For multisets `s` and `t` of elements of a commutative semiring, the elementary symmetric
functions of the union `s + t` are the convolution of those of `s` and `t`:

  `e_k(s + t) = ∑_{i + j = k} e_i(s) e_j(t)`.

For a multiset of *pairwise sums* `{a + b | a ∈ s, b ∈ t}` (with multiplicity, `|s| = r`,
`|t| = n`) the first two elementary symmetric functions are

  `e_1 = n e_1(s) + r e_1(t)`,
  `e_2 = n e_2(s) + r e_2(t) + C(n, 2) e_1(s)² + (r n - 1) e_1(s) e_1(t) + C(r, 2) e_1(t)²`.

These are the "formal computations" behind the Chern classes of a tensor product: if `s` and `t`
are the Chern roots of two vector bundles, the pairwise sums are the Chern roots of their tensor
product.

## Main results

* `Multiset.esymm_cons_succ`: `e_{k+1}(a :: s) = a e_k(s) + e_{k+1}(s)`.
* `Multiset.esymm_add`: the convolution formula for `e_k(s + t)`.
* `Multiset.esymm_one_map_add_product` and `Multiset.esymm_two_map_add_product`: the first two
  elementary symmetric functions of the multiset of pairwise sums.

## References

* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
-/

@[expose] public section

namespace Multiset

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Adjoining an element `a` to `s` gives `e_{k+1}(a :: s) = a e_k(s) + e_{k+1}(s)`. -/
theorem esymm_cons_succ (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = a * s.esymm k + s.esymm (k + 1) := by
  simp [esymm, powersetCard_cons, map_map, prod_cons, sum_map_mul_left, add_comm]

/-- Every elementary symmetric function of positive degree of the empty multiset is zero. -/
@[simp]
theorem esymm_zero_left_succ (k : ℕ) : (0 : Multiset R).esymm (k + 1) = 0 := by
  simp [esymm, powersetCard_zero_right]

/-- The first elementary symmetric function `e_1(s)` of a multiset is the sum of its elements. -/
theorem esymm_one_eq_sum (s : Multiset R) : s.esymm 1 = s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => rw [esymm_cons_succ, esymm_zero, ih, sum_cons, mul_one]

/-- The elementary symmetric functions of a union of multisets are the convolution of those of
the two multisets. -/
theorem esymm_add (s t : Multiset R) (k : ℕ) :
    (s + t).esymm k = ∑ p ∈ Finset.antidiagonal k, s.esymm p.1 * t.esymm p.2 := by
  induction s using Multiset.induction generalizing k with
  | empty =>
    cases k with
    | zero => simp
    | succ k =>
      rw [zero_add, Finset.Nat.sum_antidiagonal_succ, esymm_zero, one_mul, Finset.sum_eq_zero,
        add_zero]
      intro p _
      rw [esymm_zero_left_succ, zero_mul]
  | cons a s ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [cons_add, esymm_cons_succ, ih, ih, Finset.Nat.sum_antidiagonal_succ,
        Finset.Nat.sum_antidiagonal_succ, esymm_zero, esymm_zero, Finset.mul_sum]
      simp only [esymm_cons_succ, add_mul, Finset.sum_add_distrib, mul_assoc]
      ring

/-- The first elementary symmetric function is additive: `e_1(s + t) = e_1(s) + e_1(t)`. -/
theorem esymm_add_one (s t : Multiset R) : (s + t).esymm 1 = s.esymm 1 + t.esymm 1 := by
  simp [esymm_one_eq_sum]

/-- The second elementary symmetric function of a sum of multisets:
`e_2(s + t) = e_2(s) + e_1(s) e_1(t) + e_2(t)`. -/
theorem esymm_add_two (s t : Multiset R) :
    (s + t).esymm 2 = s.esymm 2 + s.esymm 1 * t.esymm 1 + t.esymm 2 := by
  rw [esymm_add, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero]
  simp only [Finset.sum_singleton, esymm_zero]
  ring

/-- Translating every element of `s` by `b` adds `|s| b` to the first elementary symmetric
function. -/
theorem esymm_one_map_add_const (s : Multiset R) (b : R) :
    (s.map (· + b)).esymm 1 = s.esymm 1 + card s • b := by
  simp [esymm_one_eq_sum, sum_map_add]

/-- Adjoining `b` to `t` adds the translate `s.map (· + b)` to the multiset of pairwise sums. -/
private theorem map_add_product_cons (s t : Multiset R) (b : R) :
    ((s ×ˢ (b ::ₘ t)).map fun p => p.1 + p.2) =
      s.map (· + b) + (s ×ˢ t).map fun p => p.1 + p.2 := by
  rw [product_cons, map_add, map_map]
  rfl

/-- The first elementary symmetric function of the multiset of pairwise sums
`{a + b | a ∈ s, b ∈ t}` is `|t| e_1(s) + |s| e_1(t)`. -/
theorem esymm_one_map_add_product (s t : Multiset R) :
    ((s ×ˢ t).map fun p => p.1 + p.2).esymm 1 = card t • s.esymm 1 + card s • t.esymm 1 := by
  induction t using Multiset.induction with
  | empty => simp
  | cons b t ih =>
    rw [map_add_product_cons, esymm_add_one, ih, card_cons, esymm_cons_succ, esymm_zero, mul_one,
      esymm_one_map_add_const, nsmul_add, succ_nsmul]
    abel

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

private theorem natCast_choose_two_mul_two (n : ℕ) :
    ((n.choose 2 : ℕ) : R) * 2 = n * ((n : R) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

/-- Translating every element of `s` by `b` changes the second elementary symmetric function by
`(|s| - 1) b e_1(s) + C(|s|, 2) b²`. -/
theorem esymm_two_map_add_const (s : Multiset R) (b : R) :
    (s.map (· + b)).esymm 2 =
      s.esymm 2 + ((card s : ℤ) - 1) • (b * s.esymm 1) + (card s).choose 2 • b ^ 2 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [map_cons, esymm_cons_succ, ih, esymm_one_map_add_const, esymm_cons_succ,
      esymm_cons_succ, esymm_zero, card_cons, Nat.choose_succ_succ', Nat.choose_one_right]
    simp only [zsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

/-- The second elementary symmetric function of the multiset of pairwise sums
`{a + b | a ∈ s, b ∈ t}`, for `|s| = r` and `|t| = n`, is

  `n e_2(s) + r e_2(t) + C(n, 2) e_1(s)² + (r n - 1) e_1(s) e_1(t) + C(r, 2) e_1(t)²`. -/
theorem esymm_two_map_add_product (s t : Multiset R) :
    ((s ×ˢ t).map fun p => p.1 + p.2).esymm 2 =
      card t • s.esymm 2 + card s • t.esymm 2 + (card t).choose 2 • s.esymm 1 ^ 2 +
        ((card s * card t : ℤ) - 1) • (s.esymm 1 * t.esymm 1) +
          (card s).choose 2 • t.esymm 1 ^ 2 := by
  induction t using Multiset.induction with
  | empty => simp
  | cons b t ih =>
    have hn := natCast_choose_two_mul_two (R := R) (card s)
    rw [map_add_product_cons, esymm_add_two, esymm_one_map_add_product, ih,
      esymm_one_map_add_const, esymm_two_map_add_const, card_cons, esymm_cons_succ,
      esymm_cons_succ, esymm_zero, Nat.choose_succ_succ', Nat.choose_one_right]
    simp only [zsmul_eq_mul, nsmul_eq_mul]
    push_cast
    linear_combination (-(b * t.esymm 1)) * hn

end CommRing

end Multiset

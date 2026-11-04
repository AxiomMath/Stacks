module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import StacksCore.Tactic.StacksAttribute

/-!
# Alternating sums over the subsets of a finite set

Let `x_1, …, x_r` be elements of a commutative ring and write `s_I = ∑_{i ∈ I} x_i` for a subset
`I ⊆ {1, …, r}`. This file computes the two symmetric-function inputs of the alternating product
of the total Chern classes of the exterior powers of a rank-`r` module.

The first is the alternating power sum `∑_{I ⊆ s} (-1)^{#I} s_I^d`, the `#s`-fold finite
difference of `y ↦ y^d` with increments the `x_i`. It vanishes for `d < #s` and equals
`(-1)^{#s} (#s)! ∏_{i ∈ s} x_i` for `d = #s`.

The second is the comparison of the elementary symmetric functions of the family
`(s_I)_{#I even}` with those of `(s_I)_{#I odd}`: by Newton's identities the first computation
forces them to agree in every degree below `r`, and in degree `r` their difference is
`-(r-1)! x_1 ⋯ x_r`.

## Main definitions

* `AlgebraicGeometry.altSubsetPowSum` — the alternating power sum `∑_{I ⊆ s} (-1)^{#I} s_I^d`.
* `AlgebraicGeometry.evenCardSubsets`, `AlgebraicGeometry.oddCardSubsets` — the subsets of
  `Fin r` of even and of odd cardinality.
* `AlgebraicGeometry.subsetSumEsymm`, `AlgebraicGeometry.subsetSumPsum` — the elementary
  symmetric functions and the power sums of the family `(s_I)_{I ∈ p}` for a collection `p` of
  subsets of `Fin r`.

## Main results

* `AlgebraicGeometry.altSubsetPowSum_eq_zero_of_lt` and
  `AlgebraicGeometry.altSubsetPowSum_card` — the finite-difference computation.
* `AlgebraicGeometry.newton_subsetSumEsymm` — Newton's identity for the family `(s_I)_{I ∈ p}`,
  obtained from `MvPolynomial.mul_esymm_eq_sum` by evaluation.
* `AlgebraicGeometry.subsetSumEsymm_even_eq_odd` — the even and odd elementary symmetric
  functions agree in every degree `k < r`.
* `AlgebraicGeometry.subsetSumEsymm_even_sub_odd` — in degree `r` their difference is
  `-(r-1)! x_1 ⋯ x_r`.

## Implementation notes

The cancellation of the factor `k` in Newton's identity needs a torsion-free ring, so the two
comparison results are first proved in `MvPolynomial (Fin r) ℤ` with `x_i = X i` and then
transported to an arbitrary commutative ring by `MvPolynomial.aeval`. The family indexed by a
collection `p` of subsets is presented to Mathlib's Newton identities as the family indexed by
all of `Finset (Fin r)` which is `0` off `p`; a product over a set of subsets meeting the
complement of `p` then vanishes, which is `AlgebraicGeometry.sum_powersetCard_univ_prod_ite`.

## References

* [Stacks Project, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE)
-/

@[expose] public section

namespace AlgebraicGeometry

open Finset MvPolynomial

variable {ι : Type*} {A : Type*} [CommRing A]

/-! ### The alternating power sums over the subsets of a finite set -/

/-- The alternating power sum `∑_{I ⊆ s} (-1)^{#I} (∑_{i ∈ I} x i)^d`: the `#s`-fold finite
difference of `y ↦ y^d` with increments `x i` for `i ∈ s`. -/
def altSubsetPowSum (x : ι → A) (s : Finset ι) (d : ℕ) : A :=
  ∑ I ∈ s.powerset, (-1 : A) ^ #I * (∑ i ∈ I, x i) ^ d

/-- The recursion for the alternating power sums in the size of the index set: adding one
increment replaces the sum by the signed binomial transform of the lower sums. -/
private theorem altSubsetPowSum_insert [DecidableEq ι] (x : ι → A) {j : ι} {s : Finset ι}
    (hj : j ∉ s) (d : ℕ) :
    altSubsetPowSum x (insert j s) d
      = -∑ k ∈ range d, altSubsetPowSum x s k * x j ^ (d - k) * (d.choose k : A) := by
  classical
  have e2 : ∀ I ∈ s.powerset,
      (-1 : A) ^ #(insert j I) * (∑ i ∈ insert j I, x i) ^ d
        = ∑ k ∈ range (d + 1),
            -((-1 : A) ^ #I * (∑ i ∈ I, x i) ^ k * x j ^ (d - k) * (d.choose k : A)) := by
    intro I hI
    have hjI : j ∉ I := fun h => hj (Finset.mem_powerset.mp hI h)
    rw [Finset.card_insert_of_notMem hjI, Finset.sum_insert hjI, pow_succ,
      add_comm (x j) (∑ i ∈ I, x i), add_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e3 : ∀ k ∈ range (d + 1),
      (∑ I ∈ s.powerset,
          -((-1 : A) ^ #I * (∑ i ∈ I, x i) ^ k * x j ^ (d - k) * (d.choose k : A)))
        = -(altSubsetPowSum x s k * x j ^ (d - k) * (d.choose k : A)) := by
    intro k _
    rw [altSubsetPowSum, Finset.sum_mul, Finset.sum_mul, sum_neg_distrib]
  have hgoal : altSubsetPowSum x (insert j s) d
      = altSubsetPowSum x s d
        + ∑ k ∈ range (d + 1), -(altSubsetPowSum x s k * x j ^ (d - k) * (d.choose k : A)) := by
    rw [altSubsetPowSum, Finset.sum_powerset_insert hj, Finset.sum_congr rfl e2, Finset.sum_comm,
      Finset.sum_congr rfl e3]
    rfl
  rw [hgoal, Finset.sum_range_succ, sum_neg_distrib]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
  ring

/-- **The finite-difference computation.** The `#s`-fold alternating power sum vanishes in every
degree below `#s`, and in degree `#s` it is `(-1)^{#s} (#s)! ∏_{i ∈ s} x i`. -/
private theorem altSubsetPowSum_main (x : ι → A) (s : Finset ι) :
    (∀ d < #s, altSubsetPowSum x s d = 0) ∧
      altSubsetPowSum x s #s
        = (-1 : A) ^ #s * ((Nat.factorial #s : ℕ) : A) * ∏ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun d hd => absurd hd (by simp), ?_⟩
      simp [altSubsetPowSum]
  | insert j s hj ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have hcard : #(insert j s) = #s + 1 := Finset.card_insert_of_notMem hj
      refine ⟨fun d hd => ?_, ?_⟩
      · rw [altSubsetPowSum_insert x hj d, Finset.sum_eq_zero, neg_zero]
        intro k hk
        rw [hcard] at hd
        rw [ih0 k (by have := Finset.mem_range.mp hk; omega), zero_mul, zero_mul]
      · rw [hcard, altSubsetPowSum_insert x hj (#s + 1), Finset.sum_range_succ,
          Finset.sum_eq_zero (fun k hk => by
            rw [ih0 k (Finset.mem_range.mp hk), zero_mul, zero_mul]),
          ih1, Finset.prod_insert hj, Nat.add_sub_cancel_left]
        push_cast [Nat.choose_succ_self_right, Nat.factorial_succ]
        ring

/-- The alternating power sum vanishes in every degree below the size of the index set. -/
theorem altSubsetPowSum_eq_zero_of_lt (x : ι → A) (s : Finset ι) {d : ℕ} (hd : d < #s) :
    altSubsetPowSum x s d = 0 :=
  (altSubsetPowSum_main x s).1 d hd

/-- In degree equal to the size of the index set the alternating power sum is
`(-1)^{#s} (#s)! ∏_{i ∈ s} x i`. -/
theorem altSubsetPowSum_card (x : ι → A) (s : Finset ι) :
    altSubsetPowSum x s #s
      = (-1 : A) ^ #s * ((Nat.factorial #s : ℕ) : A) * ∏ i ∈ s, x i :=
  (altSubsetPowSum_main x s).2

/-! ### The symmetric functions of the subset sums -/

/-- The subsets of `Fin r` of even cardinality. -/
def evenCardSubsets (r : ℕ) : Finset (Finset (Fin r)) :=
  Finset.univ.filter fun I => Even #I

/-- The subsets of `Fin r` of odd cardinality. -/
def oddCardSubsets (r : ℕ) : Finset (Finset (Fin r)) :=
  Finset.univ.filter fun I => ¬ Even #I

/-- The `k`-th elementary symmetric function of the subset sums `∑_{i ∈ I} x i`, as `I` runs
through a collection `p` of subsets of `Fin r`. -/
def subsetSumEsymm {r : ℕ} (x : Fin r → A) (p : Finset (Finset (Fin r))) (k : ℕ) : A :=
  ∑ T ∈ p.powersetCard k, ∏ I ∈ T, ∑ i ∈ I, x i

/-- The `k`-th power sum of the subset sums `∑_{i ∈ I} x i`, as `I` runs through a collection `p`
of subsets of `Fin r`. -/
def subsetSumPsum {r : ℕ} (x : Fin r → A) (p : Finset (Finset (Fin r))) (k : ℕ) : A :=
  ∑ I ∈ p, (∑ i ∈ I, x i) ^ k

/-- The zeroth elementary symmetric function of any family is `1`. -/
theorem subsetSumEsymm_zero {r : ℕ} (x : Fin r → A) (p : Finset (Finset (Fin r))) :
    subsetSumEsymm x p 0 = 1 := by
  simp [subsetSumEsymm]

/-- A sum over all subsets of a fixed size of a product of a family supported on `s` is the same
sum restricted to the subsets of `s`. -/
theorem sum_powersetCard_univ_prod_ite {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (s : Finset ι') (f : ι' → A) (k : ℕ) :
    ∑ T ∈ (Finset.univ : Finset ι').powersetCard k, ∏ i ∈ T, (if i ∈ s then f i else 0)
      = ∑ T ∈ s.powersetCard k, ∏ i ∈ T, f i := by
  classical
  have hsub : s.powersetCard k ⊆ (Finset.univ : Finset ι').powersetCard k :=
    Finset.powersetCard_mono (Finset.subset_univ s)
  have hzero : ∀ T ∈ (Finset.univ : Finset ι').powersetCard k, T ∉ s.powersetCard k →
      ∏ i ∈ T, (if i ∈ s then f i else 0) = 0 := by
    intro T hT hT'
    obtain ⟨i, hiT, his⟩ : ∃ i ∈ T, i ∉ s := by
      by_contra h
      exact hT' (Finset.mem_powersetCard.mpr
        ⟨fun i hi => not_not.mp fun hn => h ⟨i, hi, hn⟩, (Finset.mem_powersetCard.mp hT).2⟩)
    exact Finset.prod_eq_zero hiT (by simp [his])
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun T hT => Finset.prod_congr rfl fun i hi => ?_
  simp [(Finset.mem_powersetCard.mp hT).1 hi]

/-- Evaluating the elementary symmetric polynomial in the family of subset sums supported on `p`
gives the elementary symmetric function of the subset sums over `p`. -/
theorem aeval_esymm_subsetSum {r : ℕ} (x : Fin r → A) (p : Finset (Finset (Fin r))) (k : ℕ) :
    aeval (fun I : Finset (Fin r) => if I ∈ p then ∑ i ∈ I, x i else 0)
        (esymm (Finset (Fin r)) ℤ k) = subsetSumEsymm x p k := by
  classical
  rw [esymm, map_sum, subsetSumEsymm,
    ← sum_powersetCard_univ_prod_ite p (fun I => ∑ i ∈ I, x i) k]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun I _ => aeval_X _ I

/-- Evaluating the power-sum polynomial in the family of subset sums supported on `p` gives the
power sum of the subset sums over `p`, in every positive degree. -/
theorem aeval_psum_subsetSum {r : ℕ} (x : Fin r → A) (p : Finset (Finset (Fin r))) {k : ℕ}
    (hk : k ≠ 0) :
    aeval (fun I : Finset (Fin r) => if I ∈ p then ∑ i ∈ I, x i else 0)
        (psum (Finset (Fin r)) ℤ k) = subsetSumPsum x p k := by
  classical
  have hterm : ∀ I : Finset (Fin r),
      aeval (fun J : Finset (Fin r) => if J ∈ p then ∑ i ∈ J, x i else 0)
          ((X I : MvPolynomial (Finset (Fin r)) ℤ) ^ k)
        = if I ∈ p then (∑ i ∈ I, x i) ^ k else 0 := by
    intro I
    rw [map_pow, aeval_X]
    split
    · rfl
    · exact zero_pow hk
  rw [psum, map_sum, subsetSumPsum, Finset.sum_congr rfl fun I _ => hterm I,
    Finset.sum_ite_mem, Finset.univ_inter]

/-- **Newton's identity for the subset sums.** The identity of `MvPolynomial.mul_esymm_eq_sum`,
read on the family of subset sums over a collection `p` of subsets of `Fin r`. -/
theorem newton_subsetSumEsymm {r : ℕ} (x : Fin r → A) (p : Finset (Finset (Fin r))) (k : ℕ) :
    (k : A) * subsetSumEsymm x p k
      = (-1) ^ (k + 1) * ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1) ^ a.1 * subsetSumEsymm x p a.1 * subsetSumPsum x p a.2 := by
  classical
  have h := congrArg (aeval (fun I : Finset (Fin r) => if I ∈ p then ∑ i ∈ I, x i else 0))
    (mul_esymm_eq_sum (Finset (Fin r)) ℤ k)
  rw [map_mul, map_natCast, aeval_esymm_subsetSum, map_mul, map_pow, map_neg, map_one,
    map_sum] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp ha
  have hadd : a.1 + a.2 = k := Finset.mem_antidiagonal.mp hmem
  rw [map_mul, map_mul, map_pow, map_neg, map_one, aeval_esymm_subsetSum,
    aeval_psum_subsetSum x p (show a.2 ≠ 0 by omega)]

/-- The difference between the even and the odd power sums of the subset sums is the alternating
power sum over all subsets. -/
theorem subsetSumPsum_even_sub_odd {r : ℕ} (x : Fin r → A) (d : ℕ) :
    subsetSumPsum x (evenCardSubsets r) d - subsetSumPsum x (oddCardSubsets r) d
      = altSubsetPowSum x Finset.univ d := by
  classical
  have h1 : ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin r) => Even #I),
      (-1 : A) ^ #I * (∑ i ∈ I, x i) ^ d = subsetSumPsum x (evenCardSubsets r) d := by
    rw [subsetSumPsum, evenCardSubsets]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [Even.neg_one_pow (Finset.mem_filter.mp hI).2, one_mul]
  have h2 : ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin r) => ¬ Even #I),
      (-1 : A) ^ #I * (∑ i ∈ I, x i) ^ d = -subsetSumPsum x (oddCardSubsets r) d := by
    rw [subsetSumPsum, oddCardSubsets, ← sum_neg_distrib]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hI).2), neg_one_mul]
  rw [altSubsetPowSum, Finset.powerset_univ,
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset (Fin r)))
      (fun I => Even #I) (fun I => (-1 : A) ^ #I * (∑ i ∈ I, x i) ^ d), h1, h2,
    ← sub_eq_add_neg]

/-- The elementary symmetric functions of the subset sums are universal: evaluating the ones
built from the variables of `MvPolynomial (Fin r) ℤ` at `x` gives the ones built from `x`. -/
theorem aeval_subsetSumEsymm {r : ℕ} (x : Fin r → A) (p : Finset (Finset (Fin r))) (k : ℕ) :
    aeval x (subsetSumEsymm (X : Fin r → MvPolynomial (Fin r) ℤ) p k)
      = subsetSumEsymm x p k := by
  rw [subsetSumEsymm, subsetSumEsymm, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [map_sum, Finset.sum_congr rfl fun i _ => aeval_X x i]

/-! ### The even-odd comparison, over the integral polynomial ring and in general -/

/-- The even and odd power sums of the subset sums of the variables of `MvPolynomial (Fin r) ℤ`
agree in every degree below `r`. -/
private theorem subsetSumPsum_even_eq_odd_poly (r : ℕ) {d : ℕ} (hd : d < r) :
    subsetSumPsum (X : Fin r → MvPolynomial (Fin r) ℤ) (evenCardSubsets r) d
      = subsetSumPsum X (oddCardSubsets r) d := by
  have h := subsetSumPsum_even_sub_odd (X : Fin r → MvPolynomial (Fin r) ℤ) d
  rw [altSubsetPowSum_eq_zero_of_lt _ _ (by simpa using hd)] at h
  exact sub_eq_zero.mp h

/-- Newton's identity for the difference of the even and the odd elementary symmetric functions. -/
private theorem mul_subsetSumEsymm_even_sub_odd {r : ℕ} (x : Fin r → A) (k : ℕ) :
    (k : A) * (subsetSumEsymm x (evenCardSubsets r) k - subsetSumEsymm x (oddCardSubsets r) k)
      = (-1) ^ (k + 1) * ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
        ((-1 : A) ^ a.1 * subsetSumEsymm x (evenCardSubsets r) a.1 *
            subsetSumPsum x (evenCardSubsets r) a.2
          - (-1) ^ a.1 * subsetSumEsymm x (oddCardSubsets r) a.1 *
            subsetSumPsum x (oddCardSubsets r) a.2) := by
  rw [mul_sub, newton_subsetSumEsymm x (evenCardSubsets r) k,
    newton_subsetSumEsymm x (oddCardSubsets r) k, ← mul_sub, ← Finset.sum_sub_distrib]

/-- The even and odd elementary symmetric functions of the subset sums of the variables of
`MvPolynomial (Fin r) ℤ` agree in every degree below `r`. -/
private theorem subsetSumEsymm_even_eq_odd_poly (r : ℕ) :
    ∀ k, k < r → subsetSumEsymm (X : Fin r → MvPolynomial (Fin r) ℤ) (evenCardSubsets r) k
      = subsetSumEsymm X (oddCardSubsets r) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [subsetSumEsymm_zero, subsetSumEsymm_zero]
    have key := mul_subsetSumEsymm_even_sub_odd (X : Fin r → MvPolynomial (Fin r) ℤ) k
    rw [Finset.sum_eq_zero, mul_zero] at key
    · exact sub_eq_zero.mp
        ((mul_eq_zero.mp key).resolve_left (Nat.cast_ne_zero.mpr hkpos.ne'))
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
      rw [ih a.1 ha.2 (by omega), subsetSumPsum_even_eq_odd_poly r (show a.2 < r by omega),
        sub_self]

/-- In degree `r` the difference of the even and odd elementary symmetric functions of the subset
sums of the variables of `MvPolynomial (Fin r) ℤ` is `-(r-1)! X_0 ⋯ X_{r-1}`. -/
private theorem subsetSumEsymm_even_sub_odd_poly (r : ℕ) (hr : r ≠ 0) :
    subsetSumEsymm (X : Fin r → MvPolynomial (Fin r) ℤ) (evenCardSubsets r) r
        - subsetSumEsymm X (oddCardSubsets r) r
      = -(Nat.factorial (r - 1) • ∏ i, (X i : MvPolynomial (Fin r) ℤ)) := by
  classical
  have hmem : ((0 : ℕ), r) ∈ (Finset.antidiagonal r).filter (fun a => a.1 < r) :=
    Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (Nat.zero_add r), Nat.pos_of_ne_zero hr⟩
  have hsingle : ∑ a ∈ (Finset.antidiagonal r).filter (fun a => a.1 < r),
      ((-1 : MvPolynomial (Fin r) ℤ) ^ a.1 * subsetSumEsymm X (evenCardSubsets r) a.1 *
          subsetSumPsum X (evenCardSubsets r) a.2
        - (-1) ^ a.1 * subsetSumEsymm X (oddCardSubsets r) a.1 *
          subsetSumPsum X (oddCardSubsets r) a.2)
      = altSubsetPowSum (X : Fin r → MvPolynomial (Fin r) ℤ) Finset.univ r := by
    rw [Finset.sum_eq_single_of_mem ((0 : ℕ), r) hmem]
    · simp only [pow_zero, subsetSumEsymm_zero, one_mul]
      exact subsetSumPsum_even_sub_odd _ _
    · intro b hb hne
      obtain ⟨hmemb, hltb⟩ := Finset.mem_filter.mp hb
      have hadd : b.1 + b.2 = r := Finset.mem_antidiagonal.mp hmemb
      have hb1 : b.1 ≠ 0 := fun h => hne (Prod.ext h (by omega))
      rw [subsetSumEsymm_even_eq_odd_poly r b.1 hltb,
        subsetSumPsum_even_eq_odd_poly r (show b.2 < r by omega), sub_self]
  have hcard : #(Finset.univ : Finset (Fin r)) = r := by simp
  have htop : altSubsetPowSum (X : Fin r → MvPolynomial (Fin r) ℤ) Finset.univ r
      = (-1 : MvPolynomial (Fin r) ℤ) ^ r * ((Nat.factorial r : ℕ) : MvPolynomial (Fin r) ℤ) *
        ∏ i, (X i : MvPolynomial (Fin r) ℤ) := by
    have h := altSubsetPowSum_card (X : Fin r → MvPolynomial (Fin r) ℤ) Finset.univ
    rwa [hcard] at h
  have hsign : (-1 : MvPolynomial (Fin r) ℤ) ^ (r + 1) * (-1) ^ r = -1 := by
    rw [← pow_add, show r + 1 + r = 2 * r + 1 by omega, pow_succ, pow_mul]
    simp
  have hmain : (-1 : MvPolynomial (Fin r) ℤ) ^ (r + 1) *
      ((-1 : MvPolynomial (Fin r) ℤ) ^ r * ((Nat.factorial r : ℕ) : MvPolynomial (Fin r) ℤ) *
        ∏ i, (X i : MvPolynomial (Fin r) ℤ))
      = -(((Nat.factorial r : ℕ) : MvPolynomial (Fin r) ℤ) *
        ∏ i, (X i : MvPolynomial (Fin r) ℤ)) := by
    rw [show (-1 : MvPolynomial (Fin r) ℤ) ^ (r + 1) *
          ((-1 : MvPolynomial (Fin r) ℤ) ^ r * ((Nat.factorial r : ℕ) : MvPolynomial (Fin r) ℤ) *
            ∏ i, (X i : MvPolynomial (Fin r) ℤ))
        = ((-1 : MvPolynomial (Fin r) ℤ) ^ (r + 1) * (-1) ^ r) *
          (((Nat.factorial r : ℕ) : MvPolynomial (Fin r) ℤ) *
            ∏ i, (X i : MvPolynomial (Fin r) ℤ)) from by ring, hsign, neg_one_mul]
  have key : (r : MvPolynomial (Fin r) ℤ) *
      (subsetSumEsymm X (evenCardSubsets r) r - subsetSumEsymm X (oddCardSubsets r) r)
      = (r : MvPolynomial (Fin r) ℤ) *
        -(Nat.factorial (r - 1) • ∏ i, (X i : MvPolynomial (Fin r) ℤ)) := by
    rw [mul_subsetSumEsymm_even_sub_odd (X : Fin r → MvPolynomial (Fin r) ℤ) r,
      hsingle, htop, hmain, nsmul_eq_mul, mul_neg, ← mul_assoc,
      ← Nat.cast_mul, Nat.mul_factorial_pred hr]
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hr) key

/-- **The even and odd elementary symmetric functions of the subset sums agree below degree `r`.**
For `x_1, …, x_r` in a commutative ring and `k < r`, the `k`-th elementary symmetric function of
the sums `∑_{i ∈ I} x_i` over the even-cardinality subsets `I` equals the one over the
odd-cardinality subsets. -/
theorem subsetSumEsymm_even_eq_odd {r : ℕ} (x : Fin r → A) {k : ℕ} (hk : k < r) :
    subsetSumEsymm x (evenCardSubsets r) k = subsetSumEsymm x (oddCardSubsets r) k := by
  have h := congrArg (aeval x) (subsetSumEsymm_even_eq_odd_poly r k hk)
  rwa [aeval_subsetSumEsymm, aeval_subsetSumEsymm] at h

/-- **The degree-`r` difference of the even and odd elementary symmetric functions of the subset
sums.** For `x_1, …, x_r` in a commutative ring with `r ≥ 1` it is `-(r-1)! x_1 ⋯ x_r`. -/
theorem subsetSumEsymm_even_sub_odd {r : ℕ} (x : Fin r → A) (hr : r ≠ 0) :
    subsetSumEsymm x (evenCardSubsets r) r - subsetSumEsymm x (oddCardSubsets r) r
      = -(Nat.factorial (r - 1) • ∏ i, x i) := by
  have h := congrArg (aeval x) (subsetSumEsymm_even_sub_odd_poly r hr)
  rwa [map_sub, aeval_subsetSumEsymm, aeval_subsetSumEsymm, map_neg, map_nsmul, map_prod,
    Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => aeval_X x i] at h

end AlgebraicGeometry

end

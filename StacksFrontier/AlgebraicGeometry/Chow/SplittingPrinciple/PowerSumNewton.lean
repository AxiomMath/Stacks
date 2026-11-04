module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.PowerSumPolynomials
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Newton's identities for the universal power-sum polynomials, and additivity

Let `R` be a commutative ring and let `a = (a_0, a_1, a_2, …)` be a sequence in `R` with
`a_0 = 1`, to be thought of as the elementary symmetric functions `1, c_1, c_2, …` of some
"roots". Evaluating the universal power-sum polynomials `P_p ∈ ℤ[c_1, c_2, …]` of
[Stacks, Tag 0F9B] (`AlgebraicGeometry.powerSumPolynomial`) at `c_i = a_i` gives elements
`P_p(a) ∈ R`. This file proves, with no hypothesis on `R` beyond commutativity:

* **Newton's identities** `(p + 1) a_{p+1} = ∑_{i ≤ p} (-1)^i P_{i+1}(a) a_{p-i}`;
* **additivity under the Cauchy product**: if `c_n = ∑_{j ≤ n} a_{n-j} b_j` with `a_0 = b_0 = 1`,
  then `P_p(c) = P_p(a) + P_p(b)` for every `p`.

The second statement is the algebraic content of [Stacks, Tag 0F9C]: the Chern roots of the
middle term of a short exact sequence are those of the two outer terms. It is proved with the
generating series `A(t) = ∑ a_n t^n`: Newton's identities say `t A'(t) = L_a(t) A(t)` with
`L_a(t) = ∑_{p ≥ 1} (-1)^{p-1} P_p(a) t^p`, the Euler operator `t d/dt` is a derivation, and
`A` is a unit, so `L_{ab} = L_a + L_b`.

## Main definitions

* `AlgebraicGeometry.powerSumEval` — `P_p(a)`.

## Main results

* `AlgebraicGeometry.powerSumEval_succ` — Newton's recursion for the evaluation.
* `AlgebraicGeometry.newton_powerSumEval` — Newton's identities.
* `AlgebraicGeometry.powerSumEval_convolution` — `P_p(a * b) = P_p(a) + P_p(b)`.
* `AlgebraicGeometry.map_powerSumEval` — evaluation commutes with ring homomorphisms.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open MvPolynomial Finset

variable {R : Type*} [CommRing R]

/-- The universal power-sum polynomial `P_p` of Stacks 0F9B evaluated at `c_i = a_i`. -/
def powerSumEval (a : ℕ → R) (p : ℕ) : R :=
  aeval (fun i : ℕ+ => a i) (powerSumPolynomial p : MvPolynomial ℕ+ ℤ)

/-- The power sum `P_0(a)` vanishes. -/
theorem powerSumEval_zero (a : ℕ → R) : powerSumEval a 0 = 0 := by
  simp [powerSumEval]

/-- **Newton's recursion**, evaluated:
`P_{p+1}(a) = ∑_{j < p} (-1)^j a_{j+1} P_{p-j}(a) + (-1)^p (p + 1) a_{p+1}`. -/
theorem powerSumEval_succ (a : ℕ → R) (p : ℕ) :
    powerSumEval a (p + 1) =
      ∑ j ∈ range p, (-1) ^ j * a (j + 1) * powerSumEval a (p - j) +
        (-1) ^ p * ((p : R) + 1) * a (p + 1) := by
  simp [powerSumEval, coe_powerSumPolynomial_succ]

/-- **Evaluation commutes with ring homomorphisms.** -/
theorem map_powerSumEval {S : Type*} [CommRing S] (φ : R →+* S) (a : ℕ → R) (p : ℕ) :
    φ (powerSumEval a p) = powerSumEval (fun i => φ (a i)) p := by
  unfold powerSumEval
  exact congrArg (fun ψ : MvPolynomial ℕ+ ℤ →ₐ[ℤ] S => ψ (powerSumPolynomial p : MvPolynomial ℕ+ ℤ))
    (MvPolynomial.comp_aeval (R := ℤ) (fun i : ℕ+ => a i) φ.toIntAlgHom)

/-- `(-1)^p * (-1)^p = 1`. -/
private theorem neg_one_pow_mul_self (p : ℕ) : ((-1 : R) ^ p * (-1) ^ p) = 1 := by
  rw [← mul_pow, mul_neg_one, neg_neg, one_pow]

private theorem neg_one_pow_mul_neg_one_pow (p i : ℕ) (hi : i < p) :
    ((-1 : R) ^ p * (-1) ^ (p - 1 - i)) = -(-1) ^ i := by
  rw [← pow_add, show p + (p - 1 - i) = 2 * (p - 1 - i) + (i + 1) by omega, pow_add, pow_mul,
    neg_one_sq, one_pow, one_mul, pow_succ, mul_neg_one]

/-- **Newton's identities**: for `a_0 = 1`,
`(p + 1) a_{p+1} = ∑_{i ≤ p} (-1)^i P_{i+1}(a) a_{p-i}`. -/
theorem newton_powerSumEval (a : ℕ → R) (ha : a 0 = 1) (p : ℕ) :
    ((p : R) + 1) * a (p + 1) =
      ∑ i ∈ range (p + 1), (-1) ^ i * powerSumEval a (i + 1) * a (p - i) := by
  rw [sum_range_succ, Nat.sub_self, ha, mul_one, powerSumEval_succ, mul_add, mul_sum]
  have hcancel : ∑ i ∈ range p, (-1) ^ i * powerSumEval a (i + 1) * a (p - i) +
      ∑ j ∈ range p, (-1) ^ p * ((-1) ^ j * a (j + 1) * powerSumEval a (p - j)) = 0 := by
    rw [← sum_range_reflect (fun j => (-1 : R) ^ p * ((-1) ^ j * a (j + 1) *
      powerSumEval a (p - j))) p, ← sum_add_distrib]
    refine sum_eq_zero fun i hi => ?_
    have hip : i < p := mem_range.mp hi
    rw [show p - 1 - i + 1 = p - i by omega, show p - (p - 1 - i) = i + 1 by omega,
      ← mul_assoc, ← mul_assoc, neg_one_pow_mul_neg_one_pow p i hip]
    ring
  linear_combination (-1 : R) * hcancel -
    (((p : R) + 1) * a (p + 1)) * neg_one_pow_mul_self (R := R) p

open PowerSeries in
/-- The Euler operator `t d/dt` on power series. -/
private def eulerSeries (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => (n : R) * PowerSeries.coeff n f

open PowerSeries in
private theorem eulerSeries_mul (f g : PowerSeries R) :
    eulerSeries (f * g) = eulerSeries f * g + f * eulerSeries g := by
  ext n
  simp only [eulerSeries, coeff_mk, map_add, PowerSeries.coeff_mul, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun ij hij => ?_
  rw [← mem_antidiagonal.mp hij]
  push_cast
  ring

open PowerSeries in
/-- The generating series `∑_{p ≥ 1} (-1)^{p-1} P_p(a) t^p`. -/
private def logSeries (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n - 1) * powerSumEval a n

open PowerSeries in
private theorem eulerSeries_mk (a : ℕ → R) (ha : a 0 = 1) :
    eulerSeries (PowerSeries.mk a) = logSeries a * PowerSeries.mk a := by
  ext n
  rw [eulerSeries, coeff_mk, coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (logSeries a) *
      coeff j (PowerSeries.mk a)) n]
  rcases n with _ | p
  · simp [logSeries]
  · rw [sum_range_succ', Nat.cast_succ, newton_powerSumEval a ha p]
    simp only [logSeries, coeff_mk, ite_true, zero_mul, add_zero, Nat.add_sub_cancel,
      Nat.succ_ne_zero, ite_false, Nat.add_sub_add_right]

/-- **Additivity of the power sums under the Cauchy product.** If `a_0 = b_0 = 1` and
`c_n = ∑_{j ≤ n} a_{n-j} b_j`, then `P_p(c) = P_p(a) + P_p(b)`. This is the algebraic content of
Stacks 0F9C. -/
theorem powerSumEval_convolution (a b : ℕ → R) (ha : a 0 = 1) (hb : b 0 = 1) (p : ℕ) :
    powerSumEval (fun n => ∑ j ∈ range (n + 1), a (n - j) * b j) p =
      powerSumEval a p + powerSumEval b p := by
  set c : ℕ → R := fun n => ∑ j ∈ range (n + 1), a (n - j) * b j with hcdef
  have hc : c 0 = 1 := by simp [hcdef, ha, hb]
  have hmul : PowerSeries.mk c = PowerSeries.mk a * PowerSeries.mk b := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i
        (PowerSeries.mk a) * PowerSeries.coeff j (PowerSeries.mk b)) n,
      ← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    have hjn : j < n + 1 := mem_range.mp hj
    simp only [PowerSeries.coeff_mk]
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
  have hunit : IsUnit (PowerSeries.mk c) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, hc]
    exact isUnit_one
  have key : (logSeries c - (logSeries a + logSeries b)) * PowerSeries.mk c = 0 := by
    rw [sub_mul, ← eulerSeries_mk c hc, hmul, eulerSeries_mul, eulerSeries_mk a ha,
      eulerSeries_mk b hb]
    ring
  rcases p with _ | p
  · simp [powerSumEval_zero]
  · have h := congrArg (PowerSeries.coeff (p + 1)) (sub_eq_zero.mp (hunit.mul_left_eq_zero.mp key))
    simp only [logSeries, map_add, PowerSeries.coeff_mk, Nat.succ_ne_zero, ite_false,
      Nat.add_sub_cancel] at h
    linear_combination (-1 : R) ^ p * h -
      (powerSumEval c (p + 1) - powerSumEval a (p + 1) - powerSumEval b (p + 1)) *
        neg_one_pow_mul_self (R := R) p

/-! ### Evaluation at pairwise commuting elements of a ring -/

/-- **Evaluation at commuting elements of a ring, transported.** Let `φ : A ⟶ B` be a ring
homomorphism, `a` a sequence in a set `s ⊆ A` of pairwise commuting elements and `b` a sequence
in a set `t ⊆ B` of pairwise commuting elements, with `φ(a_i) = b_i` and `φ(s)` contained in the
subring generated by `t`. Then `φ` carries `P_p(a)`, computed in the commutative subring
generated by `s`, to `P_p(b)`, computed in the commutative subring generated by `t`. -/
theorem map_coe_powerSumEval_closure {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) {s : Set A}
    {t : Set B} (hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (ht : ∀ x ∈ t, ∀ y ∈ t, x * y = y * x)
    (a : ℕ → A) (ha : ∀ i, a i ∈ s) (b : ℕ → B) (hb : ∀ i, b i ∈ t) (hab : ∀ i, φ (a i) = b i)
    (hst : ∀ x ∈ s, φ x ∈ Subring.closure t) (p : ℕ) :
    φ ((@powerSumEval (Subring.closure s) (Subring.closureCommRingOfComm hs)
        (fun i => ⟨a i, Subring.subset_closure (ha i)⟩) p : Subring.closure s) : A) =
      ((@powerSumEval (Subring.closure t) (Subring.closureCommRingOfComm ht)
        (fun i => ⟨b i, Subring.subset_closure (hb i)⟩) p : Subring.closure t) : B) := by
  have := Subring.isMulCommutative_closure hs
  have := Subring.isMulCommutative_closure ht
  have hle : Subring.closure s ≤ (Subring.closure t).comap φ := Subring.closure_le.mpr hst
  let ψ : Subring.closure s →+* Subring.closure t :=
    φ.restrict (Subring.closure s) (Subring.closure t) fun _ hx => hle hx
  open scoped IsMulCommutative in
  have h := map_powerSumEval ψ (fun i => ⟨a i, Subring.subset_closure (ha i)⟩) p
  have hψ : (fun i => ψ ⟨a i, Subring.subset_closure (ha i)⟩) =
      fun i => (⟨b i, Subring.subset_closure (hb i)⟩ : Subring.closure t) :=
    funext fun i => Subtype.ext (hab i)
  rw [hψ] at h
  exact congrArg Subtype.val h

end AlgebraicGeometry

end

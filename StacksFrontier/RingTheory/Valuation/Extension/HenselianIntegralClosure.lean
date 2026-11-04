module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure

/-!
# The integral closure of a henselian valuation ring in an algebraic extension

Let `V` be a henselian valuation ring and `L` a field which is algebraic over `V` (for instance
any algebraic extension of the fraction field of `V`). Then the integral closure `C` of `V` in
`L` is a valuation ring of `L`: for every `x ∈ L`, `x ∈ C` or `x⁻¹ ∈ C`.

The proof uses only that `C` is local, which holds because a domain integral over a henselian
local ring is local
(`Stacks.DiscreteValuationRing.Ramification.isLocalRing_of_isIntegral_of_henselianLocalRing`).
Write `∑ᵢ aᵢ xⁱ = 0` with `aᵢ ∈ V` and `a_k` a unit (possible as `V` is a valuation ring), and
put `t_m = ∑_{j ≥ m} a_j x^{j - m}`. For `m ≥ 1` the element `x t_m` is integral over `V`: it
stabilises the `V`-module spanned by `1, x, …, x^{n-1}`, because
`x t_m · x^i = ∑_{j ≥ m} a_j x^{j-m+1+i} = -∑_{j < m} a_j x^{j-m+1+i}`. Hence `u = t_k` and
`x u` lie in `C`, and `u - a_k = x t_{k+1}` with `t_{k+1} ∈ C`. As `C` is local, `u` or
`a_k - u` is a unit of `C`: in the first case `x = (x u) u⁻¹ ∈ C`, in the second
`x⁻¹ = -t_{k+1} (a_k - u)⁻¹ ∈ C`.

## Main definitions

* `ValuationRing.integralClosureValuationSubring`: the integral closure as a valuation subring.

## Main results

* `ValuationRing.isIntegral_mul_sum_Ico`: `x t_m` is integral for `m ≥ 1`.
* `ValuationRing.mem_or_inv_mem_integralClosure_of_henselian`: the integral closure of a
  henselian valuation ring in an algebraic extension is a valuation ring.

## References

* [Stacks Project, Tag 04GJ](https://stacks.math.columbia.edu/tag/04GJ) (a finite algebra over a
  henselian local ring is a product of local rings).
* O. Zariski, P. Samuel, *Commutative algebra* II, Chapter VI, §7 (extensions of valuations to
  algebraic extensions).
-/

@[expose] public noncomputable section

open Polynomial

namespace ValuationRing

section Integrality

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]

/-- **`x t_m` is integral for `m ≥ 1`.** If `∑_{i ≤ n} aᵢ xⁱ = 0` with `aᵢ ∈ R`, then for every
`m ≥ 1` the element `x · ∑_{m ≤ j ≤ n} a_j x^{j - m}` is integral over `R`. -/
theorem isIntegral_mul_sum_Ico {x : L} {a : ℕ → R} {n : ℕ}
    (h : ∑ i ∈ Finset.range (n + 1), algebraMap R L (a i) * x ^ i = 0) {m : ℕ} (hm : 1 ≤ m) :
    IsIntegral R (x * ∑ j ∈ Finset.Ico m (n + 1), algebraMap R L (a j) * x ^ (j - m)) := by
  rcases Nat.lt_or_ge n m with hnm | hmn
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, mul_zero]
    exact isIntegral_zero
  set z := x * ∑ j ∈ Finset.Ico m (n + 1), algebraMap R L (a j) * x ^ (j - m) with hz
  set N : Submodule R L := Submodule.span R (Set.range fun i : Fin n ↦ x ^ (i : ℕ)) with hN
  have hgen : ∀ i : ℕ, i < n → x ^ i ∈ N := fun i hi ↦
    Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hterm : ∀ (c : R) (e : ℕ), e < n → algebraMap R L c * x ^ e ∈ N := fun c e he ↦ by
    rw [← Algebra.smul_def]
    exact N.smul_mem c (hgen e he)
  have hzx : ∀ i : ℕ, i < n → z * x ^ i ∈ N := by
    intro i hi
    have hexp : z * x ^ i =
        ∑ j ∈ Finset.Ico m (n + 1), algebraMap R L (a j) * x ^ (j - m + 1 + i) := by
      rw [hz, mul_comm x, mul_assoc, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [pow_add, pow_succ]
      ring
    rcases Nat.lt_or_ge (i + 1) m with him | hmi
    · rw [hexp]
      refine N.sum_mem fun j hj ↦ hterm _ _ ?_
      have := Finset.mem_Ico.mp hj
      omega
    · have hsplit := Finset.sum_range_add_sum_Ico
        (fun j ↦ algebraMap R L (a j) * x ^ (j + (i + 1 - m))) (show m ≤ n + 1 by omega)
      have htot : ∑ j ∈ Finset.range (n + 1), algebraMap R L (a j) * x ^ (j + (i + 1 - m)) =
          0 := by
        have : ∑ j ∈ Finset.range (n + 1), algebraMap R L (a j) * x ^ (j + (i + 1 - m)) =
            x ^ (i + 1 - m) * ∑ j ∈ Finset.range (n + 1), algebraMap R L (a j) * x ^ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [pow_add]
          ring
        rw [this, h, mul_zero]
      have hIco : ∑ j ∈ Finset.Ico m (n + 1), algebraMap R L (a j) * x ^ (j - m + 1 + i) =
          ∑ j ∈ Finset.Ico m (n + 1), algebraMap R L (a j) * x ^ (j + (i + 1 - m)) :=
        Finset.sum_congr rfl fun j hj ↦ by
          have := Finset.mem_Ico.mp hj
          congr 2
          omega
      rw [hexp, hIco, eq_neg_of_add_eq_zero_right (hsplit.trans htot)]
      refine N.neg_mem (N.sum_mem fun j hj ↦ hterm _ _ ?_)
      have := Finset.mem_range.mp hj
      omega
  have hstab : ∀ y ∈ N, z • y ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hzx i i.2
    | zero => simp
    | add y y' _ _ hy hy' =>
      rw [smul_add]
      exact N.add_mem hy hy'
    | smul c y _ hy =>
      rw [smul_comm]
      exact N.smul_mem c hy
  have hNbot : N ≠ ⊥ := by
    intro hbot
    have h1 : (1 : L) ∈ N := by
      have := hgen 0 (by omega)
      rwa [pow_zero] at this
    rw [hbot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  exact isIntegral_of_smul_mem_submodule N hNbot (Submodule.fg_span (Set.finite_range _)) z
    hstab

end Integrality

section Normalization

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

/-- In a valuation ring, among finitely many elements one divides all the others. -/
theorem exists_dvd_forall {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → V) :
    ∃ j ∈ s, ∀ i ∈ s, f j ∣ f i := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | cons a s has ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨a, Finset.mem_cons_self a ∅, fun i hi ↦ ?_⟩
      simp only [Finset.mem_cons, Finset.notMem_empty, or_false] at hi
      rw [hi]
    · obtain ⟨j, hj, hjd⟩ := ih hne
      rcases ValuationRing.dvd_total (f j) (f a) with hja | haj
      · refine ⟨j, Finset.mem_cons_of_mem hj, fun i hi ↦ ?_⟩
        rcases Finset.mem_cons.mp hi with rfl | hi
        · exact hja
        · exact hjd i hi
      · refine ⟨a, Finset.mem_cons_self a s, fun i hi ↦ ?_⟩
        rcases Finset.mem_cons.mp hi with rfl | hi
        · exact dvd_rfl
        · exact haj.trans (hjd i hi)

variable {L : Type*} [Field L] [Algebra V L] [FaithfulSMul V L]

/-- **A primitive equation.** An element of `L` algebraic over the valuation ring `V` satisfies
an equation `∑_{i ≤ n} aᵢ xⁱ = 0` over `V` one of whose coefficients is `1`. -/
theorem exists_sum_eq_zero_of_isAlgebraic {x : L} (hx : IsAlgebraic V x) :
    ∃ (n : ℕ) (a : ℕ → V) (k : ℕ), k ≤ n ∧ a k = 1 ∧
      ∑ i ∈ Finset.range (n + 1), algebraMap V L (a i) * x ^ i = 0 := by
  classical
  obtain ⟨p, hp0, hpx⟩ := hx
  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  obtain ⟨j, hj, hjd⟩ := exists_dvd_forall p.support hsupp p.coeff
  have hdiv : ∀ i, p.coeff j ∣ p.coeff i := fun i ↦ by
    by_cases hi : i ∈ p.support
    · exact hjd i hi
    · rw [Polynomial.notMem_support_iff.mp hi]
      exact dvd_zero _
  choose b hb using hdiv
  have hcj : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  refine ⟨p.natDegree, b, j, Polynomial.le_natDegree_of_mem_supp j hj, ?_, ?_⟩
  · have := hb j
    exact (mul_eq_left₀ hcj).mp this.symm
  · have hcjL : algebraMap V L (p.coeff j) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective V L)]
      exact hcj
    apply mul_left_cancel₀ hcjL
    rw [mul_zero, Finset.mul_sum, ← hpx, Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← hb i]

end Normalization

section Henselian

variable (V : Type*) [CommRing V] [IsDomain V] [ValuationRing V] [HenselianLocalRing V]
  (L : Type*) [Field L] [Algebra V L] [FaithfulSMul V L] [Algebra.IsAlgebraic V L]

/-- **The integral closure of a henselian valuation ring in an algebraic extension is a
valuation ring**: every `x ∈ L` or its inverse is integral over `V`. -/
theorem mem_or_inv_mem_integralClosure_of_henselian (x : L) :
    x ∈ integralClosure V L ∨ x⁻¹ ∈ integralClosure V L := by
  have : IsLocalRing (integralClosure V L) :=
    Stacks.DiscreteValuationRing.Ramification.isLocalRing_of_isIntegral_of_henselianLocalRing V
      (integralClosure V L)
  obtain ⟨n, a, k, hkn, hak, hsum⟩ :=
    exists_sum_eq_zero_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic (R := V) x)
  set t : ℕ → L := fun m ↦ ∑ j ∈ Finset.Ico m (n + 1), algebraMap V L (a j) * x ^ (j - m)
    with ht
  have ht_succ : ∀ m, m ≤ n → t m = x * t (m + 1) + algebraMap V L (a m) := by
    intro m hmn
    simp only [ht]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Nat.sub_self, pow_zero, mul_one, add_comm,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have := Finset.mem_Ico.mp hj
    rw [show j - m = (j - (m + 1)) + 1 by omega, pow_succ]
    ring
  have ht0 : t 0 = 0 := by
    simp only [ht, Nat.sub_zero, ← Finset.range_eq_Ico]
    exact hsum
  have hint : ∀ m, x * t m ∈ integralClosure V L := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [ht0, mul_zero]
      exact zero_mem _
    · exact isIntegral_mul_sum_Ico hsum hm
  -- every `t m` lies in the integral closure
  have htmem : ∀ m, t m ∈ integralClosure V L := by
    intro m
    rcases Nat.lt_or_ge n m with hnm | hmn
    · have : t m = 0 := by
        simp only [ht]
        rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      rw [this]
      exact zero_mem _
    · rw [ht_succ m hmn]
      exact add_mem (hint _) (Subalgebra.algebraMap_mem _ _)
  have hu1 : t k = x * t (k + 1) + 1 := by rw [ht_succ k hkn, hak, map_one]
  let u' : integralClosure V L := ⟨t k, htmem k⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self u' with h | h
  · left
    obtain ⟨w, hw⟩ := h.exists_right_inv
    have hw' : t k * (w : L) = 1 := congrArg Subtype.val hw
    have : x = (x * t k) * w := by rw [mul_assoc, hw', mul_one]
    rw [this]
    exact mul_mem (hint k) w.2
  · right
    obtain ⟨w, hw⟩ := h.exists_right_inv
    have hw' : (1 - t k) * (w : L) = 1 := congrArg Subtype.val hw
    rw [hu1] at hw'
    have hinv : x⁻¹ = -(t (k + 1) * w) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← hw']
      ring
    rw [hinv]
    exact neg_mem (mul_mem (htmem _) w.2)

/-- **The integral closure of a henselian valuation ring in an algebraic extension**, as a
valuation subring of the extension. -/
def integralClosureValuationSubring : ValuationSubring L :=
  ValuationSubring.ofSubring (integralClosure V L).toSubring
    (mem_or_inv_mem_integralClosure_of_henselian V L)

/-- An element of `L` lies in `integralClosureValuationSubring V L` if and only if it is
integral over `V`. -/
@[simp]
theorem mem_integralClosureValuationSubring {x : L} :
    x ∈ integralClosureValuationSubring V L ↔ x ∈ integralClosure V L := Iff.rfl

end Henselian

end ValuationRing

end

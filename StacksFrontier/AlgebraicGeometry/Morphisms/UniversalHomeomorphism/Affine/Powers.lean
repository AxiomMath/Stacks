module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Finset.Max
public import StacksCore.Tactic.StacksAttribute

/-!
# Powers in a ring extension

If two consecutive powers, starting with an exponent at least two, of an element outside a
subring belong to the subring, then some element outside the subring has both its square and
its cube in the subring.

## Main definitions

No new definitions are introduced.

## Main results

* `Subring.exists_not_mem_and_sq_mem_and_cube_mem_of_pow_mem_of_succ_pow_mem` produces the
  required element from two consecutive powers.

## Implementation notes

A ring extension is represented by a subring of the larger ring. The nonnegative integer
exponent is represented by a natural number.

## References

* [Stacks Project, Tag 0CNA](https://stacks.math.columbia.edu/tag/0CNA)
-/

@[expose] public section

universe u

namespace Subring

/-- Once two consecutive powers of `b` with exponents `n` and `n + 1` lie in `A`, every power
of `b` with exponent at least `n ^ 2` lies in `A`: such an exponent decomposes as a
nonnegative combination of `n` and `n + 1`. -/
private lemma pow_mem_of_ge_sq {B : Type u} [CommRing B] (A : Subring B) {b : B} {n m : ℕ}
    (hn : 2 ≤ n) (hpow : b ^ n ∈ A) (hpow_succ : b ^ (n + 1) ∈ A)
    (hm : n ^ 2 ≤ m) : b ^ m ∈ A := by
  let k := m / n
  let i := m % n
  have hi : i < n := Nat.mod_lt _ (by omega)
  have hkn : n ≤ k :=
    (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [pow_two, Nat.mul_comm] using hm)
  have hdecomp : m = (k - i) * n + i * (n + 1) :=
    calc
      m = k * n + i := by simpa [k, i, Nat.mul_comm] using (Nat.div_add_mod m n).symm
      _ = (k - i) * n + i * (n + 1) := by
        rw [← Nat.sub_add_cancel (show i ≤ k by omega), Nat.add_mul, Nat.mul_succ]
        simp [Nat.add_assoc, Nat.add_comm]
  rw [hdecomp, pow_add, mul_comm (k - i) n, mul_comm i (n + 1), pow_mul, pow_mul]
  exact A.mul_mem (A.pow_mem hpow _) (A.pow_mem hpow_succ _)

/-- **Stacks 0CNA.** If an element outside a subring has two consecutive powers,
with the first exponent at least two, in the subring, then some element outside the subring has
its square and cube in the subring. -/
@[stacks 0CNA]
lemma exists_not_mem_and_sq_mem_and_cube_mem_of_pow_mem_of_succ_pow_mem
    {B : Type u} [CommRing B] (A : Subring B) {b : B} {n : ℕ} (hb : b ∉ A) (hn : 2 ≤ n)
    (hpow : b ^ n ∈ A) (hpow_succ : b ^ (n + 1) ∈ A) :
    ∃ b' : B, b' ∉ A ∧ b' ^ 2 ∈ A ∧ b' ^ 3 ∈ A := by
  classical
  let S : Finset ℕ := (Finset.range (n ^ 2 + 1)).filter (fun i => b ^ i ∉ A)
  have hn2 : 2 ≤ n ^ 2 := le_trans (by decide) (Nat.pow_le_pow_left hn 2)
  have hS : S.Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by simpa using hb⟩⟩
  let i := S.max' hS
  have hi_not : b ^ i ∉ A := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hi_pos : 0 < i := Nat.pos_of_ne_zero fun h => hi_not (by simp [h])
  have hlarge : ∀ m, i < m → b ^ m ∈ A := by
    intro m him
    by_cases hmn : n ^ 2 ≤ m
    · exact pow_mem_of_ge_sq A hn hpow hpow_succ hmn
    · by_contra hmem
      have := Finset.le_max' S m (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hmem⟩)
      omega
  refine ⟨b ^ i, hi_not, ?_, ?_⟩ <;> rw [← pow_mul] <;> exact hlarge _ (by omega)

end Subring

end

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Tactic.NoncommRing

/-!
# The inverse of a Segre series

Let `R` be a ring and let `t : ℕ → R` be a sequence, read as the power series
`t̂ = 1 + t₁ z + t₂ z² + ⋯` with central variable `z` (the term `t₀` is ignored: the series is
normalised to have constant term `1`). Its right inverse `ŝ = s₀ + s₁ z + ⋯` is computed by

`s₀ = 1`,   `s_n = -∑_{j < n} t_{n-j} s_j`   (`n ≥ 1`),

and the *Chern sequence* of `t` is `c_n = (-1)^n s_n`. When `t` is the sequence of Segre
operations `t_i(ℰ) ∩ - = π_*(c₁(𝒪_P(1))^{r-1+i} ∩ π^*-)` of a finite locally free module `ℰ`
(the proof of Stacks 0ERY), `c_n` is the `n`-th Chern class `c_n(ℰ)` of Stacks 0ERZ: pushing the
defining relation of Stacks 0ERY forward after capping with powers of `c₁(𝒪_P(1))` gives
`∑_{j=0}^{n} (-1)^j t_{n-j}(ℰ) c_j(ℰ) = 0` for `n ≥ 1`, which is the recursion above.

The one algebraic fact needed for the additivity of Chern classes is
`PrivateChern.chernSeq_succ_eq_of_segre`: if `x ∈ R` commutes with every `t_i` and the two
Segre sequences satisfy `t_n = t'_n + x t_{n-1}` for `n ≥ 1` (with `t_0 = 1`), that is,
`t̂ (1 - xz) = t̂'`, then `c_{n+1} = c'_{n+1} + x c'_n` for every `n`, that is,
`ĉ = (1 + xz) ĉ'`. No commutativity among the `t_i` is needed.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.segreInverseSeq`: the sequence `s`.
* `AlgebraicGeometry.Space.PrivateChern.chernSeq`: the sequence `c_n = (-1)^n s_n`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.segreInverseSeq_succ_eq_of_segre` and
  `AlgebraicGeometry.Space.PrivateChern.chernSeq_succ_eq_of_segre`: the inverse of
  `t̂ (1 - xz)` is `(1 + xz) ŝ` when `x` commutes with the `t_i`.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* W. Fulton, *Intersection theory*, Section 3.2.
-/

@[expose] public section

namespace AlgebraicGeometry.Space.PrivateChern

variable {R : Type*} [Ring R]

/-- The coefficients of the inverse of the normalised series `1 + t₁ z + t₂ z² + ⋯`:
`s₀ = 1` and `s_n = -∑_{j < n} t_{n-j} s_j` for `n ≥ 1`. -/
def segreInverseSeq (t : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => -∑ j : Fin (n + 1), t (n + 1 - j) * segreInverseSeq t j
termination_by n => n
decreasing_by exact j.2

/-- The constant term of the inverse series is `s₀ = 1`. -/
@[simp]
theorem segreInverseSeq_zero (t : ℕ → R) : segreInverseSeq t 0 = 1 := by
  rw [segreInverseSeq]

/-- The recursion for the inverse series: `s_{n+1} = -∑_{j ≤ n} t_{n+1-j} s_j`. -/
theorem segreInverseSeq_succ (t : ℕ → R) (n : ℕ) :
    segreInverseSeq t (n + 1) =
      -∑ j : Fin (n + 1), t (n + 1 - j) * segreInverseSeq t j := by
  rw [segreInverseSeq]

/-- The Chern sequence `c_n = (-1)^n s_n` of a Segre sequence `t`; equivalently `c₀ = 1` and
`c_n = ∑_{j < n} (-1)^{n-j+1} t_{n-j} c_j`. -/
def chernSeq (t : ℕ → R) (n : ℕ) : R := (-1) ^ n * segreInverseSeq t n

/-- The Chern sequence starts with `c₀ = 1`. -/
@[simp]
theorem chernSeq_zero (t : ℕ → R) : chernSeq t 0 = 1 := by
  simp [chernSeq]

/-- The recursion for the Chern sequence: `c_{n+1} = ∑_{j ≤ n} (-1)^{n-j} t_{n+1-j} c_j`. -/
theorem chernSeq_succ (t : ℕ → R) (n : ℕ) :
    chernSeq t (n + 1) =
      ∑ j : Fin (n + 1), (-1) ^ (n - (j : ℕ)) * (t (n + 1 - j) * chernSeq t j) := by
  rw [chernSeq, segreInverseSeq_succ, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsplit : (-1 : R) ^ (n + 1) = (-1) ^ (n - (j : ℕ)) * (-1) ^ (j : ℕ) * (-1) := by
    rw [← pow_add, ← pow_succ, Nat.sub_add_cancel j.is_le]
  rw [chernSeq, hsplit]
  have hc : Commute ((-1 : R) ^ (j : ℕ)) (t (n + 1 - j)) := (Commute.neg_one_left _).pow_left _
  rw [← mul_assoc (t _), ← hc.eq]
  simp only [mul_neg, mul_one, neg_neg, neg_mul, mul_assoc]

/-- Shared proof of `s_{n+1} = s'_{n+1} - x s'_n` when `t_n = t'_n + t_{n-1} x`. -/
private theorem segreInverseSeq_succ_eq_aux (t t' : ℕ → R) (x : R) (ht0 : t 0 = 1)
    (h : ∀ n, t (n + 1) = t' (n + 1) + t n * x) (n : ℕ) :
    segreInverseSeq t (n + 1) = segreInverseSeq t' (n + 1) - x * segreInverseSeq t' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hj : ∀ j : Fin (n + 1), segreInverseSeq t j = segreInverseSeq t' j -
        x * (if (j : ℕ) = 0 then 0 else segreInverseSeq t' ((j : ℕ) - 1)) := by
      intro j
      rcases j with ⟨j, hjn⟩
      cases j with
      | zero => simp
      | succ j => simpa using ih j (by omega)
    rw [segreInverseSeq_succ, segreInverseSeq_succ t']
    simp_rw [hj, mul_sub]
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ j : Fin (n + 1), t (n + 1 - j) * segreInverseSeq t' j =
        ∑ j : Fin (n + 1), t' (n + 1 - j) * segreInverseSeq t' j +
          ∑ j : Fin (n + 1), t (n - j) * (x * segreInverseSeq t' j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
      rw [show n + 1 - (j : ℕ) = (n - j) + 1 by omega, h, add_mul, mul_assoc]
    have h2 : ∑ j : Fin (n + 1), t (n + 1 - j) *
          (x * (if (j : ℕ) = 0 then 0 else segreInverseSeq t' ((j : ℕ) - 1))) =
        ∑ j : Fin (n + 1), t (n - j) * (x * segreInverseSeq t' j) -
          t 0 * (x * segreInverseSeq t' n) := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (fun j : Fin (n + 1) =>
        t (n - j) * (x * segreInverseSeq t' j))]
      simp only [Fin.val_zero, ite_true, mul_zero, zero_add, Fin.val_succ,
        Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, Fin.val_castSucc, Fin.val_last,
        Nat.sub_self, add_sub_cancel_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show n + 1 - ((j : ℕ) + 1) = n - j by omega]
    rw [h1, h2, ht0, one_mul]
    abel

/-- Passing from the inverse sequences to the Chern sequences: `s_{n+1} = s'_{n+1} - x s'_n`
implies `c_{n+1} = c'_{n+1} + x c'_n`. -/
private theorem chernSeq_succ_eq_aux (t t' : ℕ → R) (x : R) (n : ℕ)
    (h : segreInverseSeq t (n + 1) = segreInverseSeq t' (n + 1) - x * segreInverseSeq t' n) :
    chernSeq t (n + 1) = chernSeq t' (n + 1) + x * chernSeq t' n := by
  have hc : Commute x ((-1 : R) ^ n) := ((Commute.neg_one_left x).pow_left n).symm
  rw [chernSeq, chernSeq, chernSeq, h, mul_sub, pow_succ, ← mul_assoc x, hc.eq, mul_assoc]
  noncomm_ring

/-- **The inverse of `t̂ (1 - xz)` is `(1 + xz) ŝ`.** If `x` commutes with every `t_i` and
`t_n = t'_n + x t_{n-1}` for every `n ≥ 1`, where `t₀ = 1`, then `s_n = s'_n - x s'_{n-1}` for
every `n ≥ 1`, `s` and `s'` being the inverse sequences of `t` and `t'`. -/
theorem segreInverseSeq_succ_eq_of_segre (t t' : ℕ → R) (x : R) (ht0 : t 0 = 1)
    (hx : ∀ i, Commute x (t i)) (h : ∀ n, t (n + 1) = t' (n + 1) + x * t n) (n : ℕ) :
    segreInverseSeq t (n + 1) = segreInverseSeq t' (n + 1) - x * segreInverseSeq t' n := by
  exact segreInverseSeq_succ_eq_aux t t' x ht0 (fun n => by rw [h n, (hx n).eq]) n

/-- **The Chern sequence of `t̂ (1 - xz)` is `(1 + xz) ĉ`.** If `x` commutes with every `t_i` and
`t_n = t'_n + x t_{n-1}` for every `n ≥ 1`, where `t₀ = 1`, then `c_{n+1} = c'_{n+1} + x c'_n` for
every `n`, `c` and `c'` being the Chern sequences of `t` and `t'`. -/
theorem chernSeq_succ_eq_of_segre (t t' : ℕ → R) (x : R) (ht0 : t 0 = 1)
    (hx : ∀ i, Commute x (t i)) (h : ∀ n, t (n + 1) = t' (n + 1) + x * t n) (n : ℕ) :
    chernSeq t (n + 1) = chernSeq t' (n + 1) + x * chernSeq t' n := by
  exact chernSeq_succ_eq_aux t t' x n (segreInverseSeq_succ_eq_of_segre t t' x ht0 hx h n)

/-- **The inverse of `t̂ (1 - xz)` is `(1 - xz) ŝ'`, with no commutativity.** If
`t_n = t'_n + t_{n-1} x` for every `n ≥ 1`, where `t₀ = 1`, then `s_n = s'_n - x s'_{n-1}` for
every `n ≥ 1`, `s` and `s'` being the inverse sequences of `t` and `t'`: the hypothesis says
`t̂ (1 - xz) = t̂'`, so `(1 - xz) ŝ'` is a right inverse of `t̂`, which has only one. -/
theorem segreInverseSeq_succ_eq_of_segre_mul (t t' : ℕ → R) (x : R) (ht0 : t 0 = 1)
    (h : ∀ n, t (n + 1) = t' (n + 1) + t n * x) (n : ℕ) :
    segreInverseSeq t (n + 1) = segreInverseSeq t' (n + 1) - x * segreInverseSeq t' n := by
  exact segreInverseSeq_succ_eq_aux t t' x ht0 h n

/-- **The Chern sequence of `t̂ (1 - xz)` is `(1 + xz) ĉ'`, with no commutativity.** If
`t_n = t'_n + t_{n-1} x` for every `n ≥ 1`, where `t₀ = 1`, then `c_{n+1} = c'_{n+1} + x c'_n`
for every `n`. -/
theorem chernSeq_succ_eq_of_segre_mul (t t' : ℕ → R) (x : R) (ht0 : t 0 = 1)
    (h : ∀ n, t (n + 1) = t' (n + 1) + t n * x) (n : ℕ) :
    chernSeq t (n + 1) = chernSeq t' (n + 1) + x * chernSeq t' n := by
  exact chernSeq_succ_eq_aux t t' x n (segreInverseSeq_succ_eq_of_segre_mul t t' x ht0 h n)

end AlgebraicGeometry.Space.PrivateChern

end

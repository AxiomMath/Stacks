module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# The divided power relations of a Leibniz map

Let `δ` be a divided power structure on an ideal `J` of a commutative ring `B` and let
`D : B →+ M` be an additive map into a `B`-module obeying the Leibniz rule.  The *divided power
relation* of `D` at `x ∈ J` in degree `n` is `D (δ_{n+1} x) - δ_n x · D x`, the obstruction to the
divided power chain rule.  Its dependence on `x` is not linear, but the relations in all degrees
at `x` determine the relations in all degrees at `b · x` and at `x + y`: scaling multiplies the
relation by `b^{n+1}`, and the relation at a sum is a divided-power-weighted sum of the relations
at the two summands.  Consequently the set of `x ∈ J` whose relations all lie in a fixed submodule
of `M` is itself a submodule, so the chain rule on a generating set of `J` already forces it
everywhere.

## Main definitions

* `Crystalline.dpRelation` — the relation `D (δ_{n+1} x) - δ_n x · D x`.

## Main results

* `Crystalline.dpRelation_smul` — `dpRelation` at `b * x` is `b ^ (n + 1)` times the one at `x`.
* `Crystalline.dpRelation_add` — the relation at `x + y` as a sum of the relations at `x` and `y`
  weighted by divided powers.
* `Crystalline.dpRelation_mem_of_mem_span` — if every relation at every element of a set `S ⊆ J`
  lies in a submodule `P`, then so does every relation at every element of the span of `S`.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
-/

@[expose] public section

open Finset

namespace Crystalline

variable {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {J : Ideal B}

/-- The divided power relation `D (δ_{n+1} x) - δ_n x · D x` of an additive map `D` at an element
`x` in degree `n`: the obstruction to the divided power chain rule at `x`. -/
def dpRelation (hJ : DividedPowers J) (D : B →+ M) (x : B) (n : ℕ) : M :=
  D (hJ.dpow (n + 1) x) - hJ.dpow n x • D x

/-- The divided power relation, unfolded. -/
theorem dpRelation_eq (hJ : DividedPowers J) (D : B →+ M) (x : B) (n : ℕ) :
    dpRelation hJ D x n = D (hJ.dpow (n + 1) x) - hJ.dpow n x • D x := rfl

/-- A linear map carries the divided power relations of `D` to those of its composite with it. -/
theorem map_dpRelation {N : Type*} [AddCommGroup N] [Module B N] (φ : M →ₗ[B] N)
    (hJ : DividedPowers J) (D : B →+ M) (x : B) (n : ℕ) :
    φ (dpRelation hJ D x n) = dpRelation hJ ((φ : M →+ N).comp D) x n := by
  rw [dpRelation_eq, dpRelation_eq, map_sub, map_smul]
  rfl

/-- The divided power relation at zero vanishes. -/
@[simp]
theorem dpRelation_zero (hJ : DividedPowers J) (D : B →+ M) (n : ℕ) :
    dpRelation hJ D 0 n = 0 := by
  rw [dpRelation, hJ.dpow_eval_zero (Nat.succ_ne_zero n), map_zero, smul_zero, sub_zero]

section Leibniz

variable {hJ : DividedPowers J} {D : B →+ M}
  (hmul : ∀ a b : B, D (a * b) = a • D b + b • D a)

include hmul

/-- A Leibniz map kills the unit of the ring. -/
theorem map_one_eq_zero_of_leibniz : D 1 = 0 := by
  have h := hmul 1 1
  rw [one_mul, one_smul] at h
  have h' : D 1 + 0 = D 1 + D 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

/-- A Leibniz map on a power of an element. -/
theorem map_pow_succ_of_leibniz (a : B) (n : ℕ) :
    D (a ^ (n + 1)) = (((n : B) + 1) * a ^ n) • D a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, hmul, ih, smul_smul]
      push_cast
      rw [← add_smul]
      congr 1
      ring

/-- **Scaling the divided power relation.**  The relation at `b * x` is `b ^ (n + 1)` times the
relation at `x`, because the divided powers of `b * x` are `b ^ n` times those of `x` and the
excess Leibniz terms cancel against `δ_n x · x = (n + 1) · δ_{n+1} x`. -/
theorem dpRelation_smul {x : B} (hx : x ∈ J) (b : B) (n : ℕ) :
    dpRelation hJ D (b * x) n = b ^ (n + 1) • dpRelation hJ D x n := by
  have hmulx : hJ.dpow n x * x = ((n : B) + 1) * hJ.dpow (n + 1) x := by
    have h := hJ.mul_dpow (m := n) (n := 1) hx
    rw [hJ.dpow_one hx] at h
    rw [h, Nat.choose_succ_self_right]
    push_cast
    ring
  have hda : hJ.dpow (n + 1) x • D (b ^ (n + 1)) = (b ^ n * hJ.dpow n x * x) • D b := by
    rw [map_pow_succ_of_leibniz hmul, smul_smul, mul_assoc (b ^ n) _ x, hmulx]
    congr 1
    ring
  have key : D (b ^ (n + 1) * hJ.dpow (n + 1) x) =
      b ^ (n + 1) • D (hJ.dpow (n + 1) x) + (b ^ n * hJ.dpow n x * x) • D b := by
    rw [hmul, hda]
  have key2 : (b ^ n * hJ.dpow n x) • D (b * x) =
      (b ^ (n + 1) * hJ.dpow n x) • D x + (b ^ n * hJ.dpow n x * x) • D b := by
    rw [hmul, smul_add, smul_smul, smul_smul,
      show b ^ n * hJ.dpow n x * b = b ^ (n + 1) * hJ.dpow n x from by ring]
  rw [dpRelation, dpRelation, hJ.dpow_mul hx, hJ.dpow_mul hx, key, key2, smul_sub, smul_smul]
  abel

/-- The expansion of `D (δ_{n+1} (x + y))` by the addition rule for divided powers. -/
private theorem map_dpow_add {x y : B} (hx : x ∈ J) (hy : y ∈ J) (n : ℕ) :
    D (hJ.dpow (n + 1) (x + y)) =
      (∑ k ∈ range (n + 1), hJ.dpow (n - k) x • D (hJ.dpow (k + 1) y)) +
        ∑ k ∈ range (n + 1), hJ.dpow (n - k) y • D (hJ.dpow (k + 1) x) := by
  rw [hJ.dpow_add' hx hy, map_sum]
  have hterm (i : ℕ) : D (hJ.dpow i x * hJ.dpow (n + 1 - i) y) =
      hJ.dpow i x • D (hJ.dpow (n + 1 - i) y) + hJ.dpow (n + 1 - i) y • D (hJ.dpow i x) :=
    hmul _ _
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_range_succ, Nat.sub_self, hJ.dpow_zero hy,
      map_one_eq_zero_of_leibniz hmul, smul_zero, add_zero, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show n + 1 - (n + 1 - 1 - k) = k + 1 from by omega,
      show n + 1 - 1 - k = n - k from by omega]
  · rw [Finset.sum_range_succ']
    have h0 : hJ.dpow (n + 1 - 0) y • D (hJ.dpow 0 x) = 0 := by
      rw [hJ.dpow_zero hx, map_one_eq_zero_of_leibniz hmul, smul_zero]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [show n + 1 - (k + 1) = n - k from by omega]

/-- **The divided power relation at a sum.**  The relation at `x + y` in degree `n` is the sum of
the relations at `x` and at `y` in the lower degrees, weighted by the complementary divided
powers of the other summand. -/
theorem dpRelation_add {x y : B} (hx : x ∈ J) (hy : y ∈ J) (n : ℕ) :
    dpRelation hJ D (x + y) n =
      ∑ k ∈ range (n + 1),
        (hJ.dpow (n - k) x • dpRelation hJ D y k + hJ.dpow (n - k) y • dpRelation hJ D x k) := by
  have hsum' : ∀ {x y : B}, x ∈ J → y ∈ J →
      ∑ k ∈ range (n + 1), (hJ.dpow (n - k) y * hJ.dpow k x) = hJ.dpow n (x + y) := by
    intro x y hx hy
    rw [hJ.dpow_add' hx hy]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hsum : ∑ k ∈ range (n + 1), (hJ.dpow (n - k) x * hJ.dpow k y) = hJ.dpow n (x + y) := by
    rw [add_comm x y]
    exact hsum' hy hx
  have hterm (k : ℕ) :
      hJ.dpow (n - k) x • dpRelation hJ D y k + hJ.dpow (n - k) y • dpRelation hJ D x k =
        (hJ.dpow (n - k) x • D (hJ.dpow (k + 1) y) +
            hJ.dpow (n - k) y • D (hJ.dpow (k + 1) x)) -
          ((hJ.dpow (n - k) x * hJ.dpow k y) • D y +
            (hJ.dpow (n - k) y * hJ.dpow k x) • D x) := by
    rw [dpRelation, dpRelation, smul_sub, smul_sub, smul_smul, smul_smul]
    abel
  rw [Finset.sum_congr rfl fun k _ ↦ hterm k, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, hsum, hsum' hx hy,
    ← map_dpow_add hmul hx hy n, dpRelation, map_add, smul_add]
  abel

/-- **The divided power relations of a span.**  If every relation at every element of a subset `S`
of `J` lies in a submodule `P`, then every relation at every element of the span of `S` lies in
`P`; the two previous lemmas make that set a submodule. -/
theorem dpRelation_mem_of_mem_span (P : Submodule B M) {S : Set B} (hSJ : S ⊆ J)
    (hS : ∀ s ∈ S, ∀ n : ℕ, dpRelation hJ D s n ∈ P)
    {x : B} (hx : x ∈ Submodule.span B S) (n : ℕ) : dpRelation hJ D x n ∈ P := by
  have hspan : Submodule.span B S ≤ J := Submodule.span_le.mpr hSJ
  have key : ∀ z ∈ Submodule.span B S, ∀ m : ℕ, dpRelation hJ D z m ∈ P := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem s hs => exact hS s hs
    | zero =>
        intro m
        rw [dpRelation_zero]
        exact P.zero_mem
    | add u v hu hv ihu ihv =>
        intro m
        rw [dpRelation_add hmul (hspan hu) (hspan hv) m]
        exact P.sum_mem fun k _ ↦ P.add_mem (P.smul_mem _ (ihv k)) (P.smul_mem _ (ihu k))
    | smul b u hu ihu =>
        intro m
        rw [smul_eq_mul, dpRelation_smul hmul (hspan hu) b m]
        exact P.smul_mem _ (ihu m)
  exact key x hx n

end Leibniz

end Crystalline

end

module

public import StacksFrontier.NumberTheory.BombieriStepanov.UpperBound

/-!
# A Riemann inequality from two functions of consecutive pole orders

Let `P₀` be a residue-rational place of degree one of a function field `K` over a finite field
`k`. Suppose some `a` and `b` have no pole outside `P₀` and poles of orders `e` and `e + 1` there.
Then the pole orders `i e + j (e + 1)` of the products `a^i b^j` cover every integer `o ≥ e²`.
Write `o = s e + t` with `0 ≤ t < e ≤ s`; then `o = (s - t) e + t (e + 1)`. Functions of distinct
pole orders are linearly independent over `k`, so

`#L(o P₀) ≥ q ^ (o + 1 - e²)`  for every `o`.

This is the form of Riemann's inequality `ℓ(o P₀) ≥ o + 1 - γ` that the Bombieri–Stepanov bound
needs. Only the existence of some constant `γ` matters there. On a curve, the two functions come
from writing a uniformizer at `P₀` as a quotient of two functions regular on the affine
complement of `P₀`.

## Main results

* `Stacks.BombieriStepanov.exists_mul_add_mul_succ_eq`: every `o ≥ e²` is `i e + j (e + 1)`.
* `Stacks.BombieriStepanov.pow_le_natCard_poleSpace`: `q ^ (o + 1 - e²) ≤ #L(o P₀)`.
-/

@[expose] public noncomputable section

namespace Stacks.BombieriStepanov

open Finset

variable {k K Pl : Type*} [Field k] [Field K] [Algebra k K]

/-- Every `o ≥ e²` is a nonnegative combination of `e` and `e + 1`. -/
theorem exists_mul_add_mul_succ_eq {e o : ℕ} (ho : e * e ≤ o) :
    ∃ i j : ℕ, i * e + j * (e + 1) = o := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact ⟨0, o, by simp⟩
  refine ⟨o / e - o % e, o % e, ?_⟩
  have hmod : o % e < e := Nat.mod_lt o he
  have hdiv : e ≤ o / e := (Nat.le_div_iff_mul_le he).2 ho
  have hsplit : o / e * e + o % e = o := by rw [mul_comm]; exact Nat.div_add_mod o e
  have hsub : (o / e - o % e) * e + o % e * e = o / e * e := by
    rw [← add_mul, Nat.sub_add_cancel (by omega)]
  nlinarith

/-- **Riemann's inequality from two functions of consecutive pole orders.** If `a ∈ L(e P₀)` and
`b ∈ L((e + 1) P₀)` have exact pole orders `e` and `e + 1` at the residue-rational place `P₀` of
degree one, then `#L(o P₀) ≥ q ^ (o + 1 - e²)` for every `o`. -/
theorem pow_le_natCard_poleSpace [Fintype k] {v : Pl → AddValuation K (WithTop ℤ)}
    {deg : Pl → ℕ} (hD : HasDegreeFormula v deg) {P₀ : Pl} (hP₀ : deg P₀ = 1)
    (hres : IsResidueRational (k := k) (v P₀)) {a b : K} (e : ℕ)
    (ha : a ∈ poleSpace v P₀ e) (ha0 : a ≠ 0) (hae : ordZ (v P₀) a = -e)
    (hb : b ∈ poleSpace v P₀ (e + 1)) (hb0 : b ≠ 0) (hbe : ordZ (v P₀) b = -(e + 1))
    (o : ℕ) : Fintype.card k ^ (o + 1 - e * e) ≤ Nat.card (poleSpace v P₀ o) := by
  classical
  have hfin := (finite_and_natCard_poleSpace_le hD hP₀ hres o).1
  have : Finite (poleSpace v P₀ o) := hfin.to_subtype
  set T : Finset ℕ := Finset.Icc (e * e) o with hT
  have hrep : ∀ t : T, ∃ y : K, y ∈ poleSpace v P₀ t ∧ y ≠ 0 ∧ ordZ (v P₀) y = -(t : ℤ) := by
    intro t
    obtain ⟨i, j, hij⟩ := exists_mul_add_mul_succ_eq (Finset.mem_Icc.1 t.2).1
    refine ⟨a ^ i * b ^ j, ?_, mul_ne_zero (pow_ne_zero _ ha0) (pow_ne_zero _ hb0), ?_⟩
    · rw [← hij]
      exact mul_mem_poleSpace (pow_mem_poleSpace ha i) (pow_mem_poleSpace hb j)
    · rw [ordZ_mul (pow_ne_zero _ ha0) (pow_ne_zero _ hb0), ordZ_pow ha0, ordZ_pow hb0, hae, hbe,
        ← hij]
      push_cast
      ring
  choose y hyL hy0 hyord using hrep
  have hyo : ∀ t : T, y t ∈ poleSpace v P₀ o := fun t =>
    poleSpace_mono (Finset.mem_Icc.1 t.2).2 (hyL t)
  let F : (T → k) → poleSpace v P₀ o := fun c =>
    ⟨∑ t, algebraMap k K (c t) * y t,
      sum_mem_poleSpace _ fun t _ => smul_mem_poleSpace (hyo t) (c t)⟩
  have hinj : Function.Injective F := by
    intro c c' hcc'
    have hsum : ∑ t, algebraMap k K (c t - c' t) * y t = 0 := by
      have := congrArg Subtype.val hcc'
      simp only [F] at this
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, this, sub_self]
    by_contra hne
    obtain ⟨t₀, ht₀⟩ := Function.ne_iff.1 hne
    refine sum_ne_zero_of_val_injOn (v P₀) Finset.univ _ ⟨t₀, Finset.mem_univ _, ?_⟩ ?_ hsum
    · exact mul_ne_zero (by simpa [sub_eq_zero] using ht₀) (hy0 t₀)
    · have hord : ∀ (x : k) (s : T), algebraMap k K x * y s ≠ 0 →
          ordZ (v P₀) (algebraMap k K x * y s) = -(s : ℤ) := by
        intro x s h
        have hx := left_ne_zero_of_mul h
        have h0 : ordZ (v P₀) (algebraMap k K x) = 0 := by
          have := val_algebraMap (v P₀) (c := x) fun h => hx (by rw [h, map_zero])
          rw [← coe_ordZ hx] at this
          exact_mod_cast this
        rw [ordZ_mul hx (hy0 s), h0, hyord, zero_add]
      intro t _ t' _ hzt hzt' heq
      rw [← coe_ordZ hzt, ← coe_ordZ hzt', hord _ _ hzt, hord _ _ hzt'] at heq
      exact Subtype.ext (by exact_mod_cast neg_inj.1 (WithTop.coe_injective heq))
  have hle := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := T), Fintype.card_coe, hT, Nat.card_Icc,
    Nat.card_eq_fintype_card (α := k)] at hle
  exact hle

end Stacks.BombieriStepanov

end

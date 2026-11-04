module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Eventually below, one residue class at a time

A property of the integers that holds on each residue class modulo `e` from some point
downwards holds on all sufficiently negative integers: there are only `e` classes, so the
largest of the `e` thresholds works for all of them at once.

## Main results

* `Stacks.Int.exists_forall_le_of_forall_residue`: the reduction of "`P m` for `m ≪ 0`" to
  "`P (r - j e)` for `j ≫ 0`", one `r` at a time.

## Implementation notes

The residue classes are indexed by `Fin e`, so that the thresholds form a function on a finite
type and `Finset.sup` produces a single bound; indexing them by the naturals below `e` would
make the choice dependent on the proof of `r < e`.

An integer `m` is written in its class as `m = m % e - (-(m / e)) * e`, with `m % e` in
`[0, e)` because `e` is positive and `-(m / e)` a natural number because `m` is negative.

This is the bookkeeping step of [Stacks, Tag 0FD8]. The source avoids it by replacing the pair
`(ℱ, ℒ)` with `(ℱ ⊕ ℱ ⊗ ℒ ⊕ … ⊕ ℱ ⊗ ℒ^{⊗ (e-1)}, ℒ^{⊗ e})`, which needs the depth of a finite
direct sum; running the argument in each class separately needs nothing.

## References

* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
-/

@[expose] public section

namespace Stacks.Int

/-- **A property holding on each residue class from some point downwards holds on all
sufficiently negative integers.** -/
public theorem exists_forall_le_of_forall_residue {e : ℕ} (he : 0 < e) (P : ℤ → Prop)
    (h : ∀ r : Fin e, ∃ b : ℕ, ∀ j : ℕ, b ≤ j → P ((r : ℤ) - (j : ℤ) * (e : ℤ))) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m ≤ m₀ → P m := by
  choose b hb using h
  classical
  set B : ℕ := Finset.sup Finset.univ b with hBdef
  have he' : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  refine ⟨-((B : ℤ) + 1) * (e : ℤ), fun m hm => ?_⟩
  have hr0 : 0 ≤ m % (e : ℤ) := Int.emod_nonneg m (ne_of_gt he')
  have hrlt : m % (e : ℤ) < (e : ℤ) := Int.emod_lt_of_pos m he'
  have hq : m / (e : ℤ) ≤ -((B : ℤ) + 1) := by
    have := Int.ediv_le_ediv he' hm
    rwa [Int.mul_ediv_cancel _ (ne_of_gt he')] at this
  have hB0 : (0 : ℤ) ≤ (B : ℤ) := Int.natCast_nonneg B
  set j : ℕ := (-(m / (e : ℤ))).toNat with hjdef
  have hjcast : (j : ℤ) = -(m / (e : ℤ)) := Int.toNat_of_nonneg (by linarith)
  have hjB : B ≤ j := by
    have h1 : (B : ℤ) ≤ (j : ℤ) := by rw [hjcast]; linarith
    exact_mod_cast h1
  set r : ℕ := (m % (e : ℤ)).toNat with hrdef
  have hrcast : (r : ℤ) = m % (e : ℤ) := Int.toNat_of_nonneg hr0
  have hrFin : r < e := by
    have h1 : (r : ℤ) < (e : ℤ) := by rw [hrcast]; exact hrlt
    exact_mod_cast h1
  have hmain := hb ⟨r, hrFin⟩ j (le_trans (Finset.le_sup (f := b) (Finset.mem_univ _)) hjB)
  have hrw : ((⟨r, hrFin⟩ : Fin e) : ℤ) - (j : ℤ) * (e : ℤ) = m := by
    simp only
    rw [hrcast, hjcast, Int.emod_def]
    ring
  rwa [hrw] at hmain

end Stacks.Int

end

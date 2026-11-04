module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Square-zero ideals: determinants and adic completeness

## Main results

* `Matrix.det_one_add_of_mul_eq_zero` — if the entries of `c` lie in an ideal any two of whose
  elements multiply to zero, then `det (1 + c) = 1 + tr c`.
* `isAdicComplete_of_pow_eq_bot` — a ring is complete for a nilpotent ideal.
* `discreteTopology_adicTopology_of_pow_eq_bot` — the adic topology of a nilpotent ideal is
  discrete.
-/

@[expose] public section

open Equiv

/-- A product of terms `1 + x i` whose pairwise products vanish is `1 + ∑ x i`. -/
theorem Finset.prod_one_add_of_mul_eq_zero {ι R : Type*} [CommRing R] (s : Finset ι)
    (x : ι → R) (hx : ∀ i j, x i * x j = 0) : ∏ i ∈ s, (1 + x i) = 1 + ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, add_mul, one_mul, mul_add, mul_one,
      Finset.mul_sum, Finset.sum_eq_zero fun j _ => hx a j, add_zero]
    ring

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- If the entries of `c` lie in an ideal `I` with `x * y = 0` for all `x y ∈ I`, then
`det (1 + c) = 1 + tr c`: in the Leibniz expansion every non-identity permutation moves two
indices, contributing a product of two elements of `I`. -/
theorem det_one_add_of_mul_eq_zero (I : Ideal R) (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = 0)
    (c : Matrix n n R) (hc : ∀ i j, c i j ∈ I) : (1 + c).det = 1 + c.trace := by
  rw [det_apply, Finset.sum_eq_single (1 : Perm n)]
  · simp only [Perm.sign_one, one_smul, Perm.one_apply, add_apply, one_apply_eq]
    exact Finset.prod_one_add_of_mul_eq_zero _ _ fun i j => hI _ (hc i i) _ (hc j j)
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      exact hσ (Perm.ext fun i => by_contra fun hi => h ⟨i, hi⟩)
    have hj : σ (σ i) ≠ σ i := fun h => hi (σ.injective h)
    have hmem : ∀ k, σ k ≠ k → (1 + c) (σ k) k ∈ I := fun k hk => by
      rw [add_apply, one_apply_ne hk, zero_add]
      exact hc _ _
    have hne : σ i ≠ i := hi
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ (σ i)⟩),
      ← mul_assoc, hI _ (hmem i hi) _ (hmem _ hj), zero_mul, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Matrix

variable {R : Type*} [CommRing R]

/-- Elements congruent modulo `I ^ k • ⊤` are equal when `I ^ k = ⊥`. -/
private theorem eq_of_smodEq_of_pow_eq_bot {I : Ideal R} {k : ℕ} (hk : I ^ k = ⊥) {x y : R}
    (h : x ≡ y [SMOD I ^ k • (⊤ : Ideal R)]) : x = y := by
  rwa [SModEq, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top, hk, Submodule.mem_bot,
    sub_eq_zero] at h

/-- A ring is complete for a nilpotent ideal. -/
theorem isAdicComplete_of_pow_eq_bot (I : Ideal R) {k : ℕ} (hk : I ^ k = ⊥) :
    IsAdicComplete I R where
  haus' x hx := by
    exact eq_of_smodEq_of_pow_eq_bot hk (by simpa using hx k)
  prec' f hf := by
    refine ⟨f k, fun {m} => ?_⟩
    rcases le_total m k with hm | hm
    · exact hf hm
    · rw [eq_of_smodEq_of_pow_eq_bot hk (hf hm)]

/-- The adic topology of a nilpotent ideal is discrete. -/
theorem discreteTopology_adicTopology_of_pow_eq_bot (I : Ideal R) {k : ℕ} (hk : I ^ k = ⊥) :
    @DiscreteTopology R I.adicTopology := by
  let : TopologicalSpace R := I.adicTopology
  have : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have h := (Ideal.hasBasis_nhds_zero_adic I).mem_of_mem (i := k) trivial
  rw [hk] at h
  have : ((⊥ : Ideal R) : Set R) = {0} := by ext; simp
  rw [this] at h
  exact isOpen_singleton_iff_nhds_eq_pure _ |>.2 (le_antisymm (Filter.le_pure_iff.2 h)
    (pure_le_nhds _))

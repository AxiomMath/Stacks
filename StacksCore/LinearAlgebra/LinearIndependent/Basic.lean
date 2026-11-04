module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Linear independence -/

@[expose] public section

theorem sum_mul_pow_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (s : Finset R) (f : R → R) : (∀ n, ∑ x ∈ s, f x * x ^ n = 0) ↔ ∀ x ∈ s, f x = 0 := by
  refine ⟨?_, by simp +contextual⟩
  have hlin := (linearIndependent_monoidHom _ _).comp _ (powersHom R).injective
  simpa [funext_iff] using linearIndependent_iff'.mp hlin s f

@[stacks 0EM9]
theorem Finset.Nonempty.exists_sum_pow_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {s : Finset R} (hs : s.Nonempty) : ∃ n, ∑ x ∈ s, x ^ n ≠ 0 := by
  simpa [hs.exists_mem, ← not_exists] using sum_mul_pow_eq_zero_iff s 1

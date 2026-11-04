module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of a sum of pure tensors, with respect to chosen generators

Let `R` be a commutative ring, `M` and `N` be `R`-modules, `{x_i}_{i ∈ I}` a family of generators
of `M` and `{y_j}_{j ∈ J}` a family of generators of `N`. For a finitely supported family
`{m_j}_{j ∈ J}` of elements of `M`, the sum `∑_j m_j ⊗ y_j` vanishes in `M ⊗_R N` exactly when
there are scalars `a_{ij} ∈ R`, finitely many of them nonzero, with
`m_j = ∑_i a_{ij} x_i` for all `j` and `∑_j a_{ij} y_j = 0` for all `i`.

Mathlib's `TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero` is the version for a finite
family which itself generates its factor, and with the intermediate elements left arbitrary; here
the index sets are arbitrary, only the family `m` is finitely supported, and the relation is
expressed in terms of the given generators `x_i` of `M`.

The finitely supported doubly indexed family `a_{ij}` is encoded as `a : I →₀ J →₀ R`, which is
equivalent to a finitely supported function on `I × J` (`Finsupp.finsuppProdEquiv`).

## Main results

* `TensorProduct.lTensor_linearCombination_finsuppScalarRight_symm` — the element of
  `M ⊗_R (J →₀ R)` corresponding to `m : J →₀ M` maps to `∑_j m_j ⊗ y_j` in `M ⊗_R N`.
* `TensorProduct.sum_tmul_eq_zero_iff_exists_finsupp` — the criterion for `∑_j m_j ⊗ y_j = 0`.

## References

* [Stacks Project, Tag 04VX](https://stacks.math.columbia.edu/tag/04VX)
-/

@[expose] public section

open Function

namespace TensorProduct

variable {R M N I J : Type*}

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Under `M ⊗_R (J →₀ R) ≃ (J →₀ M)`, the element corresponding to `m` maps, along the map
`M ⊗_R (J →₀ R) → M ⊗_R N` induced by `e_j ↦ y_j`, to `∑_j m_j ⊗ y_j`. -/
theorem lTensor_linearCombination_finsuppScalarRight_symm [DecidableEq J] (y : J → N) (m : J →₀ M) :
    (Finsupp.linearCombination R y).lTensor M ((finsuppScalarRight R R M J).symm m) =
      m.sum fun j mj ↦ mj ⊗ₜ[R] y j := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, Finsupp.sum_add_index', add_tmul]
  | single j mj => simp

end Semiring

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Vanishing of a sum of pure tensors.** Let `x : I → M` generate `M` and `y : J → N`
generate `N`, and let `m : J →₀ M` be a finitely supported family. Then `∑_j m_j ⊗ y_j = 0` in
`M ⊗_R N` if and only if there are scalars `a_{ij}`, only finitely many nonzero, such that
`m_j = ∑_i a_{ij} x_i` for every `j` and `∑_j a_{ij} y_j = 0` for every `i`.

The proof tensors the exact sequence `0 → K → (J →₀ R) → N → 0` given by the `y_j` with `M`,
and writes an element of `M ⊗_R K` as `∑_i x_i ⊗ k_i` using the generators `x_i`. -/
@[stacks 04VX]
theorem sum_tmul_eq_zero_iff_exists_finsupp {x : I → M}
    (hx : Submodule.span R (Set.range x) = ⊤) {y : J → N}
    (hy : Submodule.span R (Set.range y) = ⊤) (m : J →₀ M) :
    (m.sum fun j mj ↦ mj ⊗ₜ[R] y j) = 0 ↔
      ∃ a : I →₀ J →₀ R, (∀ j, m j = a.sum fun i aᵢ ↦ aᵢ j • x i) ∧
        ∀ i, ((a i).sum fun j r ↦ r • y j) = 0 := by
  classical
  set φ := Finsupp.linearCombination R y
  rw [← lTensor_linearCombination_finsuppScalarRight_symm]
  constructor
  · intro h
    have hφ : Surjective φ := (span_range_eq_top_iff_surjective_finsuppLinearCombination R).1 hy
    have hψ : Surjective (Finsupp.linearCombination R x) :=
      (span_range_eq_top_iff_surjective_finsuppLinearCombination R).1 hx
    obtain ⟨t, ht⟩ := (lTensor_exact M (LinearMap.exact_subtype_ker_map φ) hφ
      ((finsuppScalarRight R R M J).symm m)).1 h
    obtain ⟨s, rfl⟩ := LinearMap.rTensor_surjective (LinearMap.ker φ) hψ t
    obtain ⟨k, rfl⟩ := (finsuppScalarLeft R (LinearMap.ker φ) I).symm.surjective s
    have hm : (finsuppScalarRight R R M J).symm m =
        k.sum fun i kᵢ ↦ x i ⊗ₜ[R] (kᵢ : J →₀ R) := by
      rw [← ht]
      clear ht
      induction k using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp [hf, hg, Finsupp.sum_add_index', tmul_add]
      | single i kᵢ => simp
    rw [LinearEquiv.symm_apply_eq] at hm
    refine ⟨Finsupp.mapRange (fun v : LinearMap.ker φ ↦ (v : J →₀ R)) rfl k, fun j ↦ ?_, fun i ↦ ?_⟩
    · rw [hm, Finsupp.sum_mapRange_index (by simp)]
      simp [map_finsuppSum, Finsupp.sum_apply]
    · rw [Finsupp.mapRange_apply, ← Finsupp.linearCombination_apply]
      exact (k i).2
  · rintro ⟨a, ha, ha'⟩
    have hm : (finsuppScalarRight R R M J).symm m = a.sum fun i aᵢ ↦ x i ⊗ₜ[R] aᵢ := by
      rw [LinearEquiv.symm_apply_eq]
      ext j
      simp [map_finsuppSum, Finsupp.sum_apply, ha j]
    rw [hm, map_finsuppSum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp [Finsupp.linearCombination_apply, ha' i]

end TensorProduct

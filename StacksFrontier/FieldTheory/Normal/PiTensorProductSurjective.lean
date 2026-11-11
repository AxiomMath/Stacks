module

public import Mathlib.FieldTheory.SeparableDegree
public import StacksCore.FieldTheory.Normal.Closure
import StacksCore.Tactic.StacksAttribute

/-!
# The normal closure as a quotient of a tensor power

Stacks 0EXL: let `K / F` be a finite extension and `L / K` the normal closure of `K` over `F`.
Then there is a surjective map of `F`-algebras `K ⊗_F K ⊗_F ⋯ ⊗_F K → L`, where the number of
tensor factors can be taken to be `[K : F]_s ≤ [K : F]`.

The map is `piTensorProductEmbeddings F K L`, the tensor product over all `F`-embeddings
`K →ₐ[F] L` of those embeddings; it is surjective by
`IsNormalClosure.piTensorProductEmbeddings_surjective`. Here we count its tensor factors.

## Main results

* `IsNormalClosure.card_algHom_eq_finSepDegree`: the number of `F`-embeddings `K →ₐ[F] L` is
  the separable degree `[K : F]_s`.
* `IsNormalClosure.exists_surjective_piTensorProduct_fin_finSepDegree`: Stacks 0EXL, with
  `Fin [K : F]_s` indexing the tensor factors.
-/

@[expose] public section

open TensorProduct PiTensorProduct

/-- If `L` is a normal closure of an algebraic extension `K / F`, then the number of
`F`-embeddings `K →ₐ[F] L`, that is, the number of tensor factors of
`piTensorProductEmbeddings F K L`, is the separable degree `[K : F]_s`. -/
theorem IsNormalClosure.card_algHom_eq_finSepDegree
    (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Algebra.IsAlgebraic F K] [IsNormalClosure F K L] :
    Nat.card (K →ₐ[F] L) = Field.finSepDegree F K :=
  (Field.finSepDegree_eq_of_adjoin_splits F K L (IntermediateField.adjoin_univ F K) fun s _ ↦
    ⟨Algebra.IsIntegral.isIntegral s, IsNormalClosure.splits s⟩).symm

/-- **Stacks 0EXL**.
Let `K / F` be a finite extension and `L` a normal closure of `K / F`. Then the separable
degree satisfies `[K : F]_s ≤ [K : F]`, and there is a surjective `F`-algebra map
`(⨂[F] _ : Fin [K : F]_s, K) →ₐ[F] L` from the tensor product of `[K : F]_s` copies of `K`
onto `L`. -/
@[stacks 0EXL "surjection from [K : F]_s ≤ [K : F] tensor factors onto the normal closure"]
theorem IsNormalClosure.exists_surjective_piTensorProduct_fin_finSepDegree
    (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [FiniteDimensional F K] [IsNormalClosure F K L] :
    Field.finSepDegree F K ≤ Module.finrank F K ∧
      ∃ f : (⨂[F] _ : Fin (Field.finSepDegree F K), K) →ₐ[F] L, Function.Surjective f := by
  refine ⟨Field.finSepDegree_le_finrank F K, ?_⟩
  have hcard := card_algHom_eq_finSepDegree F K L
  have : Finite (K →ₐ[F] L) := Nat.finite_of_card_ne_zero (by simp)
  have := Fintype.ofFinite (K →ₐ[F] L)
  let e : Fin (Field.finSepDegree F K) ≃ (K →ₐ[F] L) := (Finite.equivFinOfCardEq hcard).symm
  refine ⟨productMap fun i ↦ e i, ?_⟩
  rw [← AlgHom.range_eq_top, range_productMap, e.iSup_comp (g := fun g : K →ₐ[F] L ↦ g.range)]
  have h := (piTensorProductEmbeddings_surjective F K L)
  rw [← AlgHom.range_eq_top, piTensorProductEmbeddings, range_productMap] at h
  exact h

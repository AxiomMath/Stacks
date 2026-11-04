module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite module over a complete Noetherian ring is complete

Let `R` be a Noetherian ring which is `I`-adically complete and let `M` be a finite `R`-module.
Then `M` is `I`-adically complete. This is the consequence of Stacks 00MA(3), `M^∧ = M ⊗_R R^∧`,
that the proof of Stacks 0EII uses: the first term of the sequence
`0 → M/H⁰_𝔞(M) → Γ(U, ℱ) → H¹_𝔞(M) → 0` is a finite module over a complete ring, hence complete.

Both halves of completeness are available over a Noetherian ring. Injectivity of `M → M^∧` is the
Hausdorff property, which Mathlib's `AdicCompletion.IsHausdorff.of_le_jacobson` supplies for a
finite module from `I ≤ jacobson ⊥`, itself a consequence of completeness of `R`. Surjectivity
comes from `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`: it identifies
`R^∧ ⊗_R M` with `M^∧`, and because `R` is complete every element of `R^∧` is `of I R a` for some
`a : R`, so every element of `R^∧ ⊗_R M` is `1 ⊗ x`, whose image is `of I M x`.

## Main results

* `AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing` — a finite module over a
  Noetherian `I`-adically complete ring is `I`-adically complete.

## Implementation notes

The ring and the module share a universe. That is forced by
`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`, whose statement in Mathlib
puts `M` in the universe of `R`; the rest of the argument is universe-polymorphic.

No `@[stacks]` attribute is placed. The matching source statement, Stacks 00MA, is a three-part
lemma — injectivity of the completion of an injection of finite modules, exactness of the
completion of a short exact sequence of finite modules, and `M^∧ = M ⊗_R R^∧` — and this file
proves none of those three; it records the corollary of the third that Stacks 0EII invokes.

## References

* [Stacks Project, Tag 00MA](https://stacks.math.columbia.edu/tag/00MA)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
-/

@[expose] public section

open TensorProduct

universe u

namespace AdicCompletion

/-- The canonical map `R → R^∧` sends `a` to `a • 1`: it is the structure map of the
`R`-algebra `AdicCompletion I R`. -/
private lemma of_eq_smul_one {R : Type u} [CommRing R] (I : Ideal R) (a : R) :
    of I R a = a • (1 : AdicCompletion I R) := by
  have h : algebraMap R (AdicCompletion I R) a = of I R a := by
    rw [AdicCompletion.algebraMap_apply (S := R)]
    simp
  rw [← h, Algebra.algebraMap_eq_smul_one]

/-- When `R` is `I`-adically complete, every element of `R^∧ ⊗_R M` is of the form `1 ⊗ x`:
the left factor is generated over `R` by `1`. -/
private lemma exists_one_tmul {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {M : Type u} [AddCommGroup M] [Module R M] (s : AdicCompletion I R ⊗[R] M) :
    ∃ x : M, s = (1 : AdicCompletion I R) ⊗ₜ[R] x := by
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
      obtain ⟨a, rfl⟩ := (of_bijective I R).surjective r
      exact ⟨a • x, by rw [of_eq_smul_one I a, TensorProduct.smul_tmul]⟩
  | add s₁ s₂ h₁ h₂ =>
      obtain ⟨x₁, rfl⟩ := h₁
      obtain ⟨x₂, rfl⟩ := h₂
      exact ⟨x₁ + x₂, (TensorProduct.tmul_add _ _ _).symm⟩

/-- **A finite module over a complete Noetherian ring is complete.** If `R` is a Noetherian ring
which is `I`-adically complete and `M` is a finite `R`-module, then `M` is `I`-adically complete.

This is the corollary of `M^∧ = M ⊗_R R^∧` (Stacks 00MA) used in the proof of Stacks 0EII to see
that `M/H⁰_𝔞(M)`, being a finite module over the complete ring `A`, is complete. -/
@[ega "0 7.8.1"]
public theorem isAdicComplete_of_finite_of_isNoetherianRing {R : Type u} [CommRing R]
    (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R] (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  refine of_bijective_iff.mp
    ⟨of_injective_iff.mpr (IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)),
      fun y ↦ ?_⟩
  obtain ⟨t, ht⟩ := (ofTensorProduct_bijective_of_finite_of_isNoetherian I M).surjective y
  obtain ⟨x, rfl⟩ := exists_one_tmul I t
  exact ⟨x, by rw [← ht, ofTensorProduct_tmul, one_smul]⟩

end AdicCompletion

end

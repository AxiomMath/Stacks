module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.FrobeniusFixed

/-!
# The Galois twists of `X_K` and of a stage base change `(X_E)_K`

Let `K/k` be Galois, `E` an intermediate field and `X` a scheme over `k`. Under the
identification `X_K ≅ (X_E)_K` (`Stacks.Picard.stageBaseChangeIso`), the twist of `(X_E)_K` by
`τ ∈ Gal(K/E)` is the twist by `τ` viewed in `Gal(K/k)`.

## Main results

* `Stacks.Picard.galoisTwist_comp_stageBaseChangeIso_hom`: the Galois twists correspond.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
  (E : IntermediateField k K)

/-- **The Galois twists of `X_K` and of `(X_E)_K` correspond.** For `τ ∈ Gal(K/E)`, the twist of
`X_K` by `τ` viewed in `Gal(K/k)` is carried by `X_K ≅ (X_E)_K` to the twist of `(X_E)_K` by
`τ`. -/
theorem galoisTwist_comp_stageBaseChangeIso_hom (τ : K ≃ₐ[E] K) :
    galoisTwist k K X (τ.restrictScalars k) ≫ (stageBaseChangeIso X E).hom =
      (stageBaseChangeIso X E).hom ≫ galoisTwist E K (stageOver X E) τ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, galoisTwist_comp_fst, stageBaseChangeIso_hom_fst]
    refine galoisTwist_comp_eq_of_mem_fixingSubgroup X E _ ?_ _ (stageProjection_comp_fst X E)
      (stageProjection_comp_snd X E)
    exact (IntermediateField.mem_fixingSubgroup_iff ..).2 fun e he => τ.commutes ⟨e, he⟩
  · rw [Category.assoc, Category.assoc, galoisTwist_comp_snd, stageBaseChangeIso_hom_snd,
      galoisTwist_comp_snd, ← Category.assoc, stageBaseChangeIso_hom_snd]
    rfl

end Stacks.Picard

end

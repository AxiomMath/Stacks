module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A dimension count for injectivity into two faces

Let `V` be a finite dimensional vector space with two additive maps `Φ₁ : V ⟶ V₁` and
`Φ₂ : V ⟶ V₂`. Suppose that `V` receives linear maps `s₁ : A ⟶ V` and `s₂ : B ⟶ V` from finite
dimensional spaces with `Φᵢ ∘ sᵢ` injective and `Φᵢ ∘ sⱼ = 0` for `i ≠ j`, and that
`dim V ≤ dim A + dim B`. Then `(Φ₁, Φ₂)` is injective: `s₁ + s₂ : A × B ⟶ V` is injective, hence
by the dimension bound an isomorphism, and `(Φ₁, Φ₂) ∘ (s₁ + s₂)` is injective.

This is the linear algebra closing the proof of the injectivity
`H¹(X × Y, 𝒪) ⟶ H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` of the proof of [Stacks, Tag 0BF3].

## Main results

* `Stacks.KunnethLowDegree.injective_prod_of_finrank_le`.
-/

@[expose] public section

namespace Stacks.KunnethLowDegree

variable {k A B V V₁ V₂ : Type*} [Field k] [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]
  [AddCommGroup V₁] [AddCommGroup V₂] [Module k A] [Module k B] [Module k V]

/-- **Injectivity into two faces from a dimension count.** -/
theorem injective_prod_of_finrank_le [FiniteDimensional k A] [FiniteDimensional k B]
    [FiniteDimensional k V] (s₁ : A →ₗ[k] V) (s₂ : B →ₗ[k] V) (Φ₁ : V →+ V₁) (Φ₂ : V →+ V₂)
    (h₁ : Function.Injective (Φ₁ ∘ s₁)) (h₂ : Function.Injective (Φ₂ ∘ s₂))
    (h₁₂ : ∀ b, Φ₁ (s₂ b) = 0) (h₂₁ : ∀ a, Φ₂ (s₁ a) = 0)
    (hdim : Module.finrank k V ≤ Module.finrank k A + Module.finrank k B) :
    Function.Injective (fun v => (Φ₁ v, Φ₂ v)) := by
  have hs : Function.Injective (s₁.coprod s₂) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    simp only [LinearMap.coprod_apply] at hab
    exact Prod.ext (h₁ (by simpa [h₁₂] using congrArg Φ₁ hab))
      (h₂ (by simpa [h₂₁] using congrArg Φ₂ hab))
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm (LinearMap.finrank_le_finrank_of_injective hs)
      (by rwa [Module.finrank_prod]))).mp hs
  intro v w hvw
  obtain ⟨⟨a, b⟩, rfl⟩ := hsurj v
  obtain ⟨⟨a', b'⟩, rfl⟩ := hsurj w
  simp only [Prod.mk.injEq, LinearMap.coprod_apply, map_add, h₁₂, h₂₁, add_zero,
    zero_add] at hvw
  rw [h₁ hvw.1, h₂ hvw.2]

end Stacks.KunnethLowDegree

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryDivisorDualityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.GlobalPurity

/-!
# Global purity along an étale boundary divisor

In the setting of `Stacks.EtaleCohomology.BoundaryDivisorDualityInput` (`f̄ : X̄ ⟶ S` smooth of
relative dimension `1`, `S` affine and smooth of dimension `e` over the algebraically closed `k`,
`i : Z ⟶ X̄` a closed immersion with `Z` finite étale over `S`), `X̄` is smooth of dimension
`e + 1` and `Z` smooth of dimension `e` over `k`, and `Z` is affine; global purity
(`Stacks.EtaleCohomology.Purity.exists_isPurityClass_of_smooth`) gives a purity class
`γ ∈ Ext²_X̄(i_* Λ_Z, Λ_X̄)`, read along `Λ_X̄ ≅ f̄⁻¹ Λ`
(`Stacks.EtaleCohomology.boundaryDivisorPurityInput`).

This is part of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

/-- **Global purity along the étale boundary divisor** (SGA 4 XVI 3.7): the input
`Stacks.EtaleCohomology.BoundaryDivisorPurityInput` holds. -/
theorem boundaryDivisorPurityInput : BoundaryDivisorPurityInput ℓ k := by
  intro hℓ S Xbar Z q e _ _ fbar i _ _ _ _ _ _
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ fbar)
  have : SmoothOfRelativeDimension (e + 1) (fbar ≫ q) := by
    rw [Nat.add_comm]
    infer_instance
  have : SmoothOfRelativeDimension e (i ≫ fbar ≫ q) := by
    have h : SmoothOfRelativeDimension (0 + e) ((i ≫ fbar) ≫ q) := inferInstance
    rw [Nat.zero_add, Category.assoc] at h
    exact h
  obtain ⟨γ, hγ⟩ := Purity.exists_isPurityClass_of_smooth k ℓ hℓ Xbar Z (fbar ≫ q) i e 1
  exact ⟨_, hγ.comp_mk₀ ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) fbar).app
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))).symm⟩

end Stacks.EtaleCohomology

end

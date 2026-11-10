module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# A Weil pairing from a cup product, transported along an isomorphism

Let `H¹` and `H²` be abelian groups with a biadditive "cup product" `∪ : H¹ × H¹ → H²` which is
left nondegenerate (for `a ≠ 0` there is `x` with `x ∪ a ≠ 0`), and `T : H² → ℤ/N` injective.
Transport along an additive isomorphism `κ : H¹ ≅ P` gives a pairing
`e(a, b) = T(κ⁻¹ b ∪ κ⁻¹ a)` on `P` which is left nondegenerate.

If moreover `R₁, R₂` are endomorphisms of `H¹, H²` with `R₁ x ∪ R₁ y = R₂(x ∪ y)`, and `σ` an
endomorphism of `P` with `κ⁻¹ σ κ = w R₁` and `w T(R₂ z) = d T(z)`, then
`e(σa, σb) = (w d) e(a, b)`. This is the shape in which the étale cup product on `H¹` of a curve
gives the Frobenius-equivariant Weil pairing on `Pic[N]`: `κ` is the Kummer isomorphism,
`R₁, R₂` the pullback, `w` the action on the root of unity used to identify `μ_N` with `ℤ/N`,
and `d` the factor by which pullback multiplies degrees.

## Main results

* `Stacks.Picard.exists_pairing_of_cup`: the pairing, its nondegeneracy and its equivariance.
-/

@[expose] public section

namespace Stacks.Picard

variable {P H₁ H₂ : Type*} [AddCommGroup P] [AddCommGroup H₁] [AddCommGroup H₂] {N : ℕ}

/-- **A Weil pairing from a nondegenerate cup product.** -/
theorem exists_pairing_of_cup (κ : H₁ ≃+ P) (T : H₂ →+ ZMod N) (hT : Function.Injective T)
    (cup : H₁ →+ H₁ →+ H₂) (hcup : ∀ a, a ≠ 0 → ∃ x, cup x a ≠ 0)
    (σ : P →+ P) (R₁ : H₁ →+ H₁) (R₂ : H₂ →+ H₂) (w d : ℤ)
    (hR : ∀ x y, cup (R₁ x) (R₁ y) = R₂ (cup x y))
    (hσ : ∀ a, κ.symm (σ a) = w • R₁ (κ.symm a))
    (hd : ∀ z, w • T (R₂ z) = d • T z) :
    ∃ e : P →+ P →+ ZMod N, (∀ a, (∀ b, e a b = 0) → a = 0) ∧
      ∀ a b, e (σ a) (σ b) = (w * d) • e a b := by
  let e : P →+ P →+ ZMod N :=
    { toFun := fun a =>
        { toFun := fun b => T (cup (κ.symm b) (κ.symm a))
          map_zero' := by simp
          map_add' := fun b b' => by simp }
      map_zero' := by ext b; simp
      map_add' := fun a a' => by ext b; simp }
  refine ⟨e, fun a ha => ?_, fun a b => ?_⟩
  · by_contra hne
    have hne' : κ.symm a ≠ 0 := fun h => hne (by simpa using congrArg κ h)
    obtain ⟨x, hx⟩ := hcup _ hne'
    refine hx (hT ?_)
    have := ha (κ x)
    simpa [e] using this
  · change T (cup (κ.symm (σ b)) (κ.symm (σ a))) = (w * d) • T (cup (κ.symm b) (κ.symm a))
    simp only [hσ, map_zsmul, AddMonoidHom.zsmul_apply, hR]
    rw [hd, smul_smul]

end Stacks.Picard

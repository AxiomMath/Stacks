module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SquareZeroSumPow
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback

/-!
# The pullback of a norm along the quotient by a symmetric group

For `π : Xⁿ ⟶ Sⁿ(X)`, `ℒᵢ = prᵢ^*ℒ` and `𝒩 = Norm_π(ℒ₁)`, the pullback of `𝒩` to `Xⁿ` is

  `π^*𝒩 = (ℒ₁ ⊗ … ⊗ ℒₙ)^{⊗(n-1)!}`  in  `Pic(Xⁿ)`.

This file proves the formula, written additively in the Picard group, for an arbitrary morphism
`π : P ⟶ Q`, a family `ℒ : Fin n → Pic(P)` permuted by pullback along morphisms `a σ : P ⟶ P`,
`(a σ)^*ℒ_{i₀} ≅ ℒ_{σ(i₀)}`, and an invertible module `𝒩` on `Q` with

  `π^*𝒩 = ∑_{σ ∈ Sₙ} (a σ)^*ℒ_{i₀}`.

## Main results

* `Stacks.SheafOfModules.pullbackPicardClass_eq_factorial_nsmul_sum` —
  `[π^*𝒩] = (n-1)! • ∑ᵢ [ℒᵢ]` in `Pic(P)`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Nat RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

/-- **The pullback of the norm, in the Picard group.** Let `π : P ⟶ Q` be a morphism of schemes,
let `ℒ : Fin n → Pic(P)` be a family of invertible modules on `P` carrying an action of the
permutations of `Fin n` by pullback along morphisms `a σ : P ⟶ P`, in the sense that
`(a σ)^*ℒ_{i₀} ≅ ℒ_{σ(i₀)}`, and let `𝒩` be an invertible module on `Q` whose pullback is the sum
over all permutations of the pullbacks of `ℒ_{i₀}`. Then

  `[π^*𝒩] = (n-1)! • ∑ᵢ [ℒᵢ]`  in  `Pic(P)`,

which for `P = Xⁿ`, `Q = Sⁿ(X)` and `𝒩 = Norm_π(ℒ₁)` is the formula
`π^*𝒩 = (ℒ₁ ⊗ … ⊗ ℒₙ)^{⊗(n-1)!}`, written additively. -/
theorem pullbackPicardClass_eq_factorial_nsmul_sum {P Q : Scheme.{u}} (π : P ⟶ Q) {n : ℕ}
    (i₀ : Fin n) (L : Fin n → SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (hL : ∀ i, IsInvertible P.presheaf P.ringCatIsSheaf (L i))
    (N : SheafOfModules.{u} (structureSheafRing Q.toRingedSpace))
    (hN : IsInvertible Q.presheaf Q.ringCatIsSheaf N)
    (a : Equiv.Perm (Fin n) → (P ⟶ P))
    (horbit : ∀ σ : Equiv.Perm (Fin n),
      pullbackPicardClass (a σ) (L i₀) (hL i₀) =
        picardClass P.presheaf P.ringCatIsSheaf (L (σ i₀)) (hL (σ i₀)))
    (hnorm : pullbackPicardClass π N hN =
      ∑ σ : Equiv.Perm (Fin n), pullbackPicardClass (a σ) (L i₀) (hL i₀)) :
    pullbackPicardClass π N hN =
      (n - 1)! • ∑ i, picardClass P.presheaf P.ringCatIsSheaf (L i) (hL i) := by
  rw [hnorm, Finset.sum_congr rfl fun σ _ ↦ horbit σ]
  exact Stacks.Chow.sum_perm_apply_eq_factorial_nsmul_sum
    (fun i ↦ picardClass P.presheaf P.ringCatIsSheaf (L i) (hL i)) i₀

end Stacks.SheafOfModules

end

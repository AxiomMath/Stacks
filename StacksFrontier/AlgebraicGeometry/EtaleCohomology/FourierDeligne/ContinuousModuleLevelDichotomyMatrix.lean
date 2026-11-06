module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseSubsheafMonodromyDichotomy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyAbsIrr

/-!
# The level dichotomy of a continuous module given by matrices up to scalars

Let `M` be a finite continuous `Λ`-`H`-module and `e : M ≃ Λ^ι` a `Λ`-linear identification under
which every matrix of a set `S₀ ⊆ M_ι(O)` (`O` a ring over which `Λ` is an algebra) is, up to a
unit scalar of `Λ`, the action of an element of `H`. Then the level dichotomy for the
`S₀`-stable submodules of `Λ^ι` (`Stacks.EtaleCohomology.exists_levelDichotomy_of_absIrr`) gives
the level dichotomy of `M` (`Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy`).

## Main results

* `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_matrix`: the level dichotomy of `M`
  from the level dichotomy of the `S₀`-stable submodules of `Λ^ι`.
-/

@[expose] public noncomputable section

open Matrix Stacks.GroupCohomology

universe v w

namespace Stacks.EtaleCohomology

variable {Λ : Type} [CommRing Λ] [Finite Λ] {H : Type v} [Group H] [TopologicalSpace H]
  {O : Type*} [CommRing O] [Algebra O Λ] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Finite Λ] [DecidableEq ι] in
/-- **The level dichotomy of a continuous module given by matrices up to unit scalars.** If under
`e : M ≃ Λ^ι` every matrix of `S₀ ⊆ M_ι(O)` is a unit multiple of the action of an element of
`H`, and the `S₀`-stable submodules of `Λ^ι` satisfy the dichotomy at `ℓ ∈ O`, `N`, `c₀`, then `M`
satisfies the level dichotomy at the image `ℓₙ ∈ ℕ` of `ℓ`. -/
theorem continuousModuleLevelDichotomy_of_matrix (S₀ : Set (Matrix ι ι O))
    {M : FiniteTypeContinuousModule.{0, v, w} Λ H} (e : M.obj.obj.obj.V ≃ₗ[Λ] (ι → Λ))
    (hS₀ : ∀ a ∈ S₀, ∃ h : H, ∃ c : Λˣ, ∀ x,
      e ((M.obj.obj.obj.ρ h).asHom.hom x) = c • (a.map (algebraMap O Λ) *ᵥ e x))
    (ℓ : O) (ℓₙ : ℕ) (hℓ : algebraMap O Λ ℓ = ℓₙ) (N c₀ : ℕ)
    (hD : ∀ S : Submodule Λ (ι → Λ), (∀ a ∈ S₀, ∀ v ∈ S, a.map (algebraMap O Λ) *ᵥ v ∈ S) →
      (∃ x ∈ S, ℓ ^ N • x ≠ 0) → ∀ w : ι → Λ, ℓ ^ c₀ • w ∈ S) :
    ContinuousModuleLevelDichotomy M ℓₙ N c₀ := by
  have hpow : ∀ (k : ℕ) (x : M.obj.obj.obj.V), ℓ ^ k • e x = e (ℓₙ ^ k • x) := fun k x ↦ by
    rw [algebra_compatible_smul Λ (ℓ ^ k), map_pow, hℓ, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul,
      map_nsmul]
  intro W hW ⟨x, hx, hxN⟩ y
  let S := W.map e.toLinearMap
  have hS : ∀ a ∈ S₀, ∀ v ∈ S, a.map (algebraMap O Λ) *ᵥ v ∈ S := by
    rintro a ha _ ⟨x', hx', rfl⟩
    obtain ⟨h, c, hc⟩ := hS₀ a ha
    have : a.map (algebraMap O Λ) *ᵥ e x' = (c⁻¹ : Λˣ) • e ((M.obj.obj.obj.ρ h).asHom.hom x') := by
      rw [hc, smul_smul, inv_mul_cancel, one_smul]
    rw [LinearEquiv.coe_coe, this]
    exact S.smul_mem _ ⟨_, hW h x' hx', rfl⟩
  have hSN : ∃ v ∈ S, ℓ ^ N • v ≠ 0 := by
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    rw [hpow]
    exact fun h0 ↦ hxN (e.injective (h0.trans (map_zero e).symm))
  have hmem := hD S hS hSN (e y)
  rw [hpow] at hmem
  obtain ⟨y', hy', hy'e⟩ := hmem
  rw [LinearEquiv.coe_coe] at hy'e
  rwa [← e.injective hy'e]

end Stacks.EtaleCohomology

end

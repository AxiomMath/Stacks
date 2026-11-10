module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TameInertiaLevelBounds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous

/-!
# Bounds on invariants and cocycles transported from an inertia group

Let `M` be a discrete module over a topological group `G`, and suppose `G` is identified, as a
topological group, with a subgroup `I` of a group `H`, and `M` with `(ℤ/ℓⁿ⁺¹)^r` so that `g ∈ G`
acts as `ρ mod ℓⁿ⁺¹` of its image in `I`, for some `ρ : H → GL_r(ℤ_ℓ)`. If `ℓ ^ e` kills the
`I`-invariants of `(ℤ/ℓⁿ⁺¹)^r` and `ℓ ^ e` times every locally constant `1`-cocycle of `I` is a
coboundary (`Stacks.EtaleCohomology.InertiaLevelsKilledBy`), then the same holds for `G` acting on
`M`. This is the last step of the computation of the boundary stalks of the levels of an ℓ-adic
sheaf on a curve: the absolute Galois group of `K^{sh}` is the inertia group of a place at
infinity, and the Galois module of a level is the level module.

## Main results

* `Stacks.EtaleCohomology.galoisInvariants_and_cocycles_killed_of_inertia`.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Matrix

universe u v w

namespace Stacks.EtaleCohomology

/-- **Invariants and cocycles of `M` are bounded by those of the inertia group.** -/
theorem galoisInvariants_and_cocycles_killed_of_inertia {G : Type u} [Group G]
    [TopologicalSpace G] {H : Type w} [Group H] [TopologicalSpace H] {ℓ r : ℕ} [Fact ℓ.Prime]
    (M : ContinuousGModule.{u, v} G) (I : Subgroup H) (ψ : G ≃ₜ I)
    (hψ : ∀ g g', ψ (g * g') = ψ g * ψ g') (ρ : H →* GL (Fin r) ℤ_[ℓ]) (n e : ℕ)
    (Θ : M.obj.obj.V ≃+ (Fin r → ZMod (ℓ ^ (n + 1))))
    (hΘ : ∀ g v, Θ ((M.obj.obj.ρ g).asHom v) = (PadicInt.toZModPow (n + 1)).mapMatrix
      (ρ (ψ g : H) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ Θ v)
    (hI : InertiaLevelsKilledBy I ρ e) :
    (∀ v : M.obj.obj.V, (∀ g, (M.obj.obj.ρ g).asHom v = v) → ℓ ^ e • v = 0) ∧
      ∀ γ : G → M.obj.obj.V, IsLocallyConstant γ →
        (∀ g₁ g₂, γ (g₁ * g₂) = (M.obj.obj.ρ g₁).asHom (γ g₂) + γ g₁) →
        ∃ x : M.obj.obj.V, ∀ g, (M.obj.obj.ρ g).asHom x - x = ℓ ^ e • γ g := by
  obtain ⟨hinv, hcoc⟩ := hI n
  have hψs : ∀ σ τ : I, ψ.symm (σ * τ) = ψ.symm σ * ψ.symm τ := fun σ τ => by
    apply ψ.injective
    rw [hψ, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  refine ⟨fun v hv => ?_, fun γ hγ hcocy => ?_⟩
  · apply Θ.injective
    rw [map_nsmul, map_zero]
    refine hinv (Θ v) fun σ hσ => ?_
    have h1 := hΘ (ψ.symm ⟨σ, hσ⟩) v
    rw [hv, Homeomorph.apply_symm_apply] at h1
    exact h1.symm
  · let c : I → Fin r → ZMod (ℓ ^ (n + 1)) := fun σ => Θ (γ (ψ.symm σ))
    have hc : IsLocallyConstant c :=
      (hγ.comp (fun z => Θ z)).comp_continuous ψ.symm.continuous
    have hcc : ∀ σ τ : I, c (σ * τ) = (PadicInt.toZModPow (n + 1)).mapMatrix
        (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ c τ + c σ := fun σ τ => by
      change Θ (γ (ψ.symm (σ * τ))) = _ *ᵥ Θ (γ (ψ.symm τ)) + Θ (γ (ψ.symm σ))
      rw [hψs, hcocy, map_add, hΘ, Homeomorph.apply_symm_apply]
    obtain ⟨m, hm⟩ := hcoc c hc hcc
    refine ⟨Θ.symm m, fun g => ?_⟩
    apply Θ.injective
    rw [map_sub, hΘ, AddEquiv.apply_symm_apply, map_nsmul]
    have h1 := hm (ψ g)
    change ℓ ^ e • Θ (γ (ψ.symm (ψ g))) = _ at h1
    rw [Homeomorph.symm_apply_apply] at h1
    exact h1.symm

end Stacks.EtaleCohomology

end

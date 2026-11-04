module

public import StacksFrontier.CategoryTheory.Abelian.CommutingFamilyTwistVanishing

/-!
# Commuting families along a functor

The image of a `Stacks.CommutingFamily` under a functor, and the transport of generation in
bounded degree along a left adjoint: a left adjoint carries jointly epimorphic families to jointly
epimorphic families, since a morphism out of the image transposes to one out of the source.

## Main definitions

* `Stacks.CommutingFamily.map`: the image of a commuting family under a functor.

## Main results

* `Stacks.CommutingFamily.generatedFrom_map_of_adjunction`: a left adjoint preserves generation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.CommutingFamily

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℬ : Type u₂} [Category.{v₂} ℬ] {r : ℕ}

/-- The image of a commuting family under a functor. -/
@[simps]
def map (Φ : 𝒜 ⥤ ℬ) (G : CommutingFamily 𝒜 r) : CommutingFamily ℬ r where
  obj n := Φ.obj (G.obj n)
  act i n := Φ.map (G.act i n)
  comm i j n := by rw [← Φ.map_comp, G.comm, Φ.map_comp]

variable [Abelian 𝒜] [Abelian ℬ]

/-- **A left adjoint preserves generation in bounded degree.**  A morphism `g : Φ Gₙ₊₁ ⟶ Q`
killed by every `Φ aᵢ` transposes to a morphism `Gₙ₊₁ ⟶ Ψ Q` killed by every `aᵢ`, which is zero;
so `g` is zero. -/
theorem generatedFrom_map_of_adjunction {Φ : 𝒜 ⥤ ℬ} {Ψ : ℬ ⥤ 𝒜} (adj : Φ ⊣ Ψ)
    (G : CommutingFamily 𝒜 r) {N : ℕ} (hG : G.GeneratedFrom N) :
    (G.map Φ).GeneratedFrom N := by
  have : Ψ.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  have : Ψ.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isRightAdjoint Ψ
  intro n hn Q g hg
  change Φ.obj (G.obj (n + 1)) ⟶ Q at g
  have hg' : ∀ i, Φ.map (G.act i n) ≫ g = 0 := hg
  have h0 : adj.homEquiv _ _ g = 0 := hG n hn _ fun i => by
    rw [← adj.homEquiv_naturality_left, hg' i, adj.homEquiv_unit, Functor.map_zero, comp_zero]
  have h1 : adj.homEquiv _ _ (0 : Φ.obj (G.obj (n + 1)) ⟶ Q) = 0 := by
    rw [adj.homEquiv_unit, Functor.map_zero, comp_zero]
  exact (adj.homEquiv _ _).injective (h0.trans h1.symm)

end Stacks.CommutingFamily

end

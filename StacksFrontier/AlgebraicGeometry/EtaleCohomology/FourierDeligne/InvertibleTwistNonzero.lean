module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.IntegralTransform
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyFreeProjectionFormula

/-!
# Twisting a morphism by an invertible sheaf

Let `L, L'` be étale-locally free sheaves of `Λ`-modules with `L' ⊗ L ≅ 𝟙`. Whiskering by `L'`
detects zero morphisms (`Stacks.EtaleCohomology.eq_zero_of_whiskerRight_eq_zero_of_tensor_iso`):
`φ ▷ L' = 0` gives `φ ▷ (L' ⊗ L) = 0`, hence `φ ▷ 𝟙 = 0`, that is `φ = 0`. So a nonzero morphism
`N ⊗ L ⟶ E` is adjoint to the nonzero morphism `N ⟶ E ⊗ L'`,
`N ≅ N ⊗ 𝟙 ≅ N ⊗ (L ⊗ L') ≅ (N ⊗ L) ⊗ L' ⟶ E ⊗ L'`
(`Stacks.EtaleCohomology.invertibleTwist_ne_zero`).

This turns a constant simple quotient `t⁻¹ M ⊗ L_ψ(x s) ⟶ E` into a nonzero morphism
`t⁻¹ M ⟶ E ⊗ L_ψ(-x s)` in the Artin–Schreier half of the generic coinvariant vanishing in
Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.invertibleTwist`.

## Main results

* `Stacks.EtaleCohomology.eq_zero_of_whiskerRight_eq_zero_of_tensor_iso`.
* `Stacks.EtaleCohomology.invertibleTwist_ne_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (Λ : Type) [CommRing Λ] {X : Scheme.{u}}

/-- **Whiskering by an invertible sheaf detects zero morphisms**: if `L' ⊗ L ≅ 𝟙` with `L`
étale-locally free, `φ ▷ L' = 0` forces `φ = 0`. -/
theorem eq_zero_of_whiskerRight_eq_zero_of_tensor_iso {P G L L' : EtaleModules.{u, 0} Λ X}
    (hL : IsLocallyFreeEtaleModule Λ L) (e : L' ⊗ L ≅ 𝟙_ (EtaleModules.{u, 0} Λ X)) (φ : P ⟶ G)
    (h : φ ▷ L' = 0) : φ = 0 := by
  have :=
    (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
      L hL).1
  have h2 : φ ▷ (L' ⊗ L) = 0 := by
    rw [whiskerRight_tensor, h]
    show (α_ _ _ _).inv ≫ (MonoidalCategory.tensorRight L).map 0 ≫ (α_ _ _ _).hom = 0
    rw [Functor.map_zero, zero_comp, comp_zero]
  have h3 : φ ▷ 𝟙_ _ = 0 := by
    have hx := whisker_exchange (W := P) (X := G) (Y := L' ⊗ L) (Z := 𝟙_ _) φ e.hom
    rw [h2, zero_comp] at hx
    have : P ◁ e.hom ≫ φ ▷ 𝟙_ _ = P ◁ e.hom ≫ 0 := by rw [hx, comp_zero]
    exact (cancel_epi _).1 this
  rw [whiskerRight_id] at h3
  have := congrArg (fun k => (ρ_ P).inv ≫ k ≫ (ρ_ G).hom) h3
  simpa using this

/-- **The twist `N ⟶ E ⊗ L'` of `φ : N ⊗ L ⟶ E`** along `e : L ⊗ L' ≅ 𝟙`:
`N ≅ N ⊗ 𝟙 ≅ N ⊗ (L ⊗ L') ≅ (N ⊗ L) ⊗ L' ⟶ E ⊗ L'`. -/
def invertibleTwist {N L L' E : EtaleModules.{u, 0} Λ X}
    (e : L ⊗ L' ≅ 𝟙_ (EtaleModules.{u, 0} Λ X)) (φ : N ⊗ L ⟶ E) : N ⟶ E ⊗ L' :=
  (ρ_ N).inv ≫ N ◁ e.inv ≫ (α_ N L L').inv ≫ φ ▷ L'

/-- **The twist of a nonzero morphism by an invertible sheaf is nonzero**, for `L ⊗ L' ≅ 𝟙` and
`L' ⊗ L ≅ 𝟙` with `L` étale-locally free. -/
theorem invertibleTwist_ne_zero {N L L' E : EtaleModules.{u, 0} Λ X}
    (hL : IsLocallyFreeEtaleModule Λ L) (e : L ⊗ L' ≅ 𝟙_ (EtaleModules.{u, 0} Λ X))
    (e' : L' ⊗ L ≅ 𝟙_ (EtaleModules.{u, 0} Λ X)) {φ : N ⊗ L ⟶ E} (hφ : φ ≠ 0) :
    invertibleTwist Λ e φ ≠ 0 := by
  intro h0
  apply hφ
  refine eq_zero_of_whiskerRight_eq_zero_of_tensor_iso Λ hL e' φ ?_
  have hiso : IsIso ((ρ_ N).inv ≫ N ◁ e.inv ≫ (α_ N L L').inv) := inferInstance
  rw [← cancel_epi ((ρ_ N).inv ≫ N ◁ e.inv ≫ (α_ N L L').inv), comp_zero]
  simpa [invertibleTwist, Category.assoc] using h0

end Stacks.EtaleCohomology

end

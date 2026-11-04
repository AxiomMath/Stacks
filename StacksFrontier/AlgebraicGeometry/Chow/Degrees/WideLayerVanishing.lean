module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToDimensionLayer
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.RationalEquivalenceReduction

/-!
# Vanishing in the wide dimension layer

Let `(S, δ)` be a base situation with a dimension function and `X` a scheme locally of finite
type over `S`. If a `k`-cycle is the difference of the cycles of two coherent modules which appear
as the third terms of two short exact sequences of `Coh_{≤k+1}(X)` with isomorphic first and
second terms, then its class in the wide layer `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` vanishes, and so
does the class of its proper pushforward along a finite morphism.

## Main results

* `Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_shortExact` — the vanishing on `X` itself.
* `Stacks.Chow.cycleDimensionLayerWideHom_properPushforward_eq_zero_of_shortExact` — the same for
  the proper pushforward of such a cycle along a finite morphism.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 0FDR](https://stacks.math.columbia.edu/tag/0FDR)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {W X : Scheme.{u}}

/-- **The wide class of a difference of two quotient cycles vanishes.** Let `S` and `T` be short
exact sequences of coherent modules of support dimension at most `k + 1` whose first terms are
isomorphic and whose second terms are isomorphic, and let `Q₁` and `Q₂` be modules of support
dimension at most `k` whose images in the layer `(·, k + 1]` are the third terms of `S` and of
`T`. Then the class of `[Q₂]_k − [Q₁]_k` in the wide layer `(k - 1, k + 1]` is zero. -/
theorem cycleDimensionLayerWideHom_eq_zero_of_shortExact (C : ChowSituation.{u}) (p : W ⟶ C.S)
    [LocallyOfFiniteType p] [CompactSpace W] (k : ℤ)
    {S T : ShortComplex (CoherentModulesDimLE C p (k + 1))}
    (hS : S.ShortExact) (hT : T.ShortExact) (e₁ : S.X₁ ≅ T.X₁) (e₂ : S.X₂ ≅ T.X₂)
    {Q₁ Q₂ : CoherentModulesDimLE C p k}
    (hQ₁ : (dimensionLayerInclusion C p k).obj Q₁ = S.X₃)
    (hQ₂ : (dimensionLayerInclusion C p k).obj Q₂ = T.X₃)
    {α : CycleGroup C p k}
    (hα : dimensionLayerCycle C p k Q₂ - dimensionLayerCycle C p k Q₁ = α) :
    cycleDimensionLayerWideHom C p k α = 0 := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian W := ⟨⟩
  have hsurj : Function.Surjective (cycleDimensionLayerHom C p k) :=
    surjective_cycleDimensionLayerHom C p k
  rw [← hα, map_sub,
    cycleDimensionLayerWideHom_dimensionLayerCycle_of_surjective C p k hsurj Q₂,
    cycleDimensionLayerWideHom_dimensionLayerCycle_of_surjective C p k hsurj Q₁, hQ₁, hQ₂,
    coherentDimensionKZeroMk_eq_of_shortExact C p (k - 1) (k + 1) hS hT e₁ e₂, sub_self]

/-- **The wide class of the pushforward of a difference of two quotient cycles vanishes.** A
`k`-cycle on `X` which is the proper pushforward, along a finite morphism `π : W ⟶ X`, of a
difference of two quotient cycles on `W` as in
`Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_shortExact` has vanishing class in the wide
layer `(k - 1, k + 1]` over `X`. -/
theorem cycleDimensionLayerWideHom_properPushforward_eq_zero_of_shortExact
    (C : ChowSituation.{u}) (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (π : W ⟶ X) [IsFinite π] [CompactSpace W] [CompactSpace X]
    (hπ : π ≫ sX = sW) (k : ℤ)
    {S T : ShortComplex (CoherentModulesDimLE C sW (k + 1))}
    (hS : S.ShortExact) (hT : T.ShortExact) (e₁ : S.X₁ ≅ T.X₁) (e₂ : S.X₂ ≅ T.X₂)
    {Q₁ Q₂ : CoherentModulesDimLE C sW k}
    (hQ₁ : (dimensionLayerInclusion C sW k).obj Q₁ = S.X₃)
    (hQ₂ : (dimensionLayerInclusion C sW k).obj Q₂ = T.X₃)
    {c : CycleGroup C sW k} {α : CycleGroup C sX k}
    (hc : dimensionLayerCycle C sW k Q₂ - dimensionLayerCycle C sW k Q₁ = c)
    (hα : properPushforwardHom C sW sX π hπ k c = α) :
    cycleDimensionLayerWideHom C sX k α = 0 :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  cycleDimensionLayerWideHom_eq_zero_of_properPushforwardHom_eq C sW sX π hπ k hα
    (cycleDimensionLayerWideHom_eq_zero_of_shortExact C sW k hS hT e₁ e₂ hQ₁ hQ₂ hc)

end Stacks.Chow

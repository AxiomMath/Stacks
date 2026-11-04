module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeSmoothBaseChange

/-!
# The relative normalization is a functor on commutative squares

For a commutative square of quasi-compact quasi-separated morphisms of schemes,
`AlgebraicGeometry.Scheme.Hom.normalizationMap` is the canonical morphism of their relative
normalizations. The canonical morphism of two squares stacked vertically is the composite of the
canonical morphisms of the two squares.

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalizationMap_comp`: the canonical morphism of a vertical
  composite of squares is the composite of the canonical morphisms.
* `AlgebraicGeometry.Scheme.Hom.normalization_hom_ext`: two morphisms of relative
  normalizations which make the same two squares commute are equal.
* `AlgebraicGeometry.Scheme.Hom.normalization_endo_eq_id`: the only endomorphism of a relative
  normalization over its target which commutes with the morphism from the source is the
  identity.

## References

* [Stacks Project, Tag 035J](https://stacks.math.columbia.edu/tag/035J)
* [Stacks Project, Tag 035E](https://stacks.math.columbia.edu/tag/035E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Y₁ Y₂ Y₃ X₁ X₂ X₃ : Scheme.{u}}

/-- **Two morphisms of relative normalizations with the same two squares are equal.** -/
theorem normalization_hom_ext (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂)
    [QuasiCompact f₁] [QuasiSeparated f₁] [QuasiCompact f₂] [QuasiSeparated f₂]
    {gY : Y₂ ⟶ Y₁} {gX : X₂ ⟶ X₁} (sq : gY ≫ f₁ = f₂ ≫ gX)
    (h h' : f₂.normalization ⟶ f₁.normalization)
    (hs : f₂.toNormalization ≫ h = gY ≫ f₁.toNormalization)
    (ht : h ≫ f₁.fromNormalization = f₂.fromNormalization ≫ gX)
    (hs' : f₂.toNormalization ≫ h' = gY ≫ f₁.toNormalization)
    (ht' : h' ≫ f₁.fromNormalization = f₂.fromNormalization ≫ gX) :
    h = h' :=
  (normalizationMap_unique f₁ f₂ gY gX sq h hs ht).trans
    (normalizationMap_unique f₁ f₂ gY gX sq h' hs' ht').symm

/-- **The relative normalization has no endomorphism over its target compatible with the
morphism from the source but the identity.** -/
theorem normalization_endo_eq_id (g : Y₁ ⟶ X₁) [QuasiCompact g] [QuasiSeparated g]
    (h : g.normalization ⟶ g.normalization)
    (hsrc : g.toNormalization ≫ h = g.toNormalization)
    (htgt : h ≫ g.fromNormalization = g.fromNormalization) :
    h = 𝟙 g.normalization :=
  normalization_hom_ext g g (gY := 𝟙 Y₁) (gX := 𝟙 X₁) (by simp) h (𝟙 _)
    (by simpa using hsrc) (by simpa using htgt) (by simp) (by simp)

/-- **Functoriality of the canonical morphism of relative normalizations.** Two commutative
squares stacked vertically compose to a commutative square, and the canonical morphism of the
composite square is the composite of the canonical morphisms. -/
theorem normalizationMap_comp (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂) (f₃ : Y₃ ⟶ X₃)
    [QuasiCompact f₁] [QuasiSeparated f₁] [QuasiCompact f₂] [QuasiSeparated f₂]
    [QuasiCompact f₃] [QuasiSeparated f₃]
    (gY : Y₂ ⟶ Y₁) (gX : X₂ ⟶ X₁) (sq : gY ≫ f₁ = f₂ ≫ gX)
    (hY : Y₃ ⟶ Y₂) (hX : X₃ ⟶ X₂) (sq' : hY ≫ f₂ = f₃ ≫ hX) :
    normalizationMap f₂ f₃ hY hX sq' ≫ normalizationMap f₁ f₂ gY gX sq =
      normalizationMap f₁ f₃ (hY ≫ gY) (hX ≫ gX)
        (by rw [Category.assoc, sq, ← Category.assoc, sq', Category.assoc]) :=
  normalizationMap_unique f₁ f₃ (hY ≫ gY) (hX ≫ gX) _ _
    (by rw [← Category.assoc, toNormalization_normalizationMap, Category.assoc,
      toNormalization_normalizationMap, Category.assoc])
    (by rw [Category.assoc, normalizationMap_fromNormalization, ← Category.assoc,
      normalizationMap_fromNormalization, Category.assoc])

end AlgebraicGeometry.Scheme.Hom

end

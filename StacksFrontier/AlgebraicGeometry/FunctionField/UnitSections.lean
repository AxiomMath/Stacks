module

public import StacksFrontier.AlgebraicGeometry.FunctionField.SectionsIntersectionStalks

/-!
# A rational function invertible at every point of an open is a unit section there

Let `X` be an integral scheme and `V ⊆ X` a nonempty open. An element of the function field
`R(X)` which is the image of a *unit* of the local ring `𝒪_{X, x}` for every `x ∈ V` is the image
of a unit of `Γ(X, V)`, not merely of a section.

This is the sentence of the penultimate paragraph of [Stacks, Tag 0BD7] which says that two
meromorphic multipliers of one meromorphic section "differ (multiplicatively) by an element of
`𝒪_{Y, y}^*`", read as a statement about sections over an open rather than about germs: the
ratio, a priori only a rational function, becomes an invertible section of `𝒪_Y`.

## Main results

* `AlgebraicGeometry.exists_units_germToFunctionField_eq_of_forall_isUnit`: a rational function
  that is the image of a unit of every local ring of `V` is the image of a unit of `Γ(X, V)`.
* `AlgebraicGeometry.exists_units_germToFunctionField_mul_eq_of_forall_isUnit`: the ratio form —
  two rational functions related at each point of `V` by a unit of the local ring there are
  related on `V` by a unit of `Γ(X, V)`.

## Implementation notes

The section and its inverse are produced separately by
`AlgebraicGeometry.exists_germToFunctionField_eq_of_forall_mem_range`, applied to `z` and to
`z⁻¹`; that they multiply to `1` is then read off in the function field and transported back by
injectivity of `Γ(X, V) ⟶ R(X)` on a nonempty open. Gluing the inverses directly would not do:
the inverse germs are only known to exist pointwise, and a cocycle condition for them is exactly
what the function field supplies here for free.

Mathlib's `AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ` is not applicable: it upgrades a
*given* section whose germs are units, whereas here there is no section until one has been
glued.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **A rational function that is a unit at every point of `V` is a unit section over `V`.** For
an integral scheme `X` and a nonempty open `V`, an element of the function field which is the
image of a unit of the local ring at every point of `V` is the image of a unit of `Γ(X, V)`. -/
theorem exists_units_germToFunctionField_eq_of_forall_isUnit (X : Scheme.{u}) [IsIntegral X]
    (V : X.Opens) [Nonempty V] (z : X.functionField)
    (hz : ∀ x : V, ∃ a : X.presheaf.stalk x.1, IsUnit a ∧
      algebraMap (X.presheaf.stalk x.1) X.functionField a = z) :
    ∃ w : (Γ(X, V))ˣ, X.germToFunctionField V w.val = z := by
  have hz0 : z ≠ 0 := by
    obtain ⟨x⟩ : Nonempty V := inferInstance
    obtain ⟨a, hau, hae⟩ := hz x
    exact hae ▸ (hau.map (algebraMap (X.presheaf.stalk x.1) X.functionField)).ne_zero
  have hinv : ∀ x : V, ∃ a : X.presheaf.stalk x.1,
      algebraMap (X.presheaf.stalk x.1) X.functionField a = z⁻¹ := by
    intro x
    obtain ⟨a, hau, hae⟩ := hz x
    refine ⟨↑hau.unit⁻¹, eq_inv_of_mul_eq_one_left ?_⟩
    rw [← hae, ← map_mul, hau.val_inv_mul, map_one]
  obtain ⟨r, hr⟩ := exists_germToFunctionField_eq_of_forall_mem_range X V z
    fun x => ((hz x).imp fun _ h => h.2)
  obtain ⟨r', hr'⟩ := exists_germToFunctionField_eq_of_forall_mem_range X V z⁻¹ hinv
  refine ⟨⟨r, r', ?_, ?_⟩, hr⟩
  · refine X.germToFunctionField_injective V ?_
    rw [map_mul, hr, hr', map_one, mul_inv_cancel₀ hz0]
  · refine X.germToFunctionField_injective V ?_
    rw [map_mul, hr, hr', map_one, inv_mul_cancel₀ hz0]

/-- **The ratio form.** Two rational functions related at every point of a nonempty open `V` of
an integral scheme by a unit of the local ring there are related over `V` by a unit of
`Γ(X, V)`. This is the form the penultimate paragraph of [Stacks, Tag 0BD7] needs: the two
meromorphic multipliers are not sections, but their ratio is an invertible one. -/
theorem exists_units_germToFunctionField_mul_eq_of_forall_isUnit (X : Scheme.{u}) [IsIntegral X]
    (V : X.Opens) [Nonempty V] (z₁ z₂ : X.functionField) (hz₂ : z₂ ≠ 0)
    (h : ∀ x : V, ∃ a : X.presheaf.stalk x.1, IsUnit a ∧
      algebraMap (X.presheaf.stalk x.1) X.functionField a * z₂ = z₁) :
    ∃ w : (Γ(X, V))ˣ, X.germToFunctionField V w.val * z₂ = z₁ := by
  obtain ⟨w, hw⟩ := exists_units_germToFunctionField_eq_of_forall_isUnit X V (z₁ / z₂)
    fun x => by
      obtain ⟨a, hau, hae⟩ := h x
      exact ⟨a, hau, by rw [← hae, mul_div_assoc, div_self hz₂, mul_one]⟩
  exact ⟨w, by rw [hw, div_mul_cancel₀ _ hz₂]⟩

end AlgebraicGeometry

end

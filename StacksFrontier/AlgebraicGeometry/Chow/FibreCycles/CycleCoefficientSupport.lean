module

public import StacksFrontier.AlgebraicGeometry.Chow.MaximalDeltaComponent
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity

/-!
# Where the cycle of a closed subscheme can have a nonzero coefficient

The cycle `[Z]_k` of a closed subscheme `i : Z ⟶ Y` has a nonzero coefficient only at a point
which is the image of a generic point of `Z` and has relative dimension `k`.

Stacks Tag 02QT says that a point at which the relative dimension attains an upper bound for the
delta-dimension of `Z` is the generic point of an irreducible component of `Z`; so once the
delta-dimension of `Z` is at most `k`, every point of `Z` of relative dimension `k` is a generic
point, and the coefficient of `[Z]_k` is zero off the range of `i`, zero where the relative
dimension is not `k`, and the multiplicity of the component otherwise.

## Main results

* `Stacks.Chow.exists_genericPoints_of_relativeDimension_eq` -- under a delta-dimension bound on
  the closed subscheme, every point of it of relative dimension `k` is a generic point.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne` -- the
  coefficient of `[Z]_k` vanishes at a point whose relative dimension is not `k`.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_componentMultiplicity_of_mem_range` --
  at a point of relative dimension `k` in the range, the coefficient is the multiplicity of the
  component that point is generic in.

## References

* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y Z : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p]
  (i : Z ⟶ Y) [IsClosedImmersion i] (k : ℤ)

/-- If the delta-dimension of a closed subscheme `Z` is at most `k`, then a point of `Z` whose
relative dimension is exactly `k` is the generic point of an irreducible component of `Z`, that
is, lies in `genericPoints Z` (Stacks Tag 02QT). -/
theorem exists_genericPoints_of_relativeDimension_eq
    (hZ : schemeDeltaDimension C (i ≫ p) ≤ (k : EInt)) (ξ : Z)
    (hξ : relativeDimension C.dimensionFunction p (i ξ) = k) :
    ∃ η : genericPoints Z, η.1 = ξ := by
  obtain ⟨W, hW⟩ := isGenericPoint_component_of_relativeDimension_eq C p i hZ ξ hξ
  exact ⟨⟨ξ, show closure {ξ} ∈ irreducibleComponents Z from hW ▸ W.2⟩, rfl⟩

/-- The coefficient of `[Z]_k` vanishes at a point whose relative dimension is not `k`, whether
or not that point lies in `Z`. -/
theorem cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne {y : Y}
    (hy : relativeDimension C.dimensionFunction p y ≠ k) :
    (cycleAssociatedToClosedSubscheme C p i k).1 y = 0 :=
  cycleAssociatedToClosedSubscheme_apply_eq_zero C p i k y fun ⟨_, _, h⟩ ↦ hy h

/-- Under a delta-dimension bound on `Z`, the coefficient of `[Z]_k` at a point of the range of
`i` of relative dimension `k` is the multiplicity of the component of `Z` that point is generic
in. -/
theorem cycleAssociatedToClosedSubscheme_apply_eq_componentMultiplicity_of_mem_range
    (hZ : schemeDeltaDimension C (i ≫ p) ≤ (k : EInt)) {y : Y} (hy : y ∈ Set.range i.base)
    (hdim : relativeDimension C.dimensionFunction p y = k) :
    ∃ η : genericPoints Z, i η.1 = y ∧
      (cycleAssociatedToClosedSubscheme C p i k).1 y = componentMultiplicity i η := by
  obtain ⟨ξ, rfl⟩ := hy
  obtain ⟨η, rfl⟩ := exists_genericPoints_of_relativeDimension_eq C p i k hZ ξ hdim
  exact ⟨η, rfl, cycleAssociatedToClosedSubscheme_apply C p i k η hdim⟩

end Stacks.Chow

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericPointsAndDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings

/-!
# Dimension and locally quasi-finite morphisms

A locally quasi-finite morphism of algebraic spaces does not raise the dimension: the
dimension of its source is at most the dimension of its target.

## Main results

* `AlgebraicGeometry.Space.dimension_le_of_isLocallyQuasiFinite` is that inequality.

## Implementation notes

The dimension of an algebraic space is the supremum of the Krull dimensions of its local
rings (Stacks 0BAN), and a locally quasi-finite morphism does not raise the dimension of a
local ring (Stacks 0ABW). Rewriting both sides by the first and comparing the two suprema
termwise along the map on points gives the statement, so no finiteness or separation
hypothesis beyond local quasi-finiteness is needed.

## References

* [Stacks Project, Tag 0ABW](https://stacks.math.columbia.edu/tag/0ABW)
* [Stacks Project, Tag 0BAN](https://stacks.math.columbia.edu/tag/0BAN)
* [Stacks Project, Tag 0ED0](https://stacks.math.columbia.edu/tag/0ED0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ED0.** The dimension of the source of a locally quasi-finite morphism of
algebraic spaces over `S` is at most the dimension of its target. -/
@[stacks 0ED0]
theorem dimension_le_of_isLocallyQuasiFinite
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyQuasiFinite B S hS f) :
    dimension B S hS X hX ≤ dimension B S hS Y hY := by
  rw [dimension_eq_iSup_localRingDimension B S hS X hX,
    dimension_eq_iSup_localRingDimension B S hS Y hY]
  refine iSup_le fun x ↦ le_iSup_of_le (pointsMap B S hS X f x) ?_
  exact_mod_cast localRingDimension_le_of_isLocallyQuasiFinite B S hS hX hY f hf x

end AlgebraicGeometry.Space

end

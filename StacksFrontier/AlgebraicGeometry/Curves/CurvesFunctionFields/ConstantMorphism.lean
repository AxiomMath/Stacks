module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Constant morphisms of varieties

Section 0BXX of the Stacks project ([Stacks, Tag 0BXX]) calls a morphism `f : X ⟶ Y` of
varieties over a field *constant* when its image `f(X)` consists of a single point `y` of `Y`,
and observes that `y` is then a closed point of `Y`, since the image of a closed point of `X` is a
closed point of `Y`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsConstant` — the image of a morphism is a single point.

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_range_eq_singleton` — the image point of a constant
  morphism of varieties is a closed point.

## Implementation notes

A variety over `k` is of finite type over a field, hence a Jacobson scheme
(`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`), and a morphism of varieties over `k` is
locally of finite type; by Stacks 01TB such a morphism carries closed points to closed points
(`AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints`). A variety is integral,
so nonempty, and a nonempty Jacobson space has a closed point.

## References

* [Stacks Project, Section 0BXX](https://stacks.math.columbia.edu/tag/0BXX)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A constant morphism** (Section 0BXX): a morphism `f : X ⟶ Y` whose image `f(X)` consists of
a single point of `Y`. -/
@[stacks 0BXX "a morphism of varieties is constant if its image consists of a single point"]
def Scheme.Hom.IsConstant {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ y : Y, Set.range f.base = {y}

/-- **The image of a constant morphism of varieties is a closed point** (Section 0BXX). Let
`f : X ⟶ Y` be a morphism of varieties over a field `k` whose image is the single point `y`.
Then `y` is a closed point of `Y`: the image of a closed point of `X` is a closed point of `Y`. -/
@[stacks 0BXX "if a morphism of varieties is constant, with image the point y, then y is a closed \
point"]
theorem isClosed_singleton_of_range_eq_singleton (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) {y : Y} (hy : Set.range f.base = {y}) :
    IsClosed ({y} : Set Y) := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : LocallyOfFiniteType (f ≫ sY) := by rw [hf]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sY
  obtain ⟨x, -, hx⟩ :=
    nonempty_inter_closedPoints (Set.univ_nonempty (α := X)) isClosed_univ.isLocallyClosed
  have hfx : f.base x ∈ closedPoints Y := f.closePoints_subset_preimage_closedPoints hx
  have : f.base x = y := by
    have : f.base x ∈ Set.range f.base := ⟨x, rfl⟩
    rwa [hy] at this
  rw [← this]
  exact hfx

/-- The image point of a constant morphism of varieties is closed, in terms of
`AlgebraicGeometry.Scheme.Hom.IsConstant`. -/
theorem Scheme.Hom.IsConstant.exists_isClosed (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]
    {f : X ⟶ Y} (hf : f ≫ sY = sX) (h : f.IsConstant) :
    ∃ y : Y, Set.range f.base = {y} ∧ IsClosed ({y} : Set Y) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy, isClosed_singleton_of_range_eq_singleton k sX sY f hf hy⟩

end AlgebraicGeometry

end

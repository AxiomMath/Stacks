module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps

/-!
# A dominant morphism carries a generic point to a generic point

Let `f : X ⟶ Y` be a dominant morphism of algebraic spaces over `S` in the sense of
Stacks 0ABL, so that the image of `|f|` is dense in `|Y|`. If `x` is a generic point of `|X|`
— the whole point space is the closure of `{x}` — then `|f|(x)` is a generic point of `|Y|`,
because the closure of its singleton is the closure of the image of `|X|`, which is all of
`|Y|`. When `Y` is decent its point space is Kolmogorov by Stacks 03K6, so that generic point
is unique and `|f|(x)` is *the* generic point of `|Y|`.

This is the situation of an integral dominant morphism, for which both point spaces are
irreducible and the two generic points are the chosen ones; no integrality or finite-type
hypothesis is used below, only dominance and Kolmogorovness of the target.

## Main results

* `AlgebraicGeometry.Space.isGenericPoint_pointsMap_of_isDominant`: the image of a generic
  point under a dominant morphism is a generic point.
* `AlgebraicGeometry.Space.pointsMap_eq_of_isGenericPoint`: on a decent target it is the
  given generic point.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here; `AlgebraicGeometry.Space.IsDominant` is stated for that topology.

## References

* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 0ABL](https://stacks.math.columbia.edu/tag/0ABL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ABL.** A dominant morphism of algebraic spaces over `S` carries a generic point
of its source to a generic point of its target: the closure of the image of the singleton is
the closure of the image of the whole point space, which is everything by dominance. -/
theorem isGenericPoint_pointsMap_of_isDominant (f : X ⟶ Y) (hf : IsDominant B S hS f)
    {x : points B S hS X} (hx : IsGenericPoint x (Set.univ : Set (points B S hS X))) :
    IsGenericPoint (pointsMap B S hS X f x) (Set.univ : Set (points B S hS Y)) := by
  have h := hx.image (continuous_pointsMap B S hS f)
  rwa [Set.image_univ, hf.closure_range] at h

/-- **Stacks 0ABL.** A dominant morphism of algebraic spaces over `S` with decent target
carries a generic point of its source to *the* generic point of its target: the point space
of a decent algebraic space is Kolmogorov by Stacks 03K6, so a generic point of it is
unique. -/
theorem pointsMap_eq_of_isGenericPoint (hY : IsAlgebraicSpace B S hS Y)
    (hdec : IsDecentSpace B S hS Y) (f : X ⟶ Y) (hf : IsDominant B S hS f)
    {x : points B S hS X} (hx : IsGenericPoint x (Set.univ : Set (points B S hS X)))
    {y : points B S hS Y} (hy : IsGenericPoint y (Set.univ : Set (points B S hS Y))) :
    pointsMap B S hS X f x = y :=
  have _ : T0Space (points B S hS Y) := t0Space_points_of_isDecentSpace B S hS hY hdec
  (isGenericPoint_pointsMap_of_isDominant B S hS f hf hx).eq hy

end AlgebraicGeometry.Space

end

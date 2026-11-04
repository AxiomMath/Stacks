module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Base change of the points in a fibre of a cartesian diagram

Let `D` be a cartesian square of algebraic spaces over `S`, an
`AlgebraicGeometry.Space.PointsFibresDiagram` with corners `W`, `Z`, `X`, `Y`. A morphism
`t : Z' ⟶ D.Z` from a further algebraic space, together with a cartesian square exhibiting `W'`
as `D.W ×_{D.Z} Z'`, produces a second such square with corners `W'`, `Z'`, `X`, `Y`: the
identity `X ×_Y Z' = (X ×_Y Z) ×_Z Z'` is the horizontal pasting of the two cartesian squares.

The set `AlgebraicGeometry.Space.fibrePoints` attached to the base-changed square surjects onto
the one attached to the original: every point of `D.W` lying over `x` and over the image of `z'`
is the image of a point of `W'` lying over `x` and over `z'`.

## Main definitions

* `AlgebraicGeometry.Space.PointsFibresDiagram.baseChange`: the base change of a cartesian
  square of algebraic spaces along a morphism into its lower-left corner.

## Main results

* `AlgebraicGeometry.Space.surjOn_fibrePoints_baseChange`: the induced map
  `F_{x, z'} → F_{x, z}` is surjective.

## References

* [Stacks Project, Tag 0AC5](https://stacks.math.columbia.edu/tag/0AC5)
* [Stacks Project, Tag 0AC1](https://stacks.math.columbia.edu/tag/0AC1)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The base change of a cartesian square `D` of algebraic spaces along a morphism
`t : Z' ⟶ D.Z` into its lower-left corner, given a cartesian square `IsPullback r q' D.q t`
exhibiting `W'` as `D.W ×_{D.Z} Z'`.

Its right-hand column is that of `D`, its lower horizontal morphism is `t ≫ D.g`, and its
own cartesian square, the identity `X ×_Y Z' = (X ×_Y Z) ×_Z Z'`, is the horizontal pasting of
the given square with that of `D`. -/
def PointsFibresDiagram.baseChange (D : PointsFibresDiagram B S hS)
    {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW' : IsAlgebraicSpace B S hS W') (hZ' : IsAlgebraicSpace B S hS Z')
    {t : Z' ⟶ D.Z} {r : W' ⟶ D.W} {q' : W' ⟶ Z'} (sq : IsPullback r q' D.q t) :
    PointsFibresDiagram B S hS where
  W := W'
  Z := Z'
  X := D.X
  Y := D.Y
  W_isAlgebraicSpace := hW'
  Z_isAlgebraicSpace := hZ'
  X_isAlgebraicSpace := D.X_isAlgebraicSpace
  Y_isAlgebraicSpace := D.Y_isAlgebraicSpace
  q := q'
  p := r ≫ D.p
  f := D.f
  g := t ≫ D.g
  isPullback := sq.paste_horiz D.isPullback

/-- Let `D` be a cartesian square of algebraic spaces, let `t : Z' ⟶ D.Z` be a morphism of
algebraic spaces and let `z'` be a point of `|Z'|`. Then the map `F_{x, z'} → F_{x, z}` induced
by `r : W' ⟶ D.W` is surjective, where `z` is the image of `z'` and `W'` is the fibre product
`D.W ×_{D.Z} Z'`. -/
@[stacks 0AC5]
theorem surjOn_fibrePoints_baseChange (D : PointsFibresDiagram B S hS)
    {W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW' : IsAlgebraicSpace B S hS W') (hZ' : IsAlgebraicSpace B S hS Z')
    {t : Z' ⟶ D.Z} {r : W' ⟶ D.W} {q' : W' ⟶ Z'} (sq : IsPullback r q' D.q t)
    (x : points B S hS D.X) (z' : points B S hS Z')
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS Z' (t ≫ D.g) z') :
    Set.SurjOn (pointsMap B S hS W' r)
      (fibrePoints (D.baseChange hW' hZ' sq) x z' h)
      (fibrePoints D x (pointsMap B S hS Z' t z')
        (by rw [h, pointsMap_comp_apply])) := by
  rintro w ⟨hwp, hwq⟩
  obtain ⟨w', hw'r, hw'q⟩ :=
    exists_points_of_isPullback B S hS sq w z' (by rw [hwq])
  refine ⟨w', ⟨?_, hw'q⟩, hw'r⟩
  show pointsMap B S hS W' (r ≫ D.p) w' = x
  rw [pointsMap_comp_apply, hw'r, hwp]

end AlgebraicGeometry.Space

end

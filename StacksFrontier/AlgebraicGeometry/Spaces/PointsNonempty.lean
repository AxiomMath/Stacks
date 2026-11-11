module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback

/-!
# Nonemptiness of the point set of an algebraic space (Stacks 03BU)

This file records how nonemptiness of the set of points `|X|` of Stacks 03BU
(`AlgebraicGeometry.Space.points`) is carried along the three comparisons of point sets the
library provides:

* along the lower-shriek extension `Λ_h` of a morphism `h : W ⟶ S` of the big fppf site, whose
  point map `AlgebraicGeometry.Space.pointsRelocalize` is a bijection;
* from a scheme of the site to the presheaf it represents, through the bijection
  `AlgebraicGeometry.Space.pointsEquivScheme`;
* along a morphism of presheaves, through the induced map
  `AlgebraicGeometry.Space.pointsMap`.

## Main results

* `AlgebraicGeometry.Space.nonempty_points_relocalizeSpace_iff`: an algebraic space over `W` has
  a point exactly when its extension to `S` has one.
* `AlgebraicGeometry.Space.nonempty_points_yoneda_of_nonempty`: a nonempty scheme of the site
  represents a presheaf with a point.
* `AlgebraicGeometry.Space.nonempty_points_of_hom`: a presheaf receiving a morphism from a
  presheaf with a point has a point.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} (hW : B.Contains W) (hS : B.Contains S)

/-- **An algebraic space over `W` has a point exactly when its lower-shriek extension to `S` does.**
The comparison `AlgebraicGeometry.Space.pointsRelocalize` of the two point sets is a bijection
(`AlgebraicGeometry.Space.pointsRelocalize_bijective`). -/
theorem nonempty_points_relocalizeSpace_iff (h : B.obj hW ⟶ B.obj hS)
    (Z : AlgebraicSpaces B W hW) :
    Nonempty (points B W hW Z.1) ↔ Nonempty (points B S hS (relocalizeSpace B hW hS h Z).1) :=
  ⟨fun ⟨x⟩ => ⟨pointsRelocalize B W S hW hS h Z.1 x⟩,
    fun ⟨y⟩ => ⟨((pointsRelocalize_surjective B W S hW hS h Z.1) y).choose⟩⟩

/-- **A nonempty scheme of the site represents a presheaf with a point.** The points of the
represented presheaf are in bijection with the points of the scheme
(`AlgebraicGeometry.Space.pointsEquivScheme`). -/
theorem nonempty_points_yoneda_of_nonempty (U : BigFppfOver B S hS)
    (hU : Nonempty ((BigFppfOver.toScheme B S hS).obj U)) :
    Nonempty (points B S hS (yoneda.obj U)) :=
  hU.map (pointsEquivScheme B S hS U).symm

/-- **A presheaf receiving a morphism from a presheaf with a point has a point**: the image of
the point under the induced map `AlgebraicGeometry.Space.pointsMap`. -/
theorem nonempty_points_of_hom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : Nonempty (points B S hS F)) : Nonempty (points B S hS G) :=
  hF.map (pointsMap B S hS F f)

end AlgebraicGeometry.Space

end

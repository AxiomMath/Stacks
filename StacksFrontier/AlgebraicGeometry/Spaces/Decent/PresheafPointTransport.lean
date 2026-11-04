module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Transport of a residue-field point along a morphism of the site

`AlgebraicGeometry.Space.presheafPoint` sends a point of an object of the big fppf site to a
point of the presheaf it represents. A morphism of the site carries one to the other, which is
checked on the underlying schemes: the points of a representable presheaf inject into the
points of the representing scheme.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the site carries the point of the represented presheaf determined by a point
of its source to the one determined by the image point. -/
theorem pointsMap_presheafPoint (T Q : BigFppfOver B S hS) (f : T ⟶ Q) (p : T.left.1)
    (hp : B.Contains (Spec (.of (T.left.1.residueField p))))
    (hq : B.Contains (Spec (.of (Q.left.1.residueField (f.left.1 p))))) :
    pointsMap B S hS (yoneda.obj T) (yoneda.map f) (presheafPoint B S hS T p hp) =
      presheafPoint B S hS Q (f.left.1 p) hq := by
  refine injective_pointsToScheme B S hS Q ?_
  rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_presheafPoint,
    pointsToScheme_presheafPoint]
  rfl

end AlgebraicGeometry.Space

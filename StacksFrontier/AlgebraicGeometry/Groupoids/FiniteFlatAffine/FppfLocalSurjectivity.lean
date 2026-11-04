module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.PointsLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings

/-!
# Functors of points of a flat covering on the big fppf site

Let `B` be a big fppf site containing a scheme `S` and let `f : U ⟶ M` be a morphism of
`S`-schemes which is flat, locally of finite presentation and surjective. The induced map of
functors of points, restricted along the canonical functor from the big fppf site over `S` to
all `S`-schemes, is then locally surjective for the fppf topology.

## Main results

* `AlgebraicGeometry.isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective`
  gives local surjectivity of the map on restricted functors of points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A flat, locally finitely presented and surjective morphism of `S`-schemes induces a
locally surjective map of functors of points on the big fppf site over `S`. -/
alias isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective :=
  isLocallySurjective_points_map_of_fppf

end AlgebraicGeometry

end

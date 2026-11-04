module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian morphisms of groupoid schemes

A morphism of groupoid schemes is cartesian when its square of source maps is a pullback.  For
a fixed groupoid scheme, morphisms between groupoid schemes cartesian over it commute with the
maps to the fixed groupoid scheme.

## Main definitions

* `AlgebraicGeometry.IsCartesian` is the cartesian condition on a morphism of groupoid schemes.
* `AlgebraicGeometry.CartesianOver` is a groupoid scheme equipped with a cartesian morphism to
  a fixed groupoid scheme.
* `AlgebraicGeometry.CartesianOver.Hom` is a morphism compatible with the two structure
  morphisms to the fixed groupoid scheme.

## Implementation notes

The fibre square in the source is represented by `CategoryTheory.IsPullback` after applying the
forgetful functor from schemes over `S` to schemes.  Thus cartesianness here is explicitly a
pullback in the category of schemes, rather than merely a pullback in the over category.
Compatibility with the structure morphisms is recorded on both the object and arrow maps; these
two equations are the componentwise form of equality of morphisms of groupoid schemes.

## References

* [Stacks Project, Tag 0APD](https://stacks.math.columbia.edu/tag/0APD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- A morphism of groupoid schemes is cartesian if its square of source maps is a pullback. -/
@[stacks 0APD "the cartesian condition"]
abbrev IsCartesian {S : Scheme.{u}} {G H : GroupoidScheme S}
    (F : GroupoidScheme.Hom G H) : Prop :=
  IsPullback F.mapArrows.left G.source.left H.source.left F.mapObjects.left

/-- A groupoid scheme cartesian over a fixed groupoid scheme `H`. -/
@[stacks 0APD "groupoid schemes cartesian over a fixed groupoid scheme"]
structure CartesianOver {S : Scheme.{u}} (H : GroupoidScheme S) where
  /-- The groupoid scheme lying over `H`. -/
  left : GroupoidScheme S
  /-- Its structure morphism to `H`. -/
  hom : GroupoidScheme.Hom left H
  /-- The structure morphism is cartesian. -/
  isCartesian : IsCartesian hom

/-- A morphism of groupoid schemes cartesian over `H` is a morphism compatible with both
components of the structure morphisms to `H`. -/
@[stacks 0APD "morphisms cartesian over a fixed groupoid scheme"]
structure CartesianOver.Hom {S : Scheme.{u}} {H : GroupoidScheme S}
    (X Y : CartesianOver H) where
  /-- The underlying morphism of groupoid schemes. -/
  hom : GroupoidScheme.Hom X.left Y.left
  /-- The maps on objects commute with the structure morphisms to `H`. -/
  mapObjects_comp : hom.mapObjects ≫ Y.hom.mapObjects = X.hom.mapObjects
  /-- The maps on arrows commute with the structure morphisms to `H`. -/
  mapArrows_comp : hom.mapArrows ≫ Y.hom.mapArrows = X.hom.mapArrows

end AlgebraicGeometry

end

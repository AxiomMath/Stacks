module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# Flat morphisms of schemes and flat modules over them

A morphism of schemes is flat at a point when its map on local rings is flat, and is flat
when this holds at every point. An `O_X`-module is flat over the target at a point when
its stalk is flat over the corresponding target stalk; it is flat over the target when
this holds everywhere.

A morphism being flat at a point is `AlgebraicGeometry.IsFlatAt`, the definition for morphisms
of ringed spaces, applied to the underlying ringed spaces of the schemes; its stalk map is the
canonical map on local rings. A flat morphism is `AlgebraicGeometry.Flat`, whose stalkwise
characterization is `AlgebraicGeometry.Flat.iff_flat_stalkMap`. Flatness of a module at a point
and everywhere are `AlgebraicGeometry.IsFlatOverAt` and `AlgebraicGeometry.IsFlatOver`, defined
for modules over a morphism of ringed spaces; they apply to arbitrary modules, and hence in
particular to quasi-coherent ones.

## References

* [Stacks Project, Tag 01U3](https://stacks.math.columbia.edu/tag/01U3)
* [Stacks Project, Tag 0253](https://stacks.math.columbia.edu/tag/0253)
-/

@[expose] public section

namespace AlgebraicGeometry

add_to_stacks 01U3 "part (1)" AlgebraicGeometry.IsFlatAt
add_to_stacks 01U3 "part (2)" AlgebraicGeometry.IsFlatOverAt
add_to_stacks 01U3 "part (3)" AlgebraicGeometry.Flat
add_to_sga "3 III 2.0" "partial" AlgebraicGeometry.Flat
add_to_sga "7 VII 1.3.8" "flatness of p" AlgebraicGeometry.Flat
add_to_ega "0 6.7.1" AlgebraicGeometry.Flat
add_to_ega "IV 2.1.1" AlgebraicGeometry.Flat
add_to_stacks 01U3 "part (4)" AlgebraicGeometry.IsFlatOver
add_to_stacks 0253 "part (1)" AlgebraicGeometry.IsFlatOverAt
add_to_stacks 0253 "part (2)" AlgebraicGeometry.IsFlatAt
add_to_stacks 0253 "part (3)" AlgebraicGeometry.Flat

end AlgebraicGeometry

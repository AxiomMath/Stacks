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
particular to quasi-coherent ones. For a morphism of schemes `f`, flatness at `x` is flatness
of `f.stalkMap x` (`AlgebraicGeometry.isFlatAt_iff_flat_stalkMap`), and `Flat f` is flatness at
every point (`AlgebraicGeometry.flat_iff_forall_isFlatAt`). A faithfully flat morphism, one that
is flat and surjective, is `AlgebraicGeometry.FaithfullyFlat`.

## References

* [Stacks Project, Tag 01U3](https://stacks.math.columbia.edu/tag/01U3)
* [Stacks Project, Tag 0253](https://stacks.math.columbia.edu/tag/0253)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

add_to_stacks 01U3 "part (1)" AlgebraicGeometry.IsFlatAt
add_to_stacks 01U3 "part (2)" AlgebraicGeometry.IsFlatOverAt
add_to_stacks 01U3 "part (3)" AlgebraicGeometry.Flat
add_to_sga "3 III 2.0" "partial" AlgebraicGeometry.Flat
add_to_sga "7 VII 1.3.8" "flatness of p" AlgebraicGeometry.Flat
add_to_ega "0 6.7.1" AlgebraicGeometry.Flat
add_to_ega "IV 2.1.1" AlgebraicGeometry.Flat
add_to_stacks 01U3 "part (4)" AlgebraicGeometry.IsFlatOver
add_to_stacks 0253 "(1) `F` flat over `Y` at `x`, for a module `F` over a morphism `f`, applied as \
  `IsFlatOverAt f.toLRSHom.toShHom F x` to any `F : X.Modules`" AlgebraicGeometry.IsFlatOverAt
add_to_stacks 0253 "(2) `f` flat at `x`, applied as `IsFlatAt f.toLRSHom.toShHom x`; this is \
  flatness of `f.stalkMap x` by `isFlatAt_iff_flat_stalkMap`" AlgebraicGeometry.IsFlatAt
add_to_stacks 0253 "(3) `f` flat, Mathlib's affine-local definition; it is flatness at every \
  point by `flat_iff_forall_isFlatAt`" AlgebraicGeometry.Flat

/-- A morphism of schemes is flat at `x`, as a morphism of the underlying ringed spaces, if and
only if its map on local rings `O_{Y, f(x)} → O_{X, x}` is flat. -/
@[stacks 0253 "(2) flat at `x` is flatness of the stalk map `O_{Y,f(x)} → O_{X,x}`"]
public theorem isFlatAt_iff_flat_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    IsFlatAt f.toLRSHom.toShHom x ↔ (f.stalkMap x).hom.Flat :=
  Iff.rfl

/-- A morphism of schemes is flat if and only if it is flat at every point of its source. -/
@[stacks 0253 "(3) flat is flat at every point of `X`"]
public theorem flat_iff_forall_isFlatAt {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Flat f ↔ ∀ x : X, IsFlatAt f.toLRSHom.toShHom x :=
  Flat.iff_flat_stalkMap f

/-- A morphism of schemes is faithfully flat if it is flat and surjective. -/
@[stacks 0253 "(4) faithfully flat: flat and surjective"]
public abbrev FaithfullyFlat {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Flat f ∧ Surjective f

end AlgebraicGeometry

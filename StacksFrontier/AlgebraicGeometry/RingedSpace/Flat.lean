module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness for morphisms of ringed spaces and for modules over them

A morphism of ringed spaces is flat at a point when its induced homomorphism on stalks is
flat; it is flat when it is flat at every point of its source. Flatness of the stalk
homomorphism is Mathlib's `RingHom.Flat`.

For a morphism of ringed spaces `f : X ⟶ Y`, an `O_X`-module is flat over `Y` at `x : X`
when its stalk at `x`, with scalars restricted along the stalk map
`O_{Y, f(x)} → O_{X, x}`, is flat. It is flat over `Y` when this holds at every point of
`X`. An `O_X`-module is represented by `SheafOfModules` over the underlying sheaf of rings
of the commutative structure sheaf; its stalk already carries its canonical
`O_{X,x}`-module structure, and `Module.compHom` restricts that structure along the
canonical stalk map induced by `f`.

## Main definitions

* `AlgebraicGeometry.IsFlatAt` says that a morphism of ringed spaces is flat at a given
  point.
* `AlgebraicGeometry.IsFlat` says that a morphism of ringed spaces is flat at every point.
* `AlgebraicGeometry.IsFlatOverAt` is flatness of a module over the target at one point.
* `AlgebraicGeometry.IsFlatOver` is flatness of a module over the target at every point.

## References

* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism of ringed spaces is flat at `x` if its induced homomorphism from
the stalk at the image of `x` to the stalk at `x` is flat. -/
@[stacks 02N3 "flat at a point", ega "0 6.7.1" "f flat at x"]
public abbrev IsFlatAt {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y) (x : X) :=
  (f.hom.stalkMap x).hom.Flat

/-- A morphism of ringed spaces is flat if it is flat at every point of its
source. -/
@[stacks 02N3 "flat", ega "0 6.7.1" "f flat"]
public abbrev IsFlat {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x, IsFlatAt f x

/-- An `O_X`-module is flat over `Y` at `x : X` if its stalk at `x`, regarded
as an `O_{Y,f(x)}`-module through the stalk map of `f`, is flat. -/
@[stacks 08KT "part (1)", ega "0 6.7.1" "F f-flat at x"]
public noncomputable abbrev IsFlatOverAt {X Y : AlgebraicGeometry.RingedSpace.{u}}
    (f : X ⟶ Y)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    (x : X) : Prop :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) := inferInstance
  letI : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  Module.Flat (Y.presheaf.stalk (f.hom.base x))
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)

/-- An `O_X`-module is flat over `Y` if it is flat over `Y` at every point of
`X`. -/
@[stacks 08KT "part (2)", ega "0 6.7.1" "F f-flat (all x)"]
public abbrev IsFlatOver {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) : Prop :=
  ∀ x : X, IsFlatOverAt f F x

end AlgebraicGeometry

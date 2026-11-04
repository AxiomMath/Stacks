module

public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors

/-!
# The two spellings of sheaves of modules on a ringed space, and what `RingedSpace.{u}` means

[Stacks, Tag 01F6] is stated over `RingedSpace.{u}` — one explicit universe level — while
`AlgebraicGeometry.RingedSpace` has two universe parameters. This file records, as Lean rather
than as prose, that the one-level spelling is sound and says exactly what it means; and it
bridges the two parallel namings of the module category that the statement of the tag mixes.

## The universe reading of `RingedSpace.{u}`

`AlgebraicGeometry.RingedSpace` is an abbreviation with signature
`RingedSpace.{u₁, u₂} : Type (max (u₂ + 1) (u₁ + 1))`, where `u₁` is the universe of the
structure sheaf's values (`CommRingCat.{u₁}`) and `u₂` that of the carrier (`TopCat.{u₂}`).
Writing `RingedSpace.{u}` is therefore a *partial* application of universe levels, which Lean
permits: the missing level is left as a universe metavariable. It is not auto-bound to a fresh
parameter in general, and in particular it is not `autoImplicit` doing the work — this file and
`StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors` both have `autoImplicit` off under
`lake build` and both use the one-level spelling.

What fixes the missing level is the module API itself. `Modules` and `structureSheafRing` are each
declared over `RingedSpace.{u, u}`, so the first mention of either solves the metavariable to
`u`, and `RingedSpace.{u}` *is* `RingedSpace.{u, u}` from that point on. The elaborated
signatures are the measurement: `ModuleFunctors` writes `(X : RingedSpace.{u})` throughout and
`#check @pushforward` reports `{X Y : RingedSpace.{u, u}}`. So the one-level spelling of
[Stacks, Tag 01F6] is well formed and denotes the two-equal-level content, which is the content
`StacksFrontier.AlgebraicGeometry.RelativeLeray.Statement` carries. The restriction to equal
levels is real but it is imposed by the module API, not by the spelling: sheaves of modules over
a ringed space are only available at `RingedSpace.{u, u}`, because
`SheafOfModules.pushforward` is known to be a right adjoint only there.

## The two namings

The statement of the tag mixes two independently introduced names for one category: `Modules X`
(from `ModuleFunctors`, built from `ringCatSheaf`) and `SheafOfModules.{u} (structureSheafRing X)`
(from `Topology.Sheaves.Functors.Module.RingedSpace`). They are the same category, and
`pushforward` and `modulePushforward` are the same functor, each on the nose — the two
structure-sheaf constructions are both `sheafCompose` applied to `forget₂ CommRingCat RingCat`, and
the two pushforwards are both `SheafOfModules.pushforward` applied to
`Functor.whiskerRight _.hom.c _`.

Note that `Modules`, `pushforward` and `ringCatSheaf` are in the **root** namespace, not in
`AlgebraicGeometry`: `AlgebraicGeometry.Modules` does not exist.

## Main results

* `Stacks.RelativeLeray.modules_eq_sheafOfModules_ringSheaf`: `Modules X` and
  `SheafOfModules.{u} (structureSheafRing X)` are the same category.
* `Stacks.RelativeLeray.pushforward_eq_modulePushforward`: `pushforward f` and
  `modulePushforward f` are the same functor.

## References

* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RelativeLeray

/-- **The two spellings of the module category agree.** `Modules X`, the category used by the
statement of [Stacks, Tag 01F6], and `SheafOfModules.{u} (structureSheafRing X)` are equal:
`ringCatSheaf` and `structureSheafRing` are both `sheafCompose` applied to the forgetful functor
`CommRingCat ⥤ RingCat`.

The binder is written `RingedSpace.{u}`, as the tag writes it; it elaborates to
`RingedSpace.{u, u}`, since the right-hand side is declared there. -/
theorem modules_eq_sheafOfModules_ringSheaf (X : RingedSpace.{u}) :
    _root_.Modules X = SheafOfModules.{u} (structureSheafRing X) :=
  rfl

/-- **The two spellings of pushforward agree.** `pushforward f`, the functor used by the
statement of [Stacks, Tag 01F6], and `modulePushforward f`, the one used in this directory, are
the same functor: both are `SheafOfModules.pushforward` applied to the morphism of structure
sheaves obtained by whiskering `f.hom.c`. -/
theorem pushforward_eq_modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    _root_.pushforward f = modulePushforward f :=
  rfl

end Stacks.RelativeLeray

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import Mathlib.Geometry.RingedSpace.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Symmetric monoidal complexes of modules on a ringed space

For a ringed space `(X, O_X)`, complexes of `O_X`-modules form a symmetric monoidal category.
Its tensor bifunctor is the total complex of the sheafified degreewise tensor product, with the
Koszul sign convention, and its unit is the structure sheaf concentrated in degree zero.

## Main definitions

* `Stacks.Cohomology.MonoidalComplexes.Mod` and `Stacks.Cohomology.MonoidalComplexes.Complexes`
  name `Mod(O_X)` and `Comp(Mod(O_X))` for a
  ringed space, so that dependent statements need not spell the ring sheaf out.
* `Stacks.Cohomology.MonoidalComplexes.cochainComplexMonoidalCategory` and
  `Stacks.Cohomology.MonoidalComplexes.cochainComplexSymmetricCategory` expose the monoidal and
    symmetric structures
  separately from the bundled statement.

## Main results

* `Stacks.Cohomology.MonoidalComplexes.symmetricMonoidalComplexes` constructs this structure for
  every ringed space.

## Implementation notes

A ringed space is a ringed site: its site is the site of opens, `Opens.grothendieckTopology`,
and its structure sheaf `X.sheaf` is a sheaf of commutative rings on that site.  So the ringed
space statement is the ringed site statement of Tag 0FPQ instantiated there, and the whole
content of this file is that instantiation.  In particular all the auxiliary data -- the
sheafification, the additivity of the sheaf tensor, the direct sums forming the total complexes
-- are the fields of `Stacks.Cohomology.MonoidalComplexesOfModules.SymmetricMonoidalComplexes`, and
-- the two payload equalities
`tensor_eq_total` and `unit_eq_structureSheaf` are available as its projections at the ringed
space without further work.

The universes do instantiate: for `X : RingedSpace.{u, u}` the site is `Opens X.carrier`, a
`Type u` whose category instance is `Preorder.smallCategory`, hence `Category.{u}`.  Tag 0FPQ's
site universes `u` and `v` are therefore both `u`, its section ring universe `max u v` is `u`,
and its module category is `SheafOfModules.{u}`, which is what a ringed space supplies.  No
specialization and no universe-raising wrapper is needed.

Both structure defs are `@[instance_reducible]`, following Tag 0FPQ; instance search does not
find them, so a consumer introduces them with `letI`.

## References

* [Stacks Project, Tag 0FP8](https://stacks.math.columbia.edu/tag/0FP8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace Stacks.Cohomology.MonoidalComplexes

variable (X : RingedSpace.{u, u})

/-- `Mod(O_X)`, the category of modules over the structure sheaf of a ringed space, regarded as
modules on the ringed site of opens of `X`. -/
abbrev Mod := Stacks.Cohomology.MonoidalComplexesOfModules.Mod X.sheaf

/-- `Comp(Mod(O_X))`, the category of cochain complexes of `O_X`-modules. -/
abbrev Complexes := Stacks.Cohomology.MonoidalComplexesOfModules.Complexes X.sheaf

/-- Complexes of modules on a ringed space form a symmetric monoidal category; its tensor
bifunctor is the total complex of the sheafified degreewise tensor product and its unit is the
structure sheaf in degree zero.  This is Tag 0FPQ at the ringed site of opens of `X`. -/
@[stacks 0FP8, ega "0 4.1.5" "partial"]
public def symmetricMonoidalComplexes :
    Stacks.Cohomology.MonoidalComplexesOfModules.SymmetricMonoidalComplexes X.sheaf :=
  Stacks.Cohomology.MonoidalComplexesOfModules.symmetricMonoidalComplexes X.sheaf

/-- The monoidal structure on complexes of modules on a ringed space. -/
@[instance_reducible]
public def cochainComplexMonoidalCategory : MonoidalCategory (Complexes X) :=
  (symmetricMonoidalComplexes X).monoidal

/-- The symmetry, with Koszul signs, on complexes of modules on a ringed space. -/
@[instance_reducible]
public def cochainComplexSymmetricCategory :
    letI := cochainComplexMonoidalCategory X
    SymmetricCategory (Complexes X) :=
  (symmetricMonoidalComplexes X).symmetric

end Stacks.Cohomology.MonoidalComplexes

end

end

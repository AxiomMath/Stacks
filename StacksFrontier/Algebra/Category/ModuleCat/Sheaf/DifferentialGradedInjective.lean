module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Graded injective differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. A right differential graded `A`-module is *graded injective* when the right
graded module obtained from it by forgetting the differential is an injective object of the
category of right graded modules over `A.toGradedAlgebra`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GradedInjective` is graded injectivity of a right
  differential graded module.

## Implementation notes

The underlying graded module is taken with `SheafOfModules.forgetToGradedModule` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetColimits.lean`. The predicate is an
abbreviation of Mathlib's categorical `CategoryTheory.Injective`, so its extension property and
its product API apply to it directly with no transfer lemmas.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module pieces
are independent; a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FSP](https://stacks.math.columbia.edu/tag/0FSP)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- A right differential graded module is graded injective when it is injective after
forgetting its differential. -/
@[stacks 0FSP]
abbrev GradedInjective (I : DifferentialGradedModule.{t, a, m} A) : Prop :=
  Injective ((forgetToGradedModule A).obj I)

end DifferentialGradedModule

end SheafOfModules

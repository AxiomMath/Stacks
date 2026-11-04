module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Limits of graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras.
[Stacks, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0) asserts, among other things, that
the category `Mod(A)` of right graded `A`-modules has arbitrary limits. This file proves that,
by assembling it from the two shapes of limit that are already available: arbitrary products,
formed degreewise, and equalizers, which an additive category with kernels has.

## Main results

* `SheafOfModules.GradedModule.hasLimitsOfSize`: right graded modules over a sheaf of graded
  algebras admit all limits of the size of the module universe.

The Stacks tags for the two colimit-and-product statements this rests on are recorded here as
well, on `SheafOfModules.GradedModule.hasProducts` and
`SheafOfModules.GradedModule.hasColimitsOfSize`.

## Implementation notes

The three inputs come from elsewhere: the preadditive structure from
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedDegreeColimits.lean`, the degreewise kernels
from `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean`, and the degreewise
products from `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleProducts.lean`. None of
them needs the site to admit sheafification, so neither does this; that is the asymmetry with
the dual statement `SheafOfModules.GradedModule.hasColimitsOfSize`, whose cokernels and direct
sums are built by sheafifying a presheaf-level construction.

The size universe is the universe of the module sections, matching
`SheafOfModules.GradedModule.hasProducts`: `SheafOfModules.{m} R` has limits only of diagrams
small relative to `m`.

## References

* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

/-- **Graded modules over a sheaf of graded algebras admit all small limits.**

A limit of any shape of the size of the module universe is built from degreewise products and
from equalizers, the latter being the kernel of a difference. -/
@[stacks 0FR0 "limits"]
instance hasLimitsOfSize : HasLimitsOfSize.{m, m} (GradedModule.{t, a, m} A) :=
  have : HasEqualizers (GradedModule.{t, a, m} A) :=
    Preadditive.hasEqualizers_of_hasKernels
  has_limits_of_hasEqualizers_and_products.{m}

end GradedModule

end SheafOfModules

add_to_stacks 0FR0 "products" SheafOfModules.GradedModule.hasProducts

add_to_stacks 0FR0 "colimits" SheafOfModules.GradedModule.hasColimitsOfSize

end

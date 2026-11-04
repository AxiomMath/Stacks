module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# Limits, filtered colimits and finite direct sums of sheaves of modules on a space

Let `O` be a sheaf of rings on a topological space `X`. The category of sheaves of
`O`-modules has all limits, those limits are computed on the underlying presheaves of
modules and hence on sections over each open, its filtered colimits are exact, and its
finite direct sums are the finite direct sums of the underlying presheaves of modules.

## Main results

* `SheafOfModules.hasLimitsOfSize`, `SheafOfModules.forgetPreservesLimitsOfSize` and
  `SheafOfModules.evaluationPreservesLimitsOfSize` are Mathlib's statements that all limits
  exist, that forgetting the sheaf condition preserves them, and that so does evaluation at
  an object of the site; for the site of open subsets of `X` the last two say that a limit
  is computed on sections over each open.
* `AlgebraicGeometry.SheafOfModules.ab5OfSize`: filtered colimits of sheaves of `O`-modules
  are exact.
* `AlgebraicGeometry.SheafOfModules.forget_preservesFiniteBiproducts`: finite direct sums of
  sheaves of `O`-modules are the finite direct sums of the underlying presheaves of modules.

## Implementation notes

Existence of limits and their computation on presheaves and on sections hold over an
arbitrary site, and are taken from Mathlib; registering those declarations records the
content of the clause for the open-cover site in particular. Exactness of filtered colimits
is proved in this project over an arbitrary site, so the statement here is its
specialization to the open-cover site of a topological space. Finite direct sums are finite
biproducts, which any additive functor preserves; forgetting the sheaf condition is additive
because it is the identity on the underlying presheaves of modules.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

add_to_stacks 01AH "part (1): all limits exist" SheafOfModules.hasLimitsOfSize
add_to_stacks 01AH "part (1): limits are the limits of the underlying presheaves of modules"
  SheafOfModules.forgetPreservesLimitsOfSize
add_to_stacks 01AH "part (1): limits commute with taking sections over opens"
  SheafOfModules.evaluationPreservesLimitsOfSize

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Filtered colimits of sheaves of modules on a topological space are exact. -/
@[stacks 01AH "part (3): filtered colimits are exact", sga "4 II 6.7" "special case"]
theorem ab5OfSize : AB5OfSize.{u, u} (_root_.SheafOfModules.{u} O) :=
  instAB5SheafOfModules O

/-- Finite direct sums of sheaves of modules are the finite direct sums of the underlying
presheaves of modules: forgetting the sheaf condition preserves finite biproducts. -/
@[stacks 01AH "part (4): finite direct sums are the finite direct sums of presheaves"]
theorem forget_preservesFiniteBiproducts :
    PreservesFiniteBiproducts
      (_root_.SheafOfModules.forget O : _root_.SheafOfModules.{u} O ⥤ _) :=
  inferInstance

end AlgebraicGeometry.SheafOfModules

end

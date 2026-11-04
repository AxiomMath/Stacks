module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint

/-!
# Forgetting the differential of a differential graded module commutes with limits

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. `SheafOfModules.forgetToGradedModule A` forgets the differential of a right
differential graded `A`-module. This file records that it preserves all limits.

## Main results

* `SheafOfModules.forgetToGradedModule_preservesLimitsOfSize` and
  `SheafOfModules.forgetToGradedModule_preservesLimits`: forgetting the differential commutes
  with limits of every size.

## Implementation notes

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetRightAdjoint.lean` exhibits
`forgetToGradedModule A` as a **right** adjoint, with the differential graded hull as its left
adjoint, so `CategoryTheory.Adjunction.rightAdjoint_preservesLimits` applies directly. This
is the dual of the colimit statement of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetColimits.lean`, where the same
functor is a *left* adjoint with the cofree module as its right adjoint; so the forgetful
functor commutes with everything.

As for colimits, the adjunction route is what keeps the universes free: it yields
`PreservesLimitsOfSize` at *every* pair of size universes, whereas a degreewise argument would
need limits of sheaves of modules indexed by types larger than the universe their sections live
in. No universe is specialized below, and no hypothesis on the site is needed.

This statement is the limit half of Tag 0FRJ. It carries no `@[stacks]` attribute: the tag
belongs to the chapter's own decomposition of that tag and is placed elsewhere.

## References

* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u s₁ s₂

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Forgetting the differential of a right differential graded module commutes with limits of
every size, because it is a right adjoint. -/
instance forgetToGradedModule_preservesLimitsOfSize (A : DifferentialGradedAlgebra.{t, a} R) :
    PreservesLimitsOfSize.{s₁, s₂} (forgetToGradedModule.{t, a, m} A) :=
  (dgHullAdjunction.{t, a, m} A).rightAdjoint_preservesLimits

/-- Forgetting the differential of a right differential graded module commutes with all
limits. -/
instance forgetToGradedModule_preservesLimits (A : DifferentialGradedAlgebra.{t, a} R) :
    PreservesLimits (forgetToGradedModule.{t, a, m} A) :=
  forgetToGradedModule_preservesLimitsOfSize A

end SheafOfModules

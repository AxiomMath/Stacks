module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafModulesGrothendieck
public import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of filtered colimits of differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. [Stacks, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ) asserts that the
category `Mod(A, d)` of right differential graded `A`-modules is abelian, that it has
arbitrary direct sums and products, and that **its filtered colimits are exact**. This file
proves the last of these, together with the part of the abelian structure that it needs.

The exactness statement is a reduction to the corresponding statement for right *graded*
`A`-modules, which Tag 0FR0 supplies: the graded modules are abelian, have colimits, and have
exact filtered colimits (`SheafOfModules.GradedModule.gradedModule_ab5`). The bridge is
`SheafOfModules.forgetToGradedModule A`, which forgets the differential. It

* preserves all colimits, because it is a **left** adjoint (Tag 0FRJ, proved in
  `GradedForgetColimits`),
* preserves all limits, because it is also a **right** adjoint (Tag 0FSK, proved in
  `GradedForgetRightAdjoint`), and
* reflects isomorphisms,

so `HasExactColimitsOfShape.domain_of_functor` pulls exactness back along it. That lemma also
needs finite limits in `Mod(A, d)`, and those are built here: products are formed degreewise
and kernels carry the restriction of the differential.

## Main results

* `SheafOfModules.DifferentialGradedModule.hasFiniteLimits`: `Mod(A, d)` has finite limits.
* `SheafOfModules.forgetToGradedModule_preservesFiniteLimits`: forgetting the differential
  preserves finite limits.
* `SheafOfModules.differentialGradedModule_hasExactColimitsOfShape`: colimits of a given shape
  of differential graded modules are exact as soon as they are exact for graded modules.
* `SheafOfModules.differentialGradedModule_ab5` is **Tag 0FRJ's exactness of filtered
  colimits**: `AB5OfSize` for `Mod(A, d)`, with the graded-module side discharged by
  `gradedModule_ab5`.

## Implementation notes

**Why finite limits are built here.** `HasExactColimitsOfShape K D` is by definition
`PreservesFiniteLimits (colim : (K ⥤ D) ⥤ D)`, so it cannot be stated, let alone proved,
without finite limits in `D`. For `D = Mod(A, d)` those are part of Tag 0FRJ's abelian
assertion, and only the *limit* half of it is needed: products, kernels and a preadditive
structure. No cokernel and no normality of monomorphisms enters the argument here, so only the
limit half of the abelian structure is used.

**Where the limit-side inputs come from.** The preadditive structure, the kernels and the
reflection of isomorphisms are *imported*, not built here: they live in
`DifferentialGradedModuleAbelian` (which also proves the full `abelian` instance under
`HasSheafify`), and `forgetToGradedModule_preservesLimitsOfSize` lives in
`DifferentialGradedForgetLimits`. The product clause is
`DifferentialGradedModule.hasProducts` in `DifferentialGradedProducts`. All the clauses of
Tag 0FRJ are gathered into its one statement in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedModuleCategoryProperties.lean`,
which is where the tag is registered.

**Universes.** Nothing is specialized. `differentialGradedModule_hasExactColimitsOfShape`
leaves the shape and all module universes free, taking the graded-module inputs as hypotheses.
`differentialGradedModule_ab5` is stated at size `(m, m)` for a module universe `m`, which is
where `gradedModule_ab5` lives; the site universes `u`, `v` and the algebra universe
`a` stay free, as in `gradedModule_ab5` itself.

## References

* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
* [Stacks Project, Tag 0FSK](https://stacks.math.columbia.edu/tag/0FSK)
* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m w w' v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- **Right differential graded modules have finite limits**: they are preadditive with
kernels, hence have equalizers, and they have products. -/
noncomputable instance hasFiniteLimits (A : DifferentialGradedAlgebra.{t, a} R) :
    HasFiniteLimits (DifferentialGradedModule.{t, a, m} A) :=
  have : HasFiniteProducts (DifferentialGradedModule.{t, a, m} A) :=
    hasFiniteProducts_of_hasProducts.{m} _
  have : HasEqualizers (DifferentialGradedModule.{t, a, m} A) :=
    Preadditive.hasEqualizers_of_hasKernels
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end DifferentialGradedModule

/-! ### Forgetting the differential preserves limits and reflects isomorphisms -/

/-- Forgetting the differential of a right differential graded module preserves finite
limits. -/
instance forgetToGradedModule_preservesFiniteLimits
    (A : DifferentialGradedAlgebra.{t, a} R) :
    PreservesFiniteLimits (forgetToGradedModule.{t, a, m} A) :=
  inferInstance

/-! ### Exactness of filtered colimits -/

/-- **Colimits of differential graded modules of a given shape are exact as soon as colimits of
graded modules of that shape are.** Forgetting the differential preserves colimits of that
shape (Tag 0FRJ), preserves finite limits and reflects isomorphisms (Tag 0FSK), hence reflects
finite limits, so exactness is pulled back along it. -/
instance differentialGradedModule_hasExactColimitsOfShape
    (A : DifferentialGradedAlgebra.{t, a} R) (K : Type w') [Category.{w} K]
    [HasColimitsOfShape K (DifferentialGradedModule.{t, a, m} A)]
    [HasColimitsOfShape K (GradedModule.{t, a, m} A.toGradedAlgebra)]
    [HasExactColimitsOfShape K (GradedModule.{t, a, m} A.toGradedAlgebra)] :
    HasExactColimitsOfShape K (DifferentialGradedModule.{t, a, m} A) :=
  HasExactColimitsOfShape.domain_of_functor K (forgetToGradedModule.{t, a, m} A)

/-- **Filtered colimits of right differential graded modules are exact.** The graded-module
half of the reduction is `SheafOfModules.GradedModule.gradedModule_ab5`; the finite limits that
exactness is about are the products and kernels of `Mod(A, d)`. It is the exactness clause of
Tag 0FRJ, whose statement is assembled in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedModuleCategoryProperties.lean`
and registered there. -/
noncomputable instance differentialGradedModule_ab5
    (A : DifferentialGradedAlgebra.{t, a} R)
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasFilteredColimitsOfSize.{m, m} (DifferentialGradedModule.{t, a, m} A)] :
    AB5OfSize.{m, m} (DifferentialGradedModule.{t, a, m} A) where
  ofShape K _ _ :=
    have : HasColimitsOfShape K (GradedModule.{t, a, m} A.toGradedAlgebra) :=
      GradedModule.hasColimitsOfSize.has_colimits_of_shape K
    have : HasExactColimitsOfShape K (GradedModule.{t, a, m} A.toGradedAlgebra) :=
      GradedModule.gradedModule_hasExactColimitsOfShape A.toGradedAlgebra K
    differentialGradedModule_hasExactColimitsOfShape A K

end SheafOfModules

end

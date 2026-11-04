module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Limits of graded modules in a fixed degree

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of `ℤ`-graded `R`-algebras, and let
`n : ℤ`. [Stacks, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0) asserts, among other
things, that taking the degree-`n` homogeneous component of a right graded `A`-module commutes
with arbitrary limits. This file proves that.

## Main results

* `SheafOfModules.GradedModule.pieceFunctor_preservesLimitsOfSize`: taking a fixed homogeneous
  component preserves all limits of the size of the module universe.

## Implementation notes

Both inputs are already available degreewise: products of graded modules are formed degreewise
(`SheafOfModules.GradedModule.pieceFunctor_preservesProduct`) and so are kernels
(`SheafOfModules.GradedModule.pieceFunctor_preservesKernel`). A preadditive functor that
preserves kernels preserves equalizers, and a functor preserving equalizers and products
preserves all limits, so the proof is the assembly of those two facts — dual to
`SheafOfModules.GradedModule.pieceFunctor_preservesColimits`, which is assembled from
degreewise direct sums and cokernels.

Binary biproducts of graded modules, which the equalizer step needs, come from products at the
smallest universe rather than from `SheafOfModules.GradedModule.hasFiniteBiproducts`; that keeps
the statement free of the sheafification hypotheses on the site, which the dual statement does
need because cokernels are built by sheafifying.

The size universe is the universe of the module sections, matching
`SheafOfModules.GradedModule.hasLimitsOfSize`: `SheafOfModules.{m} R` has limits only of
diagrams small relative to `m`.

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

/-- **Taking a fixed homogeneous component of a graded module commutes with all limits.**

A limit of any shape of the size of the module universe is built from products and equalizers,
and the degree-`n` component preserves both: products and kernels of graded modules are formed
degreewise. -/
@[stacks 0FR0 "degree_preserves_limits", sga "6 VI 2.7" "partial"]
instance pieceFunctor_preservesLimitsOfSize (n : ℤ) :
    PreservesLimitsOfSize.{m, m} (pieceFunctor.{t, a, m} A n) :=
  have : HasBinaryBiproducts (GradedModule.{t, a, m} A) :=
    have : HasProducts.{0} (GradedModule.{t, a, m} A) := has_smallest_products_of_hasProducts
    HasBinaryBiproducts.of_hasBinaryProducts
  have : HasEqualizers (GradedModule.{t, a, m} A) :=
    Preadditive.hasEqualizers_of_hasKernels
  have : PreservesLimitsOfShape WalkingParallelPair (pieceFunctor.{t, a, m} A n) :=
    Functor.preservesEqualizers_of_preservesKernels _
  have : ∀ ι : Type m, PreservesLimitsOfShape (Discrete ι) (pieceFunctor.{t, a, m} A n) :=
    fun _ => preservesLimitsOfShape_of_discrete _
  preservesLimits_of_preservesEqualizers_and_products (pieceFunctor.{t, a, m} A n)

end GradedModule

end SheafOfModules

end

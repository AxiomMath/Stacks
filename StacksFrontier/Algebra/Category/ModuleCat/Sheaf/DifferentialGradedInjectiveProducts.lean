module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleProducts

/-!
# Products of graded injective differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. A product of graded injective right differential graded `A`-modules is graded
injective.

## Main results

* `SheafOfModules.DifferentialGradedModule.gradedInjective_pi`: a product of graded injective
  right differential graded modules is graded injective.

## Implementation notes

The product is the categorical product of right differential graded modules, and graded
injectivity of a module is injectivity of the right graded module obtained by forgetting its
differential. The proof is therefore just the two facts that forgetting the differential
commutes with products — it is a right adjoint — and that a product of injective objects is
injective: `CategoryTheory.Limits.PreservesProduct.iso` transports the product past the
forgetful functor, and `CategoryTheory.Injective.instPiObj` supplies the injectivity.

The index type lies in the universe of the module sections, which is where both categories have
their products.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent;
a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FSR](https://stacks.math.columbia.edu/tag/0FSR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A product of graded injective right differential graded modules is graded injective. -/
@[stacks 0FSR]
theorem gradedInjective_pi {A : DifferentialGradedAlgebra.{t, a} R} {T : Type m}
    (I : T → DifferentialGradedModule.{t, a, m} A) (hI : ∀ t, GradedInjective (I t)) :
    GradedInjective (∏ᶜ I) :=
  Injective.of_iso (PreservesProduct.iso _ I).symm (Injective.instPiObj _)

end DifferentialGradedModule

end SheafOfModules

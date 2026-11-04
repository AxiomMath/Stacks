module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift.UniversalSolutionAlgebra
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift.WeightSpaces
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift.SmallLift
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift.LargeAndDomainLift

/-!
# Lifting maps from kernels of maps between finite free module functors

Let `A` be a commutative ring. A module-valued functor on `A`-algebras is represented as a
presheaf of modules on the opposite of `CommAlgCat A`. For an `A`-module `M`, its associated
module-valued functor sends an `A`-algebra `B` to `B ⊗[A] M`.

## Main definitions

* `AdequateFunctor.moduleExtensionOfCarrier`: the module-valued functor associated to an
  `A`-module.

## Main results

* `AdequateFunctor.exists_lift_from_finite_free_kernel`: a map from the kernel of a map between
  finite free module functors to a module functor extends across the kernel inclusion.

## Implementation notes

The hypothesis that the displayed row beginning in zero is exact is expressed by a mono kernel
inclusion together with exactness at the middle term.

## Organization

* `FiniteFreeLift.UniversalSolutionAlgebra`: Laurent coefficients, the graded symmetric algebra
  and the universal solution algebra.
* `FiniteFreeLift.WeightSpaces`: weight spaces of `B ⊗[A] M` at Laurent polynomial algebras.
* `FiniteFreeLift.SmallLift`: Tag 06V0 for a module in the ring's own universe.
* `FiniteFreeLift.LargeAndDomainLift`: Tag 06V0 in a larger universe and on a restricted
  domain of algebras.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
-/

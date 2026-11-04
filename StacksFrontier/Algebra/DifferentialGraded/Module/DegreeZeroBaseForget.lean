module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra

/-!
# The total-direct-sum functor over the base ring, forgotten to complexes

Let `R` be a commutative ring. A cochain complex `K` of `R`-modules becomes a differential
graded module over `R` placed in degree zero, by
`DifferentialGradedModule.degreeZeroTotalFunctor R R`, and the complex of `R`-modules
underlying that differential graded module is `K` again. This file records that identification
as an isomorphism of functors.

The point is that the two sides reach their `R`-module structures by different routes: the
complex underlying a differential graded module is built from the homogeneous components of its
total module, whose scalars come from the ambient algebra by restriction along `R → R`, whereas
`K` carries the `R`-module structures of its own terms.
`DifferentialGradedModule.degreeZeroTotalForgetIso` identifies the first with the second *up to
restriction of scalars along* `algebraMap R R`, and that restriction is the identity.

## Main definitions

* `DifferentialGradedModule.degreeZeroTotalForgetSelfIso`: **summing a complex of `R`-modules up
  and forgetting back down is the identity.**

## References

* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI) for differential graded
  modules.
-/

@[expose] public section

open CategoryTheory DifferentialGradedAlgebra

universe u

namespace DifferentialGradedModule

/-- **Summing a cochain complex of `R`-modules up and forgetting back down is the identity.**
The composite of `DifferentialGradedModule.degreeZeroTotalFunctor R R` with the forgetful
functor to complexes of `R`-modules is the identity functor on
`CochainComplex (ModuleCat R) ℤ`.

This is `DifferentialGradedModule.degreeZeroTotalForgetIso` at `A = R`, where the restriction of
scalars along `algebraMap R R` that appears there is the identity functor. -/
noncomputable def degreeZeroTotalForgetSelfIso (R : Type u) [CommRing R] :
    degreeZeroTotalFunctor R R ⋙ forgetToCochainComplex (degreeZero R R) ≅
      𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) :=
  degreeZeroTotalForgetIso ≪≫
    NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsId'.{u} (algebraMap R R) rfl) (ComplexShape.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (ComplexShape.up ℤ)

end DifferentialGradedModule

end

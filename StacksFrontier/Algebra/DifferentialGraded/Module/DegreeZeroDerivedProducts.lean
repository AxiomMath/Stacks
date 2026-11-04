module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Countable products in the derived category of a ring placed in degree zero

Let `R` be a commutative ring and `S` an `R`-algebra. The derived category
`D(degreeZero R S, d)` of differential graded modules over `S` placed in degree zero is equivalent
to the derived category of `T`-modules for any `T` identified with the opposite algebra of `S`
(`DifferentialGradedModule.degreeZeroDerivedEquivalence`), and the latter has countable products
because countable products of modules are exact (Tag 07KC). An equivalence carries limits, so
`D(degreeZero R S, d)` has countable products as well. This is what lets a derived limit of an
inverse system in `D(degreeZero R R, d)` — the source's `D(R)` in the differential graded
encoding — be spoken of at all.

## Main results

* `DifferentialGradedModule.hasProductsOfShape_degreeZero_derivedCategory`: `D(degreeZero R S, d)`
  has products indexed by any countable type.

## References

* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 09SC](https://stacks.math.columbia.edu/tag/09SC)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace DifferentialGradedModule

open DifferentialGradedAlgebra (degreeZero IsOppositeAlgebra)

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {S : Type u} [Ring S] [Algebra R S]

/-- **`D(degreeZero R S, d)` has countable products**, transported from the derived category of
`T`-modules, for any `T` identified with the opposite algebra of `S`, along the degree-zero
comparison equivalence. -/
theorem hasProductsOfShape_degreeZero_derivedCategory' (T : Type u) [Ring T] [Algebra R T]
    [IsOppositeAlgebra R S T] (I : Type) [Countable I] :
    HasProductsOfShape I (derivedCategory' (degreeZero R S)) :=
  have : HasProductsOfShape I (DerivedCategory (ModuleCat.{u} T)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  Adjunction.hasLimitsOfShape_of_equivalence
    (degreeZeroDerivedEquivalence (R := R) (S := S) (A := T)).functor

/-- `D(degreeZero R R, d)` has countable products. -/
instance hasProductsOfShape_degreeZero_derivedCategory (I : Type) [Countable I] :
    HasProductsOfShape I (derivedCategory' (degreeZero R R)) :=
  hasProductsOfShape_degreeZero_derivedCategory' R I

end DifferentialGradedModule

end

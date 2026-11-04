module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedTotalComplex

/-!
# The cup product and the comparison with derived sections live on one total Čech complex

Let `(X, 𝒪_X)` be a space with a sheaf of commutative rings, let `V` be an open subset, put
`A = 𝒪_X(V)` and let `U : ι → Opens X` be an open covering of `V`. The total Čech complex
`Tot(Č^•(U, K^•))` of `A`-modules on which the Čech cup product of [Stacks, Tag 07MB] is defined,
`Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA`, is the one on which the comparison with
derived sections of [Stacks, Tag 08BN] is defined, `Stacks.Cech.Linear.totalCechComplexFunctor`.

## Main results

* `Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA_eq`: the two total Čech complexes are
  equal.

## References

* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Cech.ModuleCupProduct

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (V : Opens X) {ι : Type u} (U : ι → Opens X) (hU : V = ⨆ i, U i)

/-- The total Čech complex on which the Čech cup product is defined equals the one on which the
comparison with derived sections of [Stacks, Tag 08BN] is defined: both are the totalization of
the flipped Čech bicomplex of the same complex of `A`-modules. -/
theorem totalCechComplexFunctorA_eq :
    totalCechComplexFunctorA O V U hU =
      Stacks.Cech.Linear.totalCechComplexFunctor X
        (Stacks.SheafOfModules.Tensor.ringSheaf O) V U hU :=
  rfl

end Stacks.Cech.ModuleCupProduct

end

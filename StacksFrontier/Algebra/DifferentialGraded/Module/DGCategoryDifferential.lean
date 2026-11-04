module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory

/-!
# The differential on homogeneous maps of differential graded modules

For right differential graded modules over a differential graded algebra `(A, d)` over a
commutative ring `R`, the signed commutator with the differentials of the two modules sends a
homogeneous right `A`-linear map of degree `n` to one of degree `n + 1`. That operation is
`R`-linear and squares to zero, so each Hom module is itself a differential graded `R`-module.

## Main results

The differential is `DifferentialGradedModule.homogeneousMapDifferential`, with right-linearity
and the degree shift built into its codomain. Its additivity, its `R`-linearity and the
square-zero property are the projections `DGCategory.d_add`, `DGCategory.d_smul` and
`DGCategory.d_d` of `DifferentialGradedModule.dgCategory`.

## Implementation notes

The differential graded category of right differential graded modules is
`DifferentialGradedModule.dgCategory`. Its homogeneous morphisms are the right `A`-linear maps of
a prescribed degree, and its differential is `homogeneousMapDifferential`, whose construction
already verifies that the commutator is right-linear and raises the degree by one; the three
`DGCategory` projections already state the remaining claims for it. Hence no special-case
wrappers are introduced here and this file only records which declarations carry the source's
statement.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

add_to_stacks 09LC "hom_differential" DifferentialGradedModule.homogeneousMapDifferential
add_to_stacks 09LC "hom_differential" DGCategory.d_add
add_to_stacks 09LC "hom_differential" DGCategory.d_smul
add_to_stacks 09LC "hom_differential" DGCategory.d_d

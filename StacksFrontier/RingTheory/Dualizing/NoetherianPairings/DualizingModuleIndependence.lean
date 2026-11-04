module

public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationIndependence

/-!
# Independence of the dualizing module from a finite-open factorization

For a quasi-finite map of Noetherian rings, the relative dualizing module computed from a
finite-open factorization is independent of that factorization.  The comparison is characterized
by its behavior on a common finite-open refinement whose intermediate algebra embeds into the
target.

The mathematics lives in the three modules this one re-exports.
`StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleChange` builds
`Stacks.Discriminant.dualizingModule_commonChange` and the comparisons
`Stacks.Discriminant.finiteAlgebraChangeToF` and
`Stacks.Discriminant.finiteSubalgebraChangeToF` that enlarge the finite algebra.
`StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison` assembles them into
`Stacks.Discriminant.dualizingModuleEquiv`, carrying `@[stacks 0BT1]` together with its
characterization on a common refinement and its reflexivity and transitivity.
`StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationIndependence` supplies
`Stacks.Discriminant.finiteOpenFactorization_epi`.

## References

* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
-/

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimensionDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image and direct sums for an integral morphism

[Stacks, Tag 0F0D] says that for a proper morphism of schemes `f : X ⟶ Y` and an integer
`n ≥ 1` the derived direct image `Rf_* : D(X_étale, ℤ/nℤ) ⟶ D(Y_étale, ℤ/nℤ)` commutes with
direct sums.

The statement, for a proper morphism and a torsion ring of coefficients, is
`preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper` in the namespace
`Stacks.EtaleCohomology`.

## References

* [Stacks Project, Tag 0F0D](https://stacks.math.columbia.edu/tag/0F0D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe z u r

namespace Stacks.EtaleCohomology

end Stacks.EtaleCohomology

end

module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffineSeparated

/-!
# Separated locally quasi-finite morphisms are ind-quasi-affine

A separated locally quasi-finite morphism of schemes is ind-quasi-affine:
`AlgebraicGeometry.isIndQuasiAffineHom_of_isSeparated_of_locallyQuasiFinite`.

## Implementation notes

Local quasi-finiteness is the conjunction of `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`; `AlgebraicGeometry.LocallyQuasiFinite` alone only records
the isolation of the points of the fibres.

## References

* [Stacks Project, Tag 0AP9](https://stacks.math.columbia.edu/tag/0AP9)
-/

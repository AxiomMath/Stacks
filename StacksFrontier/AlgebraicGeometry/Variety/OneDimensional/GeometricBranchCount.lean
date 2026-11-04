module

public import StacksFrontier.AlgebraicGeometry.Variety.DeltaBranches.NormalizationResidue

/-!
# Branches and the residue quotient of the normalization

For a strictly henselian reduced Nagata local ring, the geometric branches are counted by the
maximal ideals of its normalization.  For any reduced Nagata local ring, the simultaneous
residue map on the normalization also induces a surjection after quotienting its source by the
original ring and its target by the diagonal copy of the residue field.

The two statements are `Ring.numberOfGeometricBranches_eq_encard_maximalSpectrum_integralClosure`
and `Ring.normalizationResidueQuotientMap_surjective`, about the maps
`Ring.normalizationResidueProductMap` and `Ring.normalizationResidueQuotientMap`.

## References

* [Stacks Project, Tag 0C42](https://stacks.math.columbia.edu/tag/0C42)
-/

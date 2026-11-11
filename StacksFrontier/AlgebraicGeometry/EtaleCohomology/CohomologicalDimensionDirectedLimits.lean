module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.DirectedLimit

/-!
# Cohomological dimension of a directed limit of schemes: where Tag 0F0R is proved

[Stacks, Tag 0F0R] (Étale Cohomology, Lemma 59.95.2): let `X = lim X_i` be a directed limit of
quasi-compact and quasi-separated schemes with affine transition morphisms. Then
`cd(X) ≤ max cd(X_i)`.

The lemma is proved, with no hypothesis beyond the source's, as
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_iSup_of_isLimit_of_isDirected` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/CohomologicalDimension/DirectedLimit.lean`: for a
diagram `D : Iᵒᵖ ⥤ Scheme` over a directed set `I` with affine transition maps and
quasi-compact, quasi-separated values, and a limit cone `c` (`hc : IsLimit c`), it states
`etaleCohomologicalDimension c.pt ≤ ⨆ i, etaleCohomologicalDimension (D.obj i)`, where
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension` (in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/CohomologicalDimensionLimits.lean`) is the étale
cohomological dimension, valued in `ℕ∞`, so that the maximum is the supremum, attained because a
directed set is nonempty. The tag is registered by the `stacks` attribute on that
declaration.

## References

* [Stacks Project, Tag 0F0R](https://stacks.math.columbia.edu/tag/0F0R)
-/

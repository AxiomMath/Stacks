module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.BaseChange

/-!
# Base change of a property of morphisms local on the target

A property of morphisms of schemes which is local on the target for one of the standard
topologies is preserved by base change along a morphism of the corresponding class: flat for
fpqc, flat and locally of finite presentation for fppf, syntomic, smooth, étale, and open
immersions for the Zariski topology.

These statements are proved in
`StacksFrontier/AlgebraicGeometry/Descent/LocalOnTarget/BaseChange.lean`, which this module
re-exports; `AlgebraicGeometry.pullbackSnd_of_flat`,
`AlgebraicGeometry.pullbackSnd_of_flat_locallyOfFinitePresentation`,
`AlgebraicGeometry.pullbackSnd_of_syntomic`, `AlgebraicGeometry.pullbackSnd_of_smooth`,
`AlgebraicGeometry.pullbackSnd_of_etale` and
`AlgebraicGeometry.pullbackSnd_of_isOpenImmersion` are available to its importers unchanged.

## References

* [Stacks Project, Tag 04QU](https://stacks.math.columbia.edu/tag/04QU)
-/

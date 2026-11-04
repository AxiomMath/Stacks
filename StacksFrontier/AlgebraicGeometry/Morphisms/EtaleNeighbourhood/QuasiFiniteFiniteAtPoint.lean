module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# An étale neighbourhood making a quasi-finite morphism finite at a point

Let `f : X ⟶ S` be locally of finite type and let `x` be a point of `X` which is isolated in its
fibre. After an elementary étale change of the base there is an open subscheme of the base change
which is *finite* over the new base, contains exactly one point over the distinguished point of the
neighbourhood, and that point maps to `x` with the same residue field. These three properties
persist under any further elementary étale neighbourhood of the distinguished point.

This file re-exports the material. `Stacks.Flatness.IsFiniteNeighborhoodAt`,
`Stacks.Flatness.FiniteNeighborhoodAt`, `Stacks.Flatness.finiteNeighborhoodAt`,
`Stacks.Flatness.exists_etaleNeighborhood_finiteAt` and
`Stacks.Flatness.isFiniteNeighborhoodAt_baseChange` are declared in
`StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood`;
`AlgebraicGeometry.fiberIsoOfIsElementary` in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood`;
and `AlgebraicGeometry.pullback_snd_residueFieldMap_isIso` in
`StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback`.

## References

* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
-/

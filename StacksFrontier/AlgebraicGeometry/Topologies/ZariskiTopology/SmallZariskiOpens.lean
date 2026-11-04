module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpens
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

/-!
# Sheaves on the small Zariski site and on the underlying space

For a scheme `S` of a big Zariski site, an object of its small Zariski site is a scheme open
over `S`, and taking the open image of its structure morphism identifies that site with the
lattice of open subsets of the topological space of `S`. The identification matches the two
topologies, so sheaves on the small Zariski site of `S` are the same thing as sheaves on the
space of `S`.

That comparison is `AlgebraicGeometry.smallZariskiToOpens`, with
`AlgebraicGeometry.smallZariskiSiteEquiv`, `AlgebraicGeometry.smallZariskiSheafEquivWith` and
`AlgebraicGeometry.smallZariskiSheafEquiv`; they live in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpens`, which this module makes
available alongside the small Zariski site itself.

## References

* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

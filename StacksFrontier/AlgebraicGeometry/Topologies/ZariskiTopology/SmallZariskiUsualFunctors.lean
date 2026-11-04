module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiSpaceFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallZariskiOpens

/-!
# Base change on the small Zariski site and the usual functors on spaces

For a morphism `f : T ⟶ S` in a big Zariski site, base change on the small Zariski sites
corresponds, under the identification of the small Zariski site of a scheme with the lattice of
open subsets of its space, to taking inverse images of open subsets along the underlying
continuous map. So the inverse and direct image of sheaves along small-site base change are the
usual inverse and direct image of sheaves on the underlying topological spaces.

The comparison of the two base changes is
`AlgebraicGeometry.smallZariskiToOpens_baseChange_obj` and
`AlgebraicGeometry.smallZariskiToOpens_baseChange_eq`, and the two identifications of functors
are `AlgebraicGeometry.smallZariskiPullbackIso` and
`AlgebraicGeometry.smallZariskiPushforwardIso`, obtained from the comparison of direct images
`AlgebraicGeometry.smallSitePushforwardAdjointIso`; they live in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiSpaceFunctors`, which this
module makes available alongside small-site base change and the comparison with opens.

## References

* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
-/

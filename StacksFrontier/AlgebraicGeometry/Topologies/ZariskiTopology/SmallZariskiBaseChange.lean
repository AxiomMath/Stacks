module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallZariskiProjection

/-!
# Base change on small Zariski sites

A morphism `f : T ⟶ S` in a big Zariski site induces a morphism of small Zariski sites from
`T` to `S`. Its continuous functor sends an open subscheme of `S` to its fibre product with
`T` over `S`, and that functor is characterized by a natural isomorphism after including both
small sites into the slices of all schemes, so its action on objects and on arrows is explicit
without a choice of fibre products in the cutoff category.

That construction is `AlgebraicGeometry.smallZariskiBaseChange`, with the packaged existence
statement `AlgebraicGeometry.exists_smallZariskiBaseChange`, the morphism-of-sites instance
`AlgebraicGeometry.smallZariskiBaseChange_isMorphismOfSites` and the comparison with
scheme-theoretic fibre product `AlgebraicGeometry.smallZariskiBaseChangeIso`; they live in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiBaseChange`, which this module
makes available alongside the projection to the small Zariski topos.

## References

* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
-/

module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiToBig
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Precoverage

/-!
# The small Zariski topos inside a big Zariski topos

For a morphism `f : T ⟶ S` in a big Zariski site, postcomposition with `f` sends the small
Zariski category of `T` into the big Zariski category over `S`. That functor is both continuous
and cocontinuous, so it induces a morphism of topoi

`i_f : Sh(T_Zar) ⟶ Sh((Sch/S)_Zar)`

whose inverse image is restriction along the functor. Because the functor also preserves fibre
products and equalizers, the inverse image has in addition a *left* adjoint `i_{f,!}`, itself
left exact.

The functor is `AlgebraicGeometry.smallZariskiToBigZariskiFunctor`, with its two site-level
properties `AlgebraicGeometry.smallZariskiToBigZariskiFunctor_isCocontinuous` and
`AlgebraicGeometry.smallZariskiToBigZariskiFunctor_isContinuous`, the morphism of topoi
`AlgebraicGeometry.smallZariskiToBigZariskiMorphism`, and the lower shriek
`AlgebraicGeometry.smallZariskiToBigZariskiLowerShriek` with its adjunction
`AlgebraicGeometry.smallZariskiToBigZariskiLowerShriekAdjunction`; they live in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiToBig`, which this module makes
available alongside the Zariski precoverages.

## References

* [Stacks Project, Tag 020Y](https://stacks.math.columbia.edu/tag/020Y)
-/

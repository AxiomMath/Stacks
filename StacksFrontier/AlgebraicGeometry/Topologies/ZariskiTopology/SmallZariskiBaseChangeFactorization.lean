module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiFactorization
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.BigZariskiMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallZariskiBaseChange

/-!
# Factorizations of the small Zariski base-change morphism

Let `f : T ⟶ S` be a morphism in a big Zariski site. Base change along `f` is a morphism of
small Zariski sites, so it represents a geometric morphism

`f_small : Sh(T_Zar) ⟶ Sh(S_Zar)`.

This is how `f_small` sits among the other morphisms of topoi attached to `f`: base change
commutes with the inclusions of the small Zariski sites into the big Zariski slices, as a
square of site functors and hence as a square of geometric morphisms; and the morphism `i_f`
of Tag 020Y factors through the projection to the small Zariski topos.

The geometric morphism is `AlgebraicGeometry.smallZariskiMorphism`; the commuting square is
`AlgebraicGeometry.smallZariskiBaseChange_comp_inclusionIso` and
`AlgebraicGeometry.smallZariskiProjection_baseChangeIso`; the factorization of `i_f` is
`AlgebraicGeometry.smallZariskiToBigZariskiMorphism_factor_pushforwardIso` and
`AlgebraicGeometry.smallZariskiToBigZariskiMorphism_factor_inverseImageIso`; and the
factorization of `f_small` is `AlgebraicGeometry.smallZariskiMorphismIsoProjectionCompBig` and
`AlgebraicGeometry.smallZariskiMorphismIsoProjectionCompInclusion`. They live in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiFactorization`, which this module
makes available alongside the big Zariski base-change morphism.

## References

* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
-/

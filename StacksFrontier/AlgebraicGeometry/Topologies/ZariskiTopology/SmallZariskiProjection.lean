module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallToBigTopos

/-!
# The small Zariski topos as a retract of the big Zariski topos

For a scheme `S` in a big Zariski site, the inclusion of its small Zariski site into the big
Zariski site over `S` is a morphism of sites, and the resulting morphism of topoi

`π_S : Sh((Sch/S)_Zar) ⟶ Sh(S_Zar)`

is a retraction of the morphism `i_S = i_{id_S}` of Tag 020Y. Inverse image along `i_S` is
direct image along `π_S`, namely restriction of a big-site sheaf to the small site, so
`i_S⁻¹(𝒢)(U/S) = 𝒢(U/S)`.

The projection is `AlgebraicGeometry.smallZariskiProjection`, with the two site-level
hypotheses `AlgebraicGeometry.smallZariskiInclusion_isContinuous` and
`AlgebraicGeometry.smallZariskiInclusion_preservesFiniteLimits`, the retraction
`AlgebraicGeometry.smallZariskiProjection_comp_identity`, and the identification of inverse
image with restriction
`AlgebraicGeometry.smallZariskiIdentityInverseImageIsoProjectionPushforward` together with its
form on sections `AlgebraicGeometry.smallZariskiIdentityInverseImageSections`; they live in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiProjection`, which this module
re-exports.

Preservation of the final object by the small-site inclusion, which those statements consume,
is `AlgebraicGeometry.preservesTerminal_smallZariskiInclusion` in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits`.

## References

* [Stacks Project, Tag 020Z](https://stacks.math.columbia.edu/tag/020Z)
-/

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# An open immersion is an open embedding on points

An open immersion of presheaves on the big fppf site of `S` induces an open embedding on the
point spaces of Tag 03BU, with the topology of Tag 03BX. No algebraic-space condition is
needed on either side.

## Main results

* `AlgebraicGeometry.Space.isOpenEmbedding_pointsMap`: the map on points of an open immersion
  is an open embedding.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map on points of an open immersion of presheaves on the big fppf site of `S` is an
open embedding. -/
theorem isOpenEmbedding_pointsMap {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : IsOpenImmersion B S hS f) :
    Topology.IsOpenEmbedding (pointsMap B S hS F f) :=
  have : Mono f := mono_of_isOpenImmersion B S hS f hf
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_pointsMap B S hS f) (pointsMap_injective_of_mono B S hS f)
    (isOpenMap_pointsMap_of_isOpenImmersion B S hS f hf)

end AlgebraicGeometry.Space

end

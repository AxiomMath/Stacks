module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubtopos.Sets
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Immersions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A closed immersion of ringed spaces is a closed immersion of topoi

A morphism of ringed spaces whose underlying continuous map is a closed embedding presents a
morphism of topoi between the small Zariski sites which is a *closed immersion* in the sense of
Stacks 08M0(2): it is an embedding — this is
`Stacks.ToposBridge.isEmbedding_morphismOfTopoi`, an inducing map being enough — and the
essential image of its direct image on sheaves of sets is a closed subtopos, which is
`Stacks.ClosedSubtopos.isClosedSubtopos_essImage_pushforward`.

The two statements fit together because the direct image of the presented morphism of topoi *is*
`TopCat.Sheaf.pushforward` along the underlying continuous map, by
`Stacks.ToposBridge.morphismOfTopoi_pushforward`.

## Main results

* `Stacks.ClosedSubtopos.isClosedSubtopos_essImage_morphismOfTopoi`: the essential image of the
  direct image of the presented morphism of topoi is a closed subtopos.
* `Stacks.ClosedSubtopos.isClosedImmersion_morphismOfTopoi`: the presented morphism of topoi is
  a closed immersion.
* `Stacks.ClosedSubtopos.isClosedImmersion_morphismOfTopoi_of_scheme`: the same for a closed
  immersion of schemes.

## References

* [Stacks Project, Tag 08LZ](https://stacks.math.columbia.edu/tag/08LZ)
* [Stacks Project, Tag 08M0](https://stacks.math.columbia.edu/tag/08M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology AlgebraicGeometry

universe u

namespace Stacks.ClosedSubtopos

/-- **The image of `i_*` on sheaves of sets is a closed subtopos, for a morphism of ringed
spaces.** If the underlying continuous map of a morphism of ringed spaces is a closed embedding,
the essential image of the direct image on sheaves of sets of the presented morphism of topoi is
a closed subtopos of `Sh(Y)`. -/
theorem isClosedSubtopos_essImage_morphismOfTopoi {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.hom.base)) :
    IsClosedSubtopos (Opens.grothendieckTopology Y.carrier)
      (Stacks.ToposBridge.morphismOfTopoi f).pushforward.essImage :=
  isClosedSubtopos_essImage_pushforward hf

/-- **Stacks 08M0(2) for a morphism of ringed spaces with closed-embedding underlying map.** The
presented morphism of topoi is a closed immersion: an embedding whose essential image is a closed
subtopos. -/
theorem isClosedImmersion_morphismOfTopoi {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.hom.base)) :
    MorphismOfTopoi.IsClosedImmersion (Stacks.ToposBridge.morphismOfTopoi f) :=
  ⟨Stacks.ToposBridge.isEmbedding_morphismOfTopoi f hf.isInducing,
    isClosedSubtopos_essImage_morphismOfTopoi f hf⟩

/-- **Stacks 08M0(2) for a closed immersion of schemes.** The morphism of topoi presented by a
closed immersion of schemes is a closed immersion of topoi. -/
theorem isClosedImmersion_morphismOfTopoi_of_scheme {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion f] :
    MorphismOfTopoi.IsClosedImmersion
      (Stacks.ToposBridge.morphismOfTopoi f.toLRSHom.toShHom) :=
  isClosedImmersion_morphismOfTopoi f.toLRSHom.toShHom f.isClosedEmbedding

end Stacks.ClosedSubtopos

end

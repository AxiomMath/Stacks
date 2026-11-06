module

public import Mathlib.CategoryTheory.Limits.Preserves.Lattice
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.Opens
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map

/-!
# Preimages of hypercoverings of a topological space

Let `f : X ⟶ Y` be a continuous map and regard `X` and `Y` as sites through the pretopologies
of their opens. Taking preimages of opens is a functor `Opens Y ⥤ Opens X` which takes covering
families to covering families and preserves finite limits, so by [Stacks, Tag 0DAZ] the preimage
of a hypercovering of an open `V` of `Y` is a hypercovering of `f⁻¹V`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.preservesFiniteLimits_opensMap`: the preimage functor on
  opens preserves finite limits.
* `Stacks.CategoryTheory.Hypercovering.opensMap_mapsCoveringsToCoverings`: the preimage of a
  covering family of opens is a covering family of opens.
* `Stacks.CategoryTheory.Hypercovering.IsHypercovering.opensMap`: the preimage of a
  hypercovering of `V : Opens Y` is a hypercovering of `(Opens.map f).obj V`.
* `Stacks.CategoryTheory.Hypercovering.opensMap_obj_I` and
  `Stacks.CategoryTheory.Hypercovering.opensMap_obj_obj_left`: in each simplicial degree the
  preimage hypercovering has the same index type as the original, and its member at an index is
  the preimage of the original member.

## Implementation notes

The preimage functor is Mathlib's `TopologicalSpace.Opens.map`, which is by definition the
functor attached to the frame homomorphism of preimages between the complete lattices of opens;
preservation of finite limits is therefore the general fact that a map preserving finite infima
and the top element preserves finite limits of the associated preorder categories. Because
`Opens.map` is defined through that order homomorphism, the index types of the formal coproducts
and the comparison morphisms are left untouched, so the two identification lemmas hold by
definition and finiteness of the index type in each degree transfers verbatim.

The pretopology is the one of pointwise covering families, for which the covering clause of
Tag 00WV is immediate: a point of `f⁻¹V` maps into `V`, hence into one of the members of a
covering family of `V`, hence lies in the preimage of that member.

## References

* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 0DAZ](https://stacks.math.columbia.edu/tag/0DAZ)
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace

namespace Stacks.CategoryTheory.Hypercovering

section Preimage

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The preimage functor on opens preserves finite limits. -/
instance preservesFiniteLimits_opensMap : PreservesFiniteLimits (Opens.map f) :=
  inferInstanceAs
    (PreservesFiniteLimits (OrderHom.ofClass f.frameHom).toFunctor)

/-- **The covering clause of Tag 00WV for the preimage functor on opens.** The preimage of a
covering family of an open `V` of `Y` is a covering family of `f⁻¹V`. -/
theorem opensMap_mapsCoveringsToCoverings :
    MapsCoveringsToCoverings.{w} (Opens.map f) (Opens.pretopology Y) (Opens.pretopology X) := by
  intro V ι A g hg x hx
  obtain ⟨W, k, ⟨i⟩, hxW⟩ := hg (f.hom x) (Opens.mem_map.mp hx)
  exact ⟨(Opens.map f).obj (A i), (Opens.map f).map (g i), Presieve.ofArrows.mk i,
    Opens.mem_map.mpr hxW⟩

/-- **Tag 0DAZ for the preimage functor on opens.** The preimage under a continuous map
`f : X ⟶ Y` of a hypercovering of an open `V` of `Y` is a hypercovering of `f⁻¹V`. -/
theorem IsHypercovering.opensMap {V : Opens Y}
    (K : SimplicialObject (FormalCoproduct.{w} (Over V)))
    (hK : IsHypercovering (Opens.pretopology Y) K) :
    IsHypercovering (Opens.pretopology X)
      (K ⋙ mapFormalCoproduct.{w} (Over.post (Opens.map f) (X := V))) :=
  IsHypercovering.map (Opens.pretopology Y) (Opens.pretopology X) (Opens.map f)
    (opensMap_mapsCoveringsToCoverings.{w} f) K hK

/-- The preimage of a simplicial family of opens has, in each degree, the index type of the
original family. -/
theorem opensMap_obj_I {V : Opens Y} (K : SimplicialObject (FormalCoproduct.{w} (Over V)))
    (n : SimplexCategoryᵒᵖ) :
    ((K ⋙ mapFormalCoproduct.{w} (Over.post (Opens.map f) (X := V))).obj n).I =
      (K.obj n).I :=
  rfl

/-- The member of the preimage family at an index is the preimage of the member of the original
family at that index. -/
theorem opensMap_obj_obj_left {V : Opens Y}
    (K : SimplicialObject (FormalCoproduct.{w} (Over V))) (n : SimplexCategoryᵒᵖ)
    (i : (K.obj n).I) :
    (((K ⋙ mapFormalCoproduct.{w} (Over.post (Opens.map f) (X := V))).obj n).obj i).left =
      (Opens.map f).obj ((K.obj n).obj i).left :=
  rfl

end Preimage

end Stacks.CategoryTheory.Hypercovering

end

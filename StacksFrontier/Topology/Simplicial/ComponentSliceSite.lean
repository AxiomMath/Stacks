module

public import StacksFrontier.Topology.Simplicial.ComponentInclusion
public import StacksFrontier.Topology.Simplicial.SliceSite

/-!
# Localizing the inclusion of a simplicial degree at an open

`Stacks.Topology.Simplicial.levelFunctor_isContinuous` and `levelFunctor_isCocontinuous` say
that the inclusion of the open-set site of one simplicial degree into the total site of a
simplicial space is a continuous and cocontinuous functor of sites. Every statement about
*local* presentations of a sheaf on the total site — quasi-coherence among them — is a statement
about the slices of the two sites, and so needs the localization of that inclusion at an open
`W` of the degree, `CategoryTheory.Over.post (levelFunctor X n) : Over W ⥤ Over (n, W)`, to be a
functor of sites as well.

Cocontinuity of the localization is automatic from cocontinuity of the inclusion
(`CategoryTheory.Over.post` of a cocontinuous functor is cocontinuous). Continuity is not: this
file supplies it, through the preservation of one-hypercovers, which for a functor between sites
with pullbacks follows from cover preservation together with the preservation of fibre products
that `Stacks.Topology.Simplicial.levelFunctor_preservesPullbacks` already records.

## Main results

* `Stacks.Topology.Simplicial.levelFunctor_coverPreserving`: the inclusion of a simplicial
  degree carries covering sieves to covering sieves.
* `Stacks.Topology.Simplicial.levelFunctor_preservesOneHypercovers`: it preserves
  one-hypercovers.
* `Stacks.Topology.Simplicial.levelFunctor_overPost_isContinuous`: **its localization at an open
  of the degree is continuous** for the two slice topologies.

## Implementation notes

Cover preservation is read off the two pointwise descriptions of the covering sieves: a sieve on
an open `U` of the degree-`n` space is covering when every point of `U` lies in a member of it
(`CategoryTheory.Opens.mem_grothendieckTopology`), and a sieve on the object `(n, U)` of the
total site is covering when every point of `U` lies in an open whose *levelwise* arrow into
`(n, U)` belongs to it (`Stacks.Topology.Simplicial.SimplicialOpen.mem_grothendieckTopology_iff`).
The levelwise arrow of an open `V ≤ U` is the image under the inclusion of the inclusion
`V ⟶ U`, so the member produced by the first description is a member of the functor-pushforward
sieve, with the identity as the arrow of the total site that the pushforward asks for.

## References

* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

/-- **The inclusion of a simplicial degree carries covering sieves to covering sieves.** -/
theorem levelFunctor_coverPreserving (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    CoverPreserving (Opens.grothendieckTopology (X.obj n))
      (SimplicialOpen.grothendieckTopology X) (levelFunctor X n) where
  cover_preserve {U S} hS := by
    rw [SimplicialOpen.mem_grothendieckTopology_iff]
    intro x hx
    obtain ⟨V, f, hf, hxV⟩ := (Opens.mem_grothendieckTopology (X.obj n)).mp hS x hx
    refine ⟨V, leOfHom f, ⟨V, f, 𝟙 _, hf, ?_⟩, hxV⟩
    apply SimplicialOpen.Hom.ext
    show (𝟙 n) = 𝟙 n ≫ 𝟙 n
    simp

/-- The inclusion of a simplicial degree preserves one-hypercovers: it preserves fibre products
and carries covering sieves to covering sieves. -/
instance levelFunctor_preservesOneHypercovers (X : SimplicialObject TopCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    (levelFunctor X n).PreservesOneHypercovers (Opens.grothendieckTopology (X.obj n))
      (SimplicialOpen.grothendieckTopology X) :=
  Functor.PreservesOneHypercovers.of_coverPreserving (levelFunctor_coverPreserving X n)

/-- **The localization at an open of the inclusion of a simplicial degree is continuous.** -/
instance levelFunctor_overPost_isContinuous (X : SimplicialObject TopCat.{u})
    (n : SimplexCategoryᵒᵖ) (W : Opens (X.obj n)) :
    (Over.post (X := W) (levelFunctor X n)).IsContinuous
      ((Opens.grothendieckTopology (X.obj n)).over W)
      ((SimplicialOpen.grothendieckTopology X).over ((levelFunctor X n).obj W)) :=
  inferInstance

end Stacks.Topology.Simplicial

end

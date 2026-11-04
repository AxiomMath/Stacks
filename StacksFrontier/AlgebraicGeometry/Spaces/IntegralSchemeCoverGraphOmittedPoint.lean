module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGraphSplitting

/-!
# The graph omits a point of the complementary piece over every point of its image

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, and let `C`
be a subfunctor of `X ×_Z Y` whose point set is the complement of the point set of the graph of
`f` over `g` — the complementary piece of
`AlgebraicGeometry.Space.exists_graphComplement_decomposition`. The graph is a section of the
*first* projection, so it is not a section of the second; but `Γ ≫ pr₂ = f`, so over every point
of `Y` **in the image of `f`** the graph does supply a point of the fibre of the second
projection, and that point lies outside `C` because the two point sets are complementary.

This is the omitted-point input of the fibre-degree drop of the inductive step of
[Stacks, Tag 09YB]. There `f = j : U ⟶ Y` is the quasi-compact open immersion of the relative
compactification, `g = π : Y ⟶ X` is the integral morphism it is followed by, and `C = W` is the
complementary summand of `U ×_X Y = U ⨿ W`; the conclusion is that the fibre of `W ⟶ Y` over a
point of `j(U)` misses a point of the fibre of `U ×_X Y ⟶ Y`, which is the source's "the `U`
summand accounts for one of the `d`".

**The restriction to the image of `f` is essential and is not a defect of the statement.** Over a
point of `Y` outside `j(U)` the graph supplies nothing, and indeed the fibre of `W ⟶ Y` there
need not drop. Carrying the bound from `j(U)` to all of `Y` is a separate step, and it is
performed by closedness of the degree stratum of [Stacks, Tag 07S8] against topological density
of `j(U)`, not by this file.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_mem_range_graph_pointsMap_snd_eq`: over a point of `Y` in the
  image of `f` there is a point of `X ×_Z Y` lying in the point set of the graph and mapping to
  it under the second projection.
* `AlgebraicGeometry.Space.exists_notMem_range_pointsMap_ι_of_mem_range_pointsMap`: **the
  omitted point.** The same point, exhibited as lying outside the point set of any subfunctor
  whose point set is complementary to that of the graph.

## Implementation notes

The whole content is `AlgebraicGeometry.Space.graph_comp_snd`, which says `Γ ≫ pr₂ = f`, read on
points through `AlgebraicGeometry.Space.pointsMap_comp_apply`. No separatedness, étaleness or
representability is used: the statements hold for arbitrary `f` and `g`, with the complementarity
of the two point sets supplied as a hypothesis rather than derived, so that the caller may take
it from `AlgebraicGeometry.Space.exists_graphComplement_decomposition` — whose last clause is
exactly it — without this file repeating that result's hypotheses.

## What is and is not proved

Nothing here carries a Stacks attribute and no part of [Stacks, Tag 09YB] is registered. The
fibre-degree drop which consumes this
(`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_isOpenImmersion_of_omits`)
states its omitted-point hypothesis on the canonical fibre of a relatively representable morphism
at a field-valued point, and the passage from the point-set statements proved here to that shape
is not carried out here.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Graph

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The graph meets the fibre of the second projection over every point of the image of `f`.**
For `f : X ⟶ Y` and `g : Y ⟶ Z` and a point `y` of `Y` of the form `f x`, the point `Γ x` of
`X ×_Z Y` lies in the point set of the graph of `f` over `g` and is carried to `y` by the second
projection.

This is `AlgebraicGeometry.Space.graph_comp_snd` read on points. -/
theorem exists_mem_range_graph_pointsMap_snd_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    {y : points B S hS Y} (hy : y ∈ Set.range (pointsMap B S hS X f)) :
    ∃ w : points B S hS (pullback (f ≫ g) g),
      w ∈ Set.range (pointsMap B S hS X (graph B S hS f g)) ∧
        pointsMap B S hS (pullback (f ≫ g) g) (pullback.snd (f ≫ g) g) w = y := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨pointsMap B S hS X (graph B S hS f g) x, ⟨x, rfl⟩, ?_⟩
  rw [← pointsMap_comp_apply, graph_comp_snd]

/-- **The omitted point of the inductive step of [Stacks, Tag 09YB].** Let `C` be a subfunctor of
`X ×_Z Y` whose point set is the complement of the point set of the graph of `f` over `g`. Then
over every point of `Y` in the image of `f` there is a point of `X ×_Z Y` which the second
projection carries to it and which does **not** lie in the point set of `C`.

The hypothesis `hC` is the last clause of
`AlgebraicGeometry.Space.exists_graphComplement_decomposition`. -/
theorem exists_notMem_range_pointsMap_ι_of_mem_range_pointsMap (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : Subfunctor (pullback (f ≫ g) g))
    (hC : Set.range (pointsMap B S hS C.toFunctor C.ι) =
      (Set.range (pointsMap B S hS X (graph B S hS f g)))ᶜ)
    {y : points B S hS Y} (hy : y ∈ Set.range (pointsMap B S hS X f)) :
    ∃ w : points B S hS (pullback (f ≫ g) g),
      pointsMap B S hS (pullback (f ≫ g) g) (pullback.snd (f ≫ g) g) w = y ∧
        w ∉ Set.range (pointsMap B S hS C.toFunctor C.ι) := by
  obtain ⟨w, hwmem, hwy⟩ := exists_mem_range_graph_pointsMap_snd_eq B S hS f g hy
  refine ⟨w, hwy, ?_⟩
  rw [hC]
  exact fun h => h hwmem

end Graph

end AlgebraicGeometry.Space

end

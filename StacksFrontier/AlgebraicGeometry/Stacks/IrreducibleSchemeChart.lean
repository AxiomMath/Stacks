module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackDimensionFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme

/-!
# An irreducible affine smooth scheme chart, and the morphism of schemes under a chart comparison

The proof of **Stacks 0DS4** compares a 1-morphism with a smooth chart of its target by an
*irreducible* scheme: the dimension formula it ends on,
`AlgebraicGeometry.exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber_of_irreducibleSpace`,
asks the target of the morphism of schemes to be irreducible. This file produces such a chart —
affine, hence quasi-compact, and irreducible — of any nonempty locally Noetherian algebraic stack,
and records that the morphism of schemes underlying a 1-morphism of the algebraic stacks of two
schemes of the site inherits local finite type.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_isIrreducible`: a nonempty locally Noetherian scheme has
  an irreducible nonempty affine open.
* `AlgebraicGeometry.Stack.exists_irreducible_affine_smooth_chart`: a nonempty locally Noetherian
  algebraic stack over `S` has a smooth chart by an affine, irreducible, locally Noetherian scheme
  of the site.
* `AlgebraicGeometry.Stack.locallyOfFiniteType_siteMap`: the morphism of schemes underlying a
  1-morphism locally of finite type of the algebraic stacks of two schemes of the site is locally
  of finite type.

## Implementation notes

The affine open is found inside an irreducible component: a component of a locally Noetherian
space contains a nonempty open subset (a Noetherian open neighbourhood of a point meets it in a
component of the neighbourhood,
`NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`), the affine opens of a
scheme are a basis, and a nonempty open subset of an irreducible set is irreducible
(`IsPreirreducible.open_subset`). The component itself is `irreducibleComponent` of a point, which
exists because the scheme is nonempty.

Transporting the affine open to an object of the site is
`AlgebraicGeometry.BigFppfOver.exists_affineOpen_restrict`, whose inclusion is an open immersion
with the affine open as range; irreducibility of the resulting scheme of the site is pulled back
along that open embedding by `IsPreirreducible.preimage`. Smoothness of the composite chart is
`AlgebraicGeometry.Stack.isSmooth_schemeStackMap` for an open immersion followed by the given
chart, and both local Noetherianity statements are
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyNoetherian_of_isSmooth` at that composite.

The last result descends local finite type from a 1-morphism `h : schemeStack A ⟶ schemeStack V`
to `AlgebraicGeometry.Stack.siteMap h`. It goes through the morphism of representing presheaves of
**Stacks 04SW**: local finite type of a 1-morphism is smooth local on the source and target, so
the represented form of **Stacks 06FM** reads it on that morphism, which for the induced
1-morphism of a morphism of the site is `yoneda.map` of it
(`AlgebraicGeometry.Stack.representingMap_schemeStackMap`), and
`AlgebraicGeometry.Space.isLocallyOfFiniteType_yoneda_map_iff` reads that on the morphism of
schemes. The given `h` is only 2-isomorphic to the induced 1-morphism, which is what
`AlgebraicGeometry.Stack.schemeStackMapIso` supplies.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

/-- **A nonempty locally Noetherian scheme has an irreducible nonempty affine open.** An
irreducible component of the underlying space contains a nonempty open subset, the affine opens
are a basis, and a nonempty open subset of an irreducible set is irreducible. -/
theorem exists_isAffineOpen_isIrreducible (X : Scheme.{u}) [IsLocallyNoetherian X] [Nonempty X] :
    ∃ W : X.Opens, IsAffineOpen W ∧ IsIrreducible (W : Set X) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  -- the irreducible component through `x` contains a nonempty open set: a Noetherian open
  -- neighbourhood of `x` meets it in an irreducible component of the neighbourhood
  obtain ⟨O, hOopen, hOne, hOT⟩ : ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧
      V ⊆ irreducibleComponent x := by
    obtain ⟨W, hW, hxW, hWN⟩ := isLocallyNoetherianSpace_of_isLocallyNoetherian X x
    have := hWN
    have hcomp : (Subtype.val : W → X) ⁻¹' irreducibleComponent x ∈ irreducibleComponents W :=
      preimage_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents x)
        hW.isOpenEmbedding_subtypeVal ⟨x, mem_irreducibleComponent, ⟨⟨x, hxW⟩, rfl⟩⟩
    obtain ⟨V, hV, hVne, hVT⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hcomp
    exact ⟨Subtype.val '' V, hW.isOpenEmbedding_subtypeVal.isOpenMap _ hV, hVne.image _, by
      rintro _ ⟨v, hv, rfl⟩
      exact hVT hv⟩
  obtain ⟨y, hy⟩ := hOne
  obtain ⟨W, hWaff, hyW, hWO⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨O, hOopen⟩) hy
  exact ⟨W, hWaff,
    ⟨⟨y, hyW⟩, (isIrreducible_irreducibleComponent (x := x)).2.open_subset W.2
      (hWO.trans hOT)⟩⟩

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A nonempty locally Noetherian algebraic stack over `S` has a smooth chart by an affine,
irreducible, locally Noetherian scheme of the site.**

A smooth surjective scheme chart exists by the definition of an algebraic stack; its scheme is
locally Noetherian and, the chart being surjective on points, nonempty, so it has an irreducible
nonempty affine open. That open is an object of the site, its inclusion being an open immersion
and hence smooth, and the composite with the given chart is the chart asked for. -/
theorem exists_irreducible_affine_smooth_chart (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵)
    (hne : Nonempty (AlgebraicStacks.points B S hS 𝒵)) :
    ∃ (V : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V ⟶ 𝒵),
      AlgebraicStacks.IsSmooth B S hS a ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
          IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj V) ∧
            IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := by
  obtain ⟨U, a₀, ha₀sm, ha₀surj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒵
  let : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    AlgebraicStacks.isLocallyNoetherian_of_isSmooth B S hS U 𝒵 h𝒵 a₀ ha₀sm
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj U) := by
    obtain ⟨z⟩ := hne
    obtain ⟨p, -⟩ := ha₀surj z
    exact ⟨pointsHomeomorphScheme B S hS U p⟩
  obtain ⟨W, hWaff, hWirr⟩ :=
    exists_isAffineOpen_isIrreducible ((BigFppfOver.toScheme B S hS).obj U)
  obtain ⟨V, u, hu, hurange, hVaff⟩ :=
    BigFppfOver.exists_affineOpen_restrict B S hS U ⟨W, hWaff⟩
  have hu' := hu
  refine ⟨V, schemeStackMap.{u, w} B S hS u ≫ a₀,
    AlgebraicStacks.isSmooth_comp B S hS _ _
      (isSmooth_schemeStackMap.{u, w} B S hS u inferInstance) ha₀sm, hVaff, ?_, ?_⟩
  · have hemb : Topology.IsOpenEmbedding ((BigFppfOver.toScheme B S hS).map u) :=
      ((BigFppfOver.toScheme B S hS).map u).isOpenEmbedding
    refine (irreducibleSpace_def _).2 ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := hWirr.1
      obtain ⟨v, -⟩ : y ∈ Set.range ((BigFppfOver.toScheme B S hS).map u) := by
        rw [hurange]; exact hy
      exact ⟨v, trivial⟩
    · have hpre := hWirr.2.preimage hemb
      rwa [show ((BigFppfOver.toScheme B S hS).map u) ⁻¹' (W : Set _) = Set.univ by
        rw [← hurange, Set.preimage_range]] at hpre
  · exact AlgebraicStacks.isLocallyNoetherian_of_isSmooth B S hS V 𝒵 h𝒵 _
      (AlgebraicStacks.isSmooth_comp B S hS _ _
        (isSmooth_schemeStackMap.{u, w} B S hS u inferInstance) ha₀sm)

/-- **The morphism of schemes underlying a 1-morphism of the algebraic stacks of two schemes of
the site inherits local finite type.** Local finite type of a 1-morphism is smooth local on the
source and target, so the represented form of Stacks 06FM reads it on the morphism of representing
presheaves of Stacks 04SW; for the 1-morphism induced by a morphism of the site that morphism is
`yoneda.map` of it, and the given 1-morphism is 2-isomorphic to the induced one. -/
theorem locallyOfFiniteType_siteMap {A V : BigFppfOver B S hS}
    (h : schemeStack.{u, w} B S hS A ⟶ schemeStack.{u, w} B S hS V)
    (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (siteMap B S hS h)) := by
  have hmap : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (schemeStackMap.{u, w} B S hS (siteMap B S hS h)) :=
    AlgebraicStacks.isLocallyOfFiniteType_of_twoIso B S hS
      (Bicategory.InducedBicategory.isoHom (schemeStackMapIso B S hS h)) hh
  refine (Space.isLocallyOfFiniteType_yoneda_map_iff B S hS (siteMap B S hS h)).1 ?_
  rw [← representingMap_schemeStackMap.{u, w} B S hS (siteMap B S hS h)]
  refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (schemeStack.{u, w} B S hS A).property (schemeStack.{u, w} B S hS V).property
    (yoneda.obj A) (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS A)
    (isAlgebraicSpace_yoneda B S hS V) (representedChart B S hS A) (representedChart B S hS V)
    (schemeStackMap.{u, w} B S hS (siteMap B S hS h)).hom).mp ?_
  exact hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS _
    (schemeStack.{u, w} B S hS A).property (schemeStack.{u, w} B S hS V).property _ hmap

end Stack

end AlgebraicGeometry

end

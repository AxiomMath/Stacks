module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology

/-!
# Generalizations in an open subspace of an algebraic space

An open subset of a topological space contains every generalization of each of its points, so
the generalizations of a point of an open subspace of an algebraic space are exactly the
generalizations of its image in the ambient space. Consequently those generalizations may be
computed inside any open subspace containing the point, and such an open subspace can always
be chosen quasi-compact, because the quasi-compact open neighbourhoods of a point are a
fundamental system.

## Main results

* `AlgebraicGeometry.Space.image_setOf_specializes_ne_of_isOpenSubspace`: the generalizations
  of a point of an open subspace other than the point itself have as image exactly the
  generalizations of its image other than that image.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_pointsMap_eq`: every point
  of an algebraic space is the image of a point of a quasi-compact open subspace.

## Implementation notes

The specialization relation is Mathlib's `Specializes`, written `x' ⤳ x`, on the space of
points of Tag 03BU with the topology of Tag 03BX; `AlgebraicGeometry.Space.pointTopology` is a
definition rather than an instance and is made a local instance here.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04NN](https://stacks.math.columbia.edu/tag/04NN)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- An open immersion of schemes is an immersion, as an inequality of morphism properties. -/
private theorem isOpenImmersion_le_isImmersion :
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ f (_ : AlgebraicGeometry.IsOpenImmersion f) ↦ inferInstance

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open immersion of algebraic spaces over `S` is an immersion. -/
theorem isImmersion_of_isOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsOpenImmersion B S hS f) : IsImmersion B S hS f :=
  MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage _ isOpenImmersion_le_isImmersion) _ hf

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The inclusion of an open subspace of an algebraic space induces an embedding on points. -/
private theorem isEmbedding_pointsMap_ι_of_isOpenSubspace (hX : IsAlgebraicSpace B S hS X)
    {V : Subfunctor X} (hV : IsOpenSubspace B S hS V) :
    Topology.IsEmbedding (pointsMap B S hS V.toFunctor V.ι) :=
  isEmbedding_pointsMap_of_isImmersion B S hS hX V.ι (isImmersion_of_isOpenImmersion B S hS hV.2)

/-- The generalizations of a point `v` of an open subspace `V` of an algebraic space `X` over
`S`, other than `v` itself, have as image in the space of points of `X` exactly the
generalizations of the image of `v` other than that image. -/
theorem image_setOf_specializes_ne_of_isOpenSubspace (hX : IsAlgebraicSpace B S hS X)
    (V : Subfunctor X) (hV : IsOpenSubspace B S hS V) (v : points B S hS V.toFunctor) :
    pointsMap B S hS V.toFunctor V.ι '' {v' | v' ⤳ v ∧ v' ≠ v} =
      {x' | x' ⤳ pointsMap B S hS V.toFunctor V.ι v ∧
        x' ≠ pointsMap B S hS V.toFunctor V.ι v} := by
  have hemb := isEmbedding_pointsMap_ι_of_isOpenSubspace B S hS hX hV
  have hopen := isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2
  ext y
  constructor
  · rintro ⟨z, ⟨hz, hzne⟩, rfl⟩
    exact ⟨hemb.isInducing.specializes_iff.mpr hz, hemb.injective.ne hzne⟩
  · rintro ⟨hy, hne⟩
    obtain ⟨z, rfl⟩ := hy.mem_open hopen (Set.mem_range_self v)
    exact ⟨z, ⟨hemb.isInducing.specializes_iff.mp hy, mt (congrArg _) hne⟩, rfl⟩

/-- Every point of an algebraic space over `S` is the image of
a point of a quasi-compact open subspace. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_pointsMap_eq (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    ∃ V : Subfunctor X, IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧
        ∃ v, pointsMap B S hS V.toFunctor V.ι v = x := by
  obtain ⟨W, ⟨hWopen, hWcompact, hxW⟩, -⟩ :=
    (hasBasis_nhds_isOpen_isCompact B S hS X hX x).mem_iff.mp Filter.univ_mem
  obtain ⟨V, hV, hrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX W hWopen
  refine ⟨V, hV, ?_, ?_⟩
  · rw [isQuasiCompactSpace_iff_compactSpace_points B S hS V.toFunctor hV.1]
    exact ⟨(isEmbedding_pointsMap_ι_of_isOpenSubspace B S hS hX hV).isCompact_iff.mpr
      (by rwa [Set.image_univ, hrange])⟩
  · exact (Set.ext_iff.mp hrange x).mpr hxW

end AlgebraicGeometry.Space

end

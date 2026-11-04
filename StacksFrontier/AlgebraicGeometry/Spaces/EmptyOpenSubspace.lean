module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition

/-!
# The open subspace with no points

The subfunctor of a presheaf on the big fppf site of `S` cut out by a set of points is the
whole presheaf when the set is everything, and the sheafification of the bottom subfunctor when
the set is empty. Consequently an open subspace of an algebraic space has no points exactly when
it is that sheafification, which is therefore the empty open subspace.

The sheafification is not removable, and the reason is the one recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ClopenPointSetDecomposition.lean`: an object of the site
whose underlying scheme has no points carries a section of every subfunctor cut out by a set of
points, so the bottom subfunctor itself is too small to be an open subspace. What the statements
below say is that those objects are the only ones carrying a section.

## Main results

* `AlgebraicGeometry.Space.openSubspaceOfPoints_univ` and
  `AlgebraicGeometry.Space.openSubspaceOfPoints_empty`: the two extreme values of the
  subfunctor cut out by a set of points.
* `AlgebraicGeometry.Space.range_pointsMap_ι_sheafify_bot`: the sheafified bottom subfunctor has
  no points.
* `AlgebraicGeometry.Space.isOpenSubspace_sheafify_bot`: it is an open subspace of an algebraic
  space.
* `AlgebraicGeometry.Space.eq_sheafify_bot_of_range_pointsMap_ι_eq_empty` and
  `AlgebraicGeometry.Space.range_pointsMap_ι_eq_empty_iff_eq_sheafify_bot`: an open subspace of
  an algebraic space has no points if and only if it is the sheafified bottom subfunctor.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The subfunctor cut out by the whole space of points is the whole presheaf: the condition on
a section is that its points lie in the set, which is vacuous. -/
theorem openSubspaceOfPoints_univ :
    openSubspaceOfPoints B S hS F Set.univ = ⊤ := by
  ext A x
  simp [mem_openSubspaceOfPoints_iff]

/-- The subfunctor cut out by the empty set of points is the sheafification of the bottom
subfunctor: it is the meet of the pieces cut out by the empty set and by its complement, and
that meet is computed in
`AlgebraicGeometry.Space.inf_openSubspaceOfPoints_eq_sheafify_bot`. -/
theorem openSubspaceOfPoints_empty :
    openSubspaceOfPoints B S hS F (∅ : Set (points B S hS F)) =
      (⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS) := by
  have h := inf_openSubspaceOfPoints_eq_sheafify_bot B S hS (F := F)
    (∅ : Set (points B S hS F))
  rwa [Set.compl_empty, openSubspaceOfPoints_univ, top_inf_eq] at h

/-- The sheafified bottom subfunctor has no points. -/
theorem range_pointsMap_ι_sheafify_bot :
    Set.range (pointsMap B S hS
        (((⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS))).toFunctor
      ((⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)).ι) = ∅ := by
  rw [← openSubspaceOfPoints_empty B S hS F]
  exact range_pointsMap_ι_openSubspaceOfPoints B S hS (F := F)
    (∅ : Set (points B S hS F))

/-- The space of points of the sheafified bottom subfunctor is empty. -/
theorem isEmpty_points_sheafify_bot :
    IsEmpty (points B S hS
      ((⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)).toFunctor) := by
  exact Set.range_eq_empty_iff.1 (range_pointsMap_ι_sheafify_bot B S hS F)

/-- The sheafified bottom subfunctor is an open subspace of an algebraic space: it is the
subspace cut out by the empty set of points, which is open. -/
theorem isOpenSubspace_sheafify_bot (hF : IsAlgebraicSpace B S hS F) :
    IsOpenSubspace B S hS ((⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS)) := by
  rw [← openSubspaceOfPoints_empty B S hS F]
  exact isOpenSubspace_openSubspaceOfPoints B S hS hF (∅ : Set (points B S hS F)) isOpen_empty

/-- An open subspace of an algebraic space with no points is the sheafified bottom subfunctor:
an open subspace is determined by its set of points, by Stacks 03BZ. -/
theorem eq_sheafify_bot_of_range_pointsMap_ι_eq_empty (hF : IsAlgebraicSpace B S hS F)
    {G : Subfunctor F} (hG : IsOpenSubspace B S hS G)
    (hGpt : Set.range (pointsMap B S hS G.toFunctor G.ι) = ∅) :
    G = (⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS) :=
  le_antisymm
    (le_of_range_pointsMap_ι_subset B S hS (isOpenSubspace_sheafify_bot B S hS F hF)
      (hGpt.subset.trans (Set.empty_subset _)))
    (le_of_range_pointsMap_ι_subset B S hS hG
      ((range_pointsMap_ι_sheafify_bot B S hS F).subset.trans (Set.empty_subset _)))

/-- An open subspace of an algebraic space has no points exactly when it is the sheafified
bottom subfunctor. -/
theorem range_pointsMap_ι_eq_empty_iff_eq_sheafify_bot (hF : IsAlgebraicSpace B S hS F)
    {G : Subfunctor F} (hG : IsOpenSubspace B S hS G) :
    Set.range (pointsMap B S hS G.toFunctor G.ι) = ∅ ↔
      G = (⊥ : Subfunctor F).sheafify (BigFppfOver.topology B S hS) :=
  ⟨eq_sheafify_bot_of_range_pointsMap_ι_eq_empty B S hS F hF hG,
    fun h => by rw [h]; exact range_pointsMap_ι_sheafify_bot B S hS F⟩

end AlgebraicGeometry.Space

end

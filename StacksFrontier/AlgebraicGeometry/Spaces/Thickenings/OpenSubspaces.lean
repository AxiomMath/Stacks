module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite

/-!
# Open subspaces of a thickening of algebraic spaces

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, that is a closed subspace
whose inclusion is surjective on points. Every open subspace `U ⊂ G` is the inverse image of a
unique open subspace `U' ⊂ X`, that is `U = G ×_X U'`. This is Stacks 05ZP; in the notation of
the source `G` is `X` and `X` is `X'`.

## Main results

* `AlgebraicGeometry.Space.isHomeomorph_pointsMap_ι_of_isThickening`: the inclusion of a
  thickening is a homeomorphism on the point spaces of Stacks 03BU.
* `AlgebraicGeometry.Space.existsUnique_isOpenSubspace_preimage_eq_of_isThickening`:
  **Stacks 05ZP**, an open subspace of the thin side of a thickening is the inverse image of a
  unique open subspace of the ambient space.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isPullback_ι_of_isThickening`: the same
  statement with the inverse image replaced by a cartesian square, which is the form `U = G ×_X
  U'` the source writes.

## Implementation notes

The cartesian condition `U = G ×_X U'` is recorded as the equality of subfunctors
`U'.preimage G.ι = U`, Mathlib's `CategoryTheory.Subfunctor.preimage`. That the inverse-image
subfunctor *is* the fibre product is Stacks 083Q,
`CategoryTheory.Subfunctor.isPullback_preimage`, and
`AlgebraicGeometry.Space.exists_isOpenSubspace_isPullback_ι_of_isThickening` spells the square
out. Phrasing the condition as an equality of subfunctors rather than as "some cartesian
square" is what makes the uniqueness clause of the source a plain `ExistsUnique`.

**Departure from the source's proof route.** The source takes `U'` to be the object of the
spaces-étale site of `X` corresponding to `U → G` under the fundamental equivalence
(76.9.1.1) of the two spaces-étale sites, which is the topological invariance of the
spaces-étale site, Stacks 05ZH, and then observes that `U' → X` is étale and universally
injective, hence an open immersion by Stacks 05W5. That route is **not open here**: Stacks 05ZH
at an arbitrary thickening is available in this library
(`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening`), but it is proved
*from this theorem* — `AlgebraicGeometry.Space.existsUnique_section_of_isThickening` extends a
section by transporting the open image of a section across the thickening with the theorem
below — so taking it as an input would be circular. Moreover the form of
Stacks 05W5 in this library,
`AlgebraicGeometry.Space.isIso_of_isEtale_of_universallyInjective_of_isSurjective`, concludes
that an étale universally injective *surjective* morphism is an isomorphism rather than that an
étale universally injective morphism is an open immersion.

The route taken here is the restriction of the source's equivalence to the open immersions,
where it is the topological statement and needs nothing from Stacks 05ZH. Open subspaces of an
algebraic space correspond to open subsets of its point space by Stacks 03BZ, part (1)
(`AlgebraicGeometry.Space.openSubspaceOfPoints` and
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`), the inclusion of a thickening is a
homeomorphism on point spaces — it is a closed immersion, hence an embedding on points by
Stacks 0ABJ, and surjective by definition — and taking inverse images of subspaces matches
taking preimages of point sets on the nose for the subspaces cut out by a set of points
(`AlgebraicGeometry.Space.preimage_openSubspaceOfPoints`). So `U'` is the open subspace cut out
by the image of the point set of `U`, and uniqueness is injectivity of the point-set
correspondence on `X` together with surjectivity of the map on points.

## References

* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Inverse images of the subspaces cut out by a set of points -/

/-- The inverse image of the subfunctor cut out by a set of points is the subfunctor cut out by
the preimage of that set: a section of the source lands in the inverse image exactly when all
of its points are carried into the set. -/
alias preimage_openSubspaceOfPoints := preimage_openSubspaceOfPoints'

/-! ### Open subspaces of a thickening -/

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- The inclusion of a thickening of an algebraic space over `S` is a homeomorphism on the
point spaces of Stacks 03BU: it is a closed immersion, hence an immersion, hence an embedding
on points by Stacks 0ABJ, and it is surjective on points by the definition of a thickening. -/
theorem isHomeomorph_pointsMap_ι_of_isThickening (hG : IsThickening B S hS X G) :
    IsHomeomorph (pointsMap B S hS G.toFunctor G.ι) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_pointsMap_of_isImmersion B S hS X.2 G.ι
      (isImmersion_of_isClosedImmersion B S hS hG.1.2), hG.2⟩

/-- **Stacks 05ZP.** Let `G ⊂ X` be a thickening of algebraic spaces over `S`. Every open
subspace `U ⊂ G` is the inverse image of a unique open subspace `U' ⊂ X`, in other words
`U = G ×_X U'`; the inverse image is `CategoryTheory.Subfunctor.preimage`, identified with the
fibre product by Stacks 083Q.

In the notation of the source, `G` is `X` and `X` is `X'`.

The open subspace is the one cut out by the image of the point set of `U` under the inclusion
of the thickening, which is a homeomorphism on point spaces. -/
@[stacks 05ZP]
theorem existsUnique_isOpenSubspace_preimage_eq_of_isThickening
    (hG : IsThickening B S hS X G) (U : Subfunctor G.toFunctor)
    (hU : IsOpenSubspace B S hS U) :
    ∃! U' : Subfunctor X.1, IsOpenSubspace B S hS U' ∧ U'.preimage G.ι = U := by
  have hhom := isHomeomorph_pointsMap_ι_of_isThickening B S hS hG
  have hWopen : IsOpen (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2
  have hUeq : U = openSubspaceOfPoints B S hS G.toFunctor
      (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    eq_openSubspaceOfPoints_range_pointsMap B S hS hG.1.1 U hU
  refine ⟨openSubspaceOfPoints B S hS X.1 (pointsMap B S hS G.toFunctor G.ι ''
      Set.range (pointsMap B S hS U.toFunctor U.ι)),
    ⟨isOpenSubspace_openSubspaceOfPoints B S hS X.2 _ (hhom.isOpenMap _ hWopen), ?_⟩, ?_⟩
  · rw [preimage_openSubspaceOfPoints, Set.preimage_image_eq _ hhom.injective]
    exact hUeq.symm
  · rintro V ⟨hV, hVU⟩
    have hVeq : V = openSubspaceOfPoints B S hS X.1
        (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
      eq_openSubspaceOfPoints_range_pointsMap B S hS X.2 V hV
    have hpre : openSubspaceOfPoints B S hS G.toFunctor
        (pointsMap B S hS G.toFunctor G.ι ⁻¹'
          Set.range (pointsMap B S hS V.toFunctor V.ι)) = U := by
      rw [← preimage_openSubspaceOfPoints, ← hVeq]
      exact hVU
    have hkey : pointsMap B S hS G.toFunctor G.ι ⁻¹'
        Set.range (pointsMap B S hS V.toFunctor V.ι) =
        Set.range (pointsMap B S hS U.toFunctor U.ι) := by
      have h := congrArg (fun Z : Subfunctor G.toFunctor ↦
        Set.range (pointsMap B S hS Z.toFunctor Z.ι)) (hpre.trans hUeq)
      rwa [range_pointsMap_ι_openSubspaceOfPoints,
        range_pointsMap_ι_openSubspaceOfPoints] at h
    rw [hVeq, ← hkey, Set.image_preimage_eq _ hhom.surjective]

/-- **Stacks 05ZP**, with the cartesian square of the source written out. Let `G ⊂ X` be a
thickening of algebraic spaces over `S`. Every open subspace `U ⊂ G` fits into a cartesian
square over the inclusion of the thickening whose opposite edge is the inclusion of an open
subspace `U' ⊂ X`, that is `U = G ×_X U'`.

This is
`AlgebraicGeometry.Space.existsUnique_isOpenSubspace_preimage_eq_of_isThickening` combined with
the identification of the inverse-image subfunctor with the fibre product, Stacks 083Q. The
uniqueness clause is carried by that theorem, in which the cartesian condition is an equality
of subfunctors. -/
theorem exists_isOpenSubspace_isPullback_ι_of_isThickening
    (hG : IsThickening B S hS X G) (U : Subfunctor G.toFunctor)
    (hU : IsOpenSubspace B S hS U) :
    ∃ U' : Subfunctor X.1, IsOpenSubspace B S hS U' ∧
      ∃ a : U.toFunctor ⟶ U'.toFunctor, IsPullback a U.ι U'.ι G.ι := by
  obtain ⟨U', ⟨hU', hUeq⟩, -⟩ :=
    existsUnique_isOpenSubspace_preimage_eq_of_isThickening B S hS hG U hU
  subst hUeq
  exact ⟨U', hU', U'.fromPreimage G.ι, Subfunctor.isPullback_preimage G.ι U'⟩

end AlgebraicGeometry.Space

end

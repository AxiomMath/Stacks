module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryEtaleNeighborhoodSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces

/-!
# The single-point case of the base change of modifications at closed points

Let `X` be a decent algebraic space over a scheme `S`, let `x₁, …, xₙ ∈ |X|` be pairwise
distinct closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the chosen elementary étale
neighborhoods. The functor `F` of Stacks 0BHA restricts a modification of `X` away from
`{x₁, …, xₙ}` to the family of its base changes to the `Uᵢ`, and Stacks 0BHB asserts that `F`
is an equivalence.

The reduction of the essential surjectivity of `F` to the case `n = 1` is
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.essSurj_restrictionFunctor`. The case `n = 1`
is the base change of Stacks 0BGY along the single morphism `Uᵢ ⟶ X`, taken at the closed
subspace `{xᵢ}`. This file identifies the two sides of that base change with the categories the
reduction speaks about, so that the essential surjectivity of the base-change functor of
Stacks 0BGY, once available at each `(Uᵢ ⟶ X, {xᵢ})`, is exactly what the reduction consumes.

Two identifications are needed. The subspace of `Uᵢ` over which a restricted modification is
unchanged is the inverse image of `X ∖ {xᵢ}`, and that inverse image is `Uᵢ ∖ {uᵢ}`: the only
point of `Uᵢ` above `xᵢ` is `uᵢ`, which is the shrinking condition of Stacks 0BH9 together with
the defining property of an elementary étale neighborhood. And the decomposition
`Uᵢ ×_X Uᵢ = Δ(Uᵢ) ⊔ Rᵢ` of Stacks 0BGY is available at `Uᵢ ⟶ X` because that morphism is
separated, the scheme of the neighborhood being affine.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.preimage_openAwayFromSinglePoint`: the
  inverse image in `Uᵢ` of the open subspace `X ∖ {xᵢ}` is `Uᵢ ∖ {uᵢ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.essSurj_restrictionFunctor_of_exists`: the
  functor of Stacks 0BHA is essentially surjective as soon as every algebraic space over `Uᵢ`
  unchanged over `Uᵢ ∖ {uᵢ}` is the base change of an algebraic space over `X` unchanged over
  `X ∖ {xᵢ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.essSurj_restrictionFunctor_of_essSurj`: the
  functor of Stacks 0BHA is essentially surjective as soon as the base-change functor of
  Stacks 0BGY along each `Uᵢ ⟶ X`, taken outside `X ∖ {xᵢ}`, is.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_diagonalComplement_toSpaceHom`: the
  fibre square `Uᵢ ×_X Uᵢ` is the disjoint union of the image of its diagonal and a
  complementary open-and-closed subspace.

## Implementation notes

`AlgebraicGeometry.Space.ClosedPointNeighborhoods.preimage_openAwayFromSinglePoint` is an
equality of subfunctors rather than an inclusion, and so lets the two categories of
modifications over `Uᵢ` be identified by rewriting a `Prop` — the categories themselves are
full subcategories of one slice category, cut out by the two spellings of one subfunctor. The
weaker inclusion `AlgebraicGeometry.Space.ClosedPointNeighborhoods.openAwayFromPoint_le_preimage`
already in the development is not enough for that, since it only gives a functor in one
direction.

The equality is checked on points, where it is the statement that the fibre of `|Uᵢ| → |X|`
over `xᵢ` is `{uᵢ}`: the inverse image of a subspace cut out by a set of points is the subspace
cut out by the preimage of that set, which is
`AlgebraicGeometry.Space.preimage_openSubspaceOfPoints`. One inclusion is the field
`ElementaryEtaleNeighborhood.map_point`, the other the field
`ClosedPointNeighborhoods.eq_of_map_eq_point`.

`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_diagonalComplement_toSpaceHom` is the
instantiation at `Uᵢ ⟶ X` of `AlgebraicGeometry.Space.exists_diagonalComplement_decomposition`.
It is the only place in this development where separatedness of `Uᵢ ⟶ X` is used; the
comparison of properties under the base change of Stacks 0BGY does not need it, and records as
much. Separatedness comes from
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isSeparated_toSpaceHom`, that is from
affineness of the scheme of the neighborhood, and étaleness from the field
`ElementaryEtaleNeighborhood.etale_toSpace`.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace ClosedPointNeighborhoods

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {n : ℕ}
  (D : ClosedPointNeighborhoods B S hS n)

set_option synthInstance.maxHeartbeats 400000 in
-- synthesizing `HasPullbacks` for presheaves on the big fppf site exceeds the default limit
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ModificationsAtClosedPointsSinglePoint :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Limits of cospans of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_ModificationsAtClosedPointsSinglePoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The fibre of a neighborhood over its chosen point -/

/-- A point of the `i`th neighborhood lies above the chosen point `xᵢ` exactly when it is the
distinguished point `uᵢ`. -/
theorem pointsMap_toSpaceHom_eq_point_iff (i : Fin n)
    (y : points B S hS (D.neighborhoodSpace i).obj) :
    pointsMap B S hS (D.neighborhoodSpace i).obj (D.toSpaceHom i).hom y = D.point i ↔
      y = D.neighborhoodPoint i :=
  ⟨fun hy ↦ D.eq_of_map_eq_point i y hy, fun hy ↦ hy ▸ (D.neighborhood i).map_point⟩

/-- **The inverse image of `X ∖ {xᵢ}` in the `i`th neighborhood is `Uᵢ ∖ {uᵢ}`.** The fibre of
`|Uᵢ| → |X|` over `xᵢ` is the single point `uᵢ`. -/
theorem preimage_openAwayFromSinglePoint (i : Fin n) :
    (D.openAwayFromSinglePoint i).preimage (D.toSpaceHom i).hom = D.openAwayFromPoint i := by
  rw [openAwayFromSinglePoint, preimage_openSubspaceOfPoints, openAwayFromPoint]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact not_congr (D.pointsMap_toSpaceHom_eq_point_iff i y)

/-! ### Essential surjectivity from the single-point case -/

/-- **The single-point case of Stacks 0BHB implies the general case.** If every algebraic space
over `Uᵢ` which is unchanged over `Uᵢ ∖ {uᵢ}` is the base change of an algebraic space over `X`
which is unchanged over `X ∖ {xᵢ}`, then the functor `F` of Stacks 0BHA is essentially
surjective. -/
theorem essSurj_restrictionFunctor_of_exists
    (hsingle : ∀ (i : Fin n) (N : Over (D.neighborhoodSpace i).obj),
      IsModification B S hS (D.openAwayFromPoint i) N →
        ∃ M : Over D.space.obj, IsModification B S hS (D.openAwayFromSinglePoint i) M ∧
          Nonempty ((Over.pullback (D.toSpaceHom i).hom).obj M ≅ N)) :
    D.restrictionFunctor.EssSurj :=
  D.essSurj_restrictionFunctor fun i N ↦ by
    obtain ⟨M, hM, he⟩ := hsingle i N.obj N.property
    exact ⟨⟨M, hM⟩, he⟩

/-- **Stacks 0BHB**, the essential surjectivity of `F`, granted the case `n = 1`. If the
base-change functor of Stacks 0BGY along `Uᵢ ⟶ X`, taken outside `X ∖ {xᵢ}`, is essentially
surjective for every `i`, then the functor `F` of Stacks 0BHA is essentially surjective. -/
@[stacks 0BHB "essential surjectivity of the functor, granted the case n = 1 of Stacks 0BGY"]
theorem essSurj_restrictionFunctor_of_essSurj
    (hES : ∀ i : Fin n,
      (baseChangeFunctor B S hS (D.toSpaceHom i) (D.openAwayFromSinglePoint i)).1.EssSurj) :
    D.restrictionFunctor.EssSurj := by
  refine D.essSurj_restrictionFunctor_of_exists fun i N hN ↦ ?_
  have hpre : IsModification B S hS
      ((D.openAwayFromSinglePoint i).preimage (D.toSpaceHom i).hom) N := by
    rw [D.preimage_openAwayFromSinglePoint i]
    exact hN
  obtain ⟨M, he⟩ := (hES i).mem_essImage
    (⟨N, hpre⟩ : Modification B S hS
      ((D.openAwayFromSinglePoint i).preimage (D.toSpaceHom i).hom))
  exact ⟨M.obj, M.property, ⟨(ObjectProperty.ι (IsModification B S hS
    ((D.openAwayFromSinglePoint i).preimage (D.toSpaceHom i).hom))).mapIso he.some⟩⟩

/-! ### The complement of the diagonal of a neighborhood -/

/-- **The decomposition `Uᵢ ×_X Uᵢ = Δ(Uᵢ) ⊔ Rᵢ` of Stacks 0BGY at a chosen neighborhood.** The
fibre square of `Uᵢ ⟶ X` carries two subfunctors, each an open and a closed subspace, whose
join sheafifies to the whole of it and whose meet is the sheafification of the bottom
subfunctor; the point set of the second is the image of the relative diagonal and that of the
first is its complement. The morphism `Uᵢ ⟶ X` is étale and, the scheme of the neighborhood
being affine, separated. -/
theorem exists_diagonalComplement_toSpaceHom (i : Fin n) :
    ∃ C E : Subfunctor (pullback (D.toSpaceHom i).hom (D.toSpaceHom i).hom),
      IsOpenSubspace B S hS C ∧ IsClosedSubspace B S hS C ∧
      IsOpenSubspace B S hS E ∧ IsClosedSubspace B S hS E ∧
      (C ⊔ E).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      C ⊓ E = (⊥ : Subfunctor
        (pullback (D.toSpaceHom i).hom (D.toSpaceHom i).hom)).sheafify
          (BigFppfOver.topology B S hS) ∧
      Set.range (pointsMap B S hS E.toFunctor E.ι) =
        Set.range (pointsMap B S hS (D.neighborhoodSpace i).obj
          (pullback.diagonal (D.toSpaceHom i).hom)) ∧
      Set.range (pointsMap B S hS C.toFunctor C.ι) =
        (Set.range (pointsMap B S hS (D.neighborhoodSpace i).obj
          (pullback.diagonal (D.toSpaceHom i).hom)))ᶜ :=
  exists_diagonalComplement_decomposition B S hS (D.neighborhoodSpace i).property
    D.space.property (D.toSpaceHom i).hom (D.neighborhood i).etale_toSpace
    (D.isSeparated_toSpaceHom i)

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end

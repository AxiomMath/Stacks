module

public import Mathlib.CategoryTheory.Pi.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Modifications of an algebraic space at finitely many closed points

Let `X` be a decent algebraic space over a scheme `S` and let `x₁, …, xₙ ∈ |X|` be pairwise
distinct closed points. For each `i` choose an elementary étale neighborhood `(Uᵢ, uᵢ) → (X, xᵢ)`
with `Uᵢ` affine, with `uᵢ` the only point of `Uᵢ` above `xᵢ`, and — after shrinking `Uᵢ` — with
no point of `Uᵢ` above `x_j` for `j ≠ i`. Then `uᵢ` is a closed point of `Uᵢ`.

Write `C_{X, {x₁, …, xₙ}}` for the category of morphisms of algebraic spaces `f : Y ⟶ X`
inducing an isomorphism `f⁻¹(X ∖ {x₁, …, xₙ}) ⟶ X ∖ {x₁, …, xₙ}`, and `C_{Uᵢ, uᵢ}` for the
category of morphisms `gᵢ : Yᵢ ⟶ Uᵢ` inducing an isomorphism `gᵢ⁻¹(Uᵢ ∖ {uᵢ}) ⟶ Uᵢ ∖ {uᵢ}`.
Base change along the neighborhoods defines a functor

`F : C_{X, {x₁, …, xₙ}} ⟶ C_{U₁, u₁} × … × C_{Uₙ, uₙ}`

which is **Stacks 0BHA**.

## Main definitions

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods` is the chosen data: the points and the
  neighborhoods, with the conditions listed above.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.openAwayFromPoints` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.openAwayFromPoint` are the open subspaces
  `X ∖ {x₁, …, xₙ}` and `Uᵢ ∖ {uᵢ}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.modificationsAwayFromPoints` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.modificationsAt` are the two families of
  categories, and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.restrictionFunctor` is the functor `F`.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isClosed_neighborhoodPoint`: the
  distinguished point of a neighborhood is closed, because it is the whole preimage of the
  chosen point.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.restrictionFunctorCompιIso`: each
  component of `F` is base change along the corresponding neighborhood.

## Implementation notes

An object of `C_{X, {x₁, …, xₙ}}` is an algebraic space over `X` whose base change to the open
subspace `X ∖ {x₁, …, xₙ}` is an isomorphism, which is `AlgebraicGeometry.Space.IsModification`
for that subspace; likewise for `C_{Uᵢ, uᵢ}`. The two open subspaces are cut out by their point
sets through `AlgebraicGeometry.Space.openSubspaceOfPoints`, which is an open subspace exactly
because the removed sets are closed.

The component of `F` at `i` is the base-change functor of Stacks 0BGY along `Uᵢ ⟶ X`, which
lands in the modifications away from the *preimage* of `X ∖ {x₁, …, xₙ}`. That preimage contains
`Uᵢ ∖ {uᵢ}`: a point of `Uᵢ` other than `uᵢ` lies above no chosen point, by uniqueness of `uᵢ`
above `xᵢ` and by the shrinking condition, so `Uᵢ ∖ {uᵢ} ⟶ X` factors through `X ∖ {x₁, …, xₙ}`
by Stacks 03IE. An isomorphism after base change along the preimage is therefore still one after
base change along `Uᵢ ∖ {uᵢ}`, and the component is the lift of base change through the smaller
full subcategory. The functor into the product is assembled with `CategoryTheory.Functor.pi'`,
whose composition with each projection is the corresponding component definitionally.

Decency of `X`, affineness of the neighborhoods and distinctness of the chosen points are
recorded because the source fixes them, but the construction of `F` uses none of them: what it
consumes is closedness of the chosen points, uniqueness of `uᵢ` above `xᵢ`, and the shrinking
condition.

## References

* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- A morphism whose base change along `g₁` is an isomorphism has the same property along any
morphism `g₂` factoring through `g₁`, since the base change along `g₂` is then a base change of
the base change along `g₁`. -/
public theorem isIso_pullback_snd_of_factor {C : Type*} [Category C] [HasPullbacks C]
    {X Z Y₁ Y₂ : C} (f : X ⟶ Z) {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z} (k : Y₂ ⟶ Y₁)
    (hk : k ≫ g₁ = g₂) (h : IsIso (pullback.snd f g₁)) : IsIso (pullback.snd f g₂) := by
  have hw : pullback.fst f g₂ ≫ f = (pullback.snd f g₂ ≫ k) ≫ g₁ := by
    rw [Category.assoc, hk, pullback.condition]
  have hfst : pullback.lift _ _ hw ≫ pullback.fst f g₁ = pullback.fst f g₂ :=
    pullback.lift_fst _ _ hw
  have hsnd : pullback.lift _ _ hw ≫ pullback.snd f g₁ = pullback.snd f g₂ ≫ k :=
    pullback.lift_snd _ _ hw
  have hs : IsPullback (pullback.lift _ _ hw ≫ pullback.fst f g₁) (pullback.snd f g₂)
      f (k ≫ g₁) := by
    rw [hfst, hk]
    exact IsPullback.of_hasPullback f g₂
  exact (hs.of_right hsnd (IsPullback.of_hasPullback f g₁)).isIso_snd_of_isIso h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The data fixed in the strategy for resolving an algebraic space at finitely many closed
points: a decent algebraic space, pairwise distinct closed points `x₁, …, xₙ`, and for each one
an affine elementary étale neighborhood carrying a single point above it and no point above any
of the others. -/
structure ClosedPointNeighborhoods (n : ℕ) where
  /-- The algebraic space over the base. -/
  space : AlgebraicSpaces B S hS
  /-- The space is decent. -/
  decent : IsDecentSpace B S hS space.obj
  /-- The chosen points of the space. -/
  point : Fin n → points B S hS space.obj
  /-- The chosen points are pairwise distinct. -/
  point_injective : Function.Injective point
  /-- Each chosen point is a closed point. -/
  isClosed_point : ∀ i, IsClosed ({point i} : Set (points B S hS space.obj))
  /-- The elementary étale neighborhood chosen at each point. -/
  neighborhood : ∀ i, ElementaryEtaleNeighborhood B S hS space.obj space.property (point i)
  /-- Each chosen neighborhood is an affine scheme. -/
  isAffine_neighborhood : ∀ i, IsAffine (neighborhood i).scheme.left.1
  /-- The distinguished point is the only point of the `i`th neighborhood above `xᵢ`. -/
  eq_of_map_eq_point : ∀ i (y : points B S hS (yoneda.obj (neighborhood i).scheme)),
    pointsMap B S hS (yoneda.obj (neighborhood i).scheme) (neighborhood i).toSpace y =
        point i →
      y = presheafPoint B S hS (neighborhood i).scheme (neighborhood i).point
        (neighborhood i).residueField_contained
  /-- After shrinking, no point of the `i`th neighborhood lies above `x_j` for `j ≠ i`. -/
  map_ne_point : ∀ i j, i ≠ j →
    ∀ y : points B S hS (yoneda.obj (neighborhood i).scheme),
      pointsMap B S hS (yoneda.obj (neighborhood i).scheme) (neighborhood i).toSpace y ≠
        point j

namespace ClosedPointNeighborhoods

variable {B S hS} {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The `i`th chosen neighborhood, viewed as an algebraic space over the base. -/
def neighborhoodSpace (i : Fin n) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (D.neighborhood i).scheme,
    isAlgebraicSpace_yoneda B S hS (D.neighborhood i).scheme⟩

/-- The étale morphism `Uᵢ ⟶ X` from the `i`th chosen neighborhood, as a morphism of algebraic
spaces over the base. -/
def toSpaceHom (i : Fin n) : D.neighborhoodSpace i ⟶ D.space :=
  ObjectProperty.homMk (D.neighborhood i).toSpace

/-- The distinguished point `uᵢ` of the `i`th chosen neighborhood, as a point of the algebraic
space that neighborhood represents. -/
def neighborhoodPoint (i : Fin n) : points B S hS (D.neighborhoodSpace i).obj :=
  presheafPoint B S hS (D.neighborhood i).scheme (D.neighborhood i).point
    (D.neighborhood i).residueField_contained

/-- The open subspace `X ∖ {x₁, …, xₙ}` of the space, cut out by the complement of the chosen
points. -/
def openAwayFromPoints : Subfunctor D.space.obj :=
  openSubspaceOfPoints B S hS D.space.obj (Set.range D.point)ᶜ

/-- The open subspace `Uᵢ ∖ {uᵢ}` of the `i`th chosen neighborhood. -/
def openAwayFromPoint (i : Fin n) : Subfunctor (D.neighborhoodSpace i).obj :=
  openSubspaceOfPoints B S hS (D.neighborhoodSpace i).obj {D.neighborhoodPoint i}ᶜ

/-- The point set of `X ∖ {x₁, …, xₙ}` is the complement of the chosen points. -/
theorem range_pointsMap_ι_openAwayFromPoints :
    Set.range (pointsMap B S hS D.openAwayFromPoints.toFunctor D.openAwayFromPoints.ι) =
      (Set.range D.point)ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The point set of `Uᵢ ∖ {uᵢ}` is the complement of the distinguished point. -/
theorem range_pointsMap_ι_openAwayFromPoint (i : Fin n) :
    Set.range (pointsMap B S hS (D.openAwayFromPoint i).toFunctor
        (D.openAwayFromPoint i).ι) = {D.neighborhoodPoint i}ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The chosen points form a closed subset of the space of points. -/
theorem isClosed_range_point : IsClosed (Set.range D.point) := by
  simpa only [Set.iUnion_singleton_eq_range] using
    isClosed_iUnion_of_finite fun i ↦ D.isClosed_point i

/-- The distinguished point `uᵢ` is a closed point of the `i`th neighborhood: it is the whole
preimage of the closed point `xᵢ` under the étale morphism to the space. -/
theorem isClosed_neighborhoodPoint (i : Fin n) :
    IsClosed ({D.neighborhoodPoint i} :
      Set (points B S hS (D.neighborhoodSpace i).obj)) := by
  have hpre : ({D.neighborhoodPoint i} :
        Set (points B S hS (D.neighborhoodSpace i).obj)) =
      pointsMap B S hS (D.neighborhoodSpace i).obj (D.toSpaceHom i).hom ⁻¹'
        {D.point i} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h ↦ h ▸ (D.neighborhood i).map_point,
      fun h ↦ D.eq_of_map_eq_point i y h⟩
  rw [hpre]
  exact (D.isClosed_point i).preimage (continuous_pointsMap B S hS _)

/-- `X ∖ {x₁, …, xₙ}` is an open subspace of the space. -/
theorem isOpenSubspace_openAwayFromPoints :
    IsOpenSubspace B S hS D.openAwayFromPoints :=
  isOpenSubspace_openSubspaceOfPoints B S hS D.space.property _
    D.isClosed_range_point.isOpen_compl

/-- `Uᵢ ∖ {uᵢ}` is an open subspace of the `i`th neighborhood. -/
theorem isOpenSubspace_openAwayFromPoint (i : Fin n) :
    IsOpenSubspace B S hS (D.openAwayFromPoint i) :=
  isOpenSubspace_openSubspaceOfPoints B S hS (D.neighborhoodSpace i).property _
    (D.isClosed_neighborhoodPoint i).isOpen_compl

/-- A point of the `i`th neighborhood other than its distinguished point lies above none of the
chosen points. -/
theorem map_notMem_range_point (i : Fin n) (y : points B S hS (D.neighborhoodSpace i).obj)
    (hy : y ≠ D.neighborhoodPoint i) :
    pointsMap B S hS (D.neighborhoodSpace i).obj (D.toSpaceHom i).hom y ∉
      Set.range D.point := by
  rintro ⟨j, hj⟩
  rcases eq_or_ne j i with rfl | hji
  · exact hy (D.eq_of_map_eq_point j y hj.symm)
  · exact D.map_ne_point i j (Ne.symm hji) y hj.symm

/-- `Uᵢ ∖ {uᵢ}` is contained in the preimage of `X ∖ {x₁, …, xₙ}`, because a point of `Uᵢ` other
than `uᵢ` lies above no chosen point. -/
theorem openAwayFromPoint_le_preimage (i : Fin n) :
    D.openAwayFromPoint i ≤ D.openAwayFromPoints.preimage (D.toSpaceHom i).hom := by
  have hsubset :
      Set.range (pointsMap B S hS (D.openAwayFromPoint i).toFunctor
          ((D.openAwayFromPoint i).ι ≫ (D.toSpaceHom i).hom)) ⊆
        Set.range (pointsMap B S hS D.openAwayFromPoints.toFunctor
          D.openAwayFromPoints.ι) := by
    rw [D.range_pointsMap_ι_openAwayFromPoints, pointsMap_comp]
    rintro z ⟨y, rfl⟩
    refine D.map_notMem_range_point i _ ?_
    intro hcon
    have hmem : D.neighborhoodPoint i ∈
        ({D.neighborhoodPoint i} : Set (points B S hS (D.neighborhoodSpace i).obj))ᶜ := by
      rw [← D.range_pointsMap_ι_openAwayFromPoint i]
      exact ⟨y, hcon⟩
    exact hmem rfl
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS D.space.property
    (D.isOpenSubspace_openAwayFromPoint i).1 D.openAwayFromPoints
    D.isOpenSubspace_openAwayFromPoints _).2 hsubset
  rw [← Subfunctor.image_le_iff]
  calc (D.openAwayFromPoint i).image (D.toSpaceHom i).hom
      = Subfunctor.range ((D.openAwayFromPoint i).ι ≫ (D.toSpaceHom i).hom) := by
        rw [Subfunctor.range_comp, Subfunctor.range_ι]
    _ = Subfunctor.range (g ≫ D.openAwayFromPoints.ι) := by rw [hg]
    _ ≤ D.openAwayFromPoints := by
        simpa only [Subfunctor.range_ι] using
          Subfunctor.range_comp_le g D.openAwayFromPoints.ι

/-- The inclusion of `Uᵢ ∖ {uᵢ}` into the preimage of `X ∖ {x₁, …, xₙ}`. -/
def awayHom (i : Fin n) :
    (D.openAwayFromPoint i).toFunctor ⟶
      (D.openAwayFromPoints.preimage (D.toSpaceHom i).hom).toFunctor :=
  Subfunctor.lift (D.openAwayFromPoint i).ι (by
    rw [Subfunctor.range_ι]
    exact D.openAwayFromPoint_le_preimage i)

/-- `awayHom` followed by the inclusion of the preimage of `X ∖ {x₁, …, xₙ}` is the inclusion of
`Uᵢ ∖ {uᵢ}`. -/
@[simp]
theorem awayHom_ι (i : Fin n) :
    D.awayHom i ≫ (D.openAwayFromPoints.preimage (D.toSpaceHom i).hom).ι =
      (D.openAwayFromPoint i).ι :=
  Subfunctor.lift_ι _ _

/-- **Stacks 0BHA.** The category `C_{X, {x₁, …, xₙ}}` of algebraic spaces over `X` which are
unchanged over `X ∖ {x₁, …, xₙ}`. -/
@[stacks 0BHA "the source category of the functor"]
abbrev modificationsAwayFromPoints := Modification B S hS D.openAwayFromPoints

/-- **Stacks 0BHA.** The category `C_{Uᵢ, uᵢ}` of algebraic spaces over the `i`th neighborhood
which are unchanged over `Uᵢ ∖ {uᵢ}`. -/
@[stacks 0BHA "the factors of the target category of the functor"]
abbrev modificationsAt (i : Fin n) := Modification B S hS (D.openAwayFromPoint i)

/-- Base change along `Uᵢ ⟶ X`, as a functor from `C_{X, {x₁, …, xₙ}}` to `C_{Uᵢ, uᵢ}`: the base
change of a modification away from the preimage of `X ∖ {x₁, …, xₙ}` is in particular one away
from the smaller open subspace `Uᵢ ∖ {uᵢ}`. -/
def restrictionComponent (i : Fin n) :
    D.modificationsAwayFromPoints ⥤ D.modificationsAt i :=
  ObjectProperty.lift _
    ((baseChangeFunctor B S hS (D.toSpaceHom i) D.openAwayFromPoints).1 ⋙
      ObjectProperty.ι (IsModification B S hS
        (D.openAwayFromPoints.preimage (D.toSpaceHom i).hom))) (by
      intro M
      refine ⟨((baseChangeFunctor B S hS (D.toSpaceHom i)
        D.openAwayFromPoints).1.obj M).property.1, ?_⟩
      exact isIso_pullback_snd_of_factor _ (D.awayHom i) (D.awayHom_ι i)
        ((baseChangeFunctor B S hS (D.toSpaceHom i)
          D.openAwayFromPoints).1.obj M).property.2)

/-- **Stacks 0BHA.** The functor `F : C_{X, {x₁, …, xₙ}} ⟶ C_{U₁, u₁} × … × C_{Uₙ, uₙ}` given by
base change along the chosen elementary étale neighborhoods. -/
@[stacks 0BHA "the functor given by base change"]
def restrictionFunctor :
    D.modificationsAwayFromPoints ⥤ ∀ i : Fin n, D.modificationsAt i :=
  Functor.pi' D.restrictionComponent

/-- **Stacks 0BHA.** The `i`th component of `F` is base change along `Uᵢ ⟶ X`. -/
@[stacks 0BHA "base change computes the functor"]
def restrictionFunctorCompιIso (i : Fin n) :
    D.restrictionFunctor ⋙ Pi.eval _ i ⋙
        ObjectProperty.ι (IsModification B S hS (D.openAwayFromPoint i)) ≅
      ObjectProperty.ι (IsModification B S hS D.openAwayFromPoints) ⋙
        Over.pullback (D.toSpaceHom i).hom :=
  (baseChangeFunctor B S hS (D.toSpaceHom i) D.openAwayFromPoints).2

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end

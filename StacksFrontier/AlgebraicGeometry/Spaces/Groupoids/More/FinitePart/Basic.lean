module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Finite open subspaces of a base change

Fix a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`. The sections over an
algebraic space `T` of the *finite part* of `f` are the pairs consisting of a morphism
`a : T ⟶ Y` and an open subspace `Z` of the fibre product `T ×_Y X` whose projection to `T` is
finite. If moreover `f` has a section `σ`, the variant relevant to étale localization asks
that `Z` contain the induced section of `T ×_Y X` over `T`.

## Main definitions

* `AlgebraicGeometry.Space.FiniteOpenSubspace`: a pair `(a, Z)` as above.
* `AlgebraicGeometry.Space.FiniteOpenPairWithSection`: a pair `(a, Z)` whose open subspace
  contains the section induced by a section of `f`.

## Implementation notes

The ambient fibre product is the presheaf pullback, which is an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_pullback`; the open subspace is recorded as a
`CategoryTheory.Subfunctor` of it satisfying `AlgebraicGeometry.Space.IsOpenSubspace`, and its
projection to `T` is the composite of its inclusion with the first projection of the pullback.
Finiteness is `AlgebraicGeometry.Space.IsFinite`, the finite-morphism property of algebraic
spaces of Stacks 03ZP.

The condition that `Z` contain the induced section is recorded as an actual factorization of
the section through the inclusion of `Z`, rather than as a containment of images: the
factorizing morphism is unique because the inclusion is a monomorphism, so this carries no
more information and is directly usable.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04RQ](https://stacks.math.columbia.edu/tag/04RQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04PC.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` and an algebraic
space `T`, a morphism `T ⟶ Y` together with an open subspace of `T ×_Y X` which is finite
over `T`. -/
@[stacks 04PC]
structure FiniteOpenSubspace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : AlgebraicSpaces B S hS) where
  /-- The morphism from `T` to the target of `f` along which `f` is based changed. -/
  toBase : T ⟶ Y
  /-- The open subspace of the fibre product `T ×_Y X`. -/
  subspace : Subfunctor (pullback toBase.hom f.hom)
  /-- The subfunctor is an open subspace. -/
  isOpen : IsOpenSubspace B S hS subspace
  /-- The projection of the open subspace to `T` is a finite morphism. -/
  finite_projection : IsFinite B S hS (subspace.ι ≫ pullback.fst toBase.hom f.hom)

/-- **Stacks 04RQ.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` with a section
`σ`, and an algebraic space `T`, a morphism `a : T ⟶ Y` together with an open subspace `Z` of
`T ×_Y X` which is finite over `T` and contains the section of `T ×_Y X` over `T` induced
by `σ`. -/
@[stacks 04RQ]
structure FiniteOpenPairWithSection (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y T : AlgebraicSpaces B S hS) (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj) where
  /-- The morphism from `T` to the target of `f` along which `f` is base changed. -/
  a : T ⟶ Y
  /-- The open subspace of the fibre product `T ×_Y X`. -/
  Z : Subfunctor (pullback a.hom f.hom)
  /-- The subfunctor is an open subspace. -/
  isOpen : IsOpenSubspace B S hS Z
  /-- The projection of the open subspace to `T` is a finite morphism. -/
  finiteProjection : IsFinite B S hS (Z.ι ≫ pullback.fst a.hom f.hom)
  /-- The section of `T ×_Y X` over `T` induced by `σ` factors through the open subspace. -/
  containsSection : ∃ sectionLift : T.obj ⟶ Z.toFunctor,
    sectionLift ≫ Z.ι = pullback.lift (𝟙 T.obj) (a.hom ≫ σ.hom)
      (by simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id])

end AlgebraicGeometry.Space

end

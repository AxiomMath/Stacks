module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.FppfSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IsFibreSectionsSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsSheaf

/-!
# The restriction of scalars is a sheaf with representable diagonal

Let `z : Z ⟶ Q` be a finite morphism of algebraic spaces over `S` and let `x : X ⟶ Z` be étale.
This file proves the second of the three clauses of algebraicity for the restriction of scalars
`Res_{Z/Q}(X)` of Stacks 05YA, **with no separatedness hypothesis on `x`**: its diagonal is
representable by objects of the site. The first clause, that it is an fppf sheaf, holds for
arbitrary `x` and `z`; it is part (1) of Stacks 05YB,
`AlgebraicGeometry.Space.isSheaf_restrictionOfScalars`. Consequently `Res_{Z/Q}(X)` is an algebraic
space over `S` as soon as it has a surjective étale atlas by an object of the site.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_diag_restrictionOfScalars`: its diagonal is
  representable by objects of the site.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_to_restrictionOfScalars`: every
  morphism to it from an algebraic space over `S` is representable by algebraic spaces.
* `AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_exists_atlas`: it is an
  algebraic space as soon as it has a surjective étale atlas.

## References

* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04PK](https://stacks.math.columbia.edu/tag/04PK)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z} {z : Z ⟶ Q}

/-- **The diagonal of `Res_{Z/Q}(X)` is representable by objects of the site.** For `x` étale and
`z` finite, the diagonal of the restriction of scalars `Res_{Z/Q}(X)` is representable. -/
theorem relativelyRepresentable_diag_restrictionOfScalars (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) :
    yoneda.relativelyRepresentable (diag (restrictionOfScalars B S hS x z).presheaf) :=
  have := mono_restrictionOfScalarsToFinitePart hx hz
  (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (isPullback_diag_of_mono (restrictionOfScalarsToFinitePart hx hz))
    (relativelyRepresentable_diag_finiteOpenSubspacePresheaf B S hS (x ≫ z))

/-- For `x` étale and `z` finite, every morphism to `Res_{Z/Q}(X)` from an algebraic space over
`S` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_to_restrictionOfScalars (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) (a : G ⟶ (restrictionOfScalars B S hS x z).presheaf) :
    IsRepresentableByAlgebraicSpaces B S hS a :=
  isRepresentableByAlgebraicSpaces_of_diagonal B S hS
    (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable
      (relativelyRepresentable_diag_restrictionOfScalars hx hz)) hG a

/-- **Stacks 05XR, the general case, reduced to its atlas clause.** The restriction of scalars
`Res_{Z/Q}(X)` of an étale `x : X ⟶ Z` along a finite `z : Z ⟶ Q` is an algebraic space over `S`
as soon as it admits a surjective étale morphism from an object of the site. -/
theorem isAlgebraicSpace_restrictionOfScalars_of_exists_atlas (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom)
    (hatlas : ∃ (U : BigFppfOver B S hS)
      (f : yoneda.obj U ⟶ (restrictionOfScalars B S hS x z).presheaf),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f) :
    IsAlgebraicSpace B S hS (restrictionOfScalars B S hS x z).presheaf :=
  ⟨isSheaf_restrictionOfScalars x z, relativelyRepresentable_diag_restrictionOfScalars hx hz,
    hatlas⟩

end AlgebraicGeometry.Space

end

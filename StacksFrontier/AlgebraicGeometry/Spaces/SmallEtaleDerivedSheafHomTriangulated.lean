module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated

/-!
# The derived internal Hom of an algebraic space is triangulated in its dualized variable

Let `X` be an algebraic space and `M` an object of `D(𝒪_X)`. The derived internal Hom into `M`,
`R𝓗om(-, M) : D(𝒪_X)ᵒᵖ ⥤ D(𝒪_X)`, commutes with the shifts — `R𝓗om(K⟦-n⟧, M) ≅ R𝓗om(K, M)⟦n⟧`
coherently in `n`, the shift of `D(𝒪_X)ᵒᵖ` being the one of
`CategoryTheory.Pretriangulated.Opposite` — and carries distinguished triangles of `D(𝒪_X)ᵒᵖ`
to distinguished triangles (Stacks 08JC, contravariant variable).

The derived internal Hom of `X` is that of the equi-universe model of the small étale ringed
site, read through the derived equivalence with the model
(`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`). Both statements hold on the model
(`AlgebraicGeometry.RingedSite.derivedSheafHomFlipCommShift` and
`AlgebraicGeometry.RingedSite.derivedSheafHomFlipIsTriangulated`), and the two functors of the
derived equivalence are triangulated, being induced by an exact equivalence of abelian
categories.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomFlipObjIso`: `R𝓗om(-, M)` on `X` is the
  composite of the derived equivalence, `R𝓗om(-, M)` on the model and the inverse equivalence.

## Main results

* `AlgebraicGeometry.Space.commShift_smallEtaleDerivedSheafHom_flip_obj` and
  `AlgebraicGeometry.Space.isTriangulated_smallEtaleDerivedSheafHom_flip_obj`.

## References

* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] abelian_ringedToposStructureRingSheafModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **`R𝓗om(-, M)` on an algebraic space is `R𝓗om(-, M)` on the model**, read through the derived
equivalence with the model; objectwise the identity. -/
def smallEtaleDerivedSheafHomFlipObjIso
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedSheafHom B S hS X).flip.obj M ≅
      (smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategory.op ⋙
        (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).flip.obj
          ((smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategory.obj M) ⋙
        (smallEtaleModelModulesEquivalence B S hS X).inverse.mapDerivedCategory :=
  Iso.refl _

/-- **`R𝓗om(-, M)` on an algebraic space commutes with the shifts of its dualized variable.** -/
noncomputable instance commShift_smallEtaleDerivedSheafHom_flip_obj
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedSheafHom B S hS X).flip.obj M).CommShift ℤ :=
  Functor.CommShift.ofIso (smallEtaleDerivedSheafHomFlipObjIso B S hS X M).symm ℤ

/-- **Stacks 08JC on an algebraic space, contravariant variable**: `R𝓗om(-, M)` is a
triangulated functor of its dualized variable. -/
instance isTriangulated_smallEtaleDerivedSheafHom_flip_obj
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedSheafHom B S hS X).flip.obj M).IsTriangulated := by
  have :=
    Functor.CommShift.ofIso_compatibility (smallEtaleDerivedSheafHomFlipObjIso B S hS X M).symm ℤ
  exact Functor.isTriangulated_of_iso (smallEtaleDerivedSheafHomFlipObjIso B S hS X M).symm

end AlgebraicGeometry.Space

end

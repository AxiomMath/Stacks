module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Strongly cartesian morphisms between represented families of algebraic spaces

Let `m : A ⟶ C` be a morphism of algebraic spaces over varying schemes of the big fppf site of
`S`, that is a morphism of the comma category whose objects are an algebraic space `A.left` with
a morphism `A.hom` to the scheme `A.right`. When the two algebraic spaces are represented by
schemes `Z_A` and `Z_C` of the site, the structure morphisms and the morphism of total spaces
come from morphisms of schemes by the Yoneda lemma, and Stacks 04U9 says that `m` is strongly
cartesian exactly when the resulting square of schemes is cartesian. This file records the
direction used to descend schemes: a strongly cartesian morphism between represented families
gives a cartesian square of schemes, both in the big fppf category over `S` and in the category
of all schemes.

## Main results

* `AlgebraicGeometry.isPullback_preimage_of_isStronglyCartesian`: the square of morphisms of
  the big fppf category over `S`.
* `AlgebraicGeometry.isPullback_toScheme_preimage_of_isStronglyCartesian`: the same square of
  schemes.

## References

* [Stacks Project, Tag 04U9](https://stacks.math.columbia.edu/tag/04U9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The square of a strongly cartesian morphism between represented families.** Let
`m : A ⟶ C` be a strongly cartesian morphism of algebraic spaces over varying schemes whose
algebraic spaces are represented, through `eA` and `eC`, by schemes `Z_A` and `Z_C` of the big
fppf site of `S`. Then the square formed by the morphisms of schemes underlying the morphism of
total spaces, the two structure morphisms and the morphism of bases is cartesian.

This is the square of Stacks 04U9 (`AlgebraicGeometry.isPullback_hom_of_isStronglyCartesian`),
transported along `eA` and `eC` and reflected by the Yoneda embedding. -/
theorem isPullback_preimage_of_isStronglyCartesian
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (m : A ⟶ C)
    (hm : (spacesProjection B S hS).IsStronglyCartesian m.right m)
    {ZA ZC : BigFppfOver B S hS} (eA : yoneda.obj ZA ≅ A.left.1) (eC : yoneda.obj ZC ≅ C.left.1) :
    IsPullback (Yoneda.fullyFaithful.preimage (eA.hom ≫ m.left.hom ≫ eC.inv))
      (Yoneda.fullyFaithful.preimage (eA.hom ≫ A.hom))
      (Yoneda.fullyFaithful.preimage (eC.hom ≫ C.hom)) m.right := by
  have h := (isPullback_hom_of_isStronglyCartesian B S hS m hm).flip
  refine IsPullback.of_map_of_faithful yoneda ?_
  simp only [Functor.FullyFaithful.map_preimage]
  exact IsPullback.of_iso h eA.symm eC.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp)

/-- **The square of a strongly cartesian morphism between represented families, in schemes.**
`AlgebraicGeometry.isPullback_preimage_of_isStronglyCartesian` read through the functor to all
schemes, which preserves fibre products. -/
theorem isPullback_toScheme_preimage_of_isStronglyCartesian
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (m : A ⟶ C)
    (hm : (spacesProjection B S hS).IsStronglyCartesian m.right m)
    {ZA ZC : BigFppfOver B S hS} (eA : yoneda.obj ZA ≅ A.left.1) (eC : yoneda.obj ZC ≅ C.left.1) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map
        (Yoneda.fullyFaithful.preimage (eA.hom ≫ m.left.hom ≫ eC.inv)))
      ((BigFppfOver.toScheme B S hS).map (Yoneda.fullyFaithful.preimage (eA.hom ≫ A.hom)))
      ((BigFppfOver.toScheme B S hS).map (Yoneda.fullyFaithful.preimage (eC.hom ≫ C.hom)))
      ((BigFppfOver.toScheme B S hS).map m.right) :=
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  (isPullback_preimage_of_isStronglyCartesian m hm eA eC).map (BigFppfOver.toScheme B S hS)

end AlgebraicGeometry

end

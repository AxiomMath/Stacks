module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability

/-!
# The equivalence of algebraic spaces over a smaller base scheme

Let `g : S ⟶ S'` be a morphism of a big fppf site. The lower-shriek extension along `g` is an
equivalence between the category of algebraic spaces over `S` and the category of pairs
`(F', F' ⟶ S)` consisting of an algebraic space `F'` over `S'` and a morphism `F' ⟶ S` of
algebraic spaces over `S'`.

## Main definitions

* `AlgebraicGeometry.spacesOverSmallerBaseEquivalence`: the equivalence between algebraic spaces
  over `S` and algebraic spaces over `S'` equipped with a morphism to the representable algebraic
  space of `S`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_smallerBasePresheafEquivalence_inverse`: the quasi-inverse of
  the presheaf-level equivalence carries algebraic spaces over `S'` to algebraic spaces over `S`.
* `AlgebraicGeometry.isAlgebraicSpace_viewOver_iff`: a presheaf on the big fppf site of `S` is an
  algebraic space over `S` exactly when its lower-shriek extension along `g` is an algebraic space
  over `S'`.
* `AlgebraicGeometry.spacesOverSmallerBaseEquivalence_functor`: the functor of the equivalence is
  `AlgebraicGeometry.spacesOverSmallerBaseFunctor`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- If `X` is a presheaf on the big fppf site of `S'` over the representable presheaf of
`S ⟶ S'` whose underlying presheaf is an algebraic space over `S'`, then the presheaf on the big
fppf site of `S` that `AlgebraicGeometry.smallerBasePresheafEquivalence` attaches to it is an
algebraic space over `S`. -/
theorem isAlgebraicSpace_smallerBasePresheafEquivalence_inverse
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u))
    (hX : IsAlgebraicSpace B S' hS' X.left) :
    IsAlgebraicSpace B S hS
      ((smallerBasePresheafEquivalence B S S' hS hS' g).inverse.obj X) :=
  Space.isAlgebraicSpace_fibreOfSection B S' hS' (Over.mk g) X.hom
    (𝟙 (yoneda.obj (Over.mk g)))
    (isAlgebraicSpace_pullback B S' hS' _ _
      (isAlgebraicSpace_yoneda B S' hS' (Over.mk g)) hX
      (isAlgebraicSpace_yoneda B S' hS' (Over.mk g)))

/-- A presheaf on the big fppf site of `S` is an algebraic space over `S` exactly when its
lower-shriek extension along `g : S ⟶ S'` is an algebraic space over `S'`. -/
theorem isAlgebraicSpace_viewOver_iff (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsAlgebraicSpace B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F) ↔
      IsAlgebraicSpace B S hS F := by
  refine ⟨fun h => ?_, isAlgebraicSpace_viewOver B S S' hS hS' g F⟩
  refine isAlgebraicSpace_of_iso B S hS
    ((smallerBasePresheafEquivalence B S S' hS hS' g).unitIso.app F)
    (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B S S' hS hS' g _ ?_)
  exact isAlgebraicSpace_of_iso B S' hS'
    ((smallerBasePresheafForgetIso B S S' hS hS' g).app F) h

/-- The category of algebraic spaces over `S` is equivalent to the category of algebraic spaces
over `S'` equipped with a morphism to the representable algebraic space of `S`, the equivalence
being the lower-shriek extension along `g : S ⟶ S'`. -/
@[stacks 04SG "the equivalence"]
noncomputable def spacesOverSmallerBaseEquivalence :
    AlgebraicSpaces B S hS ≌ SpacesOverSmallerBase B S S' hS hS' g :=
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) =>
        IsAlgebraicSpace B S' hS' X.left) :=
    ⟨fun e hX => isAlgebraicSpace_of_iso B S' hS'
      ((Over.forget (yoneda.obj (Over.mk g))).mapIso e).symm hX⟩
  (smallerBasePresheafEquivalence B S S' hS hS' g).congrFullSubcategory (by
    funext F
    refine propext (Iff.trans ?_ (isAlgebraicSpace_viewOver_iff B S S' hS hS' g F))
    exact ⟨isAlgebraicSpace_of_iso B S' hS'
        ((smallerBasePresheafForgetIso B S S' hS hS' g).app F).symm,
      isAlgebraicSpace_of_iso B S' hS'
        ((smallerBasePresheafForgetIso B S S' hS hS' g).app F)⟩)

/-- The functor of `AlgebraicGeometry.spacesOverSmallerBaseEquivalence` is the forward functor
`AlgebraicGeometry.spacesOverSmallerBaseFunctor`. -/
theorem spacesOverSmallerBaseEquivalence_functor :
    (spacesOverSmallerBaseEquivalence B S S' hS hS' g).functor =
      spacesOverSmallerBaseFunctor B S S' hS hS' g :=
  rfl

end AlgebraicGeometry

end

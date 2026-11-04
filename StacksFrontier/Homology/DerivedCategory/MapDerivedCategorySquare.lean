module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# A commuting square of exact functors commutes on derived categories

A square of abelian categories and exact additive functors which commutes up to a natural
isomorphism induces a square of the functors on unbounded derived categories, commuting up to
a natural isomorphism as well.

This is the derived form of a base-change square of underived functors; it is what lets a
2-square be transported to derived categories before the mates correspondence is applied to it.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategorySquareIso`: the induced isomorphism
  `T.mapDerivedCategory ⋙ R.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ B.mapDerivedCategory`
  attached to an isomorphism `T ⋙ R ≅ L ⋙ B`.  The four functors are implicit arguments, read
  off the given isomorphism: supplying them explicitly lets the four categories be fixed by two
  of them while the other two are only definitionally of the right type, and instance search for
  the exactness of those two then runs on a goal whose categories are spelled otherwise than in
  their own types.

## Main results

* `CategoryTheory.Functor.mapDerivedCategorySquareIso_hom_app_Q`: its component at a complex in
  the image of the localization functor, which is the datum the construction is lifted from and
  which determines it, the localization functor being essentially surjective.

## Implementation notes

The isomorphism is produced by `CategoryTheory.Localization.liftNatIso` at
`DerivedCategory.Q`: both composites are liftings of functors defined on cochain complexes, by
`CategoryTheory.Functor.mapDerivedCategoryFactors` on each factor, and
`CategoryTheory.Functor.mapHomologicalComplexCompIso` transports the given isomorphism to
complexes. Lifting rather than defining the components by hand is what supplies naturality.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]

/-- **A square of exact functors which commutes commutes on derived categories.** An
isomorphism `T ⋙ R ≅ L ⋙ B` of composites of exact additive functors between abelian
categories induces an isomorphism of the composites of the induced functors on unbounded
derived categories. -/
def mapDerivedCategorySquareIso (e : T ⋙ R ≅ L ⋙ B) :
    T.mapDerivedCategory ⋙ R.mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ B.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ T.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (DerivedCategory.Q ⋙ L.mapDerivedCategory ⋙ B.mapDerivedCategory) _ _
    (Functor.isoWhiskerRight T.mapDerivedCategoryFactors R.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (T.mapHomologicalComplex (ComplexShape.up ℤ))
        R.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      (Functor.isoWhiskerLeft (L.mapHomologicalComplex (ComplexShape.up ℤ))
        B.mapDerivedCategoryFactors).symm ≪≫
      (Functor.isoWhiskerRight L.mapDerivedCategoryFactors B.mapDerivedCategory).symm)

/-- The component of `CategoryTheory.Functor.mapDerivedCategorySquareIso` at a cochain complex:
it is the composite of the four comparison isomorphisms identifying each side with the functor
applied termwise, with the given isomorphism in the middle. Since `DerivedCategory.Q` is
essentially surjective this determines the isomorphism. -/
theorem mapDerivedCategorySquareIso_hom_app_Q (e : T ⋙ R ≅ L ⋙ B) (K : CochainComplex C₁ ℤ) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) =
      R.mapDerivedCategory.map (T.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) ≫
        B.mapDerivedCategoryFactors.inv.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        B.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K) := by
  simp [mapDerivedCategorySquareIso, Localization.liftNatTrans_app]

end CategoryTheory.Functor

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Postcomposing a total right derived functor with an exact functor

Let `A` be a Grothendieck abelian category, let `F : A ⥤ B₁` be additive and let `G : B₁ ⥤ B₂` be
exact. Deriving `F` and then applying the functor that `G` induces on unbounded derived categories
is the same as deriving `G ∘ F`:

`R(F) ⋙ G.mapDerivedCategory ≅ R(G ∘ F)`.

## Main definitions

* `Stacks.Cohomology.SiteCohomologyPresheaf.mapDerivedCategorySourceIso`: the underived
  comparison of the two functors on the homotopy category of `A`.
* `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`: the
  comparison of the two total right derived functors.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.SiteCohomologyPresheaf

universe v₁ v₂ v₃ u₁ u₂ u₃ wG wD wD₁ wD₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
    [HasDerivedCategory.{wD} A]
  {B₁ : Type u₂} [Category.{v₂} B₁] [Abelian B₁] [HasDerivedCategory.{wD₁} B₁]
  {B₂ : Type u₃} [Category.{v₃} B₂] [Abelian B₂] [HasDerivedCategory.{wD₂} B₂]
  (F : A ⥤ B₁) [F.Additive]
  (G : B₁ ⥤ B₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The comparison, on the homotopy category of `A`, between localizing the complexes of
`F`-images and then applying `G.mapDerivedCategory`, and localizing the complexes of
`(F ⋙ G)`-images. -/
def mapDerivedCategorySourceIso :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ G.mapDerivedCategory ≅
      (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- For `F : A ⥤ B₁` additive out of a Grothendieck abelian category and `G : B₁ ⥤ B₂` exact, the
total right derived functor of `F` followed by the functor `G` induces on derived categories is
canonically the total right derived functor of `F ⋙ G`. -/
def totalRightDerivedMapDerivedCategoryIso :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⋙
        G.mapDerivedCategory ≅
      ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let FGh := (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have := isRightDerivedFunctor_totalRightDerived_comp (A := A) Fh G.mapDerivedCategory
  Functor.rightDerivedNatIso (Fh.totalRightDerived DerivedCategory.Qh W ⋙ G.mapDerivedCategory)
    (FGh.totalRightDerived DerivedCategory.Qh W)
    (totalRightDerivedCompUnit Fh G.mapDerivedCategory)
    (FGh.totalRightDerivedUnit DerivedCategory.Qh W) W (mapDerivedCategorySourceIso F G)

end Stacks.Cohomology.SiteCohomologyPresheaf

end

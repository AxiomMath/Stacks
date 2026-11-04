module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived

/-!
# Postcomposing a total right derived functor with an exact functor, along a given identification

`Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso` identifies the
total right derived functor of `F` followed by `G.mapDerivedCategory`, for `G` exact, with the
total right derived functor of `F ⋙ G`. This file gives the same comparison for a functor `H`
together with an identification `e : F ⋙ G ≅ H`.

The declarations complement
`StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived` and are placed in a
module of their own.

## Main definitions

* `Stacks.Cohomology.SiteCohomologyPresheaf.mapDerivedCategorySourceIsoOfIso`
* `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIsoOfIso`
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
`H`-images, for an identification `e : F ⋙ G ≅ H`. -/
def mapDerivedCategorySourceIsoOfIso (H : A ⥤ B₂) [H.Additive] (e : F ⋙ G ≅ H) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ G.mapDerivedCategory ≅
      H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ))
      DerivedCategory.Qh

/-- **A total right derived functor postcomposed with an exact functor derives the composite,
up to a given identification of the composite.** For `F : A ⥤ B₁` additive out of a Grothendieck
abelian category, `G : B₁ ⥤ B₂` exact and `e : F ⋙ G ≅ H`, the total right derived functor of
`F` followed by the functor `G` induces on derived categories is canonically the total right
derived functor of `H`. -/
def totalRightDerivedMapDerivedCategoryIsoOfIso (H : A ⥤ B₂) [H.Additive] (e : F ⋙ G ≅ H) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⋙
        G.mapDerivedCategory ≅
      (H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let Hh := H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have := isRightDerivedFunctor_totalRightDerived_comp (A := A) Fh G.mapDerivedCategory
  Functor.rightDerivedNatIso (Fh.totalRightDerived DerivedCategory.Qh W ⋙ G.mapDerivedCategory)
    (Hh.totalRightDerived DerivedCategory.Qh W)
    (totalRightDerivedCompUnit Fh G.mapDerivedCategory)
    (Hh.totalRightDerivedUnit DerivedCategory.Qh W) W (mapDerivedCategorySourceIsoOfIso F G H e)

end Stacks.Cohomology.SiteCohomologyPresheaf

end

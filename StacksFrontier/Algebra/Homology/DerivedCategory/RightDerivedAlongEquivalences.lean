module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# Unbounded right derived functors transported along exact equivalences

Let `F : A ⥤ B` and `G : A' ⥤ B'` be additive functors between abelian categories, and let
`E_A : A ⥤ A'`, `E_B : B ⥤ B'` be additive equivalences with `F ⋙ E_B ≅ E_A ⋙ G`. If `RF` and
`RG` are right derived functors of `F` and `G` on the unbounded derived categories, then
`RF ⋙ D(E_B) ≅ D(E_A) ⋙ RG`, where `D(E)` is the equivalence an exact equivalence induces on
derived categories.

Both sides are right derived functors of the degreewise composite: postcomposition with the
equivalence `D(E_B)` preserves left Kan extensions, and precomposition with the equivalences
`K(E_A)` and `D(E_A)` transports them
(`Stacks.DerivedFunctor.isLeftKanExtension_comp_of_equivalence`).

## Main definitions

* `Stacks.DerivedFunctor.rightDerivedCompMapDerivedCategoryIso`: the isomorphism
  `RF ⋙ D(E_B) ≅ D(E_A) ⋙ RG`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

variable {A A' B B' : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* A'] [Abelian A'] [HasDerivedCategory A']
  [Category* B] [Abelian B] [HasDerivedCategory B]
  [Category* B'] [Abelian B'] [HasDerivedCategory B']
  (F : A ⥤ B) (G : A' ⥤ B') [F.Additive] [G.Additive]
  (EA : A ⥤ A') (EB : B ⥤ B') [EA.Additive] [EB.Additive] [EA.IsEquivalence] [EB.IsEquivalence]
  (σ : F ⋙ EB ≅ EA ⋙ G)
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (RG : DerivedCategory A' ⥤ DerivedCategory B')
  (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)
  [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]

/-- The unit exhibiting `D(E_A) ⋙ RG` as a right derived functor of
`K(E_A) ⋙ K(G) ⋙ Q`: the unit of `RG` transported along `K(E_A)` and `D(E_A)`. -/
def precompMapDerivedCategoryUnit :
    EA.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ (EA.mapDerivedCategory ⋙ RG) :=
  ((Iso.refl _).hom ≫ Functor.whiskerLeft (EA.mapHomotopyCategory (ComplexShape.up ℤ)) αG ≫
      (Functor.associator _ _ _).inv) ≫
    Functor.whiskerRight EA.mapDerivedCategoryFactorsh.inv RG ≫ (Functor.associator _ _ _).hom

/-- `D(E_A) ⋙ RG` is a right derived functor of `K(E_A) ⋙ K(G) ⋙ Q`. -/
theorem isRightDerivedFunctor_precompMapDerivedCategory :
    (EA.mapDerivedCategory ⋙ RG).IsRightDerivedFunctor (precompMapDerivedCategoryUnit G EA RG αG)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have := isEquivalence_mapHomotopyCategory EA
  have := isEquivalence_mapDerivedCategory EA
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  have : RG.IsLeftKanExtension αG := by
    rw [← Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _
      (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
    infer_instance
  exact isLeftKanExtension_comp_of_equivalence EA.mapDerivedCategoryFactorsh αG (Iso.refl _) _
    rfl

/-- The unit exhibiting `RF ⋙ D(E_B)` as a right derived functor of `K(F) ⋙ Q ⋙ D(E_B)`. -/
def postcompMapDerivedCategoryUnit :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ EB.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ (RF ⋙ EB.mapDerivedCategory) :=
  Functor.whiskerRight αF EB.mapDerivedCategory ≫ (Functor.associator _ _ _).hom

/-- `RF ⋙ D(E_B)` is a right derived functor of `K(F) ⋙ Q ⋙ D(E_B)`. -/
theorem isRightDerivedFunctor_postcompMapDerivedCategory :
    (RF ⋙ EB.mapDerivedCategory).IsRightDerivedFunctor
      (postcompMapDerivedCategoryUnit F EB RF αF)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have := isEquivalence_mapDerivedCategory EB
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  have : RF.IsLeftKanExtension αF := by
    rw [← Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    infer_instance
  exact (Functor.isLeftKanExtension_postcompose₂_iff RF αF EB.mapDerivedCategory).2 this

/-- The comparison of the two functors that `RF ⋙ D(E_B)` and `D(E_A) ⋙ RG` derive. -/
def mapHomotopyCategoryCompMapDerivedCategoryIso :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ EB.mapDerivedCategory ≅
      EA.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ EB.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso σ (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (EA ⋙ G)) (ComplexShape.up ℤ)).symm)
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- **Right derived functors commute with exact equivalences**: for `F ⋙ E_B ≅ E_A ⋙ G` with
`E_A`, `E_B` additive equivalences, `RF ⋙ D(E_B) ≅ D(E_A) ⋙ RG`. -/
def rightDerivedCompMapDerivedCategoryIso :
    RF ⋙ EB.mapDerivedCategory ≅ EA.mapDerivedCategory ⋙ RG :=
  have := isRightDerivedFunctor_postcompMapDerivedCategory F EB RF αF
  have := isRightDerivedFunctor_precompMapDerivedCategory G EA RG αG
  Functor.rightDerivedNatIso _ _ (postcompMapDerivedCategoryUnit F EB RF αF)
    (precompMapDerivedCategoryUnit G EA RG αG) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (mapHomotopyCategoryCompMapDerivedCategoryIso F G EA EB σ)

end Stacks.DerivedFunctor

end

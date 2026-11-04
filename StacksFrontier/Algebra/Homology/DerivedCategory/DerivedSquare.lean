module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf

/-!
# Deriving a square of an additive functor and an exact one

Let `A`, `A'`, `B`, `B'` be abelian categories with derived categories, `A` Grothendieck abelian,
let `F : A ⥤ B`, `F' : A' ⥤ B'` be additive functors with total right derived functors `RF`,
`RF'` on the unbounded derived categories, and let `E : A ⥤ A'`, `E' : B ⥤ B'` be exact. A
natural transformation

`c : F ⋙ E' ⟶ E ⋙ F'`

induces a natural transformation

`derivedSquare c : RF ⋙ E'.mapDerivedCategory ⟶ E.mapDerivedCategory ⋙ RF'`,

the base change map of [Stacks, Tag 0A2A] and [Stacks, Tag 07A7] for an arbitrary square.

## Main definitions

* `Stacks.Homology.DerivedSquare.derivedSquare`: the derived natural transformation.

## Main results

* `Stacks.Homology.DerivedSquare.derivedSquare_fac_app`: precomposed with `E'` of the unit of
  `RF`, the derived transformation at `Q_h X` is the degreewise `c` followed by the unit of `RF'`
  (up to the exactness comparisons of `E` and `E'`).
* `Stacks.Homology.DerivedSquare.isIso_derivedSquare_app_iff`: at a complex on which the unit of
  `RF` is invertible (for example a K-injective one), the derived transformation is invertible
  if and only if the degreewise `c` followed by the unit of `RF'` is.
* `Stacks.Homology.DerivedSquare.isIso_derivedSquare_of_isIso`: if `c` is an isomorphism and `E`
  carries K-injective complexes to complexes on which the unit of `RF'` is invertible, the
  derived transformation is an isomorphism.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedCompUnit
  isRightDerivedFunctor_totalRightDerived_comp totalRightDerivedCompUnit_app)

universe wA wA' wB wB' vA vA' vB vB' uA uA' uB uB' wG

namespace Stacks.Homology.DerivedSquare

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]
  [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  (E' : B ⥤ B') [E'.Additive] [PreservesFiniteLimits E'] [PreservesFiniteColimits E']

/-- The total right derived functor of an additive functor out of an abelian category, on the
unbounded derived categories. -/
abbrev totalRightDerived (G : A ⥤ B) [G.Additive]
    [(G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The derived-functor unit `K(G) ⋙ Q_h ⟶ Q_h ⋙ RG`. -/
abbrev totalRightDerivedUnit (G : A ⥤ B) [G.Additive]
    [(G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ totalRightDerived G :=
  (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

variable {F F' E E'}

/-- Through the exactness comparison of `E'`, the degreewise `c`, followed by the unit of `RF'`
and the exactness comparison of `E`. -/
def derivedSquareBeta (c : F ⋙ E' ⟶ E ⋙ F') :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E'.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ (E.mapDerivedCategory ⋙ totalRightDerived F') :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      E'.mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E'))
      (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategory c (ComplexShape.up ℤ))
      DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F'))
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (E.mapHomotopyCategory (ComplexShape.up ℤ))
      (totalRightDerivedUnit F') ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight E.mapDerivedCategoryFactorsh.inv (totalRightDerived F') ≫
    (Functor.associator _ _ _).hom

/-- **The derived natural transformation of a square.** For `c : F ⋙ E' ⟶ E ⋙ F'` with `E`, `E'`
exact, the natural transformation `RF ⋙ E'.mapDerivedCategory ⟶ E.mapDerivedCategory ⋙ RF'`
obtained by descending the degreewise `c`, followed by the unit of `RF'`, along the universal
property of `RF ⋙ E'.mapDerivedCategory` as a right derived functor. -/
def derivedSquare (c : F ⋙ E' ⟶ E ⋙ F') :
    totalRightDerived F ⋙ E'.mapDerivedCategory ⟶
      E.mapDerivedCategory ⋙ totalRightDerived F' :=
  haveI := isRightDerivedFunctor_totalRightDerived_comp
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory
  (totalRightDerived F ⋙ E'.mapDerivedCategory).rightDerivedDesc
    (totalRightDerivedCompUnit
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (E.mapDerivedCategory ⋙ totalRightDerived F') (derivedSquareBeta c)

/-- **The defining property of `derivedSquare`.** Precomposed with `E'` of the unit of `RF`, the
derived transformation at `Q_h X` is `derivedSquareBeta c` at `X`. -/
theorem derivedSquare_fac_app (c : F ⋙ E' ⟶ E ⋙ F') (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    E'.mapDerivedCategory.map ((totalRightDerivedUnit F).app X) ≫
        (derivedSquare c).app (DerivedCategory.Qh.obj X) = (derivedSquareBeta c).app X := by
  have := isRightDerivedFunctor_totalRightDerived_comp
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory
  rw [← totalRightDerivedCompUnit_app]
  exact Functor.rightDerived_fac_app _ _ _ _ _ _

omit [IsGrothendieckAbelian.{wG} A]
  [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] in
/-- For an invertible `c`, the transformation `derivedSquareBeta c` is invertible at `X` exactly
when the unit of `RF'` is invertible at `E X`. -/
theorem isIso_derivedSquareBeta_app_iff (c : F ⋙ E' ⟶ E ⋙ F') [IsIso c]
    (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    IsIso ((derivedSquareBeta c).app X) ↔
      IsIso ((totalRightDerivedUnit F').app
        ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) := by
  have : IsIso (NatTrans.mapHomotopyCategory c (ComplexShape.up ℤ)) :=
    ⟨NatTrans.mapHomotopyCategory (inv c) (ComplexShape.up ℤ), by
      rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id], by
      rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩
  simp only [derivedSquareBeta, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Invertibility of the derived transformation, read on complexes.** For an invertible `c` and
a complex `X` on which the unit of `RF` is invertible — for instance a K-injective one — the
derived transformation is invertible at `Q_h X` exactly when the unit of `RF'` is invertible at
`E X`. -/
theorem isIso_derivedSquare_app_iff (c : F ⋙ E' ⟶ E ⋙ F') [IsIso c]
    (X : HomotopyCategory A (ComplexShape.up ℤ)) (hX : IsIso ((totalRightDerivedUnit F).app X)) :
    IsIso ((derivedSquare c).app (DerivedCategory.Qh.obj X)) ↔
      IsIso ((totalRightDerivedUnit F').app
        ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) := by
  rw [← isIso_derivedSquareBeta_app_iff c X, ← derivedSquare_fac_app, isIso_comp_left_iff]

/-- **The derived transformation of an invertible square is invertible** as soon as `E` carries
K-injective complexes to complexes on which the unit of `RF'` is invertible. -/
theorem isIso_derivedSquare_of_isIso (c : F ⋙ E' ⟶ E ⋙ F') [IsIso c]
    (h : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso ((totalRightDerivedUnit F').app ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) :
    IsIso (derivedSquare c) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage K)
  obtain ⟨I, q, hI, hq⟩ := Stacks.Cohomology.Localization.enoughKInjectives L
  have hqi : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  let e : K ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) :=
    (DerivedCategory.Qh.objObjPreimageIso K).symm ≪≫ eqToIso (by rw [← hL]) ≪≫
      asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q))
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  have := hI
  exact (isIso_derivedSquare_app_iff c _
    (Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I)).mpr (h I hI)

end Stacks.Homology.DerivedSquare

end

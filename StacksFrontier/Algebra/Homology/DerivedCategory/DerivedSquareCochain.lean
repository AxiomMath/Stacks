module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# Deriving a square along the localization of cochain complexes

Let `A`, `A'`, `B`, `B'` be abelian categories with derived categories, `A` Grothendieck abelian,
let `F : A ⥤ B`, `F' : A' ⥤ B'` be additive functors with right derived functors `RF`, `RF'` on
the unbounded derived categories along the localization `DerivedCategory.Q` of cochain
complexes, and let `E : A ⥤ A'`, `E' : B ⥤ B'` be exact. A natural transformation

`c : F ⋙ E' ⟶ E ⋙ F'`

induces a natural transformation

`cochainDerivedSquare α α' c : RF ⋙ E'.mapDerivedCategory ⟶ E.mapDerivedCategory ⋙ RF'`:

apply `c` degreewise, follow it with the unit `α'` of `RF'`, and descend along the universal
property of `RF ⋙ E'.mapDerivedCategory` as a right derived functor of
`(F ⋙ E').mapHomologicalComplex ⋙ Q`. This is the base change map of [Stacks, Tag 0A2A] for any
right derived functors formed along `DerivedCategory.Q`, such as the unbounded derived direct
image `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded` of sheaves of modules.

## Main definitions

* `Stacks.Homology.DerivedSquare.cochainDerivedSquareUnit`: the unit exhibiting
  `RF ⋙ E'.mapDerivedCategory` as a right derived functor.
* `Stacks.Homology.DerivedSquare.cochainDerivedSquare`: the derived natural transformation.

## Main results

* `Stacks.Homology.DerivedSquare.cochainDerivedSquare_fac_app`: precomposed with `E'` of the unit
  of `RF`, the derived transformation at `Q K` is the degreewise `c` followed by the unit of `RF'`,
  up to the exactness comparisons of `E` and `E'`. This determines it.

## Implementation notes

`Stacks.Homology.DerivedSquare.derivedSquare` performs the same construction for the total right
derived functors along `DerivedCategory.Qh`, the localization of the homotopy category; this file
is the version along `DerivedCategory.Q`, in which the derived functors on sheaves of modules
are formed. Postcomposing a right derived functor with any functor is a right derived functor
over a Grothendieck abelian category, by the K-injective criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Injectives.KInjectiveResolution (invertsQuasiIso_mapHomologicalComplex_comp_Q
  isRightDerivedFunctor_iff_isIso_app_of_isKInjective isIso_app_of_isKInjective)

universe wA wA' wB wB' vA vA' vB vB' uA uA' uB uB' wG

namespace Stacks.Homology.DerivedSquare

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  {F : A ⥤ B} [F.Additive] {F' : A' ⥤ B'} [F'.Additive]
  {E : A ⥤ A'} [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  {E' : B ⥤ B'} [E'.Additive] [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
  {RF : DerivedCategory A ⥤ DerivedCategory B}
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)
  {RF' : DerivedCategory A' ⥤ DerivedCategory B'}
  (α' : F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF')

/-- The unit exhibiting `RF ⋙ E'.mapDerivedCategory` as a right derived functor of
`(F ⋙ E').mapHomologicalComplex ⋙ Q`: `E'` applied to the unit `α` of `RF`, through the exactness
comparison of `E'`. -/
def cochainDerivedSquareUnit :
    (F ⋙ E').mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (RF ⋙ E'.mapDerivedCategory) :=
  Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E')) (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      E'.mapDerivedCategoryFactors.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight α E'.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- Postcomposing the right derived functor `RF` with `E'.mapDerivedCategory` gives a right
derived functor: the unit `α` is invertible at K-injective complexes, hence so is its image
under `E'`. -/
instance isRightDerivedFunctor_cochainDerivedSquareUnit
    [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))] :
    (RF ⋙ E'.mapDerivedCategory).IsRightDerivedFunctor
      (cochainDerivedSquareUnit (E' := E') α)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (F ⋙ E'))]
  intro K hK
  have := isIso_app_of_isKInjective DerivedCategory.Q RF α
    (invertsQuasiIso_mapHomologicalComplex_comp_Q F) K hK
  dsimp only [cochainDerivedSquareUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- The transformation that `cochainDerivedSquare` descends: the degreewise `c`, followed by the
unit `α'` of `RF'` and the exactness comparison of `E`. -/
def cochainDerivedSquareBeta (c : F ⋙ E' ⟶ E ⋙ F') :
    (F ⋙ E').mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (E.mapDerivedCategory ⋙ RF') :=
  Functor.whiskerRight (NatTrans.mapHomologicalComplex c (ComplexShape.up ℤ))
      DerivedCategory.Q ≫
    Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F')) (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (E.mapHomologicalComplex (ComplexShape.up ℤ)) α' ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight E.mapDerivedCategoryFactors.inv RF' ≫
    (Functor.associator _ _ _).hom

variable [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- **The derived natural transformation of a square, along `DerivedCategory.Q`.** For
`c : F ⋙ E' ⟶ E ⋙ F'` with `E`, `E'` exact, the natural transformation
`RF ⋙ E'.mapDerivedCategory ⟶ E.mapDerivedCategory ⋙ RF'` obtained by descending the degreewise
`c`, followed by the unit of `RF'`, along the universal property of
`RF ⋙ E'.mapDerivedCategory`. -/
def cochainDerivedSquare (c : F ⋙ E' ⟶ E ⋙ F') :
    RF ⋙ E'.mapDerivedCategory ⟶ E.mapDerivedCategory ⋙ RF' :=
  (RF ⋙ E'.mapDerivedCategory).rightDerivedDesc (cochainDerivedSquareUnit α)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (E.mapDerivedCategory ⋙ RF')
    (cochainDerivedSquareBeta α' c)

/-- **The defining property of `cochainDerivedSquare`.** Precomposed with the exactness comparison
of `E'` and with `E'` of the unit of `RF`, the derived transformation at `Q K` is the degreewise
`c` followed by the unit of `RF'` and the exactness comparison of `E`. -/
theorem cochainDerivedSquare_fac_app (c : F ⋙ E' ⟶ E ⋙ F') (K : CochainComplex A ℤ) :
    E'.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        E'.mapDerivedCategory.map (α.app K) ≫
          (cochainDerivedSquare α α' c).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c (ComplexShape.up ℤ)).app K) ≫
        α'.app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          RF'.map (E.mapDerivedCategoryFactors.inv.app K) := by
  have h := Functor.rightDerived_fac_app (RF ⋙ E'.mapDerivedCategory)
    (cochainDerivedSquareUnit α) (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (E.mapDerivedCategory ⋙ RF') (cochainDerivedSquareBeta α' c) K
  simp only [cochainDerivedSquareUnit, cochainDerivedSquareBeta, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc] at h
  have e₁ : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E'))
      (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := by ext; simp
  have e₂ : (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F'))
      (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := by ext; simp
  rw [e₁, e₂, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
  exact (Category.id_comp _).symm.trans (h.trans (congrArg (_ ≫ ·) (Category.id_comp _)))

/-- **The defining property of `cochainDerivedSquare`, with the degreewise comparison read
between composites of degreewise functors.** The same as
`Stacks.Homology.DerivedSquare.cochainDerivedSquare_fac_app`, with the degreewise `c` passed
through the identifications `(F ⋙ E').mapHomologicalComplex = F.mapHomologicalComplex ⋙
E'.mapHomologicalComplex` and `(E ⋙ F').mapHomologicalComplex = E.mapHomologicalComplex ⋙
F'.mapHomologicalComplex`, so that every composite is formed between syntactically equal
objects. -/
theorem cochainDerivedSquare_fac_app' (c : F ⋙ E' ⟶ E ⋙ F') (K : CochainComplex A ℤ) :
    E'.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        E'.mapDerivedCategory.map (α.app K) ≫
          (cochainDerivedSquare α α' c).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E'))
              (ComplexShape.up ℤ)).hom.app K ≫
            (NatTrans.mapHomologicalComplex c (ComplexShape.up ℤ)).app K ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F'))
              (ComplexShape.up ℤ)).inv.app K) ≫
        α'.app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          RF'.map (E.mapDerivedCategoryFactors.inv.app K) := by
  rw [cochainDerivedSquare_fac_app]
  have e₁ : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E'))
      (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by ext; simp
  have e₂ : (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F'))
      (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := by ext; simp
  rw [e₁, e₂, Category.id_comp, Category.comp_id]

end Stacks.Homology.DerivedSquare

end

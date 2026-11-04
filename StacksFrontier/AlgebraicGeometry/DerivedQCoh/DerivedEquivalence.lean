module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# An equivalence of abelian categories induces an equivalence of derived categories

Mathlib constructs `CategoryTheory.Functor.mapDerivedCategory`, the functor
`D(C₁) ⥤ D(C₂)` induced by an exact functor `F : C₁ ⥤ C₂` between abelian categories, but
proves nothing about when it is an equivalence. This file supplies the basic case: if `E` is an
equivalence of abelian categories, then `E.functor.mapDerivedCategory` is an equivalence.

The proof is the localization-theoretic one. Both `DerivedCategory.Q` and the composite
`E.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q` are candidates for
the localization of `CochainComplex C₁ ℤ` at the quasi-isomorphisms, and Mathlib's
`CategoryTheory.Localization.equivalence` turns a pair of lifts with the two composition
isomorphisms into an equivalence of the localized categories. The two composition isomorphisms
come from `CategoryTheory.Functor.mapDerivedCategoryFactors` together with
`CategoryTheory.Functor.mapHomologicalComplexCompIso` applied to the unit and counit of `E`.

## Main definitions

* `Stacks.DerivedQCoh.Equivalence.mapDerivedCategory` is the equivalence
  `DerivedCategory C₁ ≌ DerivedCategory C₂` induced by an equivalence `E : C₁ ≌ C₂` of abelian
  categories. Its underlying functor is `E.functor.mapDerivedCategory`, by definition.

## Main results

* `Stacks.DerivedQCoh.isEquivalence_mapDerivedCategory`: `E.functor.mapDerivedCategory` is an
  equivalence.

## Implementation notes

The additivity hypothesis `[E.functor.Additive]` is stated rather than derived: an equivalence
between abelian categories is automatically additive, but obtaining that instance requires
`PreservesBinaryBiproducts`, whose synthesis depends on the shape in which the equivalence is
presented. All the remaining exactness instances (`PreservesFiniteLimits`,
`PreservesFiniteColimits` for both directions and `E.inverse.Additive`) are found by instance
search, the latter through `CategoryTheory.Equivalence.inverse_additive`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Stacks.DerivedQCoh

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (E : C₁ ≌ C₂) [E.functor.Additive]

/-- The isomorphism `(E.functor.mapHomologicalComplex _ ⋙ Q) ⋙ E.inverse.mapDerivedCategory ≅ Q`
expressing that passing to cochain complexes, localizing in `D(C₂)` and coming back along
`E.inverse` is the localization functor of `C₁`. This is the datum `α` of
`CategoryTheory.Localization.equivalence`. -/
def mapDerivedCategoryCompInverseIso :
    (E.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        E.inverse.mapDerivedCategory ≅ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ E.inverse.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso E.unitIso.symm
      (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫
    Functor.leftUnitor _

/-- The isomorphism `(E.inverse.mapHomologicalComplex _ ⋙ Q) ⋙ E.functor.mapDerivedCategory ≅ Q`,
the datum `β` of `CategoryTheory.Localization.equivalence`. -/
def mapDerivedCategoryCompFunctorIso :
    (E.inverse.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        E.functor.mapDerivedCategory ≅ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ E.functor.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso E.counitIso
      (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso C₂ (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫
    Functor.leftUnitor _

/-- An equivalence `E : C₁ ≌ C₂` of abelian categories induces an equivalence
`DerivedCategory C₁ ≌ DerivedCategory C₂` whose underlying functor is
`E.functor.mapDerivedCategory`. -/
def Equivalence.mapDerivedCategory : DerivedCategory C₁ ≌ DerivedCategory C₂ :=
  Localization.equivalence
    DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ))
    (E.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    E.functor.mapDerivedCategory
    (E.inverse.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    E.inverse.mapDerivedCategory
    (mapDerivedCategoryCompInverseIso E) (mapDerivedCategoryCompFunctorIso E)

/-- The functor underlying `Stacks.DerivedQCoh.Equivalence.mapDerivedCategory` is
`CategoryTheory.Functor.mapDerivedCategory` of `E.functor`. -/
@[simp]
lemma Equivalence.mapDerivedCategory_functor :
    (Equivalence.mapDerivedCategory E).functor = E.functor.mapDerivedCategory :=
  rfl

/-- The inverse of `Stacks.DerivedQCoh.Equivalence.mapDerivedCategory` is
`CategoryTheory.Functor.mapDerivedCategory` of `E.inverse`. -/
@[simp]
lemma Equivalence.mapDerivedCategory_inverse :
    (Equivalence.mapDerivedCategory E).inverse = E.inverse.mapDerivedCategory :=
  rfl

/-- The functor `D(C₁) ⥤ D(C₂)` induced by an equivalence of abelian categories `C₁ ≌ C₂` is an
equivalence. -/
instance isEquivalence_mapDerivedCategory : E.functor.mapDerivedCategory.IsEquivalence :=
  (Equivalence.mapDerivedCategory E).isEquivalence_functor

end Stacks.DerivedQCoh

end

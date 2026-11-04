module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Homology.DerivedCategory.ModelComparison

/-!
# `D_B(A)` does not depend on the chosen model of the derived category

`HasDerivedCategory.{w} A` is the assumption that a localization of `CochainComplex A ℤ` at the
quasi-isomorphisms has been *chosen*, with morphisms in `Type w`, and this library runs two
choices side by side — the locally small one of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, with morphisms in `Type u`, and
`CategoryTheory.HasDerivedCategory.standard`, with morphisms in `Type (u + 1)`.
`StacksDraft.DerivedModel.modelEquiv` compares the two ambient derived categories. This file
carries the subcategory `DerivedCategoryB.derivedCategoryB B` of
`StacksFrontier/Algebra/Homology/DerivedCategory/SerreSubcategory.lean` across that comparison, so
that a statement about `D_B(A)` proved at one model is available at the other.

## Main definitions

* `StacksDraft.DerivedModel.modelHomologyFunctorIso` — the comparison equivalence commutes with
  the cohomology functors of the derived category.
* `StacksDraft.DerivedModel.derivedCategoryBModelEquiv` — **`D_B(A)` at one model is equivalent
  to `D_B(A)` at any other**, by the restriction of `modelEquiv`.

## Main results

* `StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff` — an object lies in
  `D_B(A)` if and only if its transport does.
* `StacksDraft.DerivedModel.derivedCategoryBModelEquiv_functor_additive` — the equivalence of
  `D_B(A)` at two models is additive.

## Implementation notes

`DerivedCategory.homologyFunctor` is not given by a universal property, but it is *determined* by
one: `CategoryTheory.DerivedCategory.homologyFunctorFactors` exhibits it as the functor induced
on the localization by `HomologicalComplex.homologyFunctor`, and
`StacksDraft.DerivedModel.modelCompQIso` identifies the two localization functors out of
`CochainComplex A ℤ`. So both `modelEquiv.functor ⋙ H^n` and `H^n` are liftings of
`HomologicalComplex.homologyFunctor` through `DerivedCategory.Q` at the first model, and
`CategoryTheory.Localization.liftNatIso` identifies them. Nothing else is needed: the two
`HasDerivedCategory` instances are named explicitly throughout, as the implementation notes of
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean` ask, so no declaration here
leaves a model to instance search.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w z v u

namespace StacksDraft.DerivedModel

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **The comparison of two models of the derived category commutes with cohomology.** Both
`modelEquiv h₁ h₂ ⋙ H^n` and `H^n` are liftings of `HomologicalComplex.homologyFunctor` through
the localization `DerivedCategory.Q` at the first model, so they are isomorphic. -/
def modelHomologyFunctorIso (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{z} A)
    (n : ℤ) :
    (modelEquiv h₁ h₂).functor ⋙ @DerivedCategory.homologyFunctor A _ _ h₂ n ≅
      @DerivedCategory.homologyFunctor A _ _ h₁ n :=
  letI : Localization.Lifting (@DerivedCategory.Q A _ _ h₁)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n)
      ((modelEquiv h₁ h₂).functor ⋙ @DerivedCategory.homologyFunctor A _ _ h₂ n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (modelCompQIso h₁ h₂)
        (@DerivedCategory.homologyFunctor A _ _ h₂ n) ≪≫
      @DerivedCategory.homologyFunctorFactors A _ _ h₂ n⟩
  letI : Localization.Lifting (@DerivedCategory.Q A _ _ h₁)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n)
      (@DerivedCategory.homologyFunctor A _ _ h₁ n) :=
    ⟨@DerivedCategory.homologyFunctorFactors A _ _ h₁ n⟩
  Localization.liftNatIso (@DerivedCategory.Q A _ _ h₁)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n)
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n)
    ((modelEquiv h₁ h₂).functor ⋙ @DerivedCategory.homologyFunctor A _ _ h₂ n)
    (@DerivedCategory.homologyFunctor A _ _ h₁ n) (Iso.refl _)

/-- **Membership in `D_B(A)` is independent of the chosen model.** An object of the derived
category at one model has all of its cohomology objects in `B` exactly when its transport to the
other model does. -/
theorem derivedCategoryB_modelEquiv_functor_obj_iff (B : ObjectProperty A)
    [B.IsClosedUnderIsomorphisms] (h₁ : HasDerivedCategory.{w} A)
    (h₂ : HasDerivedCategory.{z} A) (K : @DerivedCategory A _ _ h₁) :
    @DerivedCategoryB.derivedCategoryB A _ _ h₂ B ((modelEquiv h₁ h₂).functor.obj K) ↔
      @DerivedCategoryB.derivedCategoryB A _ _ h₁ B K :=
  forall_congr' fun n ↦
    B.prop_iff_of_iso ((modelHomologyFunctorIso h₁ h₂ n).app K)

/-- **`D_B(A)` does not depend on the chosen model of the derived category.** The comparison
equivalence `StacksDraft.DerivedModel.modelEquiv` restricts to an equivalence of the two
subcategories of complexes with cohomology in `B`. -/
def derivedCategoryBModelEquiv (B : ObjectProperty A) [B.IsClosedUnderIsomorphisms]
    (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{z} A) :
    (@DerivedCategoryB.derivedCategoryB A _ _ h₁ B).FullSubcategory ≌
      (@DerivedCategoryB.derivedCategoryB A _ _ h₂ B).FullSubcategory :=
  haveI : (@DerivedCategoryB.derivedCategoryB A _ _ h₂ B).IsClosedUnderIsomorphisms :=
    ⟨fun {_ _} e hK n ↦ B.prop_of_iso
      ((@DerivedCategory.homologyFunctor A _ _ h₂ n).mapIso e) (hK n)⟩
  (modelEquiv h₁ h₂).congrFullSubcategory
    (funext fun K ↦ propext (derivedCategoryB_modelEquiv_functor_obj_iff B h₁ h₂ K))

/-- The comparison equivalence of `D_B(A)` at two models is additive: it is the restriction of the
comparison equivalence of the two derived categories, which is additive
(`StacksDraft.DerivedModel.modelEquiv_functor_additive`).

Like that statement it is a theorem rather than an instance: when `B` is stated over a category
only definitionally equal to `A`, such as `SheafOfModules.isQuasicoherent X.ringCatSheaf` with
`A = X.Modules`, instance search does not unify it with the goal. -/
theorem derivedCategoryBModelEquiv_functor_additive (B : ObjectProperty A)
    [B.IsClosedUnderIsomorphisms] (h₁ : HasDerivedCategory.{w} A)
    (h₂ : HasDerivedCategory.{z} A) : (derivedCategoryBModelEquiv B h₁ h₂).functor.Additive where
  map_add := InducedCategory.hom_ext (modelEquiv_functor_additive h₁ h₂).map_add

end StacksDraft.DerivedModel

end

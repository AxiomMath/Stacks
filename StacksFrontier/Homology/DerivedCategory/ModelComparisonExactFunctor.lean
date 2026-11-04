module

public import StacksFrontier.Homology.DerivedCategory.ModelComparison

/-!
# Exact functors on derived categories commute with the model comparison

`HasDerivedCategory.{w} C` is a *chosen* localization of the cochain complexes of `C` at the
quasi-isomorphisms, and `StacksDraft.DerivedModel.modelEquiv h₁ h₂` compares two such choices.
For an exact functor `F : C ⥤ D` of abelian categories, `F.mapDerivedCategory` is defined for
every pair of chosen models on the source and on the target. This file proves that the
comparison equivalences intertwine those functors, on either side:

* `StacksDraft.DerivedModel.modelEquivCompMapDerivedCategoryIso`: changing the model of the
  **source** first and then applying `F` is applying `F` from the old model;
* `StacksDraft.DerivedModel.mapDerivedCategoryCompModelEquivIso`: applying `F` and then changing
  the model of the **target** is applying `F` into the new model.

Both are the unique natural isomorphisms compatible with the factorizations
`Functor.mapDerivedCategoryFactors` through the localization functors, obtained by
`CategoryTheory.Localization.liftNatIso`, exactly as
`StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso` does for the cohomology functors.

These are the general bridges that transport any statement phrased through an exact functor on
derived categories — for instance restriction to an open, as in
`Stacks.Duality.HasDualizingModelOn` — from one model to another.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u v u' v' w z w'

namespace StacksDraft.DerivedModel

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **Changing the model of the source commutes with an exact functor.** For chosen models
`h₁`, `h₂` of `D(C)` and `hD` of `D(D)`, carrying an object of the first model of `D(C)` to the
second and then applying `F` is the same as applying `F` from the first model. -/
def modelEquivCompMapDerivedCategoryIso (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{z} C) (hD : HasDerivedCategory.{w'} D) :
    (modelEquiv h₁ h₂).functor ⋙ @Functor.mapDerivedCategory C _ _ h₂ D _ _ hD F _ _ _ ≅
      @Functor.mapDerivedCategory C _ _ h₁ D _ _ hD F _ _ _ :=
  letI := h₁
  letI _l₁ : Localization.Lifting (@DerivedCategory.Q C _ _ h₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD)
      ((modelEquiv h₁ h₂).functor ⋙
        @Functor.mapDerivedCategory C _ _ h₂ D _ _ hD F _ _ _) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (modelCompQIso h₁ h₂) _ ≪≫
      @Functor.mapDerivedCategoryFactors C _ _ h₂ D _ _ hD F _ _ _⟩
  letI _l₂ : Localization.Lifting (@DerivedCategory.Q C _ _ h₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD)
      (@Functor.mapDerivedCategory C _ _ h₁ D _ _ hD F _ _ _) :=
    ⟨@Functor.mapDerivedCategoryFactors C _ _ h₁ D _ _ hD F _ _ _⟩
  Localization.liftNatIso (@DerivedCategory.Q C _ _ h₁)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD)
    _ _ (Iso.refl _)

/-- **Changing the model of the target commutes with an exact functor.** For a chosen model `h`
of `D(C)` and chosen models `hD₁`, `hD₂` of `D(D)`, applying `F` into the first model of `D(D)`
and then carrying the result to the second is the same as applying `F` into the second model. -/
def mapDerivedCategoryCompModelEquivIso (h : HasDerivedCategory.{w} C)
    (hD₁ : HasDerivedCategory.{z} D) (hD₂ : HasDerivedCategory.{w'} D) :
    @Functor.mapDerivedCategory C _ _ h D _ _ hD₁ F _ _ _ ⋙ (modelEquiv hD₁ hD₂).functor ≅
      @Functor.mapDerivedCategory C _ _ h D _ _ hD₂ F _ _ _ :=
  letI := h
  letI _l₁ : Localization.Lifting (@DerivedCategory.Q C _ _ h)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD₂)
      (@Functor.mapDerivedCategory C _ _ h D _ _ hD₁ F _ _ _ ⋙ (modelEquiv hD₁ hD₂).functor) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (@Functor.mapDerivedCategoryFactors C _ _ h D _ _ hD₁ F _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (modelCompQIso hD₁ hD₂)⟩
  letI _l₂ : Localization.Lifting (@DerivedCategory.Q C _ _ h)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD₂)
      (@Functor.mapDerivedCategory C _ _ h D _ _ hD₂ F _ _ _) :=
    ⟨@Functor.mapDerivedCategoryFactors C _ _ h D _ _ hD₂ F _ _ _⟩
  Localization.liftNatIso (@DerivedCategory.Q C _ _ h)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD₂)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ hD₂)
    _ _ (Iso.refl _)

end StacksDraft.DerivedModel

end

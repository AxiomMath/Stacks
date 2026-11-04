module

public import StacksFrontier.Homology.DerivedCategory.ModelComparison

/-!
# The functor induced by an exact functor, read at two models of the derived category

`HasDerivedCategory.{w} C` is the assumption that a localization of `CochainComplex C ℤ` at the
quasi-isomorphisms has been *chosen*, so two such assumptions give two categories
`DerivedCategory C` and a statement proved at one says nothing about the other until it is
transported. `StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport` supplies the
transport for the two *derived* functors of interest, `Rf_*` and `Lf^*`, each as an instance of
the uniqueness of a total derived functor. It does not supply it for
`CategoryTheory.Functor.mapDerivedCategory`, the functor induced on derived categories by an
exact functor, which is what restriction of modules along an open immersion gives.

This file supplies it. No derived-functor uniqueness is needed: `mapDerivedCategory` is a
lifting of `F.mapHomologicalComplex ⋙ Q` through the localization `Q`, in every model, so the
two readings become equal after composing with the localization functor of the source model and
`CategoryTheory.Localization.liftNatIso` turns that equality into an isomorphism of the two
functors on the derived category. The two `CategoryTheory.Localization.Lifting` instances are
supplied by hand, neither functor being syntactically a composite with `Q`.

## Main definitions

* `StacksDraft.DerivedModel.mapDerivedCategoryModelIso` — the functor induced by an exact functor
  on the derived categories, read at two models of the source and two of the target, agrees up to
  the comparison equivalences.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ w z w' z'

namespace StacksDraft.DerivedModel

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **The functor induced by an exact functor, read at two models.** For an exact functor
`F : C ⥤ D` and chosen derived categories `h₁, h₂` of `C` and `k₁, k₂` of `D`, the induced
functors `F.mapDerivedCategory` at `(h₁, k₁)` and at `(h₂, k₂)` agree up to the comparison
equivalences of the two models on source and target.

Both sides become `F.mapHomologicalComplex ⋙ Q` after composing with the localization functor of
the model `h₁`: for the left-hand side by `CategoryTheory.Functor.mapDerivedCategoryFactors` at
`(h₁, k₁)` followed by `StacksDraft.DerivedModel.modelCompQIso` on the target, for the
right-hand side by `modelCompQIso` on the source followed by `mapDerivedCategoryFactors` at
`(h₂, k₂)`. -/
def mapDerivedCategoryModelIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    (k₁ : HasDerivedCategory.{w'} D) (k₂ : HasDerivedCategory.{z'} D) :
    @Functor.mapDerivedCategory C _ _ h₁ D _ _ k₁ F _ _ _ ⋙ (modelEquiv k₁ k₂).functor ≅
      (modelEquiv h₁ h₂).functor ⋙ @Functor.mapDerivedCategory C _ _ h₂ D _ _ k₂ F _ _ _ :=
  letI := h₁
  letI _l₁ : Localization.Lifting (@DerivedCategory.Q C _ _ h₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ k₂)
      (@Functor.mapDerivedCategory C _ _ h₁ D _ _ k₁ F _ _ _ ⋙
        (modelEquiv k₁ k₂).functor) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactors C _ _ h₁ D _ _ k₁ F _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (modelCompQIso k₁ k₂)⟩
  letI _l₂ : Localization.Lifting (@DerivedCategory.Q C _ _ h₁)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ k₂)
      ((modelEquiv h₁ h₂).functor ⋙
        @Functor.mapDerivedCategory C _ _ h₂ D _ _ k₂ F _ _ _) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (modelCompQIso h₁ h₂) _ ≪≫
      @Functor.mapDerivedCategoryFactors C _ _ h₂ D _ _ k₂ F _ _ _⟩
  Localization.liftNatIso (@DerivedCategory.Q C _ _ h₁)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ k₂)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q D _ _ k₂)
    (@Functor.mapDerivedCategory C _ _ h₁ D _ _ k₁ F _ _ _ ⋙ (modelEquiv k₁ k₂).functor)
    ((modelEquiv h₁ h₂).functor ⋙ @Functor.mapDerivedCategory C _ _ h₂ D _ _ k₂ F _ _ _)
    (Iso.refl _)

end StacksDraft.DerivedModel

end

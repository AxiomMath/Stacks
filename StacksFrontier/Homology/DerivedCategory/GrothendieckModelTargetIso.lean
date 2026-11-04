module

public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel

/-!
# Changing the target model of a derived functor

Let `C` be a Grothendieck abelian category and `G : C₁ ⥤ C` an exact functor. The derived functor
of `G` into the standard model of `D(C)`, followed by the comparison equivalence
`grothendieckModelEquiv C`, is the derived functor of `G` computed directly into the model
`hasDerivedCategory_of_isGrothendieckAbelian C`.

## Main definitions

* `Stacks.Injectives.mapDerivedCategoryTargetModelIso`: the isomorphism between the two derived
  functors of `G`.
* `Stacks.Injectives.isoOfTargetModelIso`: an isomorphism between values of derived functors into
  the model `hasDerivedCategory_of_isGrothendieckAbelian C`, as an isomorphism between their values
  into the standard model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u w' v₂ u₂

namespace Stacks.Injectives

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

attribute [local instance] locallySmall_standardDerivedCategory

variable {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [hd₂ : HasDerivedCategory.{w'} C₂]
  (F : C ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section TargetModel

variable {C₁ : Type u₂} [Category.{v₂} C₁] [Abelian C₁] [hd₁ : HasDerivedCategory.{w'} C₁]
  (G : C₁ ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The derived functor of `G` into the standard model of `D(C)`, followed by the comparison
equivalence `grothendieckModelEquiv C`, is isomorphic to the derived functor of `G` into the model
`hasDerivedCategory_of_isGrothendieckAbelian C`. -/
def mapDerivedCategoryTargetModelIso :
    @Functor.mapDerivedCategory C₁ _ _ hd₁ C _ _ (HasDerivedCategory.standard C) G _ _ _ ⋙
        (grothendieckModelEquiv.{w} C).functor ≅
      @Functor.mapDerivedCategory C₁ _ _ hd₁ C _ _
        (hasDerivedCategory_of_isGrothendieckAbelian.{w} C) G _ _ _ :=
  letI inst := hasDerivedCategory_of_isGrothendieckAbelian.{w} C
  letI model : CochainComplex C₁ ℤ ⥤ @DerivedCategory C _ _ inst :=
    G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q C _ _ inst
  letI : Localization.Lifting (@DerivedCategory.Q C₁ _ _ hd₁)
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) model
      (@Functor.mapDerivedCategory C₁ _ _ hd₁ C _ _ (HasDerivedCategory.standard C) G _ _ _ ⋙
        (grothendieckModelEquiv.{w} C).functor) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactors C₁ _ _ hd₁ C _ _ (HasDerivedCategory.standard C)
          G _ _ _) (grothendieckModelEquiv.{w} C).functor ≪≫ Functor.associator _ _ _⟩
  Localization.liftNatIso (@DerivedCategory.Q C₁ _ _ hd₁)
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) model model
    (@Functor.mapDerivedCategory C₁ _ _ hd₁ C _ _ (HasDerivedCategory.standard C) G _ _ _ ⋙
      (grothendieckModelEquiv.{w} C).functor)
    (@Functor.mapDerivedCategory C₁ _ _ hd₁ C _ _ inst G _ _ _) (Iso.refl _)

/-- An isomorphism between values of the derived functors of two exact functors into the model
`hasDerivedCategory_of_isGrothendieckAbelian C` gives an isomorphism between the values of the
derived functors of the same functors into the standard model. -/
def isoOfTargetModelIso {C₂ : Type*} [Category C₂] [Abelian C₂] [hd₂ : HasDerivedCategory C₂]
    (G₂ : C₂ ⥤ C) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (K : @DerivedCategory C₁ _ _ hd₁) (L : @DerivedCategory C₂ _ _ hd₂)
    (e : (@Functor.mapDerivedCategory C₁ _ _ hd₁ C _ _
        (hasDerivedCategory_of_isGrothendieckAbelian.{w} C) G _ _ _).obj K ≅
      (@Functor.mapDerivedCategory C₂ _ _ hd₂ C _ _
        (hasDerivedCategory_of_isGrothendieckAbelian.{w} C) G₂ _ _ _).obj L) :
    (@Functor.mapDerivedCategory C₁ _ _ hd₁ C _ _ (HasDerivedCategory.standard C) G _ _ _).obj K ≅
      (@Functor.mapDerivedCategory C₂ _ _ hd₂ C _ _ (HasDerivedCategory.standard C)
        G₂ _ _ _).obj L :=
  (grothendieckModelEquiv.{w} C).fullyFaithfulFunctor.preimageIso
    ((mapDerivedCategoryTargetModelIso C G).app K ≪≫ e ≪≫
      ((mapDerivedCategoryTargetModelIso C G₂).app L).symm)

end TargetModel

end Stacks.Injectives

end

module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility

/-!
# The canonical map of Tag 08I3 against evaluation
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

noncomputable section

namespace Transpose

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)

/-- **The comparison of a functor with internal hom, against a morphism into the internal hom.**
For `x : C ⟶ hom(A, B)`, the transpose of `P x` followed by the comparison
`P(hom(A, B)) ⟶ hom(P A, P B)` is the monoidality comparison followed by `P` of the transpose of
`x`.  At `x = 𝟙` this is `homComparison_adjoint`; the general case is its naturality. -/
theorem map_comp_homComparison_adjoint (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁)
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂) {C A B : D₁} (x : C ⟶ (H₁.obj (op A)).obj B) :
    e₂ (P.obj C) (P.obj A) (P.obj B) (P.map x ≫ homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B) =
      m.inv.app (C, A) ≫ P.map (e₁ C A B x) := by
  have h1 : e₁ C A B x = T₁.map (x ×ₘ 𝟙 A) ≫ evaluation H₁ T₁ e₁ A B := by
    have := hnat₁ C ((H₁.obj (op A)).obj B) A B x (𝟙 _)
    rw [Category.comp_id] at this
    exact this
  have h2 := m.inv.naturality (x ×ₘ 𝟙 A)
  rw [hnat₂, homComparison_adjoint, homComparisonDatum, h1, P.map_comp, ← Category.assoc,
    ← Category.assoc]
  congr 1
  refine Eq.trans ?_ h2
  simp

end Transpose

section RingedSpaces

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- The canonical map of Tag 08I3 is the transpose construction at its defining data. -/
theorem derivedPullbackSheafHomMap_eq_homComparison
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    derivedPullbackSheafHomMap h K L = Transpose.homComparison (derivedPullbackFunctor h)
      (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Y)
      (internalHomTensorUncurried X) (tensorHomEquiv Y) (tensorHomEquiv X) (pullbackTensorIso h)
      K L :=
  rfl

/-- The transpose datum of the canonical map of Tag 08I3 is the monoidality comparison followed
by the derived pullback of the evaluation. -/
theorem homComparisonDatum_derivedPullback
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    Transpose.homComparisonDatum (derivedPullbackFunctor h)
      (Stacks.SheafOfModules.derivedSheafHom Y.sheaf) (internalHomTensorUncurried Y)
      (internalHomTensorUncurried X) (tensorHomEquiv Y) (pullbackTensorIso h) K L =
    (pullbackTensorIso h).inv.app
          (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op K)).obj L, K) ≫
        (derivedPullbackFunctor h).map (derivedEvaluation K L) :=
  rfl

/-- **The transpose of the canonical map of Tag 08I3** is the monoidality comparison of Tag 079U
followed by the derived pullback of the evaluation.  This is the recipe the map is built from,
`Transpose.homComparison_adjoint`, at the data `derivedPullbackSheafHomMap` is defined with. -/
theorem tensorHomEquiv_derivedPullbackSheafHomMap
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    tensorHomEquiv X _ _ _ (derivedPullbackSheafHomMap h K L) =
      (pullbackTensorIso h).inv.app
          (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op K)).obj L, K) ≫
        (derivedPullbackFunctor h).map (derivedEvaluation K L) := by
  have hh := Transpose.homComparison_adjoint (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Y)
    (internalHomTensorUncurried X) (tensorHomEquiv Y) (tensorHomEquiv X) (pullbackTensorIso h) K L
  convert hh using 2 <;>
    first
      | exact derivedPullbackSheafHomMap_eq_homComparison h K L
      | exact (homComparisonDatum_derivedPullback h K L).symm

/-- **The canonical map of Tag 08I3 against a morphism into the derived internal hom.**  For
`x : C ⟶ R𝓗om(K, L)` the transpose of `Lh^*x` followed by the canonical map
`Lh^*R𝓗om(K, L) ⟶ R𝓗om(Lh^*K, Lh^*L)` is the monoidality comparison of Tag 079U followed by the
derived pullback of the transpose of `x`. -/
theorem tensorHomEquiv_map_comp_derivedPullbackSheafHomMap
    {C K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (x : C ⟶ ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op K)).obj L) :
    tensorHomEquiv X _ _ _ ((derivedPullbackFunctor h).map x ≫ derivedPullbackSheafHomMap h K L) =
      (pullbackTensorIso h).inv.app (C, K) ≫
        (derivedPullbackFunctor h).map (tensorHomEquiv Y _ _ _ x) := by
  have hh := Transpose.map_comp_homComparison_adjoint (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Y)
    (internalHomTensorUncurried X) (tensorHomEquiv Y) (tensorHomEquiv X) (pullbackTensorIso h)
    (tensorHomEquivNaturalLeft_ringedSpace Y) (tensorHomEquivNaturalLeft_ringedSpace X) x
  convert hh using 2
  exact congrArg _ (derivedPullbackSheafHomMap_eq_homComparison h K L)

end RingedSpaces

end

end Stacks.Cohomology.DerivedInternalHomPullback

end

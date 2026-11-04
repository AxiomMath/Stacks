module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel

/-!
# Transporting weak generation between two models of the derived category

`StacksDraft.DerivedModel.modelEquiv h₁ h₂` compares two chosen models of `D(C)`. A statement of
the form "an object `E` receiving only zero maps from the shifts of `Q(K)` is zero" proved at one
model holds at the other: the comparison identifies the two localizations of a cochain complex,
commutes with the cohomology functors, and is an equivalence. This file records the three
transports this needs.

## Main results

* `StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff`: membership in a
  subcategory `D_B(C)` defined by the cohomology objects is the same at both models.
* `StacksDraft.DerivedModel.isZero_of_isZero_modelEquiv_functor_obj`: the comparison reflects zero
  objects.
* `StacksDraft.DerivedModel.forall_hom_shift_eq_zero_modelEquiv`: if every morphism from a shift
  of `Q(K)` to `E` vanishes at one model, then every morphism from a shift of `Q(K)` to the image
  of `E` vanishes at the other model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w z

namespace StacksDraft.DerivedModel

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The comparison of two models reflects zero objects**, being an equivalence. -/
theorem isZero_of_isZero_modelEquiv_functor_obj (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{z} C) (E : @DerivedCategory C _ _ h₁)
    (h : IsZero ((modelEquiv h₁ h₂).functor.obj E)) : IsZero E :=
  IsZero.of_iso ((modelEquiv h₁ h₂).inverse.map_isZero h) ((modelEquiv h₁ h₂).unitIso.app E)

/-- The shift of the localization of a cochain complex at the second model is the image under the
comparison of its shift at the first model. -/
def modelEquivQShiftIso (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    (K : CochainComplex C ℤ) (n : ℤ) :
    letI := h₂
    ((DerivedCategory.Q).obj K)⟦n⟧ ≅
      (modelEquiv h₁ h₂).functor.obj (letI := h₁; ((DerivedCategory.Q).obj K)⟦n⟧) :=
  letI := h₂
  ((DerivedCategory.Q.commShiftIso n).app K).symm ≪≫
    ((modelCompQIso h₁ h₂).app (K⟦n⟧)).symm ≪≫
    (modelEquiv h₁ h₂).functor.mapIso (letI := h₁; (DerivedCategory.Q.commShiftIso n).app K)

/-- **Orthogonality to the shifts of a localized complex transports between models.** If every
morphism `Q(K)[n] ⟶ E` vanishes at the first model, then every morphism `Q(K)[n] ⟶ E'` vanishes at
the second, `E'` the image of `E` under the comparison: the comparison is fully faithful and
carries `Q(K)[n]` to `Q(K)[n]`. -/
theorem forall_hom_shift_eq_zero_modelEquiv (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{z} C) (K : CochainComplex C ℤ) (E : @DerivedCategory C _ _ h₁)
    (h : letI := h₁; ∀ (n : ℤ) (g : ((DerivedCategory.Q).obj K)⟦n⟧ ⟶ E), g = 0) :
    letI := h₂
    ∀ (n : ℤ) (g : ((DerivedCategory.Q).obj K)⟦n⟧ ⟶ (modelEquiv h₁ h₂).functor.obj E), g = 0 := by
  intro n g
  have hpre := h n ((modelEquiv h₁ h₂).fullyFaithfulFunctor.preimage
    ((modelEquivQShiftIso h₁ h₂ K n).inv ≫ g))
  have hz : (modelEquivQShiftIso h₁ h₂ K n).inv ≫ g = 0 := by
    have := congrArg (modelEquiv h₁ h₂).functor.map hpre
    rw [Functor.FullyFaithful.map_preimage] at this
    rw [this]
    have : (modelEquiv h₁ h₂).functor.PreservesZeroMorphisms := by
      have := modelEquiv_functor_additive h₁ h₂
      infer_instance
    exact Functor.map_zero _ _ _
  rw [← cancel_epi (modelEquivQShiftIso h₁ h₂ K n).inv, hz, comp_zero]

end StacksDraft.DerivedModel

end

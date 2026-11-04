module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import StacksCore.Tactic.StacksAttribute

/-! ## Preadditive structure on the localization -/

add_to_stacks 05QD CategoryTheory.Localization.functor_additive
add_to_stacks 05QD CategoryTheory.Localization.preadditive
add_to_stacks 05QE CategoryTheory.Localization.instAdditiveLocalizationQ

@[expose] public section

namespace CategoryTheory.Localization

open Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.PreservesZeroMorphisms]

/-- An object `X` is sent to zero by a zero-morphism-preserving localization functor for a
morphism property `W` with left calculus of fractions if and only if the zero morphism
`0 : X ⟶ Y` belongs to `W` for some object `Y`. -/
@[stacks 05QF "1 ↔ 2"]
lemma isZero_obj_iff [W.HasLeftCalculusOfFractions] (X : C) :
    IsZero (L.obj X) ↔ ∃ (Y : C), W (0 : X ⟶ Y) := by
  refine ⟨fun hX ↦ ?_, fun ⟨Y, hY⟩ ↦ ?_⟩
  · obtain ⟨Y, s, hs, fac⟩ := (MorphismProperty.map_eq_iff_postcomp L W (𝟙 X) 0).1
      (by rw [L.map_id, L.map_zero]; exact hX.eq_zero_of_src _)
    use Y, by simp_all
  · have := inverts L W _ hY
    exact .of_mono_eq_zero (L.map (0 : X ⟶ Y)) (L.map_zero _ _)

/-- An object `X` is sent to zero by a zero-morphism-preserving localization functor for a
morphism property `W` with right calculus of fractions if and only if the zero morphism
`0 : Z ⟶ X` belongs to `W` for some object `Z`. -/
@[stacks 05QF "1 ↔ 3"]
lemma isZero_obj_iff' [W.HasRightCalculusOfFractions] (X : C) :
    IsZero (L.obj X) ↔ ∃ (Z : C), W (0 : Z ⟶ X) := by
  refine ⟨fun hX ↦ ?_, fun ⟨Z, hZ⟩ ↦ have := inverts L W _ hZ;
    .of_epi_eq_zero (L.map (0 : Z ⟶ X)) (L.map_zero _ _)⟩
  obtain ⟨Z, s, hs, fac⟩ := (MorphismProperty.map_eq_iff_precomp L W (𝟙 X) 0).1
      (by rw [L.map_id, L.map_zero]; exact hX.eq_zero_of_src _)
  rw [Category.comp_id, comp_zero] at fac
  exact ⟨Z, fac ▸ hs⟩

end CategoryTheory.Localization

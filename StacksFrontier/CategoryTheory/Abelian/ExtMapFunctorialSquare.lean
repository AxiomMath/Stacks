module

public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Exact functors commuting up to isomorphism act compatibly on `Ext`

Let `L₁ : C₁ ⥤ C₂` and `L₂ : D₁ ⥤ D₂` be fully faithful exact functors preserving injective
objects, and `I₁ : C₁ ⥤ D₁`, `I₂ : C₂ ⥤ D₂` exact functors with `L₁ ⋙ I₂ ≅ I₁ ⋙ L₂`. Then the
map induced by `I₁` on `Ext^n(Z, G)` is bijective (surjective) exactly when the map induced by
`I₂` on `Ext^n(Z', L₁ G)` is, for any `Z'` isomorphic to `L₁ Z`. This is what transports
statements about restriction maps on cohomology along a change of coefficient universe.

## Main results

* `Stacks.ExtFunctorial.bijective_mapExt_iff_of_iso`,
  `Stacks.ExtFunctorial.surjective_mapExt_iff_of_iso`: the transport.
* `Stacks.ExtFunctorial.bijective_mk₀_comp`, `Stacks.ExtFunctorial.bijective_comp_mk₀`:
  composing with the class of an isomorphism is bijective.
-/

@[expose] public noncomputable section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.ExtFunctorial

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Two maps related by bijections on both sides are bijective together and surjective
together. -/
theorem bijective_iff_and_surjective_iff_of_comp_eq {α β γ δ : Type*} {f : α → β} {g : γ → δ}
    {a : α → γ} {b : β → δ} (ha : Function.Bijective a) (hb : Function.Bijective b)
    (h : ∀ x, g (a x) = b (f x)) :
    (Function.Bijective f ↔ Function.Bijective g) ∧
      (Function.Surjective f ↔ Function.Surjective g) := by
  have hc : b ∘ f = g ∘ a := funext fun x ↦ (h x).symm
  constructor
  · rw [← hb.of_comp_iff' f, hc, Function.Bijective.of_comp_iff g ha]
  · rw [← Function.Surjective.of_comp_iff' hb f, hc, Function.Surjective.of_comp_iff g ha.2]

section Comp

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]

/-- Composing on the left with the class of an isomorphism is bijective on `Ext`. -/
theorem bijective_mk₀_comp {X X' Y : C} (e : X ≅ X') (n : ℕ) :
    Function.Bijective (fun z : Ext.{w₁} X' Y n ↦ (Ext.mk₀ e.hom).comp z (zero_add n)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z ↦ (Ext.mk₀ e.inv).comp z (zero_add n), fun z ↦ ?_, fun z ↦ ?_⟩ <;>
    simp [Ext.mk₀_comp_mk₀_assoc]

/-- Composing on the right with the class of an isomorphism is bijective on `Ext`. -/
theorem bijective_comp_mk₀ {X Y Y' : C} (e : Y ≅ Y') (n : ℕ) :
    Function.Bijective (fun z : Ext.{w₁} X Y n ↦ z.comp (Ext.mk₀ e.hom) (add_zero n)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z ↦ z.comp (Ext.mk₀ e.inv) (add_zero n), fun z ↦ ?_, fun z ↦ ?_⟩ <;>
    simp [Ext.mk₀_comp_mk₀]

end Comp

section Square

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{w₁} C₁] [EnoughInjectives C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{w₂} C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] [Abelian D₁] [HasExt.{w₃} D₁] [EnoughInjectives D₁]
  {D₂ : Type u₄} [Category.{v₄} D₂] [Abelian D₂] [HasExt.{w₄} D₂]
  (L₁ : C₁ ⥤ C₂) [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [L₁.Full] [L₁.Faithful] [L₁.PreservesInjectiveObjects]
  (L₂ : D₁ ⥤ D₂) [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [L₂.Full] [L₂.Faithful] [L₂.PreservesInjectiveObjects]
  (I₁ : C₁ ⥤ D₁) [I₁.Additive] [PreservesFiniteLimits I₁] [PreservesFiniteColimits I₁]
  (I₂ : C₂ ⥤ D₂) [I₂.Additive] [PreservesFiniteLimits I₂] [PreservesFiniteColimits I₂]
  (β : L₁ ⋙ I₂ ≅ I₁ ⋙ L₂) {Z : C₁} {Z' : C₂} (eZ : L₁.obj Z ≅ Z') (G : C₁) (n : ℕ)

include β eZ

/-- The square relating the maps induced by `I₁` and `I₂` on `Ext`, with bijections on both
sides. -/
theorem mapExt_square_bijective :
    (Function.Bijective (I₁.mapExtAddHom Z G n) ↔
      Function.Bijective (I₂.mapExtAddHom Z' (L₁.obj G) n)) ∧
    (Function.Surjective (I₁.mapExtAddHom Z G n) ↔
      Function.Surjective (I₂.mapExtAddHom Z' (L₁.obj G) n)) := by
  have hA := L₁.mapExt_bijective_of_preservesInjectiveObjects Z G n
  have hB := bijective_mk₀_comp (C := C₂) (Y := L₁.obj G) eZ.symm n
  have hC := L₂.mapExt_bijective_of_preservesInjectiveObjects (I₁.obj Z) (I₁.obj G) n
  have hΦ₁ := bijective_mk₀_comp (C := D₂) (Y := L₂.obj (I₁.obj G))
    ((I₂.mapIso eZ).symm ≪≫ β.app Z) n
  have hΦ₂ := bijective_comp_mk₀ (C := D₂) (X := I₂.obj Z') (β.app G).symm n
  refine bijective_iff_and_surjective_iff_of_comp_eq (hB.comp hA)
    (hΦ₂.comp (hΦ₁.comp hC)) (fun x ↦ ?_)
  simp only [Function.comp_apply, Functor.mapExtAddHom_apply, Iso.symm_hom, Iso.trans_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    mapExactFunctor_comp_functor L₁ I₂ Z n x,
    mapExactFunctor_comp_functor I₁ L₂ Z n x, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, mk₀_comp_mapExactFunctor β.hom Z n x,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_app, Ext.comp_mk₀_id]

/-- **Bijectivity of the map induced on `Ext` is transported along the square.** -/
theorem bijective_mapExt_iff_of_iso :
    Function.Bijective (I₁.mapExtAddHom Z G n) ↔
      Function.Bijective (I₂.mapExtAddHom Z' (L₁.obj G) n) :=
  (mapExt_square_bijective L₁ L₂ I₁ I₂ β eZ G n).1

/-- **Surjectivity of the map induced on `Ext` is transported along the square.** -/
theorem surjective_mapExt_iff_of_iso :
    Function.Surjective (I₁.mapExtAddHom Z G n) ↔
      Function.Surjective (I₂.mapExtAddHom Z' (L₁.obj G) n) :=
  (mapExt_square_bijective L₁ L₂ I₁ I₂ β eZ G n).2

end Square

end Stacks.ExtFunctorial

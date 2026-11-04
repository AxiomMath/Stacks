module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flatness of a product of two modules

A product of two modules is flat if and only if both factors are flat. Each factor is a
direct summand of the product, so flatness passes to it by retraction; conversely the
isomorphism `N ⊗ (X × Y) ≃ (N ⊗ X) × (N ⊗ Y)` of `TensorProduct.prodRight` turns injectivity
of the two maps `N ⊗ X → P ⊗ X` and `N ⊗ Y → P ⊗ Y` into injectivity of
`N ⊗ (X × Y) → P ⊗ (X × Y)`.

## Main results

* `Module.Flat.of_prod_left` and `Module.Flat.of_prod_right`: a factor of a flat product is
  flat.
* `Module.Flat.prod`: a product of two flat modules is flat.
* `Module.Flat.prod_iff`: a product of two modules is flat if and only if both factors are.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

section Prod

variable {T : Type u} [CommRing T] {X : Type v} [AddCommGroup X] [Module T X] {Y : Type w}
  [AddCommGroup Y] [Module T Y]

/-- A direct summand of a flat module is flat: the first factor of a flat product is flat. -/
theorem Module.Flat.of_prod_left [Module.Flat T (X × Y)] : Module.Flat T X :=
  Module.Flat.of_retract (LinearMap.inl T X Y) (LinearMap.fst T X Y)
    (LinearMap.fst_comp_inl T X Y)

/-- A direct summand of a flat module is flat: the second factor of a flat product is flat. -/
theorem Module.Flat.of_prod_right [Module.Flat T (X × Y)] : Module.Flat T Y :=
  Module.Flat.of_retract (LinearMap.inr T X Y) (LinearMap.snd T X Y)
    (LinearMap.snd_comp_inr T X Y)

/-- A product of two flat modules is flat. -/
theorem Module.Flat.prod [Module.Flat T X] [Module.Flat T Y] : Module.Flat T (X × Y) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ N
  have hX : Function.Injective (N.subtype.rTensor X) :=
    (Module.Flat.iff_rTensor_injectiveₛ.mp ‹Module.Flat T X›) N
  have hY : Function.Injective (N.subtype.rTensor Y) :=
    (Module.Flat.iff_rTensor_injectiveₛ.mp ‹Module.Flat T Y›) N
  have key : (TensorProduct.prodRight T T P X Y).toLinearMap ∘ₗ N.subtype.rTensor (X × Y) =
      LinearMap.prodMap (N.subtype.rTensor X) (N.subtype.rTensor Y) ∘ₗ
        (TensorProduct.prodRight T T N X Y).toLinearMap := by
    refine TensorProduct.ext' fun n p => ?_
    obtain ⟨x, y⟩ := p
    rfl
  intro z z' hzz'
  have hz := DFunLike.congr_fun key z
  have hz' := DFunLike.congr_fun key z'
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.prodMap_apply, Prod.ext_iff] at hz hz'
  refine (TensorProduct.prodRight T T N X Y).injective (Prod.ext (hX ?_) (hY ?_))
  · rw [← hz.1, ← hz'.1, hzz']
  · rw [← hz.2, ← hz'.2, hzz']

/-- A product of two modules is flat if and only if both factors are flat. -/
theorem Module.Flat.prod_iff : Module.Flat T (X × Y) ↔ Module.Flat T X ∧ Module.Flat T Y := by
  refine ⟨fun _ => ⟨Module.Flat.of_prod_left (Y := Y), Module.Flat.of_prod_right (X := X)⟩,
    fun h => ?_⟩
  obtain ⟨_, _⟩ := h
  exact Module.Flat.prod

end Prod

end

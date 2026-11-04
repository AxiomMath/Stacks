module

public import Mathlib.CategoryTheory.Products.Basic

/-!
# Linear morphisms out of a unital algebra are determined by their value at the unit

Let `T : C × C ⥤ C` be a bifunctor (in the application, the derived tensor product of `D(𝒪_X)`),
`A` an object with an action `μ : T(A, A) ⟶ A` and a morphism `u : O ⟶ A` (the unit) for which
`T(u, 1) ≫ μ : T(O, A) ⟶ A` is invertible (the unit law), and `N` an object with an action
`ν : T(N, A) ⟶ N`. A morphism `F : A ⟶ N` is `A`-linear if `T(F, 1) ≫ ν = μ ≫ F`. Two linear
morphisms which agree after `u` are equal: `(T(u, 1) ≫ μ) ≫ F = T(u ≫ F, 1) ≫ ν`. This is the
argument by which Differential Graded Sheaves, Section 0FU3, reads a module map out of the
regular module off its value at `1`; Remark 0FU7 supplies the linearity of `ξ' : Ω^• ⟶ Ω^•[n]`
(`AlgebraicGeometry.SheafOfModules.derivedForgetShiftedHom_derivedAction`).

## Main results

* `CategoryTheory.eq_of_comp_eq_of_linear`.

## References

* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public section

open scoped CategoryTheory.Prod

namespace CategoryTheory

/-- **Linear morphisms out of a unital algebra are determined after the unit.** Let `T` be a
bifunctor, `μ : T(A, A) ⟶ A` and `ν : T(N, A) ⟶ N` actions and `u : O ⟶ A` a morphism with
`T(u, 1) ≫ μ` invertible. Two morphisms `F₁ F₂ : A ⟶ N` with `T(F_i, 1) ≫ ν = μ ≫ F_i` and
`u ≫ F₁ = u ≫ F₂` are equal: both satisfy `(T(u, 1) ≫ μ) ≫ F_i = T(u ≫ F_i, 1) ≫ ν`. -/
theorem eq_of_comp_eq_of_linear {C : Type*} [Category* C] (T : C × C ⥤ C) {O A N : C}
    (u : O ⟶ A) (μ : T.obj (A, A) ⟶ A) (ν : T.obj (N, A) ⟶ N)
    [IsIso (T.map (u ×ₘ 𝟙 A) ≫ μ)] {F₁ F₂ : A ⟶ N}
    (h₁ : T.map (F₁ ×ₘ 𝟙 A) ≫ ν = μ ≫ F₁) (h₂ : T.map (F₂ ×ₘ 𝟙 A) ≫ ν = μ ≫ F₂)
    (hu : u ≫ F₁ = u ≫ F₂) : F₁ = F₂ := by
  have key : ∀ F : A ⟶ N, T.map (F ×ₘ 𝟙 A) ≫ ν = μ ≫ F →
      (T.map (u ×ₘ 𝟙 A) ≫ μ) ≫ F = T.map ((u ≫ F) ×ₘ 𝟙 A) ≫ ν := by
    intro F hF
    rw [Category.assoc, ← hF, ← Category.assoc, ← T.map_comp, prod_comp, Category.comp_id]
  rw [← cancel_epi (T.map (u ×ₘ 𝟙 A) ≫ μ), key F₁ h₁, key F₂ h₂, hu]

end CategoryTheory

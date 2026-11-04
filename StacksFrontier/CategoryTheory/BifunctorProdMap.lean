module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Splitting a bifunctor applied to a pair of morphisms

A functor `B : C₁ × C₂ ⥤ C₃` out of a product category is applied to a morphism `x ×ₘ z` of the
product.  When one of the two components is itself a composition, the image splits as a
composition in `C₃`, and the splitting can be arranged so that each factor moves only one of the
two components.  This file collects those elementary rewriting lemmas, together with the
naturality of a comparison of two bifunctors along a functor, written one component at a time.

Both are the bookkeeping that every adjunction calculus over a bifunctor runs on: the relative
cup product of [Stacks, Tag 0B68] and of [Stacks, Tag 0B6C] is built from a comparison
`α : A ⋙ L ⟶ L.prod L ⋙ B` and the counit of an adjunction in both components, so comparing two
composites of such maps means moving one counit at a time past the comparison.  Keeping these
statements at the generality of an arbitrary product category keeps every term in those
calculations small, and lets the ringed-space and ringed-topos developments share one copy.

## Main results

* `CategoryTheory.bifunctor_map_comp_left`, `CategoryTheory.bifunctor_map_comp_right`,
  `CategoryTheory.bifunctor_map_comp_both` — a composition in the first component, in the second
  component, or in both, splits off.
* `CategoryTheory.bifunctor_comparison_naturality` — naturality of a comparison of bifunctors
  along a functor, stated for a morphism of the product category given by its two components.
* `CategoryTheory.uncurry_map_mkHom_id` — the uncurried functor of `F : C ⥤ D ⥤ E` on a pair
  `φ ×ₘ 𝟙 B` is `(F.map φ).app B`.
-/

@[expose] public section

open scoped CategoryTheory.Prod

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ### Splitting the image of a pair of morphisms -/

section Bifunctor

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] (B : C₁ × C₂ ⥤ C₃)

/-- A composition in the first factor of a bifunctor splits off. -/
lemma bifunctor_map_comp_left {P P' P'' : C₁} {Q Q' : C₂} (x : P ⟶ P') (y : P' ⟶ P'')
    (z : Q ⟶ Q') :
    B.map ((x ≫ y) ×ₘ z) = B.map (x ×ₘ 𝟙 Q) ≫ B.map (y ×ₘ z) := by
  rw [← B.map_comp, prod_comp, Category.id_comp]

/-- A composition in the second factor of a bifunctor splits off. -/
lemma bifunctor_map_comp_right {P P' : C₁} {Q Q' Q'' : C₂} (x : P ⟶ P') (y : Q ⟶ Q')
    (z : Q' ⟶ Q'') :
    B.map (x ×ₘ (y ≫ z)) = B.map (𝟙 P ×ₘ y) ≫ B.map (x ×ₘ z) := by
  rw [← B.map_comp, prod_comp, Category.id_comp]

/-- A composition in both factors of a bifunctor splits. -/
lemma bifunctor_map_comp_both {P P' P'' : C₁} {Q Q' Q'' : C₂} (x : P ⟶ P') (y : P' ⟶ P'')
    (z : Q ⟶ Q') (w : Q' ⟶ Q'') :
    B.map ((x ≫ y) ×ₘ (z ≫ w)) = B.map (x ×ₘ z) ≫ B.map (y ×ₘ w) := by
  rw [← B.map_comp, prod_comp]

end Bifunctor

/-! ### Naturality of a comparison of two bifunctors -/

section Comparison

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] {L : C ⥤ D}
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- Naturality of the comparison `α` of the bifunctor `A` on the source with the bifunctor `B` on
the target, written one factor at a time: a morphism of `C × C` is given by its two components
`u` and `v`. -/
lemma bifunctor_comparison_naturality {P Q P' Q' : C} (u : P ⟶ P') (v : Q ⟶ Q') :
    L.map (A.map (u ×ₘ v)) ≫ α.app (P', Q') = α.app (P, Q) ≫ B.map (L.map u ×ₘ L.map v) :=
  α.naturality (u ×ₘ v)

end Comparison

/-- The uncurried functor of `F : C ⥤ D ⥤ E` sends `φ ×ₘ 𝟙 B` to `(F.map φ).app B`.  Stated
over three arbitrary categories, so that it is applied by one unification. -/
theorem uncurry_map_mkHom_id {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {A A' : C} (φ : A ⟶ A') (B : D) :
    (Functor.uncurry.obj F).map (φ ×ₘ 𝟙 B) = (F.map φ).app B := by
  simp [Functor.uncurry]

end CategoryTheory

end

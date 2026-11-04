module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksCore.Tactic.StacksAttribute

/-! # Groupoids form a (2,1)-category

A (2,1)-category is a strict 2-category in which every 2-morphism is invertible, equivalently
in which every `Mor(x, y)` is a groupoid (Stacks 003I). In the 2-category `Groupoids` — objects
the groupoids, 1-morphisms the functors, and `Mor(x, y)` the functor category `x ⥤ y` with
vertical composition — a natural transformation `t : F' ⟶ F` between functors into a groupoid
`y` has a two-sided inverse with components `(t.app a)⁻¹`. Hence `x ⥤ y` is itself a groupoid
and `Groupoids` is a (2,1)-category, which is Stacks 003J item 3.
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂

/-- Statement 1 (elementary content). For groupoids `x, y`, functors
`F, F' : x ⥤ y`, and a natural transformation `t : F' ⟶ F`, there exists a natural
transformation `s : F ⟶ F'` that is a two-sided inverse to `t` under vertical
composition, and whose components are the (groupoid) inverses of the components of
`t`. Here `t ≫ s = 𝟙 F'` is the informal `s ∘ t = id_{F'}` and `s ≫ t = 𝟙 F` is
`t ∘ s = id_F`. -/
theorem groupoids_is_two_one_category_existence
    {x : Type u₁} [Groupoid.{v₁} x] {y : Type u₂} [Groupoid.{v₂} y]
    (F F' : x ⥤ y) (t : F' ⟶ F) :
    ∃ s : F ⟶ F',
      (t ≫ s = 𝟙 F' ∧ s ≫ t = 𝟙 F) ∧ ∀ a : x, s.app a = inv (t.app a) := by
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨inv t, ⟨IsIso.hom_inv_id t, IsIso.inv_hom_id t⟩, ?_⟩
  intro a
  simp

/-- Statement 1 (groupoid form). Equivalently, the `Mor`-category
`Mor_Groupoids(x,y) = Fun(x,y)` is itself a groupoid whenever the target `y` is a
groupoid: every natural transformation between functors into a groupoid is a
natural isomorphism. Stated as the `Prop`-valued predicate `IsGroupoid (x ⥤ y)` so
that it carries a genuine proof obligation rather than data. -/
theorem functorCategory_into_groupoid_isGroupoid
    {x : Type u₁} [Groupoid.{v₁} x] {y : Type u₂} [Groupoid.{v₂} y] :
    IsGroupoid (x ⥤ y) := by
  refine ⟨fun f => ?_⟩
  exact NatIso.isIso_of_isIso_app f

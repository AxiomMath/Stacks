module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a commutative square from a right localization (Stacks 05Q7)

Let `W` be a right multiplicative system on a category `C` and let `L : C ⥤ D` be a
localization of `C` at `W`. A square in `D`
```
L X --- a ---> L X'
 |              |
L f            L f'
 |              |
 v              v
L Y --- b ---> L Y'
```
need not come from a square in `C`, because `a` and `b` are only fractions. This file
shows that it does come from one after replacing the left-hand column by a
`W`-equivalent one: there are objects `X''`, `Y''` of `C`, a morphism
`f'' : X'' ⟶ Y''` and morphisms `s : X'' ⟶ X`, `t : Y'' ⟶ Y` in `W` fitting into two
commutative squares of `C`, `s ≫ f = f'' ≫ t` and `g ≫ f' = f'' ≫ h`, whose image in
`D` is the given square.

The two remaining conclusions `L.map s ≫ a = L.map g` and `L.map t ≫ b = L.map h`
pin `a` and `b` down as the right fractions `g s⁻¹` and `h t⁻¹`: since `L.map s` and
`L.map t` are isomorphisms, they say exactly `a = (L.map s)⁻¹ ≫ L.map g` and
`b = (L.map t)⁻¹ ≫ L.map h`.

The proof writes `a` and `b` as right fractions, applies the right Ore condition to the
cospan formed by their denominators and `f`, and then uses right cancellation
(`MorphismProperty.map_eq_iff_precomp`) to correct the resulting square by a further
`W`-morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

universe v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (L : C ⥤ D) (W : MorphismProperty C)

/-- **Stacks 05Q7.**
Let `W : MorphismProperty C` admit a right calculus of fractions and let
`L : C ⥤ D` be a localization of `C` at `W`. Given morphisms `f : X ⟶ Y` and
`f' : X' ⟶ Y'` in `C`, and morphisms `a : L.obj X ⟶ L.obj X'`,
`b : L.obj Y ⟶ L.obj Y'` in `D` such that `a ≫ L.map f' = L.map f ≫ b`,
there exist objects `X''`, `Y''` in `C`, a morphism `f'' : X'' ⟶ Y''`,
morphisms `s : X'' ⟶ X`, `t : Y'' ⟶ Y` with `W s`, `W t`, and morphisms
`g : X'' ⟶ X'`, `h : Y'' ⟶ Y'` such that
`s ≫ f = f'' ≫ t`, `g ≫ f' = f'' ≫ h`,
`L.map s ≫ a = L.map g`, and `L.map t ≫ b = L.map h`. -/
@[stacks 05Q7]
theorem exists_rightFraction_lift_of_commSq
    [L.IsLocalization W] [HasRightCalculusOfFractions W]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y')
    (sq : a ≫ L.map f' = L.map f ≫ b) :
    ∃ (X'' Y'' : C) (f'' : X'' ⟶ Y'')
      (s : X'' ⟶ X) (_ : W s) (t : Y'' ⟶ Y) (_ : W t)
      (g : X'' ⟶ X') (h : Y'' ⟶ Y'),
        s ≫ f = f'' ≫ t ∧ g ≫ f' = f'' ≫ h ∧
        L.map s ≫ a = L.map g ∧
        L.map t ≫ b = L.map h := by
  -- Write `a`, `b` as right fractions and apply right Ore to the resulting cospan.
  have exists_eq : ∀ {A B : C} (c : L.obj A ⟶ L.obj B),
      ∃ φ : W.RightFraction A B, L.map φ.s ≫ c = L.map φ.f := fun c =>
    (CategoryTheory.Localization.exists_rightFraction L W c).imp fun φ hφ => by
      rw [hφ]; exact RightFraction.map_s_comp_map _ _ _
  obtain ⟨φa, eqa⟩ := exists_eq a
  obtain ⟨φb, eqb⟩ := exists_eq b
  obtain ⟨ψ, hψ⟩ := HasRightCalculusOfFractions.exists_rightFraction
    (W := W) (LeftFraction.mk (φa.s ≫ f) φb.s φb.hs)
  have hψ' : ψ.s ≫ φa.s ≫ f = ψ.f ≫ φb.s := hψ
  -- The two legs agree after applying `L`: this is the given square `sq`.
  have key : L.map (ψ.s ≫ φa.f ≫ f') = L.map (ψ.f ≫ φb.f) := by
    simp only [L.map_comp, ← eqa, ← eqb, Category.assoc, sq]
    simp only [← L.map_comp_assoc, hψ']
  -- Right cancellation in the localization yields a `W`-morphism `u`.
  obtain ⟨X'', u, huW, hcanc⟩ := (map_eq_iff_precomp L W _ _).mp key
  refine ⟨X'', φb.X', u ≫ ψ.f,
    u ≫ ψ.s ≫ φa.s, W.comp_mem _ _ huW (W.comp_mem _ _ ψ.hs φa.hs),
    φb.s, φb.hs, u ≫ ψ.s ≫ φa.f, φb.f,
    ?_, by simpa using hcanc, by simp [eqa], eqb⟩
  simp only [Category.assoc]
  rw [hψ]

end CategoryTheory.MorphismProperty

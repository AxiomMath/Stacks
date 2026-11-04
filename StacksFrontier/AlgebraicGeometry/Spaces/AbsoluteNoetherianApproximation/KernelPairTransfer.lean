module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Yoneda

/-!
# Kernel pairs of maps out of a representable presheaf, tested on points

Two morphisms `f : h_V ⟶ X` and `f' : h_V ⟶ X'` out of the same representable presheaf which
identify the same pairs of points `T ⟶ V` have the same kernel pairs: if `(s, t)` exhibits a
representable kernel pair of `f`, it exhibits one of `f'`.

## Main results

* `CategoryTheory.isPullback_yoneda_of_isPullback_of_forall_iff`: kernel pairs of maps out of a
  representable presheaf are determined by the pairs of points they identify.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {E V : C} {X X' : Cᵒᵖ ⥤ Type v}

/-- **Kernel pairs of maps out of a representable are determined by the identified points.** If
`(s, t)` is a kernel pair of `f : h_V ⟶ X` and `f'` identifies exactly the pairs of points of `V`
that `f` identifies, then `(s, t)` is a kernel pair of `f'`. -/
theorem isPullback_yoneda_of_isPullback_of_forall_iff (s t : E ⟶ V) (f : yoneda.obj V ⟶ X)
    (f' : yoneda.obj V ⟶ X') (h : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hiff : ∀ (T : C) (x y : T ⟶ V),
      yoneda.map x ≫ f = yoneda.map y ≫ f ↔ yoneda.map x ≫ f' = yoneda.map y ≫ f') :
    IsPullback (yoneda.map s) (yoneda.map t) f' f' := by
  have happ : ∀ {Y : Cᵒᵖ ⥤ Type v} (g : yoneda.obj V ⟶ Y) (T : C) (x y : T ⟶ V),
      (yoneda.map x ≫ g = yoneda.map y ≫ g ↔ g.app (op T) x = g.app (op T) y) := by
    intro Y g T x y
    rw [← yonedaEquiv.injective.eq_iff, yonedaEquiv_comp, yonedaEquiv_comp,
      yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  have hT := h.app T
  rw [Types.isPullback_iff] at hT ⊢
  obtain ⟨hw, hinj, hsurj⟩ := hT
  refine ⟨?_, hinj, fun x y hxy => hsurj x y ?_⟩
  · ext e
    have he : f.app T ((yoneda.map s).app T e) = f.app T ((yoneda.map t).app T e) :=
      ConcreteCategory.congr_hom hw e
    exact (happ f' T.unop _ _).1 ((hiff _ _ _).1 ((happ f T.unop _ _).2 he))
  · exact (happ f T.unop _ _).1 ((hiff _ _ _).2 ((happ f' T.unop _ _).2 hxy))

end CategoryTheory

end

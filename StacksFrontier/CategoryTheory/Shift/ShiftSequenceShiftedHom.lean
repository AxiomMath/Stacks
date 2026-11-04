module

public import Mathlib.CategoryTheory.Shift.ShiftSequence
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Shift sequences and the composition of shifted morphisms

Let `F : C ⥤ A` be a functor equipped with a shift sequence, so that a morphism
`f : X ⟶ Y⟦n⟧` induces `F.shiftMap f a a' : F_a(X) ⟶ F_{a'}(Y)` whenever `n + a = a'`. This file
proves that `Functor.shiftMap` turns the composition `ShiftedHom.comp` of shifted morphisms
into composition, and records what it does on morphisms of degree zero.

## Main results

* `CategoryTheory.Functor.shiftMap_shiftedHomComp` — `F.shiftMap (β.comp α)` is
  `F.shiftMap β ≫ F.shiftMap α`.
* `CategoryTheory.Functor.shiftMap_mk₀` — on a degree-zero shifted morphism `shiftMap` is `map`.
* `CategoryTheory.Functor.shiftMap_id` — on the identity of `X⟦n⟧` it is the shift isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Category

variable {C A : Type*} [Category* C] [Category* A] {M : Type*} [AddMonoid M] [HasShift C M]
  (F : C ⥤ A) [F.ShiftSequence M]

/-- **`Functor.shiftMap` is multiplicative for the composition of shifted morphisms.** For
`β : L ⟶ K⟦j⟧` and `α : K ⟶ Z⟦i⟧`, with `i + j = c`, `c + a = a'` and `i + a' = a''`, the
morphism induced by the composite `β.comp α : L ⟶ Z⟦c⟧` is the composite of the morphisms
induced by `β` and by `α`. -/
theorem shiftMap_shiftedHomComp {L K Z : C} {i j c : M} (β : ShiftedHom L K j)
    (α : ShiftedHom K Z i) (h : i + j = c) (a a' a'' : M) (ha' : j + a = a')
    (ha'' : i + a' = a'') :
    F.shiftMap (β.comp α h) a a'' (by rw [← ha'', ← ha', ← add_assoc, h]) =
      F.shiftMap β a a' ha' ≫ F.shiftMap α a' a'' ha'' := by
  simp only [shiftMap, ShiftedHom.comp, Functor.map_comp, assoc]
  congr 1
  rw [← F.shiftIso_hom_naturality_assoc, F.shiftIso_hom_app_comp j i c h a a' a'' ha' ha'']

/-- **On a morphism of degree zero `Functor.shiftMap` is `Functor.map`.** -/
theorem shiftMap_mk₀ {X Y : C} (g : X ⟶ Y) (a : M) :
    F.shiftMap (ShiftedHom.mk₀ (0 : M) rfl g) a a (by rw [zero_add]) = (F.shift a).map g := by
  simp only [shiftMap, ShiftedHom.mk₀, Functor.map_comp, assoc]
  rw [F.shiftIso_zero_hom_app, ← Functor.map_comp, ← Functor.map_comp]
  simp [shiftFunctorZero']

/-- **On the identity of `X⟦n⟧`, regarded as a morphism `X⟦n⟧ ⟶ X⟦n⟧` of degree `n`,
`Functor.shiftMap` is the shift isomorphism** `F_a(X⟦n⟧) ≅ F_{a'}(X)`. -/
theorem shiftMap_id (X : C) (n a a' : M) (ha' : n + a = a') :
    F.shiftMap (𝟙 (X⟦n⟧)) a a' ha' = (F.shiftIso n a a' ha').hom.app X := by
  simp [shiftMap]

end CategoryTheory.Functor

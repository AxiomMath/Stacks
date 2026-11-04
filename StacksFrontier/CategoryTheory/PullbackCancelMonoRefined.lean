module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import StacksCore.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# Cancelling a monomorphism in a cartesian square

If the first projection of a cartesian square factors through a monomorphism, then moving that
monomorphism onto the adjacent side of the square gives a cartesian square again.

## Main results

* `CategoryTheory.isPullback_of_fst_eq_comp_mono`: if the square with sides `p ≫ a, snd, f, g`
  is cartesian and `a` is a monomorphism, then the square with sides `p, snd, a ≫ f, g` is
  cartesian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A cartesian square whose first projection factors through a monomorphism is cartesian over
the factorisation: if `fst = p ≫ a` with `a` a monomorphism, then the square with sides
`p, snd, a ≫ f, g` is again cartesian. -/
public theorem isPullback_of_fst_eq_comp_mono {C : Type*} [Category C] {P A X Y Z : C}
    {p : P ⟶ A} {snd : P ⟶ Y} {a : A ⟶ X} [Mono a] {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback (p ≫ a) snd f g) : IsPullback p snd (a ≫ f) g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by rw [← Category.assoc]; exact h.w)
    (fun s => h.lift (s.fst ≫ a) s.snd (by rw [Category.assoc]; exact s.condition))
    (fun s => ?_) (fun s => h.lift_snd _ _ _) (fun s m h₁ h₂ => ?_))
  · rw [← cancel_mono a, Category.assoc]
    exact h.lift_fst _ _ _
  · exact h.hom_ext (by rw [h.lift_fst, ← Category.assoc, h₁]) (by rw [h.lift_snd]; exact h₂)

end CategoryTheory

end

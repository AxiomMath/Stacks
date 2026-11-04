module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import StacksCore.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cancelling a monomorphism in a cartesian square

A cartesian square whose two cospan legs are composites with one monomorphism stays cartesian
after that monomorphism is cancelled: the square over the factorisations has the same cones,
because a cone over the composites is a cone over the factorisations once the monomorphism is
cancelled from the commuting condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A cartesian square both of whose cospan legs factor through one monomorphism is cartesian
over the factorisations. -/
public theorem isPullback_of_comp_mono {C : Type*} [Category C] {P A A' Z W : C}
    {f : P ⟶ A} {g : P ⟶ A'} {x : A ⟶ W} {y : A' ⟶ W} (m : W ⟶ Z) [Mono m]
    (hsq : IsPullback f g (x ≫ m) (y ≫ m)) : IsPullback f g x y :=
  IsPullback.of_isLimit
    (Limits.PullbackCone.isLimitOfFactors (x ≫ m) (y ≫ m) m x y rfl rfl _ hsq.isLimit)

/-- A cartesian square stays cartesian after composing both cospan legs with one monomorphism. -/
public theorem isPullback_comp_mono {C : Type*} [Category C] {P X Y Z Z' : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (i : Z ⟶ Z')
    [Mono i] : IsPullback fst snd (f ≫ i) (g ≫ i) := by
  refine IsPullback.mk' (by rw [← Category.assoc, ← Category.assoc, h.w]) ?_ ?_
  · intro _ _ _ h₁ h₂
    exact h.hom_ext h₁ h₂
  intro T a b hab
  have hab' : a ≫ f = b ≫ g := by
    rw [← cancel_mono i, Category.assoc, Category.assoc]
    exact hab
  exact ⟨h.lift a b hab', by simp, by simp⟩

end CategoryTheory

end

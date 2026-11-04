module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of a morphism property across a commuting square

Let `P` be a morphism property stable under base change, let `f : X ⟶ Y`, and let
`a ≫ g = b ≫ h` be a commuting square whose two composites land in `Y`. Then the base change of
`f` along `g` carries `P` only if the base change along `b` of the base change along `h` does:
both are base changes of `f` along the common composite `a ≫ g = b ≫ h`, and the two iterated
fibre products are identified by the associativity isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`.

## Main results

* `CategoryTheory.MorphismProperty.pullbackSnd_of_comm`: the transport across the square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

/-- A two-square cancellation for a base-change-stable morphism property: given a commuting
square `a ≫ g = b ≫ h`, the property of the base change of `f` along `g` transports to the base
change along `b` of the base change along `h`. -/
theorem pullbackSnd_of_comm {C : Type*} [Category* C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] {X Y A A' D : C}
    (f : X ⟶ Y) (g : A ⟶ Y) (h : A' ⟶ Y) (a : D ⟶ A) (b : D ⟶ A')
    (comm : a ≫ g = b ≫ h) (hf : P (pullback.snd f g)) :
    P (pullback.snd (pullback.snd f h) b) := by
  have h₁ : P (pullback.snd (pullback.snd f g) a) :=
    IsStableUnderBaseChange.of_isPullback
      (P := P) (IsPullback.of_hasPullback (pullback.snd f g) a) hf
  let e₁ := pullbackLeftPullbackSndIso f g a
  have h₂ : P (pullback.snd f (a ≫ g)) := by
    apply (P.cancel_left_of_respectsIso e₁.hom _).mp
    simpa only [e₁, pullbackLeftPullbackSndIso_hom_snd] using h₁
  have h₃ : P (pullback.snd f (b ≫ h)) :=
    (congrArg (fun k => P (pullback.snd f k)) comm).mp h₂
  let e₂ := pullbackLeftPullbackSndIso f h b
  apply (P.cancel_left_of_respectsIso e₂.hom _).mpr at h₃
  simpa only [e₂, pullbackLeftPullbackSndIso_hom_snd] using h₃

end CategoryTheory.MorphismProperty

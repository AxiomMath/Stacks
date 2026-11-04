module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Transporting a Cartesian square along equalities of its morphisms

A Cartesian square stays Cartesian when each of its four morphisms is replaced by an equal one.

## Main results

* `CategoryTheory.IsPullback.of_eq`: the transport of a Cartesian square along equalities of its
  four morphisms.

## Implementation notes

The four equations are separate arguments, so that the transport is a `subst` rather than a
rewrite under the dependently typed `IsPullback`.  This is also what makes the statement usable
where a corner of the square has two definitionally equal spellings: `rw` refuses such a goal,
because the intermediate expression is not type-correct at `implicit` transparency, whereas an
application is checked at `default` transparency and so reconciles the two spellings by
unfolding them.
-/

@[expose] public section

namespace CategoryTheory

/-- A Cartesian square transports along equalities of its four morphisms. -/
theorem IsPullback.of_eq {C : Type*} [Category C] {P X Y Z : C}
    {fst fst' : P ⟶ X} {snd snd' : P ⟶ Y} {f f' : X ⟶ Z} {g g' : Y ⟶ Z}
    (h : IsPullback fst snd f g) (e₁ : fst = fst') (e₂ : snd = snd') (e₃ : f = f')
    (e₄ : g = g') : IsPullback fst' snd' f' g' := by
  subst e₁; subst e₂; subst e₃; subst e₄; exact h

end CategoryTheory

end

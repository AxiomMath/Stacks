module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute

/-!
# Properties of morphisms étale local on the source and target

A property of morphisms of schemes is étale local on the source and target if it is preserved
by precomposition with étale morphisms and by étale base change, and if it can be checked in
étale neighbourhoods of every point of the source.

## Main definitions

* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` expresses that a morphism property is
  étale local on both source and target.

## Main results

There are no results beyond the definition.

## Implementation notes

The fibre product in the base-change condition is Mathlib's chosen categorical pullback. The
locality condition retains both étale vertical maps, their commutative square, and a point
above the specified source point. The structure fields form the API used downstream.

## References

* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- A property of morphisms of schemes is étale local on the source and target if it is
preserved by étale precomposition and étale base change, and can be checked in a commutative
square of étale neighbourhoods around every point of the source. -/
@[stacks 04QZ]
structure IsEtaleLocalOnSourceAndTarget (P : MorphismProperty Scheme.{u}) : Prop where
  /-- Precomposing a morphism having the property with an étale morphism preserves the
  property. -/
  precomp : P.RespectsLeft (@Etale : MorphismProperty Scheme.{u})
  /-- Base change of a morphism having the property along an étale morphism preserves the
  property. -/
  pullbackSnd_of_etale : ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y), P f →
    ∀ (g : Y' ⟶ Y), Etale g → P (pullback.snd f g)
  /-- The property holds exactly when every source point has étale source and target
  neighbourhoods on which the induced morphism has the property. -/
  iff_forall_exists_etale_neighborhood : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    P f ↔ ∀ x : X,
      ∃ (U V : Scheme.{u}) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V) (u : U),
        Etale a ∧ Etale b ∧ a.base u = x ∧ h ≫ b = a ≫ f ∧ P h

end AlgebraicGeometry

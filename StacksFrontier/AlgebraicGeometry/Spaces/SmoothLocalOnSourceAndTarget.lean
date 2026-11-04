module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Smooth locality on the source and target for algebraic spaces (Stacks 06F8)

A property of morphisms of algebraic spaces over a scheme `S` is *smooth local on the
source-and-target* when it is stable under precomposition by smooth morphisms and under smooth
base change, and when it can be checked on smooth neighbourhoods of every point of the source.
This is the hypothesis under which Stacks 06FM defines the corresponding property of morphisms
of algebraic stacks, and the three fields are the API every locality result above it uses.

## Main definitions

* `AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget`: **Stacks 06F8**.

## Main results

There are no propositional results here: the three fields of the structure give the defining
properties directly.

## Implementation notes

Algebraic spaces are presheaves on the big fppf site of `S` satisfying
`AlgebraicGeometry.IsAlgebraicSpace`, and morphism properties here are predicates on natural
transformations of such presheaves rather than on morphisms of
`AlgebraicGeometry.AlgebraicSpaces`, so each clause restricts to algebraic spaces by explicit
hypotheses. The base-change clause uses the canonical presheaf pullback, with its second
projection to the new target. The locality clause records both smooth vertical arrows, the
commuting square, and a point of the neighbourhood mapping to the specified source point.

This is a **Chapter 74 tag**. Stacks 06FM (Chapter 101) takes it as a hypothesis, so it is part
of 06FM's statement.

## References

* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 06F8.** A property of morphisms of algebraic spaces over `S` is *smooth local on
the source-and-target* when it is stable under smooth precomposition and smooth base change, and
can be checked in smooth neighbourhoods of every point of the source. -/
@[stacks 06F8]
structure IsSmoothLocalOnSourceAndTarget
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) : Prop where
  /-- Precomposition with a smooth morphism preserves the property. -/
  precomp :
    ∀ {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X)
      (_hY : IsAlgebraicSpace B S hS Y)
      (_hZ : IsAlgebraicSpace B S hS Z)
      (f : X ⟶ Y) (g : Y ⟶ Z),
      IsSmooth B S hS f → P g → P (f ≫ g)
  /-- Smooth base change preserves the property. -/
  pullbackSnd_of_smooth :
    ∀ {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X)
      (_hY : IsAlgebraicSpace B S hS Y)
      (_hY' : IsAlgebraicSpace B S hS Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y),
      P f → IsSmooth B S hS g → P (pullback.snd f g)
  /-- The property can be checked on smooth source-and-target neighbourhoods of each source
  point. -/
  iff_forall_exists_smooth_neighborhood :
    ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X)
      (_hY : IsAlgebraicSpace B S hS Y)
      (f : X ⟶ Y),
      P f ↔
        ∀ x : points B S hS X,
          ∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
            (_hU : IsAlgebraicSpace B S hS U)
            (_hV : IsAlgebraicSpace B S hS V)
            (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
            (u : points B S hS U),
            IsSmooth B S hS a ∧
              IsSmooth B S hS b ∧
              pointsMap B S hS U a u = x ∧
              h ≫ b = a ≫ f ∧ P h

end AlgebraicGeometry.Space

end

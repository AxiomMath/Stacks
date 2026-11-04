module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Perfect

/-!
# Local complete intersection morphisms of algebraic spaces are perfect

A local complete intersection morphism of algebraic spaces over a scheme `S` is locally of
finite presentation, pseudo-coherent and perfect: this is **Stacks 06C6**.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isLocalCompleteIntersection`:
  part (1) of Stacks 06C6.
* `AlgebraicGeometry.Space.isPseudoCoherent_of_isLocalCompleteIntersection`: part (2).
* `AlgebraicGeometry.Space.isPerfect_of_isLocalCompleteIntersection`: part (3).

## Implementation notes

All four properties involved are the every-étale-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ applied to a property of
scheme morphisms, so each of the three parts reduces chartwise to the part of the same number
of the schemes version, Stacks 069H. That is the deduction the source proof indicates, and it
needs no étale locality of any of the three conclusions: one commuting square of étale charts
carries the hypothesis and the conclusion at once, so the chart quantifier passes through the
implication unchanged. For the same reason none of the three parts needs the source or the
target to be algebraic, exactly as in the source.

The three parts are stated separately rather than as a single conjunction because the schemes
version is stated that way, and because part (3) implies part (2) implies part (1) through
Stacks 067H and Stacks 0682 at the level of scheme morphisms, which is how Stacks 069H is
proved; the chartwise form of those two implications is Stacks 06C2 and Stacks 06BU.

## References

* [Stacks Project, Tag 069H](https://stacks.math.columbia.edu/tag/069H)
* [Stacks Project, Tag 06C6](https://stacks.math.columbia.edu/tag/06C6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 06C6, part (1).** A local complete intersection morphism of algebraic spaces over
`S` is locally of finite presentation. -/
@[stacks 06C6 "part (1): locally of finite presentation"]
theorem isLocallyOfFinitePresentation_of_isLocalCompleteIntersection (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsLocalCompleteIntersection B S hS f) :
    IsLocallyOfFinitePresentation B S hS f := fun U V a b h ha hb comm =>
  @_root_.AlgebraicGeometry.locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism
    _ _ _ (hf U V a b h ha hb comm)

/-- **Stacks 06C6, part (2).** A local complete intersection morphism of algebraic spaces over
`S` is pseudo-coherent. -/
@[stacks 06C6 "part (2): pseudo-coherent"]
theorem isPseudoCoherent_of_isLocalCompleteIntersection (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsLocalCompleteIntersection B S hS f) :
    IsPseudoCoherent B S hS f := fun U V a b h ha hb comm =>
  @_root_.AlgebraicGeometry.pseudoCoherent_of_isLocalCompleteIntersectionMorphism
    _ _ _ (hf U V a b h ha hb comm)

/-- **Stacks 06C6, part (3).** A local complete intersection morphism of algebraic spaces over
`S` is perfect. -/
@[stacks 06C6 "part (3): perfect"]
theorem isPerfect_of_isLocalCompleteIntersection (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsLocalCompleteIntersection B S hS f) :
    IsPerfect B S hS f := fun U V a b h ha hb comm =>
  @_root_.AlgebraicGeometry.perfect_of_isLocalCompleteIntersectionMorphism
    _ _ _ (hf U V a b h ha hb comm)

end AlgebraicGeometry.Space

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningComposition

/-!
# Surjectivity in a morphism of thickenings of algebraic stacks (Stacks 0CJ9, part (2))

Stacks 0CJ9 part (2) reads, verbatim:

> Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks. Then
> (2) `f` is a surjective morphism if and only if `f'` is a surjective morphism.

A thickening of algebraic stacks is a closed immersion which is surjective on points, so it is
*bijective* on points: injectivity is
`AlgebraicGeometry.Stack.AlgebraicStacks.injective_pointsMap_of_isClosedImmersion`, since a
closed immersion is fully faithful (**Stacks 04ZZ**, (1) ⟹ (2)) and a fully faithful 1-morphism
is injective on points (**Stacks 0500**). The restriction square of a morphism of thickenings
becomes, on points, a commutative square whose two vertical maps are bijections, and the two
horizontal ones are then surjective together.

That is the whole of part (2): the source deduces it from the stronger statement that
`𝒳 → 𝒳'` and `𝒴 → 𝒴'` are *universal homeomorphisms* (Stacks 0CJ7) and that any condition on
`|f|` is therefore equivalent to the corresponding condition on `|f'|`, but surjectivity is a
condition on the maps of sets alone, and bijectivity of the two vertical maps is all it needs.

## Main results

* `AlgebraicGeometry.Stack.injective_pointsMap_of_isThickening` and
  `AlgebraicGeometry.Stack.bijective_pointsMap_of_isThickening`: a thickening of algebraic
  stacks is injective, hence bijective, on points.
* `AlgebraicGeometry.Stack.isSurjective_inner_iff_outer`: **Stacks 0CJ9**, part (2).

## Implementation notes

Bijectivity on points is the *set-theoretic* half of the homeomorphism clause of **Stacks 0BPP**
part (1), which `StacksFrontier.AlgebraicGeometry.Stacks.Thickening` does not state. It is not the
whole clause, so nothing here carries a `@[stacks 0BPP]` attribute: the topological half still
needs the point topology of Stacks 04XL.

Only the forward implication of part (2) was available before, as
`AlgebraicGeometry.Stack.isSurjective_outer_of_inner`; it is used here unchanged, and the
implementation notes of `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningComposition` record why
the converse was not. The missing input named there — injectivity on points of a thickening — is
exactly what `StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful` supplies.

## References

* [Stacks Project, Tag 0500](https://stacks.math.columbia.edu/tag/0500)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A thickening of algebraic stacks is injective on points.** A thickening is a closed
immersion, and a closed immersion of algebraic stacks is injective on points. -/
theorem injective_pointsMap_of_isThickening {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {i : 𝒳 ⟶ 𝒴}
    (hi : IsThickening i) :
    Function.Injective (AlgebraicStacks.pointsMap B S hS i) :=
  AlgebraicStacks.injective_pointsMap_of_isClosedImmersion B S hS i hi.1

/-- **A thickening of algebraic stacks is bijective on points**: it is surjective on points by
definition, and injective because it is a closed immersion.

This is the set-theoretic half of the homeomorphism clause of **Stacks 0BPP** part (1); the
topological half needs the point topology of Stacks 04XL and is not available. -/
theorem bijective_pointsMap_of_isThickening {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {i : 𝒳 ⟶ 𝒴}
    (hi : IsThickening i) :
    Function.Bijective (AlgebraicStacks.pointsMap B S hS i) :=
  ⟨injective_pointsMap_of_isThickening hi, hi.2⟩

/-- In a morphism of thickenings of algebraic stacks, if the ambient 1-morphism is surjective then
so is the restricted one.

Given a point of `𝒴`, its image under the target thickening is hit by a point of `𝒳'`, which is
itself the image of a point of `𝒳` because the source thickening is surjective on points; the
restriction square then identifies the image of that point in `𝒴` with the one started from,
because the target thickening is *injective* on points. -/
theorem isSurjective_inner_of_outer {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
    (m : ThickeningMorphism i j hi hj) (hm : IsSurjective B S hS m.outer) :
    IsSurjective B S hS m.inner := by
  intro y
  obtain ⟨x', hout⟩ := hm (AlgebraicStacks.pointsMap B S hS j y)
  obtain ⟨x, hx⟩ := hi.2 x'
  have hin : AlgebraicStacks.pointsMap B S hS i x = x' := hx
  refine ⟨x, ?_⟩
  have h := congrFun (pointsMap_thickeningMorphism_comm m) x
  simp only [Function.comp_apply] at h
  rw [hin, hout] at h
  exact injective_pointsMap_of_isThickening hj h.symm

/-- **Stacks 0CJ9, part (2).** In a morphism of thickenings of algebraic stacks over `S`, the
restricted 1-morphism is surjective if and only if the ambient 1-morphism is surjective.

Surjectivity is a condition on the map of sets of points of **Stacks 04ZS**, the restriction
square induces a commutative square of those maps, and the two vertical maps of that square —
the thickenings — are bijective. -/
@[stacks 0CJ9 "part (2): surjective"]
theorem isSurjective_inner_iff_outer {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
    (m : ThickeningMorphism i j hi hj) :
    IsSurjective B S hS m.inner ↔ IsSurjective B S hS m.outer :=
  ⟨isSurjective_outer_of_inner m, isSurjective_inner_of_outer m⟩

end AlgebraicGeometry.Stack

end

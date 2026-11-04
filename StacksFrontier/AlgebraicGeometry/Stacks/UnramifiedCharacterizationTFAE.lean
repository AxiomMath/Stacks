module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedCharacterization

/-!
# The characterization of unramified 1-morphisms of algebraic stacks (Stacks 0CIY)

This file states **Stacks 0CIY** with no hypothesis beyond the source's: for a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, unramifiedness (**Stacks 0CIT**), condition (2) and
condition (3) of the lemma are equivalent.

## Main results

* `AlgebraicGeometry.Stack.isUnramified_tfae`: **Stacks 0CIY**.

## Implementation notes

The three implications are proved in
`StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedCharacterization`, where the forward direction of
**Stacks 06N3** is an explicit argument of the assembled equivalence
`AlgebraicGeometry.Stack.isUnramified_tfae_of_existsEtalePresentationOfIsAbsolutelyDM`. This file
supplies it, as `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, at
`AlgebraicGeometry.BigFppfSite.contains_terminal`.

## References

* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIY.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are
equivalent:
1. `f` is unramified (**Stacks 0CIT**);
2. `f` is DM, and for every algebraic space `V` with a 1-morphism `V ⟶ 𝒴` and every algebraic
   space `U` with an étale 1-morphism `U ⟶ V ×_𝒴 𝒳`, the morphism `U ⟶ V` is unramified;
3. there are an algebraic space `W` with a surjective, flat, locally finitely presented
   1-morphism `W ⟶ 𝒴` and an algebraic space `T` with a surjective étale 1-morphism
   `T ⟶ 𝒳 ×_𝒴 W` such that `T ⟶ W` is unramified. -/
@[stacks 0CIY]
theorem isUnramified_tfae {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    [IsUnramified B S hS f, IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f,
      HasUnramifiedEtalePresentationOverFlatCover.{u, w} B S hS f].TFAE :=
  isUnramified_tfae_of_existsEtalePresentationOfIsAbsolutelyDM B S hS
    (existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f

end AlgebraicGeometry.Stack

end

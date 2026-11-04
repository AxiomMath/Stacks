module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleAlgebraicSpaceCriterionTFAE

/-!
# Stacks 0CIQ

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0CIQ** asserts that the
following are equivalent:

1. `f` is étale (**Stacks 0CIL**);
2. `f` is Deligne–Mumford and for every `V ⟶ 𝒴` with `V` an algebraic space and every étale
   `U ⟶ V ×_𝒴 𝒳` with `U` an algebraic space, the morphism `U ⟶ V` is étale;
3. there are a surjective, flat, locally finitely presented `W ⟶ 𝒴` with `W` an algebraic space
   and a surjective étale `T ⟶ W ×_𝒴 𝒳` with `T` an algebraic space such that `T ⟶ W` is étale.

## Main results

* `AlgebraicGeometry.Stack.isEtale_tfae_algebraicSpaceCharts`: **Stacks 0CIQ**.

## Implementation notes

`AlgebraicGeometry.Stack.isEtale_tfae_of_forward` proves the equivalence from the existence of
surjective étale presentations of Deligne–Mumford algebraic stacks by schemes, the forward
direction of **Stacks 06N3**, which enters through **Stacks 0CIA** and **Stacks 0CIN**; that
direction is `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, at the terminal
scheme, which every big fppf site contains (`AlgebraicGeometry.BigFppfSite.contains_terminal`).

## References

* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIQ](https://stacks.math.columbia.edu/tag/0CIQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIQ.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are
equivalent:

1. `f` is étale, `AlgebraicGeometry.Stack.IsEtale` (**Stacks 0CIL**);
2. `f` is Deligne–Mumford and for every `V ⟶ 𝒴` with `V` an algebraic space and every étale
   `U ⟶ V ×_𝒴 𝒳` with `U` an algebraic space, `U ⟶ V` is étale,
   `AlgebraicGeometry.Stack.EtaleOnEveryAlgebraicSpaceDiagram`;
3. there are a surjective, flat, locally finitely presented `W ⟶ 𝒴` with `W` an algebraic space
   and a surjective étale `T ⟶ W ×_𝒴 𝒳` with `T` an algebraic space such that `T ⟶ W` is étale,
   `AlgebraicGeometry.Stack.HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange`. -/
@[stacks 0CIQ]
theorem isEtale_tfae_algebraicSpaceCharts
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    List.TFAE [IsEtale B S hS f, EtaleOnEveryAlgebraicSpaceDiagram B S hS f,
      HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange B S hS f] :=
  isEtale_tfae_of_forward B S hS
    (existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f

end AlgebraicGeometry.Stack

end

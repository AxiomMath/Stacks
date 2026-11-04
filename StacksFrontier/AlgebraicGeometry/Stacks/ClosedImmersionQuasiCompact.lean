module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism

/-!
# A closed immersion of algebraic stacks is quasi-compact (Stacks 0CL1)

**Stacks 0CL1** says that a closed immersion of algebraic stacks over `S` is quasi-compact. As the
source puts it, this follows from the fact that immersions are always representable together with
the corresponding fact for closed immersions of algebraic spaces.

Both halves of that sentence are available directly. A closed immersion in the sense of
**Stacks 04YL** part (2) is by definition representable by algebraic spaces *together with*
`AlgebraicGeometry.Stack.IsClosedImmersion`, the notion of **Stacks 04XB** at
`AlgebraicGeometry.Space.IsClosedImmersion`; and `AlgebraicGeometry.Stack.IsQuasiCompact` is the
notion of Stacks 04XB at `AlgebraicGeometry.Space.IsQuasiCompact`. Those two have the *same*
quantifier structure over scheme-valued points of the target, differing only in which property the
structural morphism of the representing algebraic space is asked to have, so **Stacks 04CG** —
a closed immersion of algebraic spaces is quasi-compact — transfers one to the other pointwise,
with no detour through the relative property of Stacks 03YK. **Stacks 050T** then converts that
into the base-change form, which is **Stacks 050U**.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_of_isClosedImmersion`:
  **Stacks 0CL1**.

## Implementation notes

The source asserts one proposition and the covering set is the one declaration below.

The representability half of Stacks 04YL part (2) is exactly the hypothesis Stacks 050T needs, so
it is consumed and not re-derived, and nothing is carried as a hypothesis that the definition of a
closed immersion does not already supply.

## References

* [Stacks Project, Tag 04CG](https://stacks.math.columbia.edu/tag/04CG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 0CL1](https://stacks.math.columbia.edu/tag/0CL1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CL1.** A closed immersion of algebraic stacks over `S` is quasi-compact.

A closed immersion is representable by algebraic spaces (Stacks 04YL, part (2)), which is the
hypothesis of **Stacks 050T**; and its second conjunct `AlgebraicGeometry.Stack.IsClosedImmersion`
differs from `AlgebraicGeometry.Stack.IsQuasiCompact` only in the property demanded of the
structural morphism of each representing algebraic space, so **Stacks 04CG** transfers it
pointwise. -/
@[stacks 0CL1]
theorem isQuasiCompactMorphism_of_isClosedImmersion
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsClosedImmersion B S hS f) :
    Stack.IsQuasiCompactMorphism.{u, w} B S hS f :=
  (Stack.isQuasiCompact_iff_baseChange_quasiCompact.{u, w} B S hS f hf.1).mp
    (fun U y hy F hF he =>
      Space.isQuasiCompact_of_isClosedImmersion' B S hS (hf.2 U y hy F hF he))

end AlgebraicGeometry.Stack.AlgebraicStacks

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordFibreProductEtaleCover
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence

/-!
# Permanence of unramifiedness in a tower of algebraic stacks (Stacks 0CIZ)

Let `𝒳 → 𝒴 → 𝒵` be 1-morphisms of algebraic stacks over `S`. **Stacks 0CIZ** says that if
`𝒳 → 𝒵` is unramified and `𝒴 → 𝒵` is Deligne–Mumford then `𝒳 → 𝒴` is unramified. This file
states and proves it under exactly those hypotheses.

## Main results

* `AlgebraicGeometry.Stack.isUnramified_of_comp_of_isDM`: **Stacks 0CIZ**.

## Implementation notes

The source's proof is assembled from three pieces already in the library: `𝒳 → 𝒴` is
Deligne–Mumford by **Stacks 050M**, `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_comp`; the
nested presentations its proof chooses are
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagramOver_of_isDM_of_forward`, which uses the
Deligne–Mumford hypothesis on `𝒴 → 𝒵` through **Stacks 0CIA**, with the structure theorem
**Stacks 06N3** supplied by `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`; and
given them, the remaining argument (unramifiedness of `U → W`, then **Stacks 06G6** for
`U → V`) is `AlgebraicGeometry.Stack.isUnramified_of_comp`. The terminal scheme the absolute
Deligne–Mumford condition is read over lies in every big fppf site,
`AlgebraicGeometry.BigFppfSite.contains_terminal`, so it is no hypothesis.

## References

* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIZ](https://stacks.math.columbia.edu/tag/0CIZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIZ.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over
`S`. If `f ≫ g` is unramified and `g` is Deligne–Mumford, then `f` is unramified.

`f` is Deligne–Mumford by Stacks 050M. Choose a surjective smooth `W ⟶ 𝒵`, a surjective étale
`V ⟶ 𝒴 ×_𝒵 W` and a surjective étale `U ⟶ 𝒳 ×_𝒴 V`, the last two by Stacks 0CIA (the second
because `g` is Deligne–Mumford, the third because `f` is); then `U ⟶ W` is unramified, and
`U ⟶ V` is unramified by Stacks 06G6. -/
@[stacks 0CIZ]
theorem isUnramified_of_comp_of_isDM {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hfg : IsUnramified B S hS (f ≫ g)) (hg : IsDM B S hS g) :
    IsUnramified B S hS f :=
  isUnramified_of_comp B S hS f g hfg
    (hasSurjectiveEtaleSmoothDiagramOver_of_isDM_of_forward B S hS
      (existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f g
      (AlgebraicStacks.isDM_of_comp B S hS f g hfg.1) hg)

end AlgebraicGeometry.Stack

end

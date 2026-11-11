module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism

/-!
# Local complete intersection 1-morphisms of algebraic stacks (Stacks 0CJ3)

Following Stacks 0CJ3, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a *local
complete intersection morphism*, or *Koszul*, when the equivalent conditions of Stacks 06FM hold
at the local complete intersection property of morphisms of algebraic spaces: for every
2-commutative square of algebraic spaces over `f` whose two vertical 1-morphisms are smooth and
whose every comparison 1-morphism to a 2-fibre product of `(b, f)` is smooth, the top horizontal
morphism of algebraic spaces is a local complete intersection morphism.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocalCompleteIntersection`: **Stacks 0CJ3**.

## Main results

There are no propositional results: the definition is an abbreviation, so the smooth-diagram API
of `AlgebraicGeometry.Stack.HasPropertyOnEverySmoothDiagram` applies to it directly.

## Implementation notes

The test is condition (1) of Stacks 06FM, formalized as
`AlgebraicGeometry.Stack.HasPropertyOnEverySmoothDiagram`, at
`AlgebraicGeometry.Space.IsLocalCompleteIntersection` (**Stacks 06C4**, part (1)). This is the
same shape as the sister notions `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFiniteType`
(**Stacks 06FS**, part (1)) and `...IsLocallyOfFinitePresentation` (**Stacks 06Q2**, part (1));
the named condition is used directly rather than inlined so that the family stays one notion.

Stacks 0CJ3 phrases the definition as "the equivalent conditions of Stacks 06FM hold", so either
condition may serve; the universal one is taken, as for the two sister notions above. The
equivalence itself is Stacks 06FM and is not used here. Its hypothesis — smooth locality on the
source-and-target of the local complete intersection property of morphisms of algebraic spaces —
is `AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`, so the
two conditions are interchangeable for this property.

Smoothness of the two vertical 1-morphisms is `AlgebraicGeometry.Stack.IsRelativelySmooth`, the
relative property of **Stacks 03YK** at `AlgebraicGeometry.Space.smoothMorphismProperty`, whose
two instance hypotheses are discharged for smoothness, so this carries no hypothesis on either
property.

## References

* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 0CJ3](https://stacks.math.columbia.edu/tag/0CJ3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CJ3.** A 1-morphism of algebraic stacks over `S` is a *local complete intersection
morphism*, or *Koszul*, when it passes the universal smooth-diagram test of Stacks 06FM at the
local complete intersection property of morphisms of algebraic spaces: every 2-commutative square
of algebraic spaces over `f` whose two vertical 1-morphisms are smooth and whose every comparison
1-morphism to a 2-fibre product is smooth has its top horizontal morphism a local complete
intersection morphism. -/
@[stacks 0CJ3]
abbrev IsLocalCompleteIntersection {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    Prop :=
  Stack.HasPropertyOnEverySmoothDiagram B S hS
    (fun _ _ h => Space.IsLocalCompleteIntersection B S hS h) f.hom

end AlgebraicGeometry.Stack.AlgebraicStacks

end

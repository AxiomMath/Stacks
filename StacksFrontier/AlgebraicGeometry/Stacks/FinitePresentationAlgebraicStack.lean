module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedQuasiSeparatedAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism

/-!
# 1-morphisms of algebraic stacks of finite presentation (Stacks 06Q2)

Following Stacks 06Q2, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is locally of
finite presentation* when it passes the universal smooth-diagram test of Stacks 06FM at local
finite presentation of morphisms of algebraic spaces: for every 2-commutative square

```
U ---h---> V
|          |
a          b
v          v
𝒳 ---f---> 𝒴
```

with `U`, `V` algebraic spaces over `S` and `a`, `b` smooth in the sense of Stacks 04XB, whose
every comparison 1-morphism to a 2-fibre product of `(b, f)` is smooth, the morphism `h` of
algebraic spaces is locally of finite presentation.

Local finite presentation of morphisms of algebraic spaces is smooth local on the source and the
target, so by Stacks 06FM this is equivalent to the existential test on *one* smooth diagram
surjective over the source; the equivalence itself is Stacks 06FM and is not used here, since
Stacks 06Q2 part (1) *is* the universal form.

Part (2) of Stacks 06Q2 adds two further conditions: `f` *is of finite presentation* when it is
locally of finite presentation, quasi-compact (**Stacks 050U**) and quasi-separated
(**Stacks 04YW**).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation`: **Stacks 06Q2**,
  part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsFinitePresentation`: **Stacks 06Q2**, part (2).

## Implementation notes

The test is condition (1) of Stacks 06FM, which is formalized as
`AlgebraicGeometry.Stack.HasPropertyOnEverySmoothDiagram`, applied at local finite presentation
of morphisms of algebraic spaces, `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation`
(**Stacks 03XP**, part (1)). The named condition is used directly rather than inlined, so that
this notion and `AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat` (**Stacks 06PW**) and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth` (**Stacks 075U**) stay one family and cannot
drift; note that 06PW and 075U are the *existential* condition (2) while this one is the
*universal* condition (1), exactly as the source states them.

Smoothness of the two vertical 1-morphisms is the different notion
`AlgebraicGeometry.Stack.IsRelativelySmooth` of Stacks 04XB — the relative property of
**Stacks 03YK** at `AlgebraicGeometry.Space.smoothMorphismProperty` — whose two instance
hypotheses are both discharged for smoothness, so this definition carries no hypothesis on
either property.

Part (2) is the conjunction of part (1) with quasi-compactness
(`AlgebraicGeometry.Stack.IsQuasiCompactMorphism`, **Stacks 050U**) and quasi-separatedness
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated`, **Stacks 04YW**) of a 1-morphism of
algebraic stacks. These rest on 050U being stated over quasi-compactness of an algebraic stack
(**Stacks 04YB**) and thence over the canonical topology on the points of an algebraic stack
(**Stacks 04XL**); all of 04XL, 04YB, 050U and 04YW are formalized, so the covering set of
Stacks 06Q2 is completed below, and part (2) of Stacks 06FS is likewise recorded there.

Quasi-separatedness is written `Stack.AlgebraicStacks.IsQuasiSeparated` rather than unqualified,
because `AlgebraicGeometry.Space.IsQuasiSeparated` is the algebraic-space namesake.

## References

* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06Q2, part (1).** A 1-morphism of algebraic stacks over `S` is *locally of finite
presentation* when it passes the universal smooth-diagram test of Stacks 06FM at local finite
presentation of morphisms of algebraic spaces: every 2-commutative square of algebraic spaces
over `f` whose two vertical 1-morphisms are smooth and whose every comparison 1-morphism to a
2-fibre product is smooth has its top horizontal morphism locally of finite presentation. -/
@[stacks 06Q2 "part (1): locally of finite presentation"]
abbrev IsLocallyOfFinitePresentation {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) : Prop :=
  Stack.HasPropertyOnEverySmoothDiagram B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h) f.hom

/-- **Stacks 06Q2, part (2).** A 1-morphism of algebraic stacks over `S` is *of finite
presentation* when it is locally of finite presentation, quasi-compact and quasi-separated. -/
@[stacks 06Q2 "part (2): finite presentation"]
abbrev IsFinitePresentation {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsLocallyOfFinitePresentation B S hS f ∧ Stack.IsQuasiCompactMorphism B S hS f ∧
    Stack.AlgebraicStacks.IsQuasiSeparated B S hS f

end AlgebraicGeometry.Stack.AlgebraicStacks

end

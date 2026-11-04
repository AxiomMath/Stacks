module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeUniquenessSeparated

/-!
# The comparison of two fibre products is locally of finite type (Stacks 050H, part (1))

Let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` and `h : 𝒵 ⟶ 𝒯` be 1-morphisms of algebraic stacks over `S` and
let

    i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴

be the induced 1-morphism of Stacks 050H. Part (1) of Stacks 050H asserts that `i` is
representable by algebraic spaces *and locally of finite type*. The representability half is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_comparison`; this file proves the
locally-of-finite-type half, which completes part (1) and with it the whole of Stacks 050H.

The argument is the source's own, and the same one the other six assertions use: by Stacks 04Z1
the square

```text
                   i
  𝒳 ×_𝒵 𝒴  ------------>  𝒳 ×_𝒯 𝒴
    |                         |
    |                         |
    v                         v
    𝒵  --Δ_{𝒵/𝒯}-->       𝒵 ×_𝒯 𝒵
```

is 2-cartesian, so `i` is a base change of the relative diagonal `Δ_{𝒵/𝒯}`; that diagonal is
locally of finite type by part (2) of Stacks 04XS, and Stacks 045C carries the property across.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_comparison`: **Stacks 050H**, the
  locally-of-finite-type half of part (1).

## Implementation notes

Local finiteness of type is read in the sense of Properties of Stacks, Section 04XB, as
`AlgebraicGeometry.Stack.IsLocallyOfFiniteType` — the quantifier over the algebraic spaces
representing the base changes of `i` along scheme-valued points of `𝒳 ×_𝒯 𝒴`. This is the same
reading the other six assertions of Stacks 050H are proved with in
`StacksFrontier/AlgebraicGeometry/Stacks/FibreProductComparisonSeparation.lean`, and it is the
reading the source supports: `i` is representable by algebraic spaces by the other half of
part (1), and the proof cites Stacks 04XS together with *"the material in Properties of Stacks,
Section 04XB"* and nothing else.

The transport is `AlgebraicGeometry.Stack.relativeProperty_baseChange`, the instance-free form of
Stacks 045C, at `AlgebraicGeometry.Space.locallyOfFiniteTypeProperty`; no
`CategoryTheory.MorphismProperty.IsLocalAtTarget` instance for the fppf precoverage is needed and
none is registered. The input is the second component of part (2) of Stacks 04XS,
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack`, whose first
component is the representability of `Δ_{𝒵/𝒯}` that the statement of part (2) bundles.

This half needs neither Stacks 041S nor part (2) of Stacks 04YQ: the general form of part (2)
of Stacks 04XS needs no hypothesis on the 1-morphism and no locality instance.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 050H, part (1), locally-of-finite-type half.** The comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is locally of finite type, in the sense of Properties of Stacks,
Section 04XB.

By Stacks 04Z1 the comparison is the base change of the relative diagonal `Δ_{𝒵/𝒯}` along the
right-hand leg of `AlgebraicGeometry.Stack.comparisonSquare`; that diagonal is locally of finite
type by part (2) of Stacks 04XS, with no hypothesis on `h`, and Stacks 045C carries the property
across. Together with `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_comparison` this
is the whole of part (1). -/
@[stacks 050H "part (1): locally of finite type"]
theorem isLocallyOfFiniteType_comparison (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    IsLocallyOfFiniteType B S hS (comparison B S hS f g h).hom :=
  relativeProperty_baseChange.{u, u, u + 1} B S hS
    (Space.locallyOfFiniteTypeProperty B S hS)
    𝒵.val (twoFibreProductAlgebraicStack B S hS h h).val
    (twoFibreProductAlgebraicStack B S hS (f ≫ h) (g ≫ h)).val
    (relativeDiagonalAlgebraicStacks B S hS h).hom
    (comparisonCospanRight B S hS f g h).hom
    (comparisonSquare B S hS f g h)
    (isTwoFibreProduct_comparisonSquare B S hS f g h)
    (isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack.{u, w} B S hS h).choose_spec

end AlgebraicGeometry.Stack

end

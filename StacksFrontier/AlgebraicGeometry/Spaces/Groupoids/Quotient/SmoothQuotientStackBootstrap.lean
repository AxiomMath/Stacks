module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRepresentableDiagonal

/-!
# Stacks 04TK on the bootstrap theorem alone

**Stacks 04TK** says that the quotient stack `[U/R]` of a smooth groupoid in algebraic spaces is
an algebraic stack. It is formalized in this library as
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth`, carrying two hypotheses:
`AlgebraicGeometry.Stack.QuotientAtlas.Presentation`, which is **Stacks 04M9** in the 2-category
of categories fibred in groupoids, and
`AlgebraicGeometry.Stack.QuotientStackIsomSheavesAlgebraic`, which is the conclusion of
**Stacks 04TB**.

Both are discharged here. The first is
`AlgebraicGeometry.Stack.QuotientAtlas.presentation`. The second is Stacks 04TB,
`AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`, which itself carries only part (3) of
the bootstrap theorem **Stacks 04S6** — the one input of the whole chain that this library does
not prove, and which it carries everywhere in the packaged form
`AlgebraicGeometry.Stack.Bootstrap04S6`.

So what is left of Stacks 04TK is: *a smooth groupoid in algebraic spaces has an algebraic
quotient stack, granted the bootstrap theorem.*

## Main results

* `AlgebraicGeometry.Stack.quotientStackIsomSheavesAlgebraic`: **Stacks 04TB** in the packaged
  form its consumers take.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth_of_bootstrap`:
  **Stacks 04TK** with Stacks 04M9 and Stacks 04TB discharged.

## Implementation notes

`AlgebraicGeometry.Stack.quotientStackIsomSheavesAlgebraic` is the bridge term that four call
sites of the library already write inline —
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_quotientStack` (Stacks 04WZ) and
`AlgebraicGeometry.Stack.representable_quotientStackProjectionHom` among them — named once here
so that the Stacks 04TB hypothesis of
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_hasSmoothPresentation` can be fed
from `AlgebraicGeometry.Stack.Bootstrap04S6` directly.

The representability of the quotient-stack projection, the one field of the presentation that
Stacks 04M9 does not supply, is `AlgebraicGeometry.Stack.representable_quotientStackProjectionHom`
on the same bootstrap hypothesis, so no second input appears.

Stacks 04S6 is now proved (`AlgebraicGeometry.Stack.bootstrap04S6`), and Stacks 04TB and 04TK
hold without it (`AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`,
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth`); the two results here keep
their bootstrap hypothesis for the callers written against it, and no longer use it.

## References

* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **Stacks 04TB in the packaged form its consumers take.** Every isomorphism sheaf of a fibre
of the quotient stack of a groupoid in algebraic spaces is an algebraic space over the scheme the
fibre sits over.

This is `AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf` with its per-test-object
instance of the bootstrap theorem supplied from the packaged
`AlgebraicGeometry.Stack.Bootstrap04S6`. -/
theorem quotientStackIsomSheavesAlgebraic (G : GroupoidInAlgebraicSpaces C S hS B)
    (_h04S6 : Bootstrap04S6 C S hS) :
    QuotientStackIsomSheavesAlgebraic C S hS G :=
  fun T x y => isAlgebraicSpace_isomPresheaf C S hS B G T x y

/-- **Stacks 04TK with Stacks 04M9 and Stacks 04TB discharged.** Let `S` be a scheme contained in
a big fppf site, and let `G = (U, R, s, t, c)` be a smooth groupoid in algebraic spaces over an
algebraic space `B` over `S`. Then the quotient stack `[U/R]` of Stacks 044Q is an algebraic
stack over `S`.

The only input is part (3) of the bootstrap theorem **Stacks 04S6**, which this library does not
prove and carries everywhere as `AlgebraicGeometry.Stack.Bootstrap04S6`. Stacks 04M9 comes from
`AlgebraicGeometry.Stack.QuotientAtlas.presentation` and Stacks 04TB from
`AlgebraicGeometry.Stack.quotientStackIsomSheavesAlgebraic`. -/
theorem isAlgebraicStack_quotientStack_of_isSmooth_of_bootstrap
    {G : GroupoidInAlgebraicSpaces C S hS B} (_h04S6 : Bootstrap04S6 C S hS)
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) :=
  isAlgebraicStack_quotientStack_of_isSmooth hG

end AlgebraicGeometry.Stack

end

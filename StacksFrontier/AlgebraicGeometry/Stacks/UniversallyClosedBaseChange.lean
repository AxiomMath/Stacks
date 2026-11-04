module

public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedPoints
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Universal closedness is stable under base change (Stacks 0514)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is *universally closed*
(`AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyClosed`, **Stacks 0513** part (2)) when
every base change of it is closed on the topological spaces of points of Stacks 04XG and 04XL.
This file proves **Stacks 0514**: the property is inherited by a base change, so that if `f` is
universally closed and `R` is *any* 2-fibre product square of a cospan `(g, f)`, then the first
projection `R.fst` — the base change of `f` along `g` — is universally closed too.

The content is the pasting law for 2-fibre products,
`CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`, and nothing else. A base change of
`R.fst` along `h : 𝒵 ⟶ 𝒴'` is the outer rectangle of

```text
             R.fst
  𝒵 ×_𝒴' R.pt ---> R.pt ---> 𝒳
      |              |        |
   h' |              |        | f
      v              v        v
      𝒵 -----h----> 𝒴' ---g--> 𝒴
```

so it is *also* a 2-fibre product of the cospan `(h ≫ g, f)`; and a base change of `f` along
`h ≫ g` is closed because `f` is universally closed, by definition and with no further argument.
Closedness on points then transfers between the two 2-fibre products of that one cospan by
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_fst_congr`.

So the whole statement is the quantifier in the definition of `UniversallyClosed` reindexed
along `h ↦ h ≫ g`, and the pasting law is exactly what licenses the reindexing. That is worth
saying because the two obvious alternative routes are both unavailable: there is no stability
theorem for `AlgebraicGeometry.Stack.AlgebraicStacks.IsClosed` to invoke, and the canonical
iterated apex of Stacks 02XD
(`AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndSquareAlgebraicStacks`) recognises one
*particular* apex rather than an arbitrary pair of squares, so it cannot see `R`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_baseChange_of_isTwoFibreProduct`:
  universal closedness passes to the first projection of an arbitrary 2-fibre product square.

## Implementation notes

The statement is made at an **arbitrary** 2-fibre product square rather than at the canonical
one of Stacks 04T2, following
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_baseChange_of_isTwoFibreProduct` and its
siblings: the canonical form is the one-term instantiation `R :=
AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks B S hS g f`, and stating it at an
arbitrary square costs nothing here because `CategoryTheory.Bicategory.TwoCommSq.pasteFst`
already takes an arbitrary outer square.

The `@[stacks 0514]` attribute sits on the single theorem below, which is that tag's whole
covering set. Stacks 0513 part (2) is the *definition* of universal closedness, and its covering
set is carried separately by `AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyClosed` in
`StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack`; base-change stability is not an
assertion of that definition but the assertion of the lemma immediately after it, Stacks 0514,
whose statement is *"the base change of a universally closed morphism of algebraic stacks by any
morphism of algebraic stacks is universally closed"* and whose proof the source gives as *"this
is immediate from the definition"*. Registering the theorem under 0513 would have been the
covering-set rule inverted; registering it under 0514 is that rule applied.

## References

* [Stacks Project, Tag 0514](https://stacks.math.columbia.edu/tag/0514)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0514.** Universal closedness is stable under base change: let `f : 𝒳 ⟶ 𝒴` be a
universally closed 1-morphism of algebraic stacks over `S` and let `R` be a 2-fibre product
square of the cospan `(g, f)` for some `g : 𝒴' ⟶ 𝒴`. Then the base change `R.fst : R.pt ⟶ 𝒴'`
of `f` along `g` is universally closed.

The square is arbitrary, so this applies to any square a consumer has already exhibited as a
2-fibre product rather than only to the canonical one of Stacks 04T2. -/
@[stacks 0514]
theorem universallyClosed_baseChange_of_isTwoFibreProduct
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : UniversallyClosed B S hS f) :
    UniversallyClosed B S hS R.fst := by
  intro 𝒵 h
  exact Stack.isClosedMap_pointsMap_fst_congr B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS (h ≫ g) f).underlying
    (R.pasteFst (twoFibreProductSquareAlgebraicStacks B S hS h R.fst)).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (h ≫ g) f))
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Bicategory.isTwoFibreProduct_pasteFst R hR
        (twoFibreProductSquareAlgebraicStacks B S hS h R.fst)
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h R.fst)))
    (hf 𝒵 (h ≫ g))

end AlgebraicGeometry.Stack.AlgebraicStacks

end

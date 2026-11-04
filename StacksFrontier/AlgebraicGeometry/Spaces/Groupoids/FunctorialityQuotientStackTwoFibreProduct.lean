module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackFullyFaithful
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackSurjectivity

/-!
# The quotient stack of the auxiliary groupoid is the 2-fibre product (Stacks 04Y4)

Let `φ : G ⟶ G'` be a morphism of groupoids in algebraic spaces over an algebraic space `B` over
a scheme `S` of a big fppf site, written `f : U ⟶ U'` on object spaces, and let
`(U'', R'', s'', t'', c'')` be the groupoid in algebraic spaces over `B` of Section 78.21,

```
U'' = U ×_{f, U', t'} R',      R'' = R ×_{f ∘ s, U', t'} R',
s''(r, r') = (s(r), r'),       t''(r, r') = (t(r), c'(f(r), r')),
c''((r₁, r'₁), (r₂, r'₂)) = (c(r₁, r₂), r'₂).
```

Stacks 04Y4 asserts that the square

```
[U''/R''] ---[g]---> [U/R]
    |                  |
    |                 [φ]
    v                  v
  𝒮_{U'} ----π'----> [U'/R']
```

2-commutes and identifies `[U''/R'']` with the 2-fibre product `[U/R] ×_{[φ], [U'/R'], π'} 𝒮_{U'}`.
Here `[g]` is the 1-morphism of Stacks 046Q induced by the projection
`g : (U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)`, the vertical leg is the descent to `[U''/R'']`
of the `R''`-invariant morphism `U'' ⟶ U'`, `(u, r') ↦ s'(r')`, and `π'` is the canonical
projection of Stacks 044R.

## Main results

* `AlgebraicGeometry.Stack.isEquivalenceOver_auxQuotientComparison`: the comparison 1-morphism
  `[U''/R''] ⟶ [U/R] ×_{[U'/R']} 𝒮_{U'}` determined by the square is an equivalence over the big
  fppf site.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare`: **Stacks 04Y4** — the square is
  a 2-fibre product (Stacks 003Q) in the 2-category of stacks in groupoids over the big fppf
  site.

## Implementation notes

The square is `AlgebraicGeometry.Stack.auxQuotientSquare`; its 2-commutativity is the filler
`AlgebraicGeometry.Stack.auxSquareCell`, which at a point `(u, r')` of `U''` over a test object is
the arrow `r'` of the evaluated groupoid of `G'` running from `s'(r')` to `t'(r') = f(u)`, the
equality being the defining cartesian square of `U''`. The 2-fibre product property is
*terminality* in the category of 2-commutative squares over the cospan (Stacks 003O), which
transports along the comparison 1-morphism once that is an equivalence over the site; the
reduction is `AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare_of`.

The comparison 1-morphism is an equivalence because it is fully faithful
(`AlgebraicGeometry.Stack.auxQuotientComparison_full` and
`AlgebraicGeometry.Stack.auxQuotientComparison_faithful`) and locally essentially surjective on
fibres (`AlgebraicGeometry.Stack.locallyEssSurjOnFibers_auxQuotientComparison`), and the source is
a stack, so Stacks 046N in the form
`AlgebraicGeometry.Stack.isEquivalenceOver_functorialityTwoFibreProduct` applies.

The object-space side of the cospan is the universe-enlarged fibred category
`AlgebraicGeometry.Stack.liftedFibredCategory`, exactly as in the square of Stacks 04ZN: the
enlargement is what lets the three categories of the cospan share a hom universe, which is what
condition (2) of Stacks 026F asks of a 2-fibre product, and it changes neither the stack nor the
projection `π'`, which is the un-enlarged one precomposed with the canonical equivalence.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 026G](https://stacks.math.columbia.edu/tag/026G)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-- **The comparison 1-morphism of the square of Section 78.21 is an equivalence over the big
fppf site.** It is fully faithful and locally essentially surjective on fibres, and its source
`[U''/R'']` is a stack, so descent is effective there; Stacks 046N in the form
`AlgebraicGeometry.Stack.isEquivalenceOver_functorialityTwoFibreProduct` turns the two into a
quasi-inverse over the site with vertical unit and counit. -/
theorem isEquivalenceOver_auxQuotientComparison (φ : Hom G G') :
    Nonempty (Functor.IsEquivalenceOver (quotientStack (auxGroupoid φ)).p
      (functorialityTwoFibreProduct φ) (auxQuotientComparison φ)) :=
  have := auxQuotientComparison_full φ
  have := auxQuotientComparison_faithful φ
  have : (quotientStack (auxGroupoid φ)).p.IsFibered :=
    (isStack_quotientStack (auxGroupoid φ)).isFibered
  isEquivalenceOver_functorialityTwoFibreProduct φ
    (isStack_quotientStack (auxGroupoid φ)).hasEffectiveDescent
    (isFibredOneMorphism_auxQuotientComparison φ)
    (locallyEssSurjOnFibers_auxQuotientComparison φ)

/-- **Stacks 04Y4.** Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in
algebraic spaces over an algebraic space `B` over a scheme `S` of a big fppf site, written
`f : U ⟶ U'` on object spaces, and let `(U'', R'', s'', t'', c'')` be the groupoid in algebraic
spaces over `B` of Section 78.21, with `U'' = U ×_{f, U', t'} R'`, `R'' = R ×_{f ∘ s, U', t'} R'`,
`s''(r, r') = (s(r), r')`, `t''(r, r') = (t(r), c'(f(r), r'))` and
`c''((r₁, r'₁), (r₂, r'₂)) = (c(r₁, r₂), r'₂)`. Then the square

```
[U''/R''] ---[g]---> [U/R]
    |                  |
    |                 [φ]
    v                  v
  𝒮_{U'} ----π'----> [U'/R']
```

— whose horizontal arrow is the 1-morphism `[g]` of Stacks 046Q induced by the projection
`g : (U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)`, whose vertical arrow on the left is the descent
to `[U''/R'']` of the `R''`-invariant morphism `U'' ⟶ U'`, `(u, r') ↦ s'(r')`, whose vertical
arrow on the right is the 1-morphism `[φ]` of Stacks 046Q, whose lower horizontal arrow is the
canonical projection `π'` of Stacks 044R, and whose filler
`AlgebraicGeometry.Stack.auxSquareCell` is the arrow `r'` of the evaluated groupoid of `G'` at a
point `(u, r')` of `U''` — **is a 2-fibre product** in the 2-category of stacks in groupoids over
the big fppf site, so it identifies `[U''/R'']` with `[U/R] ×_{[φ], [U'/R'], π'} 𝒮_{U'}`. -/
@[stacks 04Y4 "the 2-commutative square of Section 78.21 and the identification of the \
quotient stack of the auxiliary groupoid with the 2-fibre product of the cospan"]
noncomputable def isTwoFibreProduct_auxQuotientSquare (φ : Hom G G') :
    Bicategory.IsTwoFibreProduct (auxQuotientSquare φ) :=
  isTwoFibreProduct_auxQuotientSquare_of φ (auxQuotientComparison_full φ)
    (auxQuotientComparison_faithful φ) (locallyEssSurjOnFibers_auxQuotientComparison φ)

end AlgebraicGeometry.Stack

end

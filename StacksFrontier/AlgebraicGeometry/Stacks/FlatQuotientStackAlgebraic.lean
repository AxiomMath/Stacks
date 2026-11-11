module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackShrinkHoms

/-!
# The quotient stack of a flat, locally finitely presented groupoid is algebraic (Stacks 06FI)

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S` with `s` and `t` flat and locally
of finite presentation. Then the quotient stack `[U/R]` is an algebraic stack over `S`.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_flat`: **Stacks 06FI**.
* `AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack_of_flat`: the same, quantified
  over the groupoids on a fixed base.

## References

* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over
a scheme `S` of a big fppf site. If the source and the target of `G` are flat and locally of finite
presentation, then the quotient stack `[U/R]` is an algebraic stack over `S`.

The source states it for a groupoid over `S`; a groupoid over `A` is the more general statement,
the source's case being `A = S`, with `S` the final algebraic space over `S`. Nothing is assumed:
the proof is Artin's theorem **Stacks 06DC**,
`AlgebraicGeometry.Stack.isAlgebraicStack_of_flatCover`, applied to the projection
`S_U ⟶ [U/R]` of Stacks 044R, read with the morphisms of `[U/R]` shrunk to the site's universe.
The projection is representable by algebraic spaces by Stacks 04WZ and Stacks 04TB, and it is
surjective, flat and locally of finite presentation by **Stacks 06FH**. -/
@[stacks 06FI "stated for a groupoid in algebraic spaces over an arbitrary algebraic space A over \
S, the source's groupoid over S being the case A = S; Stacks 06DC, 06FH and 04TB are proved"]
theorem isAlgebraicStack_quotientStack_of_flat {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (hsflat : Space.IsFlat C S hS G.source.hom)
    (htflat : Space.IsFlat C S hS G.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) :=
  isAlgebraicStack_quotientStack_of_small G
    (isAlgebraicStack_of_flatCover (smallQuotientStackProjection G)
      (isStack_smallQuotientStackCFG G)
      (isRepresentableByAlgebraicSpace_fibredCategory C S hS G.objects.obj G.objects.property)
      (isRepresentableByAlgebraicSpaces_smallQuotientStackProjection G)
      (surjective_flat_lfp_smallQuotientStackProjection G hsflat htflat hslfp htlfp))

/-- Every groupoid in algebraic spaces over `A` whose source and target are flat and locally of
finite presentation has an algebraic quotient stack. -/
theorem forall_isAlgebraicStack_quotientStack_of_flat (A : AlgebraicSpaces C S hS) :
    ∀ H : GroupoidInAlgebraicSpaces C S hS A,
      Space.IsFlat C S hS H.source.hom → Space.IsFlat C S hS H.target.hom →
        Space.IsLocallyOfFinitePresentation C S hS H.source.hom →
          Space.IsLocallyOfFinitePresentation C S hS H.target.hom →
            IsAlgebraicStack.{u, w} C S hS (quotientStack H) :=
  fun H => isAlgebraicStack_quotientStack_of_flat H

end AlgebraicGeometry.Stack

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.Uniqueness

/-! # Recognising the quotient stack of a groupoid in algebraic spaces

Let `B` be an algebraic space over a scheme `S` of a big fppf site and let `G` be a groupoid in
algebraic spaces over `B`. By Stacks 044Q the quotient stack `[U/R]` of `G` is the stackification
of the pointwise groupoid fibration of `G`, and the tree already proves that the canonical
1-morphism `AlgebraicGeometry.Stack.toQuotientStack` satisfies the two clauses of Stacks 02ZN:
`AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack` is clause (1) and
`AlgebraicGeometry.Stack.essImage_toQuotientStack` is clause (2).

Feeding those to the determinacy clause of Stacks 02ZN and 02ZP,
`CategoryTheory.Functor.Stackification.nonempty_isEquivalenceOver_extend`, turns the two clauses
into a **recognition criterion for the quotient stack**: a 1-morphism from the pointwise groupoid
fibration into a stack which again satisfies them exhibits that stack as `[U/R]`, up to
equivalence over the site.

That is how Stacks 05YQ identifies the stack `ℋ_d` of degree-`d` finite locally free covers with
the quotient stack `[X/G]` of the conjugation action: it exhibits a 1-morphism
`Spec : FA_d ⟶ ℋ_d` out of the pointwise groupoid fibration of the action groupoid, checks the two
clauses for it — clause (a) of that proof being clause (1) and clause (b) being clause (2) — and
cites Stacks 02ZP.

## Main results

* `AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_extend_toQuotientStack`: a 1-morphism from
  the pointwise groupoid fibration of `G` into a stack over the big fppf site satisfying the two
  clauses of Stacks 02ZN extends to an equivalence of the quotient stack `[U/R]` with that stack
  over the site.

## Implementation notes

The hypotheses are read on `AlgebraicGeometry.Stack.quotientPrestack`, the pointwise groupoid
fibration with its morphisms raised to `Type (u + 1)`, and not on the unlifted
Grothendieck construction. That is the only shape available: the stackification used is the
explicit three-stage construction, which needs objects and morphisms in one universe, so the two
clauses of Stacks 02ZN are proved in the tree for `AlgebraicGeometry.Stack.toQuotientStack` out of
the lifted fibration, and only `IsFibredOneMorphism` is proved for
`AlgebraicGeometry.Stack.pointwiseToQuotientStack`. The lift is an equivalence commuting strictly
with the projection to the site, `AlgebraicGeometry.Stack.quotientPrestackEquivalence`, so a
1-morphism out of the unlifted fibration may be transported across it.

For the same reason the target's morphism universe is pinned to `u + 1`: the comparison of
morphism presheaves that clause (1) speaks about has the morphism universes of its two categories
for its values.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 02ZP](https://stacks.math.columbia.edu/tag/02ZP)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u u₄

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  {𝒳 : Type u₄} [Category.{u + 1} 𝒳] {q : 𝒳 ⥤ BigFppfOver C S hS} [q.IsFibered]
  {K : (quotientPrestack G).obj ⥤ 𝒳}
  (hK : (quotientPrestack G).p.IsFibredOneMorphism q K)
  (hKmor : ∀ (U : BigFppfOver C S hS) (a b : (quotientPrestack G).p.Fiber U),
    Presheaf.IsLocallyInjective ((BigFppfOver.topology C S hS).over U)
        (hK.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective ((BigFppfOver.topology C S hS).over U)
        (hK.morPresheafMap a b))
  (hKobj : ∀ (U : BigFppfOver C S hS) (x : q.Fiber U),
    ∃ R ∈ BigFppfOver.topology C S hS U, ∀ ⦃V : BigFppfOver C S hS⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (Functor.fiberFunctorOfCompEq hK.comp_eq V).essImage (Functor.pullbackFiber q x f))
  (hq : q.IsStack (BigFppfOver.topology C S hS))

include hKmor hKobj hq

/-- **A 1-morphism out of the pointwise groupoid fibration satisfying the two clauses of
Stacks 02ZN exhibits its target as the quotient stack.** Let `G` be a groupoid in algebraic spaces
over an algebraic space `B` of a big fppf site, let `q` be a stack over that site and let
`K : quotientPrestack G ⥤ 𝒳` be a 1-morphism of fibred categories over the site such that

* `hKmor`, the induced maps of morphism presheaves are locally injective and locally surjective,
  so that `q` sheafifies the morphism presheaves of the presentation, and
* `hKobj`, every object of a fibre of `q` is, along a covering sieve, in the essential image of `K`
  on fibres.

Then the extension of `K` along `AlgebraicGeometry.Stack.toQuotientStack` is an equivalence of the
quotient stack `[U/R]` of Stacks 044Q with `q`, over the big fppf site.

The two clauses for `AlgebraicGeometry.Stack.toQuotientStack` itself are
`AlgebraicGeometry.Stack.isLocallyBijective_toQuotientStack` and
`AlgebraicGeometry.Stack.essImage_toQuotientStack`, and `[U/R]` is a stack by
`AlgebraicGeometry.Stack.isStack_quotientStack`; the conclusion is then the determinacy clause of
Stacks 02ZN and 02ZP,
`CategoryTheory.Functor.Stackification.nonempty_isEquivalenceOver_extend`. -/
theorem nonempty_isEquivalenceOver_extend_toQuotientStack :
    Nonempty (Functor.IsEquivalenceOver (quotientStack G).p q
      (Functor.Stackification.extend (isFibredOneMorphism_toQuotientStack G) hK
        (isLocallyBijective_toQuotientStack G) hq.isMorSheaf (essImage_toQuotientStack G)
        hq.hasEffectiveDescent)) :=
  Functor.Stackification.nonempty_isEquivalenceOver_extend
    (isFibredOneMorphism_toQuotientStack G) (BigFppfOver.topology C S hS) hK
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G) hKmor hKobj
    (isStack_quotientStack G) hq

end AlgebraicGeometry.Stack

end

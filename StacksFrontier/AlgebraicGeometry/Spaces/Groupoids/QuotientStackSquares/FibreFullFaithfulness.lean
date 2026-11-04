module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence

/-!
# Full faithfulness of the presentation of a quotient stack on each fibre (Stacks 044X)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `[U/R]` be its quotient stack and let
`π : 𝒮_U ⟶ [U/R]` be the canonical 1-morphism from the pointwise groupoid presentation. On the
fibre over a single test object `T`, `π` is fully faithful: a transition isomorphism between two
objects of `[U/R]_T` that come from points of the object space is the image under `π` of a unique
arrow of the arrow space.

## Main results

* `AlgebraicGeometry.Stack.fullyFaithful_fiberFunctor_toQuotientStack`: **Stacks 044X**,
  part (2) on a single test object.

## Implementation notes

This is Stacks 044V — the identification of the isomorphism sheaf of two objects of the quotient
stack coming from points of `U` with the fibre of the arrow space — read through the identity map
of the test object: over the terminal object of `(BigFppfOver C S hS)/T` the induced map of
morphism presheaves *is* the action of `π` on the fibre over `T`, conjugated by the comparison
isomorphisms with the chosen pullbacks along the identity. That reduction is
`CategoryTheory.Comma.bijective_fiberFunctor_map_of_bijective_app`.

The statement asserts the *existence* of a `CategoryTheory.Functor.FullyFaithful` witness rather
than producing one: the witness is not canonical, since the inverse on hom-sets is obtained from
a bijection.

## References

* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **Stacks 044X**, part (2). A transition isomorphism between two objects of a fibre of the
quotient stack that come from points of the object space is the image under `π` of a unique
arrow of the arrow space: the functor induced by `π` on the fibre over any test object is fully
faithful. This is Stacks 044V read through the identity map of the test object. -/
@[stacks 044X "part (2): transition arrows"]
theorem fullyFaithful_fiberFunctor_toQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) :
    Nonempty (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_toQuotientStack G).comp_eq T).FullyFaithful := by
  refine (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr fun x y => ?_
  have := isomPresheaf_equiv_arrowFiber C S hS G T x y
  exact Comma.bijective_fiberFunctor_map_of_bijective_app
    (isFibredOneMorphism_toQuotientStack G) x y ((isIso_iff_bijective _).mp inferInstance)

end AlgebraicGeometry.Stack

end

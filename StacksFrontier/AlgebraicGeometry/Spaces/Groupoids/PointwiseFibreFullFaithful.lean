module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FibreFullFaithfulness
public import StacksFrontier.CategoryTheory.Sites.Stackification.RawLocalEquality

/-!
# The groupoid of points maps fully faithfully into the fibre of the quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space over a scheme
`S` of a big fppf site, and let `[U/R]` be its quotient stack. Over a test object `T`, the
groupoid of points of `G` maps to the fibre `[U/R]_T` by
`AlgebraicGeometry.Stack.pointwiseToQuotientStackFiber`, and that functor is fully faithful: an
arrow between two points of the object space over `T` is the same thing as a morphism of `[U/R]_T`
between the two objects they present.

This is part (2) of Stacks 044X —
`AlgebraicGeometry.Stack.fullyFaithful_fiberFunctor_toQuotientStack` — read through the two
equivalences that separate the groupoid of points from the fibre of the pointwise groupoid
fibration: the fibre inclusion of the Grothendieck construction, which is an equivalence onto the
fibre, and the universe lift of the morphisms.

## Main results

* `AlgebraicGeometry.Stack.fullyFaithful_pointwiseToQuotientStackFiber`: **Stacks 044X**, part (2),
  read on the groupoid of points.

## Implementation notes

The three functors compose on the nose: both the factorisation of
`AlgebraicGeometry.Stack.pointwiseToQuotientStackFiber` through the fibre inclusion of the
Grothendieck construction and the factorisation of the fibre functor of
`AlgebraicGeometry.Stack.pointwiseToQuotientStack` through the universe lift hold by `rfl`, so the
full faithfulness of the composite transfers without a comparison isomorphism.

## References

* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Deformation

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **Stacks 044X, part (2), read on the groupoid of points.** The functor from the groupoid of
points of `G` at a test object `T` to the fibre of the quotient stack over `T` is fully faithful:
a morphism of `[U/R]_T` between two presented objects is the image of a unique arrow of the
groupoid of points.

The functor is the composite of the fibre inclusion of the Grothendieck construction, which is an
equivalence onto the fibre, the fibre functor of the universe lift of the morphisms, which is fully
faithful because the universe lift is an equivalence strictly over the site, and the fibre functor
of the stackification, which is fully faithful by part (2) of Stacks 044X. -/
theorem fullyFaithful_pointwiseToQuotientStackFiber
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS) :
    Nonempty (pointwiseToQuotientStackFiber G T).FullyFaithful := by
  obtain ⟨hlift⟩ := Functor.fullyFaithful_fiberFunctorOfCompEq
    (quotientPrestackEquivalence_comp G) inferInstance inferInstance T
  obtain ⟨hstack⟩ := fullyFaithful_fiberFunctor_toQuotientStack G T
  have hincl : (Functor.Fiber.inducedFunctor (CoGrothendieck.comp_const
      (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' T)).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  exact ⟨hincl.comp (hlift.comp hstack)⟩

end AlgebraicGeometry.Stack

end

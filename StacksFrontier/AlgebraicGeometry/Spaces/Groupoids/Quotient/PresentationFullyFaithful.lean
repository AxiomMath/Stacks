module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FibreFullFaithfulness

/-!
# The presentation of a quotient stack is fully faithful

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site. The canonical 1-morphism from the pointwise groupoid fibration of
`G` to the quotient stack `[U/R]` is fully faithful as a functor, both out of the presentation
`AlgebraicGeometry.Stack.quotientPrestack` and out of the unlifted pointwise groupoid fibration.

## Main results

* `AlgebraicGeometry.Stack.fullyFaithfulToQuotientStack`: the stackification map
  `[U/_pR] ⥤ [U/R]` out of the presentation is fully faithful.
* `AlgebraicGeometry.Stack.fullyFaithfulPointwiseToQuotientStack`: the same for the map out of
  the unlifted pointwise groupoid fibration.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The stackification map out of the presentation of a quotient stack is fully faithful.** -/
noncomputable def fullyFaithfulToQuotientStack (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toQuotientStack G).FullyFaithful := by
  have h := (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
    (quotientPrestack G).p (quotientStack G).p
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G)
    (toQuotientStack G)
    (isFibredOneMorphism_toQuotientStack G).comp_eq).2
    (fun T => ⟨(fullyFaithful_fiberFunctor_toQuotientStack G T).some.full,
      (fullyFaithful_fiberFunctor_toQuotientStack G T).some.faithful⟩)
  have : (toQuotientStack G).Full := h.1
  have : (toQuotientStack G).Faithful := h.2
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- **The map from the unlifted pointwise groupoid fibration to the quotient stack is fully
faithful.** -/
noncomputable def fullyFaithfulPointwiseToQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwiseToQuotientStack G).FullyFaithful :=
  (quotientPrestackEquivalence G).fullyFaithfulFunctor.comp (fullyFaithfulToQuotientStack G)

end AlgebraicGeometry.Stack

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionSquaringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TwistedLineQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient

/-!
# The quotient map of a group action is the canonical map of its graph relation

The quotient of an object `V` of a big fppf site by a group action is the quotient sheaf of the
graph relation of the action (**Stacks 02Z2**), and there are two maps from `V` into it: the
projection `AlgebraicGeometry.Space.actionProjection`, defined through the functor of points of
`V`, and the canonical quotient map `AlgebraicGeometry.Space.quotientMap` of **Stacks 02WW**,
defined by the Yoneda correspondence at the identity section.  This file identifies them.

## Main results

* `AlgebraicGeometry.Space.quotientMap_eq_actionProjection`: the two maps agree.

## References

* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Groupoids

universe u v

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u})
  (hS : B.Contains S) (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))
  (hR : B.Contains (actionRelationScheme (underlyingOver B hS V) G).left)

/-- **The canonical quotient map of the graph relation of a group action is the projection onto
the quotient.** -/
theorem quotientMap_eq_actionProjection :
    quotientMap B S hS (siteActionRelationSource G B hS V hR)
        (siteActionRelationTarget G B hS V hR a) =
      actionProjection G B hS V a := by
  rw [quotientMap, ← yonedaEquiv_symm_naturality_right, pointsYonedaIso_inv_eq, actionProjection]
  rfl

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
import all StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits

/-!
# The statement of affine-stage descent for a site

`AlgebraicGeometry.Space.HasAffineStageDescentOfSmallIndex`: the statement of Stacks 07SQ for the
big fppf site `B`, that an affine limit of a descent situation indexed small compared to the
cofinality of the site's size cutoff has an affine stage.

These declarations supplement `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits`.
They live in their own module.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

/-- **Stacks 07SQ.** In the situation of Stacks 084R, if the limit of the inverse system is an
affine algebraic space then some stage beyond the distinguished one is an affine algebraic
space.

The index is required to be small compared to the cofinality of the site's size cutoff, which
is what keeps the limit computed in the site equal to the limit the source speaks of; see the
implementation notes of this module for the system that refutes the statement without that
restriction, and `AlgebraicGeometry.Space.HasAffineStageDescentOfSmallIndex` is stated with the
same bound `#I < B.cutoff.ord.cof` as the field
`AlgebraicGeometry.Space.MorphismDescentSystem.indexSize`.

Stacks 07SI, the identification `Γ(X, 𝒪_X) = colim_i Γ(X_i, 𝒪_{X_i})` that supplies the ring
an affine stage maps to, is
`AlgebraicGeometry.Space.DescentSituation.isStagesColimit_modelProjection`, and the étale
algebra of the chart of the affine limit is
`AlgebraicGeometry.Space.etale_globalFunctionsChartRestriction`, both in
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineStage.lean`.

This property holds of every big fppf site: `AlgebraicGeometry.Space.hasAffineStageDescent` of
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineStageDescent.lean` proves it, as
a case of `AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj_of_bounded`,
whose size hypothesis — the base changes of the stages along affine points are bounded below the
cutoff — is implied by the bound on the index set and also covers an index of any size below a
singular cutoff whose transition morphisms are closed immersions or finite. The tag is carried by
`DescentSituation.exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits`, the statement
under the convention of Section 70.2 (tag 07SD). -/
def HasAffineStageDescentOfSmallIndex (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) : Prop :=
  ∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] (E : DescentSituation B S hS hZ J),
    Cardinal.mk J < B.cutoff.ord.cof → IsAffineSpace B S hS E.limitCone.pt →
      ∃ j, E.base ≤ j ∧ IsAffineSpace B S hS (E.system.obj (Opposite.op j))

end AlgebraicGeometry.Space

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCoverSurjective
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# The chart fibre products of `X ×_Y Z` cover it

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of fppf sheaves on the big fppf site of `S`. Given a family `{Vⱼ ⟶ Y}` inducing a
surjection of sheaves and, for each `j`, families `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and `{Wⱼₖ ⟶ Vⱼ ×_Y Z}`
inducing surjections of sheaves, the fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` induce a surjection of
sheaves onto `X ×_Y Z`. This is the assertion of the proofs of Stacks 0GBB and Stacks 0GBD that
the family `{Xⱼᵢ ×_{Yⱼ} Zⱼₖ ⟶ X ×_Y Z}` is a covering as in Definition 0AIM, as far as joint
surjectivity goes.

## Main results

* `AlgebraicGeometry.FormalSpace.hasChartPullbackCover`: the hypothesis
  `AlgebraicGeometry.FormalSpace.HasChartPullbackCover` holds for every pair of morphisms.

## Implementation notes

The joint surjectivity of the chart fibre products is
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_chartPullbackMap`, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCoverSurjective`; this file reads it
at the shape of `AlgebraicGeometry.FormalSpace.HasChartPullbackCover`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart cover of `X ×_Y Z` is jointly surjective**, for all morphisms `f` and `g`: the
covering condition of Definition 0AIM for the family of chart fibre products used in the proofs
of Stacks 0GBB and Stacks 0GBD holds unconditionally. -/
theorem hasChartPullbackCover {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) :
    HasChartPullbackCover B S hS f g := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro J V v hv I U a ha K W b hb
  exact isLocallySurjective_sigmaDesc_chartPullbackMap B S hS f g v hv.2.2 a (fun j ↦ (ha j).2.2)
    b (fun j ↦ (hb j).2.2)

end AlgebraicGeometry.FormalSpace

end

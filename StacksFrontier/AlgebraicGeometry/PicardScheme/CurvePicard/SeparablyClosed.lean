module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Representability
public import StacksFrontier.AlgebraicGeometry.Curves.BaseChangeTwistLowCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed

/-!
# Smooth projective curves over a separably closed field are normalized by twisting

Let `k` be separably closed and `X` a smooth projective curve over `k`. The conclusion of
[Stacks, Tag 0B9Y] holds for `X`
(`AlgebraicGeometry.exists_invertible_baseChangeTwist_finrank_eq_one_of_isSepClosed`), in the form
`Stacks.PicardFunctor.TwistToNormalized` that the local charts of the Picard scheme consume
(`StacksFrontier/AlgebraicGeometry/PicardScheme/CurvePicard/LocalCharts.lean`). Representability of
the Picard functor itself, [Stacks, Tag 0B9Z], is
`Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed`.

## Main results

* `Stacks.PicardFunctor.twistToNormalized_of_isSepClosed`: the conclusion of Tag 0B9Y.

## References

* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

/-- **The conclusion of [Stacks, Tag 0B9Y] for a smooth projective curve over a separably closed
field**, in the form the representability argument consumes. -/
theorem twistToNormalized_of_isSepClosed [IsSepClosed k] [IsCurve k (B.inclusion.map f)]
    [Smooth (B.inclusion.map f)] (hproj : IsProjective (B.inclusion.map f)) :
    TwistToNormalized B hX hk f :=
  fun K _ _ _ f' p hp L _ =>
    exists_invertible_baseChangeTwist_finrank_eq_one_of_isSepClosed k K (B.inclusion.map f) f' p
      hp hproj L

end Stacks.PicardFunctor

end

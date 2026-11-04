module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Flatness of the base-changed module of the functor of quotients

For the data `(X ⟶ Y, F)` of Stacks 082M with `F` flat over `Y`, the base change `F_T` of `F` to a
test scheme `T` over `Y` is flat over `T` (Stacks 05VW at the cartesian square of the base
change). This is the flatness of `F_{T'}` over `T'` that the deformation theory of the functor of
quotients (Stacks 0CZU, 0CZV) starts from.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.isPullback_baseChange`: the base change square is
  cartesian.
* `AlgebraicGeometry.Space.QuotientSituation.isFlatOver_baseChangeModule`: `F` flat over `Y`
  implies `F_T` flat over `T`.

## References

* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- The base change `X_T = X ×_Y T` of the situation is the fibre product, as a cartesian square
`X_T ⟶ X`, `X_T ⟶ T` over `X ⟶ Y`, `T ⟶ Y`. -/
theorem isPullback_baseChange (T : SchemesOver D.Y) :
    IsPullback (D.sourceProjection T) (D.projection T) D.f
      ((schemesOverToOver D.Y).obj T).hom :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS D.f ((schemesOverToOver D.Y).obj T).hom

/-- **If `F` is flat over `Y` then `F_T` is flat over `T`** (Stacks 05VW at the cartesian square
of the base change). This is the flatness of `F_{T'}` over `T'` that Stacks 0CZU and 0CZV derive
from the hypothesis that `F` is flat over `B`. -/
theorem isFlatOver_baseChangeModule (hF : IsFlatOver B S hS D.X.2 D.f.hom D.F)
    (T : SchemesOver D.Y) :
    IsFlatOver B S hS (D.space T).2 (D.projection T).hom (D.baseChangeModule T) := by
  have := D.quasicoherent
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.sourceProjection T) D.F D.quasicoherent
  exact isFlatOver_modulePullback B S hS (D.isPullback_baseChange T) D.F hF

end QuotientSituation

end AlgebraicGeometry.Space

end

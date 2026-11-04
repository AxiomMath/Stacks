module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullbackRepresents
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleBlowup

/-!
# A good triple is good over every morphism with defined divisor pullback

Part (3) of Stacks tag 0F8T says that goodness of a triple `(X, D, M)` as in Situation 0F8S is
inherited by the pulled-back triple `(Y, h⁻¹D, Lh^*M)` along any `h : Y ⟶ X` for which `h⁻¹D` is
defined.  Condition (1) of Stacks tag 0GTY is named in this library as
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodOver`, the conjunction of those two
statements, so part (3) is exactly what produces an `IsGoodOver` from goodness of the triple.
This file records that implication, and its two automatic cases: a flat `h`, and the inclusion
of an open subscheme.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_of_isGoodTriple`: a good triple is
  good over any morphism along which the divisor's pullback is defined.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_of_flat`: for a flat `h` the
  definedness of the pullback is automatic, by Stacks tag 02OO (6).
* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_ι`: in particular a good triple is
  good over the inclusion of every open subscheme, open immersions being flat.

## Implementation notes

The hypotheses of the statements registered for tags 0F8U, 0F8V, 0F8W and 0F8X in this
directory are phrased with `IsGoodOver`, so these are the shape in which part (3) of tag 0F8T
reaches them.  They do not discharge those hypotheses for the morphism `b` of tag 0GTY: there
the base triple is *not* assumed good — `b` is what makes it good — so goodness of
`(X', b⁻¹D, Lb^*M)` is not an instance of part (3).

## References

* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A good triple is good over every morphism along which the divisor's pullback is
defined.**  The two fields of `IsGoodOver` are the hypothesis itself and part (3) of Stacks tag
0F8T, `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodTriple_pullback`. -/
theorem isGoodOver_of_isGoodTriple (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined h S.D) (hS : IsGoodTriple S) :
    S.IsGoodOver h where
  pullbackDefined := hD
  isGoodTriple := S.isGoodTriple_pullback h hD hS

/-- **A good triple is good over every flat morphism.**  The pullback of an effective Cartier
divisor along a flat morphism is defined, by Stacks tag 02OO (6)
(`Stacks.Divisors.isPullbackDefined_of_flat`), so no hypothesis beyond flatness is needed. -/
theorem isGoodOver_of_flat (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) [AlgebraicGeometry.Flat h] (hS : IsGoodTriple S) :
    S.IsGoodOver h :=
  S.isGoodOver_of_isGoodTriple h
    (Stacks.Divisors.isPullbackDefined_of_flat h S.D S.isEffectiveCartierDivisor) hS

/-- **A good triple is good over the inclusion of every open subscheme.**  An open immersion is
flat, so this is `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_of_flat`. -/
theorem isGoodOver_ι (S : ComplexAndDivisorSituation.{u, d}) (V : S.X.Opens)
    (hS : IsGoodTriple S) :
    S.IsGoodOver V.ι :=
  S.isGoodOver_of_flat V.ι hS

end AlgebraicGeometry.ComplexAndDivisorSituation

end

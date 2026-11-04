module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupTag
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfectOfIsGoodOver

/-!
# Stacks tag 0F8U at the morphism of tag 0GTY

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be the morphism of Stacks tag
0GTY and let `D' = b⁻¹D` with ideal sheaf `ℐ'`.  Stacks tag 0F8U asserts that
`Q = Lη_{ℐ'}Lb^*M` is a perfect object of `D(𝒪_{X'})`.

`GoodOverEtaPerfect.lean` states this for a morphism `b` satisfying condition (1) of tag 0GTY.
The morphism of tag 0GTY satisfies it, by
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_goodBlowupToBase`, so this file reads
the statement off at that morphism: `b` is the one tag 0GTY produces,
`AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase`.

## Main results

* `isPerfect_etaDerivedPullbackObject_goodBlowupToBase`:
  **Stacks tag 0F8U for the morphism of tag 0GTY**, with the affine-chart comparison for the
  derived décalage of the pulled-back divisor as the hypothesis `hcomp`.

## The hypothesis `hcomp`

`hcomp` is `AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage` for the pulled-back
triple `(X', D', Lb^*M)`: on an affine chart `(V, B, g, N^•)` of that triple whose determinantal
ideals are principal, the restriction of `Lη_{ℐ'}Lb^*M` to `V` is identified with the complex of
`𝒪_V`-modules coming from the algebraic décalage `η_g N^•`.  It is the hypothesis of the
formalization of Stacks tag 0GTW,
`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEta_obj`, and is the second
assertion of Stacks tag 0GTV read at an affine open of a general scheme rather than on a
spectrum; the statement on a spectrum is
`Stacks.Divisors.Eta.derivedEta_isQuasicoherent_and_affineComparison`.  What separates the two
breaks into three identifications, analysed in the module documentation of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect`: the commutation of
`Lη` with restriction along an open immersion
(`Stacks.Divisors.Eta.derivedEtaRestrictOpenObjIso`), the transport along `V ≅ Spec Γ(X', V)`
(`Stacks.AffineTilde.transportTildeComplexIsoRestrict`), and the affine statement over
`Γ(X', V)` itself, which is the one of the three with no declaration behind it.

The companion hypothesis of tag 0GTW, charts with principal determinantal ideals at the points
off the divisor, is discharged here and in `ChartBasis.lean`: see
`exists_chart_isPrincipal_determinantalIdeal_of_notMem_supportSet` in the namespace
`AlgebraicGeometry.ComplexAndDivisorSituation`.

## References

* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : ComplexAndDivisorSituation.{u, d})

/-- **Stacks tag 0F8U for the morphism `b : X' ⟶ X` of Stacks tag 0GTY.**  In Situation 0F8S let
`b` be the morphism of tag 0GTY and `D' = b⁻¹D` with ideal sheaf `ℐ'`.  Then
`Q = Lη_{ℐ'}Lb^*M` is a perfect object of `D(𝒪_{X'})`.

The morphism is `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase`; it satisfies
condition (1) of tag 0GTY by
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_goodBlowupToBase`, so this is
`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_etaDerivedPullbackObject_of_chartDecalage`
read at it.  The hypothesis `hcomp` is the affine-chart comparison for `Lη_{ℐ'}` described in
the module documentation. -/
@[stacks 0F8U "perfectness of `Q = Lη_{I'} Lb^* M` for the morphism `b` of tag 0GTY itself, \
namely AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase, with the datum `hcomp` of \
the formalization of tag 0GTW: the second assertion of tag 0GTV read at an affine open of `X'`"]
theorem isPerfect_etaDerivedPullbackObject_goodBlowupToBase
    (hcomp : ChartDecalage
      (S.pullback S.goodBlowupToBase S.isGoodOver_goodBlowupToBase.pullbackDefined)
      (@Stacks.Divisors.Eta.derivedEtaData S.goodBlowup (S.D.comap S.goodBlowupToBase)
        S.isGoodOver_goodBlowupToBase.pullbackDefined)) :
    RingedSpace.IsPerfect (X := S.goodBlowup.toRingedSpace)
      (S.etaDerivedPullbackObject S.goodBlowupToBase
        S.isGoodOver_goodBlowupToBase.pullbackDefined) :=
  S.isPerfect_etaDerivedPullbackObject_of_isGoodOver_of_chartDecalage S.goodBlowupToBase
    S.isGoodOver_goodBlowupToBase hcomp

end AlgebraicGeometry.ComplexAndDivisorSituation

end

module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfectOffDivisor
public import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up complexes: Stacks tag 0F8U for a morphism good for the triple

For `b : X' ⟶ X` good for a triple `(X, D, M)` as in Situation 0F8S, the object
`Q = Lη_{ℐ'} Lb^*M` is perfect: this is tag 0GTW,
`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEta_obj_of_isGoodTriple`, at the
pulled-back triple, with its functor-valued input discharged by
`Stacks.Divisors.Eta.derivedEtaData`.

## Main results

* `isPerfect_etaDerivedPullbackObject_of_isGoodOver_of_chartDecalage`: tag 0F8U for a morphism
  good for the triple.

## References

* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks tag 0F8U, for a morphism good for the triple.**  Let `(X, D, M)` be a triple as in
Situation 0F8S and let `b : X' ⟶ X` be good for it — condition (1) of tag 0GTY, which the
morphism of that tag satisfies.  Then `Q = Lη_{ℐ'} Lb^*M` is a perfect object of `D(𝒪_{X'})`,
for every affine-chart comparison `hcomp` of the shape of the second assertion of tag 0GTV. -/
@[stacks 0F8U "perfectness of `Q = Lη_{I'} Lb^* M` for any `b` satisfying condition (1) of tag \
0GTY, with the datum `hcomp` of the formalization of tag 0GTW: the second assertion of tag 0GTV \
read at an affine open of the pulled-back scheme"]
theorem isPerfect_etaDerivedPullbackObject_of_isGoodOver_of_chartDecalage
    (S : ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hb : S.IsGoodOver b)
    (hcomp : ChartDecalage (S.pullback b hb.pullbackDefined)
      (@Stacks.Divisors.Eta.derivedEtaData X' (S.D.comap b) hb.pullbackDefined)) :
    RingedSpace.IsPerfect (X := X'.toRingedSpace)
      (S.etaDerivedPullbackObject b hb.pullbackDefined) :=
  isPerfect_derivedEta_obj_of_isGoodTriple (S.pullback b hb.pullbackDefined) _ hb.isGoodTriple
    hcomp

end AlgebraicGeometry.ComplexAndDivisorSituation

end

module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartDecalage
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupTag
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect

/-!
# Stacks tag 0F8U: the décalage on the universal good modification is perfect

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be the morphism of Stacks tag
0GTY and let `D' = b⁻¹D`, with ideal sheaf `ℐ'`.  Then `Q = Lη_{ℐ'}Lb^*M` is a perfect object of
`D(𝒪_{X'})`.  Here `Lη_{ℐ'}` is the derived décalage `Stacks.Divisors.Eta.derivedEtaData` of
tag 0F8Q and `Lb^*` the derived pullback of modules.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_etaDerivedPullbackObject_of_isGoodOver`:
  `Lη_{ℐ'}Lb^*M` is perfect for every morphism `b` along which `D` pulls back to an effective
  Cartier divisor `D'` with `(X', D', Lb^*M)` a good triple.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_etaDerivedPullbackObject_goodBlowup`:
  **Stacks tag 0F8U**.

## References

* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : ComplexAndDivisorSituation.{u, d})

/-- If `D` pulls back along `b : X' ⟶ X` to an effective Cartier divisor `D'` with ideal sheaf
`ℐ'` and `(X', D', Lb^*M)` is a good triple, then `Lη_{ℐ'}Lb^*M` is perfect: this is Stacks tag
0GTW for the pulled-back triple. -/
theorem isPerfect_etaDerivedPullbackObject_of_isGoodOver {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hb : S.IsGoodOver b) :
    RingedSpace.IsPerfect (X := X'.toRingedSpace)
      (S.etaDerivedPullbackObject b hb.pullbackDefined) :=
  isPerfect_derivedEtaData_obj_of_isGoodTriple (S.D.comap b) hb.pullbackDefined
    (S.derivedPullbackObject b) (S.isPerfect_derivedPullbackObject b) hb.isGoodTriple

/-- **Stacks tag 0F8U.**  In Situation 0F8S let `b : X' ⟶ X` be the morphism of Stacks tag 0GTY
and `D' = b⁻¹D`, with ideal sheaf `ℐ'`.  Then `Q = Lη_{ℐ'}Lb^*M` is a perfect object of
`D(𝒪_{X'})`. -/
@[stacks 0F8U "`Q = Lη_{I'} Lb^* M` is perfect, for `b` the morphism goodBlowupToBase of tag \
0GTY (existsUnique_isGoodBlowup), `Lη_{I'}` the derived décalage \
Stacks.Divisors.Eta.derivedEtaData of `D' = b⁻¹D` and `Lb^*` the derived pullback of modules"]
theorem isPerfect_etaDerivedPullbackObject_goodBlowup :
    RingedSpace.IsPerfect (X := S.goodBlowup.toRingedSpace)
      (S.etaDerivedPullbackObject S.goodBlowupToBase
        S.isGoodOver_goodBlowupToBase.pullbackDefined) :=
  S.isPerfect_etaDerivedPullbackObject_of_isGoodOver _ S.isGoodOver_goodBlowupToBase

end AlgebraicGeometry.ComplexAndDivisorSituation

end

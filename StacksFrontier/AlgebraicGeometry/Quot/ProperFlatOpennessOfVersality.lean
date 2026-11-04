module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersalityDischarge
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitPreservingUnconditional
public import StacksFrontier.Deformation.Artin.Versality.OpennessOfVersality

/-!
# Openness of versality for `Spaces'_{fp, flat, proper}` and for curves, by Artin's criterion

The source proves Stacks 0D3X — openness of versality for the stack `Spaces'_{fp, flat, proper}`
of finitely presented, flat and proper families of algebraic spaces — by Artin's criterion
Stacks 0CXU, whose four hypotheses are: the diagonal is representable by algebraic spaces
(Stacks 0D1F), (RS\*) (Stacks 0D1J), limit preservation (Stacks 0D1I), and the effectiveness of
square-zero systems, which is the body of the proof of Stacks 0D3X. Stacks 0D59, openness of
versality for the stack of curves, is then read off along the fully faithful inclusion of
Stacks equation 0D50.

This file is that assembly on the library's Artin criterion,
`Deformation.Artin.isOpenVersality_of_isSquareZeroEffective` (Stacks 0CXU), applied at
`AlgebraicGeometry.Space.properFlatSpacesStack`. Limit preservation is discharged by
`AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory` (Stacks 0D1I). The other
three hypotheses of Stacks 0CXU are arguments here, each in exactly the form in which Stacks 0CXU
asks for it.

None of these declarations is registered: they are the plumbing from the four hypotheses of
Stacks 0CXU to Stacks 0D3X and Stacks 0D59.

## Main results

* `AlgebraicGeometry.openVersalityOf_cartesianProperFlat_of_isSquareZeroEffective`: openness of
  versality for `Spaces'_{fp, flat, proper}` over a locally Noetherian base `S`.
* `AlgebraicGeometry.curves_openVersalityOf_specZ_of_isSquareZeroEffective` and
  `AlgebraicGeometry.curves_openVersalityOf_of_isSquareZeroEffective`: the two clauses of
  Stacks 0D59, over `Spec ℤ` and after base change to a Noetherian scheme `S`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D59](https://stacks.math.columbia.edu/tag/0D59)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public section

open CategoryTheory Deformation.Artin

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Openness of versality for `Spaces'_{fp, flat, proper}` from Artin's criterion.** Over a
locally Noetherian base `S`, if the diagonal of the stack of finitely presented, flat and proper
families of algebraic spaces is representable by algebraic spaces, the stack has (RS\*), and
square-zero systems are effective, then the stack satisfies openness of versality: this is
Stacks 0CXU, with limit preservation from Stacks 0D1I. -/
theorem openVersalityOf_cartesianProperFlat_of_isSquareZeroEffective [IsLocallyNoetherian S]
    (hΔ : Stack.HasRepresentableDiagonal B S hS (Space.properFlatSpacesStack B S hS))
    (hRS : SatisfiesRSStar B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS))
    (heff : IsSquareZeroEffective B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)) :
    OpenVersalityOf (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) :=
  fun U hU x hx u₀ hu₀ hversal =>
    isOpenVersality_of_isSquareZeroEffective B S hS (Space.properFlatSpacesStack B S hS) hΔ hRS
      (isLimitPreserving_cartesianProperFlatFiberedCategory B S hS) heff U hU x hx u₀ hu₀ hversal

variable (hZ : B.Contains integerBase)

/-- **The first clause of Stacks 0D59 from the hypotheses of Artin's criterion for
`Spaces'_{fp, flat, proper}` over `Spec ℤ`**: the stack of curves satisfies openness of versality
over `Spec ℤ`. -/
theorem curves_openVersalityOf_specZ_of_isSquareZeroEffective
    (hΔ : Stack.HasRepresentableDiagonal B integerBase hZ
      (Space.properFlatSpacesStack B integerBase hZ))
    (hRS : SatisfiesRSStar B integerBase hZ (cartesianProperFlatProjection B integerBase hZ)
      (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ))
    (heff : IsSquareZeroEffective B integerBase hZ (cartesianProperFlatProjection B integerBase hZ)
      (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ)) :
    OpenVersalityOf (curvesProjectionOver B hZ ⋙ Over.post B.inclusion) :=
  have := isNoetherian_integerBase.{u}
  curves_openVersality_specZ_of_properFlatSpaces B hZ
    (openVersalityOf_cartesianProperFlat_of_isSquareZeroEffective B integerBase hZ hΔ hRS heff)

/-- **The second clause of Stacks 0D59 from the hypotheses of Artin's criterion for
`Spaces'_{fp, flat, proper}` over a Noetherian scheme `S`**: the stack of `S`-curves, the base
change of Stacks 0D54, satisfies openness of versality over `S`. -/
theorem curves_openVersalityOf_of_isSquareZeroEffective [IsNoetherian S]
    (hΔ : Stack.HasRepresentableDiagonal B S hS (Space.properFlatSpacesStack B S hS))
    (hRS : SatisfiesRSStar B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS))
    (heff : IsSquareZeroEffective B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)) :
    OpenVersalityOf
      (CostructuredArrow.pre (AlgebraicGeometry.curvesProjection B hZ)
        (𝟭 B.Schemes) (B.obj hS) ⋙ Over.post B.inclusion) :=
  curves_openVersality_of_properFlatSpaces B hZ S hS
    (openVersalityOf_cartesianProperFlat_of_isSquareZeroEffective B S hS hΔ hRS heff)

end AlgebraicGeometry

end

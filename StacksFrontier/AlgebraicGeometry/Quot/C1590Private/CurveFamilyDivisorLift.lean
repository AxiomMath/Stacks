module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineCentre

/-!
# Lifting divisors of a closed fibre of a family of curves

Let `X ⟶ S` be a family of curves, `s` a closed point of `S` given by a field valued point
`P : Spec κ(s) ⟶ S` which is a closed immersion, and `V` a scheme presenting the fibre `X_s`.
This module states the property that effective Cartier divisors of `V` with finite support lift
to relative effective Cartier divisors of the family after an elementary étale base change, its
version for divisors supported in exactly one point, and the reduction of the former to the
latter.

## Main definitions

* `AlgebraicGeometry.C1590Private.DivisorLiftAtClosedFibre`: every effective Cartier divisor of
  the fibre with finite support lifts, over an elementary étale neighbourhood of `s`, to a
  relative effective Cartier divisor of the base-changed family whose preimage in the fibre is
  the closed subspace cut out by the divisor.
* `AlgebraicGeometry.C1590Private.DivisorLiftAtClosedFibreLocal`: the same for divisors whose
  support is a single point.
* `AlgebraicGeometry.C1590Private.DivisorLiftReduction`: the second implies the first.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Over an affine base, an effective Cartier divisor `E` of the fibre with finite
support lifts over an affine elementary étale neighbourhood `φ : U ⟶ S` of the closed point (the
residue point lifts to `U`, again a closed immersion) to a relative effective Cartier divisor `D`
of a base change `Y` of the family to `U`, whose preimage in the fibre is the closed subspace cut
out by `E`. -/
def DivisorLiftAtClosedFibre : Prop :=
  ∀ (X : CurveFamily B hZ) (_ : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (_ : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (_ : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor E →
      (E.support : Set ((BigFppfOver.toScheme B integerBase hZ).obj V)).Finite →
    ∃ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (t : P.siteObject ⟶ Y.base)
      (q' : yoneda.obj V ⟶ Y.total.obj) (D : Space.ClosedSubspaces B integerBase hZ Y.total.obj),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧ t ≫ φ.baseMap = P.value ∧
      IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map t) ∧
      IsPullback q' (yoneda.map v) Y.toBase.hom (yoneda.map t) ∧ q' ≫ φ.totalMap.hom = q ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) ∧
      Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y.toBase D ∧
      D.1.preimage q' = (Space.closedSubspaceOfIdeal V E).1

/-- `AlgebraicGeometry.C1590Private.DivisorLiftAtClosedFibre` for divisors supported in exactly one
point. -/
def DivisorLiftAtClosedFibreLocal : Prop :=
  ∀ (X : CurveFamily B hZ) (_ : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (_ : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (_ : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor E →
      (∃ x, (E.support : Set ((BigFppfOver.toScheme B integerBase hZ).obj V)) = {x}) →
    ∃ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (t : P.siteObject ⟶ Y.base)
      (q' : yoneda.obj V ⟶ Y.total.obj) (D : Space.ClosedSubspaces B integerBase hZ Y.total.obj),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧ t ≫ φ.baseMap = P.value ∧
      IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map t) ∧
      IsPullback q' (yoneda.map v) Y.toBase.hom (yoneda.map t) ∧ q' ≫ φ.totalMap.hom = q ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) ∧
      Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y.toBase D ∧
      D.1.preimage q' = (Space.closedSubspaceOfIdeal V E).1

/-- `AlgebraicGeometry.C1590Private.DivisorLiftAtClosedFibreLocal` implies
`AlgebraicGeometry.C1590Private.DivisorLiftAtClosedFibre`. -/
def DivisorLiftReduction : Prop :=
  DivisorLiftAtClosedFibreLocal B hZ → DivisorLiftAtClosedFibre B hZ

end AlgebraicGeometry.C1590Private

end

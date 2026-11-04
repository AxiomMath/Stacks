module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent

/-!
# The base change of a family of curves along a cartesian square

A cartesian square of algebraic spaces with right column the structure morphism `X ⟶ S` of a family
of curves and bottom a morphism of schemes `t : U ⟶ S` exhibits its left column `A ⟶ U` as a
family of curves, which maps to `X` by a morphism of families. When `A` is itself a scheme, the
structure morphism is a flat, proper morphism of schemes locally of finite presentation.

## Main definitions

* `AlgebraicGeometry.C1590Private.curveFamilyOfIsPullback`: the family of curves `A ⟶ U`.
* `AlgebraicGeometry.C1590Private.curveFamilyOfIsPullbackHom`: its morphism to `X`.

## Main results

* `AlgebraicGeometry.C1590Private.curveFamilyOfIsPullback_total` and
  `AlgebraicGeometry.C1590Private.curveFamilyOfIsPullback_toBase`: its total space and structure
  morphism. That a base change represented by a morphism of schemes is flat, locally of finite
  presentation and proper is `AlgebraicGeometry.CurveFamily.flat_toScheme_map_of_isPullback`,
  `AlgebraicGeometry.CurveFamily.locallyOfFinitePresentation_toScheme_map_of_isPullback` and
  `AlgebraicGeometry.CurveFamily.isProper_toScheme_map_of_isPullback_schemeSpaceMap`.

## Implementation notes

The construction is the one in the proof that families of curves form a fibred category
(`AlgebraicGeometry.curvesProjection_isFiberedInGroupoids`), applied to an arbitrary cartesian
square instead of a chosen one, so that it can be used with base changes that are schemes.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5B](https://stacks.math.columbia.edu/tag/0D5B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The base change of a family of curves along a cartesian square.** If
`A --iA--> X.total`, `pA : A ⟶ U` is a cartesian square over `t : U ⟶ X.base`, then `pA` is a
family of curves: flatness, properness, finite presentation and the relative dimension bound are
stable under base change. -/
def curveFamilyOfIsPullback (X : CurveFamily B hZ) {U : BigFppfOver B integerBase hZ}
    (t : U ⟶ X.base) {A : AlgebraicSpaces B integerBase hZ} (iA : A ⟶ X.total)
    (pA : A ⟶ schemeSpace U) (h : IsPullback iA pA X.toBase (schemeSpaceMap t)) :
    CurveFamily B hZ where
  base := U
  total := A
  toBase := pA
  flat := (Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback h X.flat
  proper := (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback h X.proper
  finitePresentation :=
    ⟨(Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B integerBase hZ).of_isPullback
        h X.finitePresentation.1,
      Space.isQuasiCompact_of_isPullback B integerBase hZ
        (AlgebraicSpaces.isPullback_hom B integerBase hZ h) X.finitePresentation.2.1,
      Space.isQuasiSeparated_of_isPullback B integerBase hZ
        (AlgebraicSpaces.isPullback_hom B integerBase hZ h) X.finitePresentation.2.2⟩
  relativeDimensionLE := by
    intro x'
    obtain ⟨e, he, hrel⟩ := X.relativeDimensionLE
      (Space.pointsMap B integerBase hZ A.obj iA.hom x')
    refine ⟨e, he, ?_⟩
    have hfinite : Space.IsLocallyOfFiniteType B integerBase hZ X.toBase.hom :=
      Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        X.finitePresentation.1
    exact (Space.hasRelativeDimensionAt_iff_of_isPullback B integerBase hZ
      (AlgebraicSpaces.isPullback_hom B integerBase hZ h) X.total.property
      (isAlgebraicSpace_yoneda B integerBase hZ U)
      (isAlgebraicSpace_yoneda B integerBase hZ X.base) hfinite x' (e : ℕ∞)).mp hrel

/-- The base of `curveFamilyOfIsPullback X t iA pA h` is `U`. -/
@[simp]
theorem curveFamilyOfIsPullback_base (X : CurveFamily B hZ) {U : BigFppfOver B integerBase hZ}
    (t : U ⟶ X.base) {A : AlgebraicSpaces B integerBase hZ} (iA : A ⟶ X.total)
    (pA : A ⟶ schemeSpace U) (h : IsPullback iA pA X.toBase (schemeSpaceMap t)) :
    (curveFamilyOfIsPullback X t iA pA h).base = U := rfl

/-- The total space of `curveFamilyOfIsPullback X t iA pA h` is `A`. -/
@[simp]
theorem curveFamilyOfIsPullback_total (X : CurveFamily B hZ) {U : BigFppfOver B integerBase hZ}
    (t : U ⟶ X.base) {A : AlgebraicSpaces B integerBase hZ} (iA : A ⟶ X.total)
    (pA : A ⟶ schemeSpace U) (h : IsPullback iA pA X.toBase (schemeSpaceMap t)) :
    (curveFamilyOfIsPullback X t iA pA h).total = A := rfl

/-- The structure morphism of `curveFamilyOfIsPullback X t iA pA h` is `pA`. -/
@[simp]
theorem curveFamilyOfIsPullback_toBase (X : CurveFamily B hZ) {U : BigFppfOver B integerBase hZ}
    (t : U ⟶ X.base) {A : AlgebraicSpaces B integerBase hZ} (iA : A ⟶ X.total)
    (pA : A ⟶ schemeSpace U) (h : IsPullback iA pA X.toBase (schemeSpaceMap t)) :
    (curveFamilyOfIsPullback X t iA pA h).toBase = pA := rfl

/-- The morphism of families of curves from a base change to the family. -/
def curveFamilyOfIsPullbackHom (X : CurveFamily B hZ) {U : BigFppfOver B integerBase hZ}
    (t : U ⟶ X.base) {A : AlgebraicSpaces B integerBase hZ} (iA : A ⟶ X.total)
    (pA : A ⟶ schemeSpace U) (h : IsPullback iA pA X.toBase (schemeSpaceMap t)) :
    curveFamilyOfIsPullback X t iA pA h ⟶ X where
  baseMap := t
  totalMap := iA
  cartesian := h

end AlgebraicGeometry.C1590Private

end

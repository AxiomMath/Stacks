module

public import StacksFrontier.AlgebraicGeometry.Quot.FlatLfpPushoutGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.EtaleChartLifts

/-!
# Rim–Schlessinger for proper flat spaces and for curves: Tags 0D1J and 0D56

For a pushout `S' = S ⨿_T T'` of schemes along a thickening `T ⟶ T'` and an affine morphism
`T ⟶ S`, restriction from the finitely presented, flat and proper algebraic spaces over `S'` to
the compatible pairs over `S` and `T'` is an equivalence ([Stacks Project, Tag 0D1J]), and so is
restriction of families of curves ([Stacks Project, Tag 0D56]).

`StacksFrontier.AlgebraicGeometry.Quot.FlatLfpPushoutGluing` proves both from the lift of étale
scheme charts across thickenings (`AlgebraicGeometry.Space.HasEtaleChartLifts`); that lift is
`AlgebraicGeometry.Space.hasEtaleChartLifts`, and is supplied here.

## Main definitions

* `AlgebraicGeometry.Space.properPushoutRS`: Tag 0D1J.
* `AlgebraicGeometry.curvePushoutEquivalenceOfIsPushout`: Tag 0D56.

## References

* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
* [Stacks Project, Tag 0D56](https://stacks.math.columbia.edu/tag/0D56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S₀ : Scheme.{u}) (hS₀ : B.Contains S₀)

/-- **[Stacks Project, Tag 0D1J].** For every pushout `S' = S ⨿_T T'` of schemes of the site
along a thickening `T ⟶ T'` and an affine morphism `T ⟶ S`, the canonical restriction functor
from the finitely presented, flat and proper algebraic spaces over `S'` to the compatible pairs
of such spaces over `S` and `T'` is an equivalence. -/
@[stacks 0D1J]
def properPushoutRS : ProperPushoutRS B S₀ hS₀ :=
  properPushoutRS_of_hasEtaleChartLifts (hasEtaleChartLifts B S₀ hS₀)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **[Stacks Project, Tag 0D56].** For a pushout `S' = S ⨿_T T'` of schemes along a
thickening `i : T ⟶ T'` and an affine morphism `f : T ⟶ S`, the canonical restriction functor
from the families of curves over `S'` to the compatible pairs of families over `S` and `T'` is
an equivalence. -/
@[stacks 0D56]
def curvePushoutEquivalenceOfIsPushout {T T' S S' : B.Schemes}
    (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (hi : Stacks.Thickenings.IsThickening (B.inclusion.map i))
    [IsAffineHom (B.inclusion.map f)]
    (hsq : IsPushout (B.inclusion.map i) (B.inclusion.map f)
      (B.inclusion.map g) (B.inclusion.map h)) :
    CurvePushoutEquivalenceData B hZ i f g h :=
  curvePushoutEquivalence_of_hasEtaleChartLifts B hZ (Space.hasEtaleChartLifts B integerBase hZ)
    i f g h hi hsq

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs

/-!
# `Curves^{h0,1}` is an open substack, from the cohomological inputs

The strictly full subcategory `Curves^{h0,1}` of families of curves with `f_*𝒪_X = 𝒪_S`
universally and fibres of dimension `1` is an open substack of `Curves`, and a family factors
through it exactly when it satisfies these two conditions. The statement takes as hypotheses
`hbetti`, the upper semicontinuity of `dim H^0` of the fibres of a proper, flat, finitely presented
morphism of algebraic spaces, and `hstruct`, that such a morphism whose fibres have `H^0` equal to
the base field satisfies `f_*𝒪_X = 𝒪_Y` universally.

## Main results

* `AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_of_h01Statements`: `Curves^{h0,1}`
  is an open substack of `Curves`, given `hbetti` and `hstruct`.

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`Curves^{h0,1}` is an open substack**, given `hbetti` and `hstruct`. The
strictly full subcategory `Curves^{h0,1}` of families with `f_*𝒪_X = 𝒪_S` universally and fibres
of dimension `1` is an open substack of `Curves` — its inclusion is representable by algebraic
spaces and an open immersion — and the classifying morphism of a family of curves factors through
it exactly when the family satisfies these two conditions. -/
theorem curvesH01_isOpenSubstack_and_factors_iff_of_h01Statements
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g))) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
            hstruct).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
            hstruct).prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        IsH01CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left)))) :=
  isOpenImmersion_curvesSubstackInclusion_and_factors_iff
    (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct)

end AlgebraicGeometry

end

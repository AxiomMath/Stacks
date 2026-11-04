module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpec

/-!
# The representable case of the normalization of `X` in `Y`

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces and let
`ν : X' ⟶ X` be the normalization of `X` in `Y` built from a pair of charts in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpec`. This file regards `X'`
as an algebraic space affine over `X`, identifies the direct image of its structure sheaf with
the integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`, and shows that `X'` is representable when `X`
is (the representability clause of Stacks 0ABP, part (2)).

## Main definitions

* `AlgebraicGeometry.Space.normalizationInChartAffineOver`: `X'` as an algebraic space affine
  over `X`, with structure morphism `ν`.

## Main results

* `AlgebraicGeometry.Space.normalizationInChartAffineOverPushforwardIso`: the direct-image algebra
  of `X'` is the integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`.
* `AlgebraicGeometry.Space.isRepresentable_normalizationInChartQuotient`: if `X` is representable
  then so is `X'`.

## Implementation notes

The source assumes `X` and `Y` both representable. Representability of `Y` is not needed: `ν` is
representable with no hypothesis on `Y`, being affine
(`AlgebraicGeometry.Space.relativelyRepresentable_normalizationInChartQuotientHom`).

## References

* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 035E](https://stacks.math.columbia.edu/tag/035E)
* [Stacks Project, Tag 02W9](https://stacks.math.columbia.edu/tag/02W9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)

include hfqc hfqs hsq hsurj

/-- **`X' = \underline{Spec}_X(𝒪')` as an algebraic space affine over `X`.** The structure
morphism is `ν`, which is affine by
`AlgebraicGeometry.Space.isAffineHom_normalizationInChartQuotientHom`. -/
def normalizationInChartAffineOver : AffineOver B S hS X :=
  ⟨Over.mk (normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq),
    isAffineHom_normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq hsurj⟩

/-- The direct image of the structure sheaf of `X'` along `ν` is the integral closure `𝒪'` of
`𝒪_X` in `f_* 𝒪_Y`; this is
`AlgebraicGeometry.Space.normalizationInChartQuotientPushforwardIso`, inverted. -/
def normalizationInChartAffineOverPushforwardIso :
    pushforwardAlgebra B S hS
        (normalizationInChartAffineOver B S hS f hfqc hfqs pr₁ pr₂ hsq hsurj).obj ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)) :=
  (normalizationInChartQuotientPushforwardIso B S hS f hfqc hfqs pr₁ pr₂ hsq hsurj).symm

/-- **Stacks 0ABP, part (2), representability.** For a quasi-compact, quasi-separated
`f : Y ⟶ X` with `X` representable, the normalization `X'` of `X` in `Y` is representable. -/
theorem isRepresentable_normalizationInChartQuotient {X₀ : BigFppfOver B S hS}
    (eX : X.1 ≅ yoneda.obj X₀) :
    (normalizationInChartQuotient B S hS f hfqc hfqs pr₁ pr₂ hsq).1.IsRepresentable :=
  have hrep : yoneda.relativelyRepresentable
      (normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq).hom :=
    relativelyRepresentable_normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq hsurj
  have hid : IsPullback (𝟙 _)
      ((normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq).hom ≫ eX.hom)
      (normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq).hom eX.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  Functor.IsRepresentable.mk' (hid.isoIsPullback _ _ (hrep.isPullback eX.inv)).symm

end AlgebraicGeometry.Space

end

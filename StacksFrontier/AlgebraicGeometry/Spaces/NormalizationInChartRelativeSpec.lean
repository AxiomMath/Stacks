module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureChartRelativeSpecContained
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn

/-!
# The normalization of `X` in `Y` as a relative spectrum built from charts

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` and let
`𝒪'` be the integral closure of `𝒪_X` in `f_* 𝒪_Y`. Definition 0822 names the normalization of
`X` in `Y` as the relative spectrum `ν : X' = \underline{Spec}_X(𝒪') ⟶ X`, together with the
factorization of `f` through it. Here `X'` is built as the quotient of the relation of a pair
`pr₁, pr₂ : V' ⟶ V₂` of étale charts of `X` with `V₂ ⟶ X` surjective.

## Main definitions

* `AlgebraicGeometry.Space.normalizationInChartQuotient`: `X' = \underline{Spec}_X(𝒪')`, as an
  algebraic space over `S`.
* `AlgebraicGeometry.Space.normalizationInChartQuotientHom`: the morphism `ν : X' ⟶ X`.
* `AlgebraicGeometry.Space.normalizationInChartQuotientPushforwardIso`: `𝒪' ≅ ν_* 𝒪_{X'}` as
  sheaves of commutative `𝒪_X`-algebras on the small étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_normalizationInChartQuotientHom`: `ν` is an affine
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.relativelyRepresentable_normalizationInChartQuotientHom`: `ν` is
  representable.

## References

* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
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

include hfqc hfqs hsq

/-- `X' = \underline{Spec}_X(𝒪')`, the normalization of `X` in `Y`, as an algebraic space over
`S`: the relative spectrum `AlgebraicGeometry.Space.chartRelativeSpecQuotient` of the integral
closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`. -/
def normalizationInChartQuotient : AlgebraicSpaces B S hS :=
  chartRelativeSpecQuotient B S hS X
    (AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)))
    (isQuasicoherent_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs) pr₁ pr₂ hsq
    (contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs V')
    (contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs V₂)
    (contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs
      (Limits.pullback pr₁ pr₂))

/-- The structure morphism `ν : X' ⟶ X` of the normalization of `X` in `Y`. -/
def normalizationInChartQuotientHom :
    normalizationInChartQuotient B S hS f hfqc hfqs pr₁ pr₂ hsq ⟶ X :=
  chartRelativeSpecQuotientHom B S hS X
    (AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)))
    (isQuasicoherent_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs) pr₁ pr₂ hsq
    (contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs V')
    (contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs V₂)
    (contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs
      (Limits.pullback pr₁ pr₂))

include hsurj

/-- The morphism `ν : X' ⟶ X` is an affine morphism of algebraic spaces. -/
theorem isAffineHom_normalizationInChartQuotientHom :
    IsAffineHom B S hS
      (normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq).hom :=
  isAffineHom_chartRelativeSpecQuotientHom B S hS X _ _ pr₁ pr₂ hsq hsurj _ _ _

/-- The morphism `ν : X' ⟶ X` is representable. -/
theorem relativelyRepresentable_normalizationInChartQuotientHom :
    yoneda.relativelyRepresentable
      (normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq).hom :=
  relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X _ _ pr₁ pr₂ hsq hsurj _ _ _

/-- The direct image of the structure sheaf of `X' = \underline{Spec}_X(𝒪')` along `ν` is the
integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`, as sheaves of commutative `𝒪_X`-algebras on the
small étale site of `X`. -/
def normalizationInChartQuotientPushforwardIso :
    AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)) ≅
      pushforwardAlgebra B S hS
        (Over.mk (normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq)) :=
  chartRelativeSpecQuotientPushforwardIso B S hS X _ _ pr₁ pr₂ hsq hsurj _ _ _
    (contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs)

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.IntegralSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpec
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty

/-!
# The relative spectrum of an integral algebra is an integral morphism

Let `X` be an algebraic space over `S` and let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site which is *integral*, that is, whose structure-algebra map
is an integral ring homomorphism over every affine étale chart.  This file proves that the
structure morphism `ν : \underline{Spec}_X(A) ⟶ X` of the chart-built relative spectrum is an
**integral** morphism of algebraic spaces, and instantiates that at the integral closure `𝒪'` of
`𝒪_X` in `f_* 𝒪_Y`, where it needs nothing of `f` beyond quasi-compactness and
quasi-separatedness.

## Main results

* `AlgebraicGeometry.Space.isIntegralHom_chartRelativeSpecToChart`: over a chart the structure
  morphism of the relative spectrum is an integral morphism of *schemes*.
* `AlgebraicGeometry.Space.isIntegralHom_chartRelativeSpecQuotientHom`: the structure morphism
  `ν` of the relative spectrum of an integral quasi-coherent algebra is an integral morphism of
  algebraic spaces.
* `AlgebraicGeometry.Space.isIntegralHom_normalizationInChartQuotientHom`: the normalization
  morphism `ν : X' ⟶ X` of `AlgebraicGeometry.Space.normalizationInChartQuotientHom` is
  integral.

## Implementation notes

The three steps mirror `AlgebraicGeometry.Space.isAffineHom_chartRelativeSpecQuotientHom` with
integrality in place of affineness, and each step has its integral counterpart already available.

* Over a chart's scheme the relative spectrum is the glued spectrum of the chart restriction
  `AlgebraicGeometry.Space.chartSchemeAlgebra` of `A`, so
  `Stacks.RelativeSpec.isIntegralHom_toBase_of_isIntegral_app` applies.  Its hypothesis is
  integrality of the sections of the algebra over every affine open `O` of the chart's scheme,
  and those sections are the sections of `A` over the étale chart `O` cuts out
  (`AlgebraicGeometry.Space.chartSchemeAlgebra_hom_app`), which is an affine chart by
  `AlgebraicGeometry.Space.chartScheme_openChart`; the extra factor is restriction of regular
  functions along `O ⊆ chartScheme V`, an isomorphism, so integrality is unaffected.
* Affineness of `ν` reads the Cartesian square
  `AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientHom` through item (4) of
  Stacks 03WG; integrality reads the same square through
  `AlgebraicGeometry.Space.isIntegralHom_of_surjectiveEtaleChart`, which is the matching
  implication of Stacks 03ZQ, and through stability under base change, Stacks 03ZS.
* The algebra `𝒪'` is integral over `𝒪_X` with no hypothesis beyond quasi-coherence of
  `f_* 𝒪_Y`: its sections over an affine chart are the integral closure there, by
  `AlgebraicGeometry.Space.AlgebraSheaf.isIntegralLocalOnAffineCharts_of_isQuasicoherent` and
  `AlgebraicGeometry.Space.AlgebraSheaf.isIntegral_integralClosureSheaf`.  So the last statement
  carries exactly the hypotheses of the construction it is about.

No `stacks` attribute is carried.  Integrality of `ν` is one of the three conditions of
Stacks 0823 on the canonical factorization of Stacks 0822, and the factorization itself is not
proved of this `X'`; the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpec` record what that owes.

## References

* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (hAint : A.IsIntegral) (V : SmallEtale B S hS X.1)

include hAint

/-- **The relative spectrum over a chart of an integral quasi-coherent algebra is an integral
morphism of schemes.**

Over an affine open `O` of the chart's scheme the sections of the structure morphism are
restriction of regular functions to `O`, an isomorphism, followed by the structure-algebra map of
`A` over the étale chart `O` cuts out, which is integral by hypothesis. -/
theorem isIntegralHom_chartRelativeSpecToChart :
    _root_.AlgebraicGeometry.IsIntegralHom (chartRelativeSpecToChart B S hS X A hA V) := by
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  let : (RingHom.toMorphismProperty RingHom.IsIntegral).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  refine Stacks.RelativeSpec.isIntegralHom_toBase_of_isIntegral_app
    (Stacks.AffineAlgebraEquivalence.situation (chartSchemeAlgebra B S hS X A V))
    fun O hO => ?_
  have hint : RingHom.toMorphismProperty RingHom.IsIntegral
      (A.hom.hom.app (op (openChart B S hS X.1 V O))) :=
    hAint (openChart B S hS X.1 V O) hO
  exact MorphismProperty.RespectsIso.precomp
    (RingHom.toMorphismProperty RingHom.IsIntegral)
    ((Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app (op O)) _ hint

/-- **The relative spectrum over a chart, read in the site, is an integral morphism of algebraic
spaces.**  Its underlying morphism of schemes is integral, and integrality of a represented
morphism of presheaves is integrality of the underlying morphism of schemes. -/
theorem isIntegralHom_yoneda_map_chartRelativeSpecSiteToChart
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) :
    IsIntegralHom B S hS
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V hV)) :=
  HoldsOnAffineBaseChange.of_presheaf
    (fun p hp hZ => isAffine_of_isIntegralHom p hp hZ)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u})
      (chartRelativeSpecSiteToChart B S hS X A hA V hV)).2
      (isIntegralHom_chartRelativeSpecToChart B S hS X A hA hAint V))

end Chart

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
instance hasPullbacks_presheaf_NormalizationInChartRelativeSpecIntegral
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_NormalizationInChartRelativeSpecIntegral
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Quotient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (hAint : A.IsIntegral)
    {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))

include hAint hsq hsurj hV'' in
/-- **The structure morphism `ν : \underline{Spec}_X(A) ⟶ X` of the relative spectrum of an
integral quasi-coherent algebra is an integral morphism of algebraic spaces.**

This is Stacks 03ZQ at the chart `V₂`: the base change of `ν` along the surjective étale chart
is the structure morphism of the relative spectrum over the chart, by
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientHom`, and that is integral. -/
theorem isIntegralHom_chartRelativeSpecQuotientHom :
    IsIntegralHom B S hS
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom := by
  have hsqr := isPullback_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
    hV' hV₂ hV''
  -- Named so that the two instance arguments of `CategoryTheory.IsPullback.of_horiz_isIso`
  -- are available before its `CommSq` argument is elaborated.
  have : IsIso (𝟙 (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V₂))) := inferInstance
  have hiso : IsPullback hsqr.isoPullback.inv
      (pullback.snd (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom
        V₂.obj.hom)
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂))
      (𝟙 (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V₂))) :=
    IsPullback.of_horiz_isIso ⟨hsqr.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
  exact isIntegralHom_of_surjectiveEtaleChart B S hS
    (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').property X.property _
    (isSurjective_of_presheafSurjective B S hS V₂.obj.hom hsurj)
    (isEtale_of_presheaf_etale B S hS V₂.property)
    (isIntegralHom_of_isPullback B S hS hiso
      (isIntegralHom_yoneda_map_chartRelativeSpecSiteToChart B S hS X A hA hAint V₂ hV₂))

end Quotient

section Normalization

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)

include hfqc hfqs

/-- **The integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y` is an integral `𝒪_X`-algebra**, at
quasi-compactness and quasi-separatedness of `f` and nothing else.

`f_* 𝒪_Y` is quasi-coherent there, so over an affine étale chart a locally integral section of it
is already integral, and the sections of `𝒪'` are exactly those. -/
theorem isIntegral_integralClosureSheaf_pushforwardAlgebra :
    (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsIntegral :=
  AlgebraSheaf.isIntegral_integralClosureSheaf
    (AlgebraSheaf.isIntegralLocalOnAffineCharts_of_isQuasicoherent _
      (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs))

include hsq hsurj in
/-- **`ν : X' ⟶ X`, the normalization of `X` in `Y`, is an integral morphism of algebraic
spaces**, at exactly the hypotheses of
`AlgebraicGeometry.Space.normalizationInChartQuotientHom`: quasi-compactness and
quasi-separatedness of `f`, together with the chart quadruple the construction is parameterised
by.

It is `AlgebraicGeometry.Space.isIntegralHom_chartRelativeSpecQuotientHom` at the integral
closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`, which is an integral algebra by
`AlgebraicGeometry.Space.isIntegral_integralClosureSheaf_pushforwardAlgebra`. -/
theorem isIntegralHom_normalizationInChartQuotientHom :
    IsIntegralHom B S hS
      (normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq).hom :=
  isIntegralHom_chartRelativeSpecQuotientHom B S hS X _ _
    (isIntegral_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs) pr₁ pr₂ hsq hsurj
    _ _ _

end Normalization

end AlgebraicGeometry.Space

end

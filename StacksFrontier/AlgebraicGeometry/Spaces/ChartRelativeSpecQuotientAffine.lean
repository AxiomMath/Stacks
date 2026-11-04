module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecPullbackChart

/-!
# The relative spectrum of a quasi-coherent algebra is affine over the algebraic space

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site, and let `ν : X' = \underline{Spec}_X(A) ⟶ X` be the
structure morphism of `StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotient`, built at
a relation `pr₁, pr₂ : V' ⟶ V₂` of étale charts of `X` with `V₂ ⟶ X` surjective.  This file
proves that `ν` is an **affine** morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_chartRelativeSpecQuotientHom`: **`ν` is affine.**

## Implementation notes

This is item (4) of Stacks 03WG, `AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`,
at the chart `V₂`: affineness of a morphism of algebraic spaces may be tested after base change
along one surjective étale scheme chart of the target.  The base change of `ν` along the chart is
the structure morphism `\underline{Spec}_{V₂}(A|_{V₂}) ⟶ V₂` of the relative spectrum over the
chart — that is the cartesian square
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientHom` — and that morphism is affine
because its underlying morphism of schemes is, by
`AlgebraicGeometry.Space.isAffineHom_chartRelativeSpecToChart`.

The square has to be transported from the leg it provides to Mathlib's
`CategoryTheory.Limits.pullback.snd`, which is what item (4) names; that transport is the
isomorphism `CategoryTheory.IsPullback.isoPullback` of the two cartesian squares over the same
cospan, and affineness travels along it by Stacks 03WI,
`AlgebraicGeometry.Space.IsAffineHom.of_isPullback`.

## References

* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (V : SmallEtale B S hS X.1)
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V))

/-- **The morphism of the relative spectrum over a chart to the chart is an affine morphism of
algebraic spaces.**  Its underlying morphism of schemes is affine, by
`AlgebraicGeometry.Space.isAffineHom_chartRelativeSpecToChart`, and affineness of a represented
morphism of presheaves is affineness of the underlying morphism of schemes. -/
theorem isAffineHom_yoneda_map_chartRelativeSpecSiteToChart :
    IsAffineHom B S hS
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V hV)) :=
  isAffineHom_of_presheaf ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@_root_.AlgebraicGeometry.IsAffineHom.{u})
    (chartRelativeSpecSiteToChart B S hS X A hA V hV)).2
    (isAffineHom_chartRelativeSpecToChart B S hS X A hA V))

end Chart

section Quotient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))

include hsq hsurj hV'' in
/-- **The structure morphism `ν : \underline{Spec}_X(A) ⟶ X` of the relative spectrum is an
affine morphism of algebraic spaces.**

This is item (4) of Stacks 03WG at the chart `V₂`: the base change of `ν` along the surjective
étale chart is the structure morphism of the relative spectrum over the chart, by
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientHom`, and that is affine. -/
theorem isAffineHom_chartRelativeSpecQuotientHom :
    IsAffineHom B S hS
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom := by
  have hsqr := isPullback_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
    hV' hV₂ hV''
  have htfae := (isAffineHom_tfae_of_isAlgebraicSpace B S hS
    (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom
    (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').property
    X.property).out 4 2
  refine htfae.mp
    ⟨(SmallEtale.toOver B S hS X.1).obj V₂, V₂.obj.hom,
      isSurjective_of_presheafSurjective B S hS V₂.obj.hom hsurj,
      isEtale_of_presheaf_etale B S hS V₂.property, ?_⟩
  -- Named so that the two instance arguments of `CategoryTheory.IsPullback.of_horiz_isIso`
  -- are available before its `CommSq` argument is elaborated.
  have : IsIso (𝟙 (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V₂))) := inferInstance
  have hiso : IsPullback hsqr.isoPullback.inv
      (pullback.snd (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom
        V₂.obj.hom)
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂))
      (𝟙 (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V₂))) :=
    IsPullback.of_horiz_isIso ⟨hsqr.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
  exact IsAffineHom.of_isPullback hiso
    (isAffineHom_yoneda_map_chartRelativeSpecSiteToChart B S hS X A hA V₂ hV₂)

end Quotient

end AlgebraicGeometry.Space

end

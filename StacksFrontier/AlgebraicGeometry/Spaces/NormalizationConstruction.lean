module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Constructing the normalization of a representable algebraic space

`StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization` introduces
`AlgebraicGeometry.Space.NormalizationData`, the normalization of an algebraic space as data:
a morphism `ν : F^ν ⟶ F` of algebraic spaces whose base change along every surjective étale
scheme chart of `F` is the normalization of that chart. Nothing in this library constructed
such data, so every result about it was an implication with no known instance of its
hypothesis. This module constructs it for a *representable* algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationData.ofIsNormal` is the normalization of the algebraic
  space represented by an object of the big fppf site whose underlying scheme is normal. It is
  the identity morphism, and it needs no hypothesis beyond normality and the finiteness of
  irreducible components.
* `AlgebraicGeometry.Space.NormalizationData.ofRepresentable` is the normalization of the
  algebraic space represented by an arbitrary object of the big fppf site, under the hypothesis
  that the site contains the normalization scheme of the representing scheme.

## Main results

* `AlgebraicGeometry.Space.etale_of_isEtale_yoneda_map`: the scheme morphism underlying an
  étale morphism between representable algebraic spaces is étale.

## Implementation notes

**Why only the representable case.** The chart condition of
`AlgebraicGeometry.Space.NormalizationData` quantifies over *every* surjective étale scheme
chart, which for a representable space means every object of the site étale and surjective over
the representing one. Checking it there is exactly the statement that normalization commutes
with étale base change, `AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale`. For a
non-representable `F` one would first have to form `U^ν/R^ν` by Tag 02WW from a presentation
`F = U/R` and then prove the result independent of the presentation; neither step is carried out
here.

**The normalization of a chart is automatically in the site.** The only object whose containment
in the site has to be assumed is the normalization of the representing scheme itself. For a chart
`φ : U ⟶ X` the pullback `U ×_X X^ν` is formed *inside* the site — `BigFppfOver B S hS` has
pullbacks — and `AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale` identifies its
underlying scheme with `U^ν`. So `hcontains` is a hypothesis about `X` alone and not about every
chart, and it is the only size condition in the construction. It is a genuine condition and not
bookkeeping: `AlgebraicGeometry.BigFppfSite.Contains` is a bound on
`AlgebraicGeometry.Scheme.size`, and no bound on the size of a normalization is available in this
library.

**The normal case needs no size hypothesis.** When the representing scheme is normal its
normalization morphism is an isomorphism (`AlgebraicGeometry.isIso_normalization_of_isNormal`),
and every étale chart is again normal by the ascent half of Tag 034F
(`AlgebraicGeometry.isNormal_of_etale`). So each chart may be normalized by *itself*, with the
identity as the comparison morphism, and no new scheme — hence no size condition — enters.
`AlgebraicGeometry.Space.NormalizationData.ofIsNormal` is therefore an unconditional instance of
the structure.

**No tag.** Tag 07U4 asserts the existence of the normalization of an algebraic space satisfying
the equivalent conditions of Tag 0BB1, with four numbered properties. What is constructed here
is the existence in the representable case; it is not one of the four numbered parts, and the
existence statement itself is not proved in the generality the tag asks for. So nothing here
carries `@[stacks 07U4]`.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
* [Stacks Project, Tag 034F](https://stacks.math.columbia.edu/tag/034F)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme morphism underlying an étale morphism between the algebraic spaces represented by
two objects of the big fppf site of `S` is étale.

Étaleness of a morphism of algebraic spaces specialises on a representable source to étaleness
after every representable base change
(`AlgebraicGeometry.Space.presheaf_etale_of_isEtale`), and for a represented morphism that is
étaleness of the underlying scheme morphism
(`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`). -/
theorem etale_of_isEtale_yoneda_map {U X : BigFppfOver B S hS} {φ : U ⟶ X}
    (hf : IsEtale B S hS (yoneda.map φ)) :
    Etale ((BigFppfOver.toScheme B S hS).map φ) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.Etale.{u}) φ).1 (presheaf_etale_of_isEtale B S hS hf)

namespace NormalizationData

/-- **The normalization of a normal representable algebraic space.** Let `X` be an object of the
big fppf site of `S` whose underlying scheme is normal and every quasi-compact open of which has
finitely many irreducible components. Then the identity of the algebraic space represented by `X`
is normalization data for it.

Every étale chart of `X` is again normal by the ascent half of Tag 034F, so its normalization
morphism is an isomorphism and the chart is its own normalization; the required cartesian square
is the one with two identities down its verticals.

This is an *unconditional* instance of `AlgebraicGeometry.Space.NormalizationData`, so the
results proved for arbitrary normalization data are not vacuous. -/
def ofIsNormal (X : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj X)]
    (hX : ∀ V : ((BigFppfOver.toScheme B S hS).obj X).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj X)) →
        (irreducibleComponents V).Finite) :
    NormalizationData B S hS (yoneda.obj X) where
  space := yoneda.obj X
  isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS X
  hom := 𝟙 _
  chart := by
    intro U f _ hfe
    obtain ⟨φ, rfl⟩ : ∃ φ : U ⟶ X, yoneda.map φ = f :=
      ⟨yoneda.preimage f, yoneda.map_preimage f⟩
    have hetale : Etale ((BigFppfOver.toScheme B S hS).map φ) :=
      etale_of_isEtale_yoneda_map B S hS hfe
    have hsmooth : Smooth ((BigFppfOver.toScheme B S hS).map φ) := inferInstance
    have hU := finite_irreducibleComponents_of_smooth
      ((BigFppfOver.toScheme B S hS).map φ) hX
    have hUnormal : _root_.AlgebraicGeometry.IsNormal
        ((BigFppfOver.toScheme B S hS).obj U) :=
      isNormal_of_etale ((BigFppfOver.toScheme B S hS).map φ)
    have hiso : IsIso (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU) :=
      Scheme.isIso_normalization_of_isNormal _ hU
    refine ⟨hU, U, 𝟙 U, yoneda.map φ,
      (asIso (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU)).symm, ?_, ?_⟩
    · simp
    · have hid : yoneda.map (𝟙 U) = 𝟙 (yoneda.obj U) := yoneda.map_id U
      rw [hid]
      exact IsPullback.of_id_snd

/-- **The normalization of a representable algebraic space.** Let `X` be an object of the big
fppf site of `S` every quasi-compact open of whose underlying scheme has finitely many
irreducible components, and assume the site contains the normalization scheme of that scheme.
Then the normalization morphism of the representing scheme, read in the site, is normalization
data for the algebraic space represented by `X`.

The chart condition is `AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale`: for an
étale chart `φ : U ⟶ X` the normalization of `U` is the fibre product `U ×_X X^ν`, which is
formed inside the site, so no further size condition is needed. -/
def ofRepresentable (X : BigFppfOver B S hS)
    (hX : ∀ V : ((BigFppfOver.toScheme B S hS).obj X).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj X)) →
        (irreducibleComponents V).Finite)
    (hcontains : B.Contains
      (Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj X) hX)) :
    NormalizationData B S hS (yoneda.obj X) :=
  let Xν : BigFppfOver B S hS := BigFppfOver.mk B S hS hcontains
    (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj X) hX ≫
      B.inclusion.map X.hom)
  let hex : ∃ ψ : Xν ⟶ X, (BigFppfOver.toScheme B S hS).map ψ =
      Scheme.normalization ((BigFppfOver.toScheme B S hS).obj X) hX :=
    BigFppfOver.exists_hom_of_comp_eq B S hS _ rfl
  { space := yoneda.obj Xν
    isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS Xν
    hom := yoneda.map hex.choose
    chart := by
      intro U f _ hfe
      obtain ⟨φ, rfl⟩ : ∃ φ : U ⟶ X, yoneda.map φ = f :=
        ⟨yoneda.preimage f, yoneda.map_preimage f⟩
      have hetale : Etale ((BigFppfOver.toScheme B S hS).map φ) :=
        etale_of_isEtale_yoneda_map B S hS hfe
      have hsmooth : Smooth ((BigFppfOver.toScheme B S hS).map φ) := inferInstance
      have hU := finite_irreducibleComponents_of_smooth
        ((BigFppfOver.toScheme B S hS).map φ) hX
      -- The fibre product of the chart with the normalization, formed in the site.
      have hsite : IsPullback (pullback.fst hex.choose φ) (pullback.snd hex.choose φ)
          hex.choose φ := IsPullback.of_hasPullback _ _
      have hschemes := hsite.map (BigFppfOver.toScheme B S hS)
      rw [hex.choose_spec] at hschemes
      -- Normalization commutes with étale base change.
      have hnorm := isPullback_normalizationSchemeMap_of_etale
        ((BigFppfOver.toScheme B S hS).map φ) hX
      refine ⟨hU, pullback hex.choose φ, pullback.snd hex.choose φ,
        yoneda.map (pullback.fst hex.choose φ),
        hschemes.isoIsPullback _ _ hnorm, ?_, ?_⟩
      · exact (hschemes.isoIsPullback_hom_snd _ _ hnorm).symm
      · exact hsite.map yoneda }

end NormalizationData

end AlgebraicGeometry.Space

end

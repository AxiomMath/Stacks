module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpec

/-!
# The normalization of `X` in `Y` does not depend on the chart pair

Let `f : Y ⟶ X` be a **quasi-compact, quasi-separated** morphism of algebraic spaces over `S`,
the two hypotheses of Definition 0822, and let `𝒪'` be the integral closure of `𝒪_X` in
`f_* 𝒪_Y`.  `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpec` builds
`ν : X' = \underline{Spec}_X(𝒪') ⟶ X` as the quotient of the relation of a *chosen* pair
`pr₁, pr₂ : V' ⟶ V₂` of morphisms of étale charts of `X`, with `V₂ ⟶ X` surjective — a
quadruple `(pr₁, pr₂, hsq, hsurj)` — and every declaration there is parameterised by that
quadruple.  Definition 0822 names *the* normalization, 0823 *the* normalization and part (2) of
0ABP says `X'` "is canonically isomorphic to" the scheme normalization: all three are definite
descriptions, and a construction depending on an arbitrary quadruple does not name a definite
object.  This file removes the dependence.

## Main results

* `AlgebraicGeometry.Space.exists_iso_normalizationInChartQuotient`: **any two chart pairs give
  the same normalization.**  For two quadruples the two `X'` are isomorphic as algebraic spaces
  over `S`, compatibly with the two structure morphisms `ν`, so the isomorphism is one over
  `X`.  There is no hypothesis beyond the two of Definition 0822 and the four components of each
  quadruple.
* `AlgebraicGeometry.Space.nonempty_isoOver_normalizationInChartQuotientHom`: the same
  comparison as an isomorphism of the two `ν` in `CategoryTheory.Over X`, which is the form in
  which "the same relative spectrum over `X`" is one statement.

## Implementation notes

**Why this is unconditional while the statement for a general algebra is not.**  The comparison
itself is `AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_contains`, which
needs the relative spectrum of the algebra over *every* étale chart of `X` to be an object of
the site — in particular over the common refinement `Z = V₂ ×_X W₂` of the two charts, over
`Z ×_X Z` and over the kernel pair of its projections, none of which is among the chart objects
either quadruple mentions.  For an arbitrary quasi-coherent algebra that is a genuine side
condition, which is why
`AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_contains_prod` carries three
containment hypotheses.  For the algebra Definition 0822 takes the relative spectrum of it is a
theorem and not a hypothesis:
`AlgebraicGeometry.Space.contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra`
proves it for the integral closure of `𝒪_X` in `f_* 𝒪_Y` **for every chart**, from
quasi-compactness and quasi-separatedness of `f` and nothing else, by the cardinality bound of
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureChartRelativeSpecContained`.  So the
common refinement needs no hypothesis here, and the independence holds for *any* two chart
pairs.

**The sense in which the isomorphism is canonical.**  A morphism over `X` between two relative
spectra of the same algebra is not unique — base changing it along the chart gives an
automorphism of an affine morphism over its target, and those are the automorphisms of the
algebra.  What is unique is the morphism compatible with the two atlases, which is the
uniqueness clause of
`AlgebraicGeometry.Space.existsUnique_desc_chartRelativeSpecQuotientChartAtlas`; the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientChartIndependence` discuss it,
and `AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_chartHom` is where the
compatibility with the atlas is recorded.

**What this does and does not unblock.**  It discharges the chart-pair dependence recorded as an
open obstruction in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` and of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpec`.  It is **independent of
clause (1)** of Definition 0822, the factorization `f' : Y ⟶ X'`: the note in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` proposed to obtain the independence from
a mapping property of `X'`, of which clause (1) is half, but the route taken here is the descent
route of `StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientChartIndependence` —
both quotients are quotients of the same atlas by the same kernel pair, Stacks 0262 part (3) —
and it uses nothing about a morphism from `Y`.  Clause (1), the factorization, is constructed
in `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqs`, where Definition 0822 is
registered.

**No `stacks` attribute is carried.**  Independence of the chart pair is not by itself any of
0822, 0823 or 0ABP; it is the step that turns "a normalization per chart pair" into "the
normalization", and registration belongs where the clauses of those tags are proved.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    {V' V₂ W' W₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂) (qr₁ qr₂ : W' ⟶ W₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsq' : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map qr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map qr₂)) W₂.obj.hom W₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hsurj' : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      W₂.obj.hom)

include hfqc hfqs hsq hsq' hsurj hsurj' in
/-- **The normalization of `X` in `Y` does not depend on the chart pair it is built at.**

For a quasi-compact, quasi-separated `f : Y ⟶ X` — the two hypotheses of Definition 0822 — and
two pairs `pr₁, pr₂ : V' ⟶ V₂` and `qr₁, qr₂ : W' ⟶ W₂` of morphisms of étale charts of `X`,
each exhibiting its relation as the self fibre product of its chart over `X` and each with
surjective chart, the two relative spectra
`X' = \underline{Spec}_X(𝒪')` are isomorphic, and the isomorphism commutes with the two
morphisms `ν : X' ⟶ X`, hence is an isomorphism over `X`.

**There is no restriction on the two pairs.**  The comparison runs through the common refinement
`Z = V₂ ×_X W₂` of the two charts,
`AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_contains`, and the only thing
that refinement needs — that the relative spectrum of `𝒪'` over it is an object of the site — is
`AlgebraicGeometry.Space.contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra`,
a theorem for every chart at quasi-compactness and quasi-separatedness of `f`.

This is what makes `AlgebraicGeometry.Space.normalizationInChartQuotient` name *the*
normalization of `X` in `Y` rather than one per chart pair. -/
theorem exists_iso_normalizationInChartQuotient :
    ∃ e : normalizationInChartQuotient B S hS f hfqc hfqs pr₁ pr₂ hsq ≅
        normalizationInChartQuotient B S hS f hfqc hfqs qr₁ qr₂ hsq',
      e.hom ≫ normalizationInChartQuotientHom B S hS f hfqc hfqs qr₁ qr₂ hsq' =
        normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq :=
  exists_iso_chartRelativeSpecQuotient_of_contains B S hS X
    (AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)))
    (isQuasicoherent_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs)
    pr₁ pr₂ qr₁ qr₂ hsq hsq' hsurj hsurj'
    (contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra B S hS f hfqc hfqs)

include hfqc hfqs hsq hsq' hsurj hsurj' in
/-- **The two normalizations are isomorphic objects of the slice category over `X`.**

The same comparison as `AlgebraicGeometry.Space.exists_iso_normalizationInChartQuotient`, stated
as an isomorphism of the two structure morphisms `ν : X' ⟶ X` in `CategoryTheory.Over X` rather
than as an isomorphism of the two sources together with a commuting triangle.  That is the form
in which "the same relative spectrum over `X`" is a single statement, and the form a definite
description of `ν` needs: `AlgebraicGeometry.Space.normalizationInChartQuotientHom` is one
object of `CategoryTheory.Over X` up to isomorphism, independently of the chart pair. -/
theorem nonempty_isoOver_normalizationInChartQuotientHom :
    Nonempty (Over.mk (normalizationInChartQuotientHom B S hS f hfqc hfqs pr₁ pr₂ hsq) ≅
      Over.mk (normalizationInChartQuotientHom B S hS f hfqc hfqs qr₁ qr₂ hsq')) := by
  obtain ⟨e, he⟩ := exists_iso_normalizationInChartQuotient B S hS f hfqc hfqs pr₁ pr₂ qr₁ qr₂
    hsq hsq' hsurj hsurj'
  exact ⟨Over.isoMk e he⟩

end AlgebraicGeometry.Space

end

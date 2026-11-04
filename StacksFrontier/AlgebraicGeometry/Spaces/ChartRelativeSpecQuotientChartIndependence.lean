module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecPullbackChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# The relative spectrum of a quasi-coherent algebra does not depend on the chart pair

Let `X` be an algebraic space over `S` and let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site.
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotient` builds the relative spectrum

`ν : X' = \underline{Spec}_X(A) ⟶ X`

as the quotient of an étale equivalence relation of relative spectra over a *chosen* pair
`pr₁, pr₂ : V' ⟶ V₂` of morphisms of étale charts exhibiting `V'` as `V₂ ×_X V₂`, with
`V₂ ⟶ X` surjective.  This file removes that choice: two such pairs give the same `X'` and the
same `ν`, up to a canonical isomorphism over `X`, and the isomorphism is unique as an
isomorphism compatible with the two atlases.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpecQuotientChartAtlas`: for a chart `W₂` of `X` and a
  morphism of charts `m : W₂ ⟶ V₂`, the morphism
  `\underline{Spec}_{W₂}(A|_{W₂}) ⟶ X'` obtained from the atlas of `X'` at `V₂`.

## Main results

* `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp_quotientChart`: **any two morphisms of
  charts `W ⟶ V₂` have the same composite into `X'`**, because the relation identifies them.
* `AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientChartAtlas`: **the cartesian
  square at a second chart.**  `\underline{Spec}_{W₂}(A|_{W₂}) = X' ×_X W₂` for every chart
  `W₂` admitting a morphism to the chart `V₂` the quotient was built at.
* `AlgebraicGeometry.Space.existsUnique_desc_chartRelativeSpecQuotientChartAtlas`: **`X'` is
  the quotient of `\underline{Spec}_{W₂}(A|_{W₂})` by the relation of a second pair**, for any
  pair at a chart `W₂` mapping to `V₂`.  This is the engine of the comparison, and its
  uniqueness clause is the uniqueness of the comparison.
* `AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_chartHom`: **the comparison
  for a pair at a refining chart**: if `m : W₂ ⟶ V₂`, the relative spectrum built at the pair
  over `W₂` is canonically isomorphic over `X` to the one built at the pair over `V₂`.
* `AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_common_chart`:
  **independence.**  Two arbitrary pairs give isomorphic relative spectra over `X`, as soon as
  there is a third pair whose chart maps to both of theirs.
* `AlgebraicGeometry.Space.SmallEtale.isPullback_prod`: the binary product of two étale charts
  is their fibre product over the presheaf, and
  `AlgebraicGeometry.Space.presheafSurjective_prodObj_hom`: it is surjective when both factors
  are.
* `AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_contains_prod`:
  **independence with the third pair built.**  The third pair is `Z = V₂ ×_X W₂` and
  `Z' = Z ×_X Z` in the small étale site, so the only remaining hypotheses are the three
  containments in the site that the construction of the relative spectrum carries anyway.
* `AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_contains`: **independence
  with no side condition on the two chart pairs**, for an algebra whose relative spectrum over
  *every* étale chart lies in the site.  That hypothesis is about the algebra alone and is the
  shape in which the containment obligation is already carried elsewhere; for the integral
  closure of `𝒪_X` in `f_* 𝒪_Y` it is a theorem at quasi-compactness and quasi-separatedness
  of `f`, which is what makes
  `AlgebraicGeometry.Space.exists_iso_normalizationInChartQuotient` of
  `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartIndependence` unconditional.

## Implementation notes

**What the comparison is built from, and why no common refinement has to be constructed
here.**  The whole argument is Stacks 0262 part (3),
`AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas`: a sheaf with a representable
surjective étale atlas is the quotient of that atlas by its kernel pair.  Given a pair at `V₂`
and a morphism of charts `m : W₂ ⟶ V₂`, the composite
`\underline{Spec}_{W₂}(A|_{W₂}) ⟶ \underline{Spec}_{V₂}(A|_{V₂}) ⟶ X'` is such an atlas of
`X'`: it is the base change of `W₂ ⟶ X` along `ν`, by the cartesian square at `V₂` of
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientHom` pasted with the cartesian
square of `AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap` at `m`, so it inherits
surjectivity and étaleness from the chart `W₂` — surjectivity from the hypothesis the second
pair carries anyway, étaleness from `AlgebraicGeometry.Space.IsEtaleChart`, which *is* the
étaleness condition.  Its kernel pair is the relation of the second pair, by the same two
squares and the fibre-product hypothesis `hsq` of the second pair.  So `X'` *and* the relative
spectrum built at the second pair are both quotients of
`\underline{Spec}_{W₂}(A|_{W₂})` by the same pair of maps, and
`Stacks.Groupoids.exists_iso_quotientSheaf_of_descent` compares them.

Nothing in this chain compares two charts directly: the comparison is one-sided, between a
pair and a pair at a refining chart, and two arbitrary pairs are then compared through a third
one.  `AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_common_chart` takes that
third pair as a hypothesis;
`AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_contains_prod` builds it.  The
chart of the third pair is the binary product `V₂ ×_X W₂` of the small étale site,
`AlgebraicGeometry.Space.SmallEtale.prodObj`, and its relation is the self-product of that —
both of them products *over `X`*, which is what the relation of a pair has to be, and not
fibre products over an object of the site.  **The lemma that makes this cheap was already in
the library**: `AlgebraicGeometry.Space.SmallEtale.prodObj` is built out of the representability
of its first factor, so the cartesian square over `X` exhibiting the two projections as the
fibre product is `CategoryTheory.Functor.relativelyRepresentable.isPullback'` of that factor and
nothing more — `AlgebraicGeometry.Space.SmallEtale.isPullback_prod` below is the one-line
packaging of a square that until now was re-derived inline where it was wanted.  What is *not*
discharged is the containment of the three new chart objects in the site; those are hypotheses
of the construction of the relative spectrum itself, and are left as hypotheses here.

**Why the uniqueness is stated against the atlases and not over `X` alone.**  A morphism
`X' ⟶ X''` over `X` between two relative spectra of the same algebra is *not* unique: base
changing it along the chart gives a morphism
`\underline{Spec}_{W₂}(A|_{W₂}) ⟶ \underline{Spec}_{W₂}(A|_{W₂})` over `W₂`, and an affine
morphism has non-trivial automorphisms over its target — they are the automorphisms of the
algebra.  What is unique is the morphism compatible with the atlases, which is what
`AlgebraicGeometry.Space.existsUnique_desc_chartRelativeSpecQuotientChartAtlas` provides, and
that is the sense in which the comparison below is canonical.

**No `stacks` attribute is carried.**  Independence of the chart pair is not by itself either
of the two tags it serves.  Definition 0822 names the normalization `ν` *and* the factorization
of `f` through it, and the factorization is not available; Stacks 081V is the relative spectrum
together with the identifications `ν` affine and `ν_* 𝒪_{X'} ≅ A`, of which only the first is
proved (`AlgebraicGeometry.Space.isAffineHom_chartRelativeSpecQuotientHom`).  This file is
infrastructure for both: it is the step that turns "a relative spectrum built at a chosen
atlas" into "the relative spectrum".

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The atlas of the quotient at a second chart -/

section ChartAtlas

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

include hsq in
/-- **Any two morphisms of étale charts `W ⟶ V₂` induce the same morphism of relative spectra
into the quotient.**

The two morphisms have the same composite with the chart of `X`, so the universal property of
`V' = V₂ ×_X V₂` factors the pair through `V'`
(`AlgebraicGeometry.Space.chartRelationLift`), and the chart of the quotient sheaf identifies
the two projections of the relation. -/
theorem chartRelativeSpecSiteMap_comp_quotientChart
    {W : SmallEtale B S hS X.1} (hW : B.Contains (chartRelativeSpec B S hS X A hA W))
    (a b : W ⟶ V₂) :
    yoneda.map (chartRelativeSpecSiteMap B S hS X A hA a hW hV₂) ≫
        Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (chartRelativeSpecSite B S hS X A hA V₂ hV₂)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) =
      yoneda.map (chartRelativeSpecSiteMap B S hS X A hA b hW hV₂) ≫
        Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (chartRelativeSpecSite B S hS X A hA V₂ hV₂)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) := by
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : W ⟶ V', l ≫ pr₁ = a ∧ l ≫ pr₂ = b :=
    ⟨chartRelationLift pr₁ pr₂ hsq a b, chartRelationLift_comp_fst pr₁ pr₂ hsq a b,
      chartRelationLift_comp_snd pr₁ pr₂ hsq a b⟩
  rw [← hl₁, ← hl₂, chartRelativeSpecSiteMap_comp B S hS X A hA hW hV' hV₂ l pr₁,
    chartRelativeSpecSiteMap_comp B S hS X A hA hW hV' hV₂ l pr₂,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, Stacks.Groupoids.map_comp_quotientChart (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion)
      (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
      (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)
      (prod.lift_snd _ _) (prod.lift_fst _ _)]

variable {W₂ : SmallEtale B S hS X.1}
    (hW₂ : B.Contains (chartRelativeSpec B S hS X A hA W₂)) (m : W₂ ⟶ V₂)

/-- **The atlas of `X' = \underline{Spec}_X(A)` at a second chart.**  For a morphism of étale
charts `m : W₂ ⟶ V₂` into the chart the quotient was built at, this is the morphism of relative
spectra over `m` followed by the chart of the quotient sheaf. -/
def chartRelativeSpecQuotientChartAtlas :
    yoneda.obj (chartRelativeSpecSite B S hS X A hA W₂ hW₂) ⟶
      chartRelativeSpecQuotientPresheaf B S hS X A hA pr₁ pr₂ hV' hV₂ :=
  yoneda.map (chartRelativeSpecSiteMap B S hS X A hA m hW₂ hV₂) ≫
    Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion)
      (chartRelativeSpecSite B S hS X A hA V₂ hV₂)
      (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))

include hsq hsurj hV'' in
/-- **The relative spectrum of `A` over a second étale chart is the fibre product of `ν` and
that chart**:

`\underline{Spec}_{W₂}(A|_{W₂}) = \underline{Spec}_X(A) ×_X W₂`,

for every chart `W₂` admitting a morphism to the chart `V₂` at which the quotient was built.

It is `AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientHom`, the square at `V₂`,
pasted with the square of `AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap` at
`m`. -/
theorem isPullback_chartRelativeSpecQuotientChartAtlas :
    IsPullback (chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m)
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA W₂ hW₂))
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom
      W₂.obj.hom := by
  have h := ((isPullback_chartRelativeSpecSiteMap B S hS X A hA m hW₂ hV₂).map
    yoneda).paste_horiz (isPullback_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq
      hsurj hV' hV₂ hV'')
  rwa [yoneda_map_toOver_map_comp_hom] at h

include hsq hsurj hV'' in
/-- **The atlas of `X'` at a second chart is surjective**, being the base change of the chart
along `ν`. -/
theorem presheafSurjective_chartRelativeSpecQuotientChartAtlas
    (hW₂surj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      W₂.obj.hom) :
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m) := by
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
      hW₂ m).flip hW₂surj

include hsq hsurj hV'' in
/-- **The atlas of `X'` at a second chart is étale**, being the base change of the chart along
`ν`.  Étaleness of the chart is not a hypothesis: it is
`AlgebraicGeometry.Space.IsEtaleChart`, the defining property of an object of the small étale
site. -/
theorem presheafEtale_chartRelativeSpecQuotientChartAtlas :
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m) := by
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
      hW₂ m).flip W₂.property

variable {W' : SmallEtale B S hS X.1} (qr₁ qr₂ : W' ⟶ W₂)
    (hsq' : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map qr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map qr₂)) W₂.obj.hom W₂.obj.hom)
    (hW' : B.Contains (chartRelativeSpec B S hS X A hA W'))

include hsq in
/-- **The two projections of a second pair have the same composite into `X'`.** -/
theorem chartRelativeSpecSiteMap_comp_chartRelativeSpecQuotientChartAtlas :
    yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₂ hW' hW₂) ≫
        chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m =
      yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₁ hW' hW₂) ≫
        chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m := by
  have hdef : chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m =
      yoneda.map (chartRelativeSpecSiteMap B S hS X A hA m hW₂ hV₂) ≫
        Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (chartRelativeSpecSite B S hS X A hA V₂ hV₂)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) := rfl
  rw [hdef, ← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp,
    ← chartRelativeSpecSiteMap_comp B S hS X A hA hW' hW₂ hV₂ qr₂ m,
    ← chartRelativeSpecSiteMap_comp B S hS X A hA hW' hW₂ hV₂ qr₁ m]
  exact chartRelativeSpecSiteMap_comp_quotientChart B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hW'
    (qr₂ ≫ m) (qr₁ ≫ m)

include hsq hsurj hV'' hsq' in
/-- **The relation of a second pair is the kernel pair of the atlas of `X'` at its chart.**

Both squares that go into it are base changes of `ν`: the relation of relative spectra is
`X' ×_X W'` and `W' = W₂ ×_X W₂`, so the square is the cartesian square at `W₂` with the
fibre-product hypothesis of the second pair stacked on it. -/
theorem isPullback_chartRelativeSpecQuotientChartAtlas_self :
    IsPullback (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₂ hW' hW₂))
      (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₁ hW' hW₂))
      (chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m)
      (chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m) := by
  have hsqr := isPullback_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hsq hsurj
    hV' hV₂ hV'' hW₂ m
  refine IsPullback.of_bot ?_
    (chartRelativeSpecSiteMap_comp_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂
      hsq hV' hV₂ hW₂ m qr₁ qr₂ hW') hsqr
  have hleg : yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₁ hW' hW₂) ≫
        yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA W₂ hW₂) =
      yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA W' hW') ≫
        yoneda.map ((SmallEtale.toOver B S hS X.1).map qr₁) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      (isPullback_chartRelativeSpecSiteMap B S hS X A hA qr₁ hW' hW₂).w]
  rw [hleg, hsqr.w]
  exact ((isPullback_chartRelativeSpecSiteMap B S hS X A hA qr₂ hW' hW₂).map
    yoneda).paste_vert hsq'.flip

include hsq hsurj hV'' hsq' in
/-- **`X'` is the quotient of the relative spectrum over a second chart by the relation of a
second pair.**

This is Stacks 0262 part (3), `AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas`,
at the atlas `AlgebraicGeometry.Space.chartRelativeSpecQuotientChartAtlas`: that morphism is
representable, surjective and étale, and its kernel pair is the relation of the second pair.
The uniqueness clause is what makes the comparison of two relative spectra canonical. -/
theorem existsUnique_desc_chartRelativeSpecQuotientChartAtlas
    (hW₂surj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      W₂.obj.hom)
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (k : yoneda.obj (chartRelativeSpecSite B S hS X A hA W₂ hW₂) ⟶ G)
    (hk : yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₂ hW' hW₂) ≫ k =
      yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₁ hW' hW₂) ≫ k) :
    ∃! d : chartRelativeSpecQuotientPresheaf B S hS X A hA pr₁ pr₂ hV' hV₂ ⟶ G,
      chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m ≫ d = k :=
  existsUnique_desc_of_surjective_etale_atlas B S hS
    (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').property.isSheaf
    (chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m)
    (isPullback_chartRelativeSpecQuotientChartAtlas_self B S hS X A hA pr₁ pr₂ hsq hsurj hV'
      hV₂ hV'' hW₂ m qr₁ qr₂ hsq' hW')
    (presheafSurjective_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' hW₂ m hW₂surj)
    (presheafEtale_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hsq hsurj hV'
      hV₂ hV'' hW₂ m)
    hG k hk

end ChartAtlas

/-! ### The comparison of two relative spectra -/

section Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ W' W₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (qr₁ qr₂ : W' ⟶ W₂)
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
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))
    (hW' : B.Contains (chartRelativeSpec B S hS X A hA W'))
    (hW₂ : B.Contains (chartRelativeSpec B S hS X A hA W₂))
    (hW'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback qr₁ qr₂)))

include hsq hsq' hsurj hsurj' hV'' hW'' in
/-- **The relative spectrum built at a pair over a refining chart is the relative spectrum.**

Given a pair `pr₁, pr₂ : V' ⟶ V₂` and a pair `qr₁, qr₂ : W' ⟶ W₂` of morphisms of étale
charts of `X`, both exhibiting their relation as the self fibre product of their chart over `X`
and both with surjective chart, and given a morphism of charts `m : W₂ ⟶ V₂`, the two relative
spectra are canonically isomorphic over `X`.

Both are quotients of `\underline{Spec}_{W₂}(A|_{W₂})` by the relation of the second pair: for
the second one that is its construction, and for the first it is
`AlgebraicGeometry.Space.existsUnique_desc_chartRelativeSpecQuotientChartAtlas`.  The
isomorphism is the comparison of two coequalizers of the same pair of maps,
`Stacks.Groupoids.exists_iso_quotientSheaf_of_descent`; it is unique as an isomorphism carrying
the one atlas to the other, by the uniqueness clause of that same descent property. -/
theorem exists_iso_chartRelativeSpecQuotient_of_chartHom (m : W₂ ⟶ V₂) :
    ∃ e : chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' ≅
        chartRelativeSpecQuotient B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'',
      e.hom ≫ chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'' =
          chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' ∧
        chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m ≫ e.hom.hom =
          Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
            (Over.post (X := B.obj hS) B.inclusion)
            (chartRelativeSpecSite B S hS X A hA W₂ hW₂)
            (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA qr₂ hW' hW₂)
              (chartRelativeSpecSiteMap B S hS X A hA qr₁ hW' hW₂)) := by
  have hdesc := existsUnique_desc_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂
    hsq hsurj hV' hV₂ hV'' hW₂ m qr₁ qr₂ hsq' hW' hsurj'
  have hker := isPullback_chartRelativeSpecQuotientChartAtlas_self B S hS X A hA pr₁ pr₂ hsq
    hsurj hV' hV₂ hV'' hW₂ m qr₁ qr₂ hsq' hW'
  obtain ⟨e₀, he₀⟩ := Stacks.Groupoids.exists_iso_quotientSheaf_of_descent
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (chartRelativeSpecSiteMap B S hS X A hA qr₂ hW' hW₂)
    (chartRelativeSpecSiteMap B S hS X A hA qr₁ hW' hW₂) (prod.lift_snd _ _)
    (prod.lift_fst _ _)
    (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').property.isSheaf
    (chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m) hker.w
    (fun T k hk => hdesc T.obj T.property k hk)
  refine ⟨ObjectProperty.isoMk _ e₀, ObjectProperty.hom_ext _ ?_, he₀⟩
  have hk : yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₂ hW' hW₂) ≫
        chartRelativeSpecSiteToSpace B S hS X A hA W₂ hW₂ =
      yoneda.map (chartRelativeSpecSiteMap B S hS X A hA qr₁ hW' hW₂) ≫
        chartRelativeSpecSiteToSpace B S hS X A hA W₂ hW₂ := by
    rw [chartRelativeSpecSiteMap_comp_chartRelativeSpecSiteToSpace,
      chartRelativeSpecSiteMap_comp_chartRelativeSpecSiteToSpace]
  obtain ⟨d₀, -, huniq⟩ := hdesc X.1 X.property.isSheaf
    (chartRelativeSpecSiteToSpace B S hS X A hA W₂ hW₂) hk
  have h₁ : chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m ≫
      (e₀.hom ≫ (chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'').hom) =
      chartRelativeSpecSiteToSpace B S hS X A hA W₂ hW₂ :=
    (Category.assoc (chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m)
        e₀.hom
        (chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'').hom).symm.trans
      ((congrArg (fun t => t ≫ (chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' hW'
          hW₂ hW'').hom) he₀).trans
        (isPullback_chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' hsurj' hW' hW₂
          hW'').w)
  have h₂ : chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW₂ m ≫
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom =
      chartRelativeSpecSiteToSpace B S hS X A hA W₂ hW₂ :=
    (isPullback_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂
      hV'' hW₂ m).w
  exact (huniq _ h₁).trans (huniq _ h₂).symm

variable {Z' Z : SmallEtale B S hS X.1} (zr₁ zr₂ : Z' ⟶ Z)
    (hsqz : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map zr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map zr₂)) Z.obj.hom Z.obj.hom)
    (hsurjz : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      Z.obj.hom)
    (hZ' : B.Contains (chartRelativeSpec B S hS X A hA Z'))
    (hZ : B.Contains (chartRelativeSpec B S hS X A hA Z))
    (hZ'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback zr₁ zr₂)))

include hsq hsq' hsqz hsurj hsurj' hsurjz hV'' hW'' hZ' hZ hZ'' in
/-- **The relative spectrum of a quasi-coherent algebra over an algebraic space is independent
of the chosen pair of étale charts.**

Two pairs `pr₁, pr₂ : V' ⟶ V₂` and `qr₁, qr₂ : W' ⟶ W₂` of morphisms of étale charts of `X`,
each exhibiting its relation as the self fibre product of its chart over `X` and each with
surjective chart, give relative spectra canonically isomorphic over `X`, as soon as there is a
third such pair `zr₁, zr₂ : Z' ⟶ Z` whose chart `Z` maps to both `V₂` and `W₂`.

Each of the two is compared with the third by
`AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_chartHom`, and the two
comparisons are composed.  A third pair always exists mathematically — take `Z = V₂ ×_X W₂`,
the binary product `AlgebraicGeometry.Space.SmallEtale.prodObj` of the small étale site, and
`Z' = Z ×_X Z` — and it is taken as a hypothesis here because its chart objects have to be
contained in the site, which is a hypothesis of the construction itself and not something this
file can discharge. -/
theorem exists_iso_chartRelativeSpecQuotient_of_common_chart (n : Z ⟶ V₂) (n' : Z ⟶ W₂) :
    ∃ e : chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' ≅
        chartRelativeSpecQuotient B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'',
      e.hom ≫ chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'' =
        chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' := by
  obtain ⟨e₁, he₁, -⟩ := exists_iso_chartRelativeSpecQuotient_of_chartHom B S hS X A hA pr₁ pr₂
    zr₁ zr₂ hsq hsqz hsurj hsurjz hV' hV₂ hV'' hZ' hZ hZ'' n
  obtain ⟨e₂, he₂, -⟩ := exists_iso_chartRelativeSpecQuotient_of_chartHom B S hS X A hA qr₁ qr₂
    zr₁ zr₂ hsq' hsqz hsurj' hsurjz hW' hW₂ hW'' hZ' hZ hZ'' n'
  have hinv : e₂.inv ≫ chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'' =
      chartRelativeSpecQuotientHom B S hS X A hA zr₁ zr₂ hsqz hZ' hZ hZ'' := by
    rw [← he₂]
    simp
  refine ⟨e₁ ≪≫ e₂.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hinv, he₁]

end Comparison

/-! ### The common refinement of two charts -/

section Refinement

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The binary product of two étale charts is their fibre product over the presheaf.**  The
product of `AlgebraicGeometry.Space.SmallEtale.prodObj` is built from the representability of
the first chart, so its two projections are the two legs of the representing cartesian square
`CategoryTheory.Functor.relativelyRepresentable.isPullback'`. -/
theorem SmallEtale.isPullback_prod (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (U V : SmallEtale B S hS F) :
    IsPullback (yoneda.map ((SmallEtale.toOver B S hS F).map (SmallEtale.prodFst B S hS F U V)))
      (yoneda.map ((SmallEtale.toOver B S hS F).map (SmallEtale.prodSnd B S hS F U V)))
      U.obj.hom V.obj.hom :=
  U.property.rep.isPullback' V.obj.hom

variable (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ W' W₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (qr₁ qr₂ : W' ⟶ W₂)
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

include hsurj hsurj' in
/-- **The binary product of two surjective étale charts is surjective over the presheaf.**  Its
structure morphism is by construction the second projection followed by the second chart, and
the second projection is the base change of the first chart along the second. -/
theorem presheafSurjective_prodObj_hom :
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (SmallEtale.prodObj B S hS X.1 V₂ W₂).obj.hom := by
  have := surjective_isStableUnderComposition.{u}
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hsnd : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map
        (SmallEtale.prodSnd B S hS X.1 V₂ W₂))) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (SmallEtale.isPullback_prod B S hS X.1 V₂ W₂) hsurj
  have hcomp : (SmallEtale.prodObj B S hS X.1 V₂ W₂).obj.hom =
      yoneda.map ((SmallEtale.toOver B S hS X.1).map
        (SmallEtale.prodSnd B S hS X.1 V₂ W₂)) ≫ W₂.obj.hom := rfl
  rw [hcomp]
  exact MorphismProperty.comp_mem _ _ _ hsnd hsurj'

variable (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))
    (hW' : B.Contains (chartRelativeSpec B S hS X A hA W'))
    (hW₂ : B.Contains (chartRelativeSpec B S hS X A hA W₂))
    (hW'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback qr₁ qr₂)))

include hsq hsq' hsurj hsurj' hV'' hW'' in
/-- **The relative spectrum of a quasi-coherent algebra over an algebraic space is independent
of the chosen pair of étale charts**, as soon as the three chart objects of the common
refinement are contained in the site.

The common refinement is `Z = V₂ ×_X W₂`, the binary product
`AlgebraicGeometry.Space.SmallEtale.prodObj` of the small étale site, with `Z' = Z ×_X Z` its
self-product; its two projections to `V₂` and to `W₂` feed
`AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_common_chart`.  The three
containment hypotheses are of exactly the shape the construction of the relative spectrum
itself carries, and are the only thing that keeps this from being unconditional. -/
theorem exists_iso_chartRelativeSpecQuotient_of_contains_prod
    (hZ : B.Contains (chartRelativeSpec B S hS X A hA
      (SmallEtale.prodObj B S hS X.1 V₂ W₂)))
    (hZ' : B.Contains (chartRelativeSpec B S hS X A hA (SmallEtale.prodObj B S hS X.1
      (SmallEtale.prodObj B S hS X.1 V₂ W₂) (SmallEtale.prodObj B S hS X.1 V₂ W₂))))
    (hZ'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback
      (SmallEtale.prodFst B S hS X.1 (SmallEtale.prodObj B S hS X.1 V₂ W₂)
        (SmallEtale.prodObj B S hS X.1 V₂ W₂))
      (SmallEtale.prodSnd B S hS X.1 (SmallEtale.prodObj B S hS X.1 V₂ W₂)
        (SmallEtale.prodObj B S hS X.1 V₂ W₂))))) :
    ∃ e : chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' ≅
        chartRelativeSpecQuotient B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'',
      e.hom ≫ chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' hW' hW₂ hW'' =
        chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' :=
  exists_iso_chartRelativeSpecQuotient_of_common_chart B S hS X A hA pr₁ pr₂ qr₁ qr₂
    hsq hsq' hsurj hsurj' hV' hV₂ hV'' hW' hW₂ hW''
    (SmallEtale.prodFst B S hS X.1 (SmallEtale.prodObj B S hS X.1 V₂ W₂)
      (SmallEtale.prodObj B S hS X.1 V₂ W₂))
    (SmallEtale.prodSnd B S hS X.1 (SmallEtale.prodObj B S hS X.1 V₂ W₂)
      (SmallEtale.prodObj B S hS X.1 V₂ W₂))
    (SmallEtale.isPullback_prod B S hS X.1 (SmallEtale.prodObj B S hS X.1 V₂ W₂)
      (SmallEtale.prodObj B S hS X.1 V₂ W₂))
    (presheafSurjective_prodObj_hom B S hS X hsurj hsurj')
    hZ' hZ hZ''
    (SmallEtale.prodFst B S hS X.1 V₂ W₂) (SmallEtale.prodSnd B S hS X.1 V₂ W₂)

include hsq hsq' hsurj hsurj' in
/-- **The relative spectrum of a quasi-coherent algebra over an algebraic space does not depend
on the chart pair at all**, for an algebra whose relative spectrum over *every* étale chart is
an object of the site.

This is `AlgebraicGeometry.Space.exists_iso_chartRelativeSpecQuotient_of_contains_prod` with its
three remaining hypotheses discharged.  Those three hypotheses say that the relative spectra of
`A` over the common refinement `Z = V₂ ×_X W₂`, over `Z ×_X Z` and over the kernel pair of its
two projections lie in the site; they are instances of `hcon`, which is the shape in which the
containment obligation is already carried by
`AlgebraicGeometry.Space.chartRelativeSpecQuotientPushforwardIso`, and which
`AlgebraicGeometry.Space.contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra`
supplies for the integral closure of `𝒪_X` in `f_* 𝒪_Y` from quasi-compactness and
quasi-separatedness of `f` alone.  So for that algebra — the one Definition 0822 takes the
relative spectrum of — the chart pair is immaterial with no side condition whatsoever.

The hypotheses that remain are the two halves of the chart pair itself: that each relation is
the self fibre product of its chart over `X`, and that each chart is surjective.  A quadruple
that fails either is not a chart pair, so no hypothesis of the independence statement restricts
*which* chart pairs are compared. -/
theorem exists_iso_chartRelativeSpecQuotient_of_contains
    (hcon : ∀ V : SmallEtale B S hS X.1, B.Contains (chartRelativeSpec B S hS X A hA V)) :
    ∃ e : chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq (hcon V') (hcon V₂)
          (hcon (Limits.pullback pr₁ pr₂)) ≅
        chartRelativeSpecQuotient B S hS X A hA qr₁ qr₂ hsq' (hcon W') (hcon W₂)
          (hcon (Limits.pullback qr₁ qr₂)),
      e.hom ≫ chartRelativeSpecQuotientHom B S hS X A hA qr₁ qr₂ hsq' (hcon W') (hcon W₂)
            (hcon (Limits.pullback qr₁ qr₂)) =
        chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq (hcon V') (hcon V₂)
          (hcon (Limits.pullback pr₁ pr₂)) :=
  exists_iso_chartRelativeSpecQuotient_of_contains_prod B S hS X A hA pr₁ pr₂ qr₁ qr₂
    hsq hsq' hsurj hsurj' (hcon V') (hcon V₂) (hcon (Limits.pullback pr₁ pr₂)) (hcon W')
    (hcon W₂) (hcon (Limits.pullback qr₁ qr₂)) (hcon _) (hcon _) (hcon _)

end Refinement

end AlgebraicGeometry.Space

end

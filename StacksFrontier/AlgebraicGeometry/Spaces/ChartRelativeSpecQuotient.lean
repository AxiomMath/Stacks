module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionSquaringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# The relative spectrum of a quasi-coherent algebra over an algebraic space, and its structure
morphism

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site, and let `pr₁, pr₂ : V' ⟶ V₂` be a pair of morphisms of
étale charts of `X` exhibiting `V'` as the fibre product `V₂ ×_X V₂`.
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecEquivalenceRelation` makes the pair of
relative spectra `\underline{Spec}_{V'}(A|_{V'}) ⇉ \underline{Spec}_{V₂}(A|_{V₂})` an étale
equivalence relation over `S`.  This file forms its quotient and the structure morphism of the
quotient to `X`:

`ν : \underline{Spec}_X(A) ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpecSiteToSpace`: the morphism
  `\underline{Spec}_{V}(A|_V) ⟶ X` of presheaves attached to a chart, the structure morphism over
  the chart followed by the chart itself.
* `AlgebraicGeometry.Space.chartRelativeSpecQuotient`: **the quotient `\underline{Spec}_X(A)`, as
  an algebraic space over `S`.**
* `AlgebraicGeometry.Space.chartRelativeSpecQuotientHom`: **the morphism `ν` from it to `X`.**

## Main results

* `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp_chartRelativeSpecSiteToSpace`: the
  morphisms to `X` attached to the charts are compatible with the morphisms of relative spectra,
  which is what lets them descend.
* `AlgebraicGeometry.Space.toQuotientSheaf_comp_chartRelativeSpecQuotientHom`: **`ν` restricts on
  the chart to the chart's own morphism to `X`**, which characterises it.
* `AlgebraicGeometry.Space.chartRelativeSpecQuotientHom_unique`: and characterises it uniquely.

## Implementation notes

**What `ν` is and what it is not.**  It is the structure morphism of the relative spectrum of
Stacks 081V, built where the source builds it: as the morphism which the chart's own structure
morphism `\underline{Spec}_{V₂}(A|_{V₂}) ⟶ V₂ ⟶ X` descends to along the quotient map, by the
universal property `AlgebraicGeometry.Space.quotientSheafDesc` of the quotient sheaf.  The two
composites out of the relative spectrum over `V'` agree because
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap` makes each of the two morphisms of
relative spectra a morphism over the corresponding projection of charts, and the two projections
of charts have the same composite with the chart of `X`.

It is *not* claimed here that `ν` is affine, nor that `ν_* 𝒪_{\underline{Spec}_X(A)}` is `A`;
both are needed before Definition 0822 is reached, and neither is proved anywhere in this
development.  See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` for the remaining steps.

**The factorization `Y ⟶ X'` is not a separate obstruction, and it is not Stacks 081X.**  A
route through the refuted `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` is one route,
not the mathematics: the content of 081X is a morphism into a relative spectrum classified
by an algebra map, and at the chart — where `X'` is built — it is available outright, as
`AlgebraicGeometry.Space.chartRelativeSpecLift` and
`AlgebraicGeometry.Space.pushforwardAlgebraMap_chartRelativeSpecLift` of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecUniversalProperty`, at quasi-coherence of
`A` and nothing else.  (At the scheme level the whole of 081X is proved twice over, as
`Stacks.RelativeSpec.toRelativeSpec` and `Stacks.RelativeSpec.canonicalMap`, both tagged
Stacks 01LY.)  What the factorization still owes is the same thing the two identifications above
owe: descent through this quotient.  For `f' : Y ⟶ X'` that descent is the harder of the two,
because an étale chart `V₂ ⟶ X` does not pull a quasi-compact quasi-separated `Y` back to a
scheme: the algebra map handed to `AlgebraicGeometry.Space.chartRelativeSpecLift` has to be
formed on a scheme chart of `Y ×_X V₂`, which is also a chart of `Y`, and the resulting morphism
descended through the relation of that chart as well as through the quotient here.

**No `stacks` attribute is carried**: Definition 0822 names both `ν` and the
factorization of `f` through it, and the factorization is not available.  Stacks 02WW is
registered on the quotient construction itself, in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional`, and Stacks 081V is
not discharged by this file either: the relative spectrum is built here at the pair of charts
supplied by the caller, not shown independent of that choice.

**No sheafification hypothesis is carried.** The quotient presheaf is sheafified in the universe
of the sections, which is not Mathlib's size-matched case — the objects of the big fppf category
over `S` lie one universe above its morphisms — but it needs no assumption all the same:
`AlgebraicGeometry.hasSheafifyBigFppfOver` is a global instance, obtained from the essential
smallness of the affine objects of the site and the dense inclusion of Tag 021V. So the results
below hold under exactly the hypotheses of Stacks 02WW.

## References

* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-! ### Naturality of the restricted functor of points -/

/-- Composition with the image of a morphism, read on restricted functors of points, is
`CategoryTheory.yoneda` of the morphism across `AlgebraicGeometry.Space.pointsYonedaIso`.  This is
`AlgebraicGeometry.Space.pointsYonedaIso_inv_comp_whiskerLeft` at a morphism which is itself an
image, written in the direction the universal property of a quotient sheaf consumes. -/
theorem whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom {C : Type v} [Category.{u} C]
    {S : Scheme.{u}} (F : C ⥤ Over S) [F.Full] [F.Faithful] {V W : C} (g : V ⟶ W) :
    F.op.whiskerLeft (yoneda.map (F.map g)) ≫ (pointsYonedaIso F W).hom =
      (pointsYonedaIso F V).hom ≫ yoneda.map g := by
  have h := pointsYonedaIso_inv_comp_whiskerLeft F (F.map g)
  rw [F.preimage_map, Iso.inv_comp_eq] at h
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### The morphism of a chart's relative spectrum to the algebraic space -/

section ToSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent)

/-- **The morphism `\underline{Spec}_{V}(A|_V) ⟶ X` attached to an étale chart `V` of `X`**: the
structure morphism over the chart, followed by the chart itself. -/
def chartRelativeSpecSiteToSpace (V : SmallEtale B S hS X.1)
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) :
    yoneda.obj (chartRelativeSpecSite B S hS X A hA V hV) ⟶ X.1 :=
  yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA V hV) ≫ V.obj.hom

/-- **The morphisms to `X` attached to the charts are compatible with the morphisms of relative
spectra.**  This is what makes them descend to the quotient: the square of
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap` makes the morphism of relative
spectra a morphism over the morphism of charts, and a morphism of charts commutes with the two
charts of `X`. -/
theorem chartRelativeSpecSiteMap_comp_chartRelativeSpecSiteToSpace
    {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) :
    yoneda.map (chartRelativeSpecSiteMap B S hS X A hA h hV' hV) ≫
        chartRelativeSpecSiteToSpace B S hS X A hA V hV =
      chartRelativeSpecSiteToSpace B S hS X A hA V' hV' := by
  rw [chartRelativeSpecSiteToSpace, chartRelativeSpecSiteToSpace, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp,
    (isPullback_chartRelativeSpecSiteMap B S hS X A hA h hV' hV).w,
    CategoryTheory.Functor.map_comp, Category.assoc, yoneda_map_toOver_map_comp_hom]

end ToSpace

/-! ### The quotient and its structure morphism -/

section Quotient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))

/-- The quotient sheaf of the étale equivalence relation of relative spectra, as a presheaf. -/
abbrev chartRelativeSpecQuotientPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
      (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))).obj

include hsq hV'' in
/-- **The quotient `\underline{Spec}_X(A)` is an algebraic space over `S`.**  This is Tag 02WW
applied to the étale equivalence relation of
`AlgebraicGeometry.Space.isEtaleEquivalenceRelation_chartRelativeSpecSiteMap_of_isPullback`. -/
theorem isAlgebraicSpace_chartRelativeSpecQuotientPresheaf :
    IsAlgebraicSpace B S hS
      (chartRelativeSpecQuotientPresheaf B S hS X A hA pr₁ pr₂ hV' hV₂) :=
  have := isEtaleEquivalenceRelation_chartRelativeSpecSiteMap_of_isPullback B S hS X A hA
    pr₁ pr₂ hsq hV' hV₂ hV''
  isAlgebraicSpace_quotient_unconditional B S hS _ _

include hsq hV'' in
/-- **The relative spectrum `\underline{Spec}_X(A)` of a quasi-coherent algebra over an algebraic
space, as an algebraic space over `S`**: the quotient of the étale equivalence relation of the
relative spectra over a relation of étale charts. -/
def chartRelativeSpecQuotient : AlgebraicSpaces B S hS :=
  ⟨chartRelativeSpecQuotientPresheaf B S hS X A hA pr₁ pr₂ hV' hV₂,
    isAlgebraicSpace_chartRelativeSpecQuotientPresheaf B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV''⟩

/-- The chart's morphism to `X`, read on the restricted functor of points, identifies the two
projections of the relation — which is the hypothesis the universal property of the quotient
sheaf asks for. -/
theorem sourceMap_comp_pointsYonedaIso_hom_chartRelativeSpecSiteToSpace :
    Stacks.Groupoids.sourceMap (Over.post B.inclusion)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) ≫
        ((pointsYonedaIso (Over.post B.inclusion)
            (chartRelativeSpecSite B S hS X A hA V₂ hV₂)).hom ≫
          chartRelativeSpecSiteToSpace B S hS X A hA V₂ hV₂) =
      Stacks.Groupoids.targetMap (Over.post B.inclusion)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) ≫
        ((pointsYonedaIso (Over.post B.inclusion)
            (chartRelativeSpecSite B S hS X A hA V₂ hV₂)).hom ≫
          chartRelativeSpecSiteToSpace B S hS X A hA V₂ hV₂) := by
  have hsrc : (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)).source =
      (Over.post (X := B.obj hS) B.inclusion).map
        (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂) := prod.lift_snd _ _
  have htgt : (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)).target =
      (Over.post (X := B.obj hS) B.inclusion).map
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂) := prod.lift_fst _ _
  rw [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap, hsrc, htgt, ← Category.assoc,
    ← Category.assoc, whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom,
    whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom, Category.assoc, Category.assoc,
    chartRelativeSpecSiteMap_comp_chartRelativeSpecSiteToSpace,
    chartRelativeSpecSiteMap_comp_chartRelativeSpecSiteToSpace]

include hsq hV'' in
/-- **The structure morphism `ν : \underline{Spec}_X(A) ⟶ X`.**  It is the morphism which the
chart's own morphism `\underline{Spec}_{V₂}(A|_{V₂}) ⟶ V₂ ⟶ X` descends to along the quotient
map, by the universal property of the quotient sheaf. -/
def chartRelativeSpecQuotientHom :
    chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' ⟶ X :=
  ObjectProperty.homMk
    (Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
        (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))
      ⟨X.1, X.property.isSheaf⟩
      ((pointsYonedaIso (Over.post B.inclusion)
          (chartRelativeSpecSite B S hS X A hA V₂ hV₂)).hom ≫
        chartRelativeSpecSiteToSpace B S hS X A hA V₂ hV₂)
      (sourceMap_comp_pointsYonedaIso_hom_chartRelativeSpecSiteToSpace B S hS X A hA
        pr₁ pr₂ hV' hV₂)).hom

include hsq hV'' in
/-- **`ν` restricts on the chart to the chart's own morphism to `X`.** -/
theorem toQuotientSheaf_comp_chartRelativeSpecQuotientHom :
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) ≫
        (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom =
      (pointsYonedaIso (Over.post B.inclusion)
          (chartRelativeSpecSite B S hS X A hA V₂ hV₂)).hom ≫
        chartRelativeSpecSiteToSpace B S hS X A hA V₂ hV₂ :=
  Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc _ _ _ _ _ _

include hsq hV'' in
/-- **`ν` is the only morphism to `X` which restricts on the chart to the chart's own morphism to
`X`.** -/
theorem chartRelativeSpecQuotientHom_unique
    (d : chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' ⟶ X)
    (hd : Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) ≫ d.hom =
      (pointsYonedaIso (Over.post B.inclusion)
          (chartRelativeSpecSite B S hS X A hA V₂ hV₂)).hom ≫
        chartRelativeSpecSiteToSpace B S hS X A hA V₂ hV₂) :
    d = chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'' := by
  refine ObjectProperty.hom_ext _ ?_
  have h := Stacks.Groupoids.quotientSheafDesc_unique (BigFppfOver.topology B S hS)
    (Over.post B.inclusion)
    (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
      (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))
    ⟨X.1, X.property.isSheaf⟩
    ((pointsYonedaIso (Over.post B.inclusion)
        (chartRelativeSpecSite B S hS X A hA V₂ hV₂)).hom ≫
      chartRelativeSpecSiteToSpace B S hS X A hA V₂ hV₂)
    (sourceMap_comp_pointsYonedaIso_hom_chartRelativeSpecSiteToSpace B S hS X A hA
      pr₁ pr₂ hV' hV₂)
    ⟨d.hom⟩ hd
  exact congrArg (fun f => f.hom) h

end Quotient

end AlgebraicGeometry.Space

end

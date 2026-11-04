module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecChartMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeMapEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOverHom

/-!
# The atlas relation of the relative spectrum of a quasi-coherent algebra on an algebraic space

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site, and let `V` run over the étale scheme charts of `X`.
`AlgebraicGeometry.Space.chartRelativeSpec` is the scheme `\underline{Spec}_V(A|_V)` and
`AlgebraicGeometry.Space.chartRelativeSpecChartMap` makes it depend on the chart; for the two
projections of a relation `R ⇉ U` of charts the resulting pair of morphisms of schemes is the
candidate étale equivalence relation whose quotient by Tag 02WW is `\underline{Spec}_X(A)`.

This file assembles that pair **as a pair of morphisms of the big fppf site over `S`**, which is
the shape `AlgebraicGeometry.Space.relation` and hence
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional` consume, and discharges the
étaleness of the two legs outright.  What it does *not* do is produce the internal
equivalence-relation structure on the pair; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpecSite`: the relative spectrum over a chart as an
  object of the big fppf site over `S`, given that its underlying scheme is contained in the
  site.
* `AlgebraicGeometry.Space.chartRelativeSpecSiteMap`: the morphism of site objects induced by a
  morphism of charts.

## Main results

* `AlgebraicGeometry.Space.etale_chartRelativeSpecChartMap`: **the morphism of relative spectra
  induced by any morphism of étale charts is étale**, unconditionally.  This is the
  étale-legs input of `Stacks.Groupoids.IsEtaleEquivalenceRelation`.
* `AlgebraicGeometry.Space.surjective_chartRelativeSpecChartMap`: it is surjective whenever the
  morphism of chart schemes is.
* `AlgebraicGeometry.Space.etale_toScheme_map_chartRelativeSpecSiteMap`: the same, read on the
  morphism of site objects.
* `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp` and
  `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_id`: **the morphisms of site objects are
  functorial in the chart.**  This is the cocycle condition, and it is unconditional beyond
  quasi-coherence of `A`; the implementation notes record why the cartesian squares do not prove
  it and what does.
* `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_chartRelativeSpecSiteMap`: **the pair of
  site morphisms attached to a pair of morphisms of charts is an étale equivalence relation as
  soon as the represented pair of morphisms of presheaves is an internal equivalence
  relation.**  The equivalence-relation hypothesis is the one remaining input; everything else
  is discharged here.

## Implementation notes

**The cocycle condition is a theorem, and the cartesian squares are not what proves it.**
Reflexivity, symmetry and transitivity of the pair are, in the representable analogue
`AlgebraicGeometry.Space.NormalizationGluing.equivalenceRelation_normRel`, instances of the
*functoriality* of the chart construction: the three identities are
`AlgebraicGeometry.Space.NormalizationGluing.normChartMap_comp` together with an identity
between morphisms of charts.  The corresponding functoriality of the relative spectrum is
`AlgebraicGeometry.Space.chartRelativeSpecChartMap_comp` and
`AlgebraicGeometry.Space.chartRelativeSpecChartMap_id`, read on site objects as
`AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp` and
`AlgebraicGeometry.Space.chartRelativeSpecSiteMap_id` below.  Both are unconditional beyond
quasi-coherence of `A`.

`AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap` cannot supply them.  A cartesian
square `IsPullback (chartRelativeSpecChartMap h) (chartRelativeSpecToChart V')
(chartRelativeSpecToChart V) (chartSchemeMap h)` determines its top edge only up to an
automorphism of `\underline{Spec}_{V'}(A|_{V'})` over `chartScheme V'`, and an affine morphism
has such automorphisms; concretely, taking `h = 𝟙` the square says that
`chartRelativeSpecChartMap (𝟙 V)` is a map over the identity of `chartScheme V`, not that it is
the identity, and the uniqueness clause of the lift is circular in exactly that statement.  So
the cocycle is extra information, and it comes from the algebra side.  The route taken is
*rigidity* rather than a cocycle for the two factors out of which
`AlgebraicGeometry.Space.chartRelativeSpecChartMap` is built:
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeMap_eq_relativeSpecMapOverBase`
identifies that composite with the morphism which the universal property of the relative
spectrum over a *varying* base attaches to the adjunct algebra map
`A|_V ⟶ (chartSchemeMap h)_*(A|_{V'})`, and such a morphism is *determined* by its algebra map
(`Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom_ext`).  The composition law is then
`Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase_comp` together with functoriality of
the chart comparison, `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom_comp`, which on
underlying sheaves of rings is the restriction map of `A` and so is functoriality of `A` itself.
No `_comp` or `_id` lemma for `AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom` is
needed, and no compatibility of `Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso` with
a *composite* base change: one single-base computation of its algebra map,
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecBaseChangeIso_inv`, replaces
the three-base cocycle.

**The hypothesis `hrel` is discharged, in a later file.**  With the cocycle in hand, the
remaining content of `hrel` is the internal equivalence-relation *structure*, built as
`AlgebraicGeometry.Space.NormalizationGluing.equivalenceRelation_normRel` builds it: the
`CategoryTheory.JointlyMono₂` clause, the reflexivity and symmetry identities — immediate
from `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp` and
`AlgebraicGeometry.Space.chartRelativeSpecSiteMap_id` applied to the diagonal and the swap of
the chart relation — and the transitivity cone, which asks for the triple fibre product of the
two legs and hence for a composite of two squares of
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap`, in the shape of
`AlgebraicGeometry.Space.NormalizationGluing.isPullback_normRel₂`.  That structure is
`AlgebraicGeometry.Space.equivalenceRelation_chartRelativeSpecSiteMap` of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecEquivalenceRelation`, and
`AlgebraicGeometry.Space.isEquivalenceRelation_chartRelativeSpecSiteMap` there supplies `hrel`
whenever `pr₁` and `pr₂` exhibit the source chart as the fibre product of the target chart with
itself over `X`.  The containment hypotheses its relation objects need are the same condition
`hV'` and `hV₂` carry, at the triple fibre product of charts.

**No `stacks` attribute is carried.**  What is assembled here is a step of the atlas
construction of Stacks 081V at a single algebra, not a numbered assertion of the source, and
Definition 0822 is not reached: the morphism `ν` and the factorization of `f` through it are
not constructed, so nothing here may carry `0822`.  The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` record the remaining steps.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent)

/-! ### The two legs are étale, and surjective when the charts are -/

section Legs

variable {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V)

/-- **The morphism of relative spectra induced by a morphism of étale charts is étale.**

Both inputs are unconditional: `AlgebraicGeometry.Space.etale_chartSchemeMap` is Stacks 03EC on
the small étale site, and
`AlgebraicGeometry.Space.chartRelativeSpecChartMap_of_isStableUnderBaseChange` transports a
base-change-stable property across the cartesian square of
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap`.

This is the étaleness of the source and target maps that
`Stacks.Groupoids.IsEtaleEquivalenceRelation` asks for. -/
theorem etale_chartRelativeSpecChartMap :
    Etale (chartRelativeSpecChartMap B S hS X A hA h) :=
  have : MorphismProperty.IsStableUnderBaseChange
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    Etale.etale_isStableUnderBaseChange
  chartRelativeSpecChartMap_of_isStableUnderBaseChange B S hS X A hA h
    (@Etale.{u} : MorphismProperty Scheme.{u}) (etale_chartSchemeMap h)

/-- **The morphism of relative spectra induced by a morphism of étale charts is surjective
whenever the morphism of chart schemes is.**  Surjectivity is stable under base change, so this
is again the cartesian square of
`AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap`. -/
theorem surjective_chartRelativeSpecChartMap (hsurj : Surjective (chartSchemeMap h)) :
    Surjective (chartRelativeSpecChartMap B S hS X A hA h) :=
  chartRelativeSpecChartMap_of_isStableUnderBaseChange B S hS X A hA h
    (@Surjective.{u} : MorphismProperty Scheme.{u}) hsurj

variable {B S hS X A hA} in
/-- The structure morphism to `S` of a chart of `X` is unchanged by a morphism of charts: the
triangle of `AlgebraicGeometry.Space.chartSchemeMap` over `S`. -/
theorem chartSchemeMap_comp_inclusion_map_hom :
    chartSchemeMap h ≫ B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V).hom =
      B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V').hom := by
  rw [show chartSchemeMap h =
      B.inclusion.map ((SmallEtale.toOver B S hS X.1).map h).left from rfl,
    ← B.inclusion.map_comp, Over.w]

end Legs

/-! ### The relative spectra over the charts as objects of the site -/

/-- **The relative spectrum of `A` over an étale chart of `X`, as an object of the big fppf site
over `S`.**  Its structure morphism to `S` is the structure morphism over the chart followed by
that of the chart, which is what `AlgebraicGeometry.BigFppfOver.siteObjectOver` forms.

Containment of the underlying scheme is a hypothesis: for the integral closure of `𝒪_X` in
`f_* 𝒪_Y` it is
`AlgebraicGeometry.Space.contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra`, at
the two hypotheses of Definition 0822. -/
def chartRelativeSpecSite (V : SmallEtale B S hS X.1)
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) : BigFppfOver B S hS :=
  BigFppfOver.siteObjectOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) hV
    (chartRelativeSpecToChart B S hS X A hA V)

/-- The underlying scheme of `AlgebraicGeometry.Space.chartRelativeSpecSite` is the relative
spectrum `AlgebraicGeometry.Space.chartRelativeSpec` over the chart. -/
@[simp]
theorem toScheme_obj_chartRelativeSpecSite (V : SmallEtale B S hS X.1)
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) :
    (BigFppfOver.toScheme B S hS).obj (chartRelativeSpecSite B S hS X A hA V hV) =
      chartRelativeSpec B S hS X A hA V :=
  rfl

section SiteMap

variable {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V))

/-- **The morphism of site objects induced by a morphism of étale charts.**  Underlying it is
`AlgebraicGeometry.Space.chartRelativeSpecChartMap`; the triangle over `S` is the commuting
square `AlgebraicGeometry.Space.chartRelativeSpecChartMap_comp_chartRelativeSpecToChart`
followed by `AlgebraicGeometry.Space.chartSchemeMap_comp_inclusion_map_hom`. -/
def chartRelativeSpecSiteMap :
    chartRelativeSpecSite B S hS X A hA V' hV' ⟶ chartRelativeSpecSite B S hS X A hA V hV :=
  Over.homMk (ObjectProperty.homMk (chartRelativeSpecChartMap B S hS X A hA h)) (by
    apply ObjectProperty.hom_ext
    change chartRelativeSpecChartMap B S hS X A hA h ≫
        chartRelativeSpecToChart B S hS X A hA V ≫
          B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V).hom =
      chartRelativeSpecToChart B S hS X A hA V' ≫
        B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V').hom
    rw [← Category.assoc, chartRelativeSpecChartMap_comp_chartRelativeSpecToChart,
      Category.assoc, chartSchemeMap_comp_inclusion_map_hom])

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.chartRelativeSpecSiteMap` is
`AlgebraicGeometry.Space.chartRelativeSpecChartMap`. -/
@[simp]
theorem toScheme_map_chartRelativeSpecSiteMap :
    (BigFppfOver.toScheme B S hS).map
        (chartRelativeSpecSiteMap B S hS X A hA h hV' hV) =
      chartRelativeSpecChartMap B S hS X A hA h :=
  rfl

/-- **The morphism of site objects is étale**, which is
`AlgebraicGeometry.Space.etale_chartRelativeSpecChartMap` read through
`AlgebraicGeometry.BigFppfOver.toScheme`. -/
theorem etale_toScheme_map_chartRelativeSpecSiteMap :
    Etale ((BigFppfOver.toScheme B S hS).map
      (chartRelativeSpecSiteMap B S hS X A hA h hV' hV)) :=
  etale_chartRelativeSpecChartMap B S hS X A hA h

/-- The morphism of site objects lies in the inverse image of the class of étale morphisms under
`AlgebraicGeometry.BigFppfOver.toScheme`. -/
theorem inverseImage_etale_chartRelativeSpecSiteMap :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (chartRelativeSpecSiteMap B S hS X A hA h hV' hV) :=
  etale_chartRelativeSpecChartMap B S hS X A hA h

end SiteMap

section SiteCocycle

variable {V'' V' V : SmallEtale B S hS X.1}
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA V''))
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V))

/-- **The morphisms of site objects are functorial in the chart: the composite.**  A morphism of
the big fppf category over `S` is determined by its underlying morphism of schemes, so this is
`AlgebraicGeometry.Space.chartRelativeSpecChartMap_comp`. -/
theorem chartRelativeSpecSiteMap_comp (h' : V'' ⟶ V') (h : V' ⟶ V) :
    chartRelativeSpecSiteMap B S hS X A hA (h' ≫ h) hV'' hV =
      chartRelativeSpecSiteMap B S hS X A hA h' hV'' hV' ≫
        chartRelativeSpecSiteMap B S hS X A hA h hV' hV := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact chartRelativeSpecChartMap_comp B S hS X A hA h' h

/-- **The morphisms of site objects are functorial in the chart: the identity.** -/
theorem chartRelativeSpecSiteMap_id :
    chartRelativeSpecSiteMap B S hS X A hA (𝟙 V) hV hV =
      𝟙 (chartRelativeSpecSite B S hS X A hA V hV) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact chartRelativeSpecChartMap_id B S hS X A hA V

end SiteCocycle

/-! ### The étale equivalence relation, modulo the cocycle -/

section Relation

variable {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))

/-- **The pair of morphisms of relative spectra attached to a pair of morphisms of étale charts
is an étale equivalence relation over `S` as soon as the represented pair of morphisms of
presheaves is an internal equivalence relation.**

The two étaleness conditions are
`AlgebraicGeometry.Space.etale_chartRelativeSpecChartMap` and need no hypothesis; the
equivalence-relation condition is the hypothesis `hrel`, and the implementation notes of this
file record precisely which two missing identities would discharge it.

Applied to the two projections of `R = U ×_X U` this is the étale equivalence relation whose
quotient, by `AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`, is the
algebraic space `\underline{Spec}_X(A)` of Stacks 081V — and, for `A` the integral closure of
`𝒪_X` in `f_* 𝒪_Y`, the normalization of `X` in `Y` of Definition 0822. -/
theorem isEtaleEquivalenceRelation_chartRelativeSpecSiteMap
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hrel : IsEquivalenceRelation
      (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))
      (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂))) :
    IsEtaleEquivalenceRelation (relation B S hS
      (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
      (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) := by
  refine isEtaleEquivalenceRelation_of_yoneda B S hS _ _ (Iso.refl _) ?_
    (inverseImage_etale_chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)
    (inverseImage_etale_chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
  simpa only [Iso.refl_hom, Category.id_comp] using hrel

end Relation

end AlgebraicGeometry.Space

end

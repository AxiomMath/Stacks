module

public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSiteObject

/-!
# The chart diagram of a square-zero extension as a candidate étale equivalence relation

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X` over `Y`, in the sense of `AlgebraicGeometry.Space.SquareZeroExtension`.  The ambient
space of [Stacks Project, Tag 05ZT] is, in the shape of the source's own proof, the quotient of
an étale equivalence relation: `U₀` a covering chart of the small étale site of `X`,
`R₀ = U₀ ×_X U₀` the chart of its kernel pair, and the ambient space the quotient of
`Spec(𝒜(R₀)) ⇉ Spec(𝒜(U₀))`.  That quotient is an algebraic space over `S` by
[Stacks Project, Tag 02WW], which is unconditional in this development
(`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`) as soon as the pair is an
étale equivalence relation.

This file assembles everything in that hypothesis **except its equivalence-relation half**, which
is not proved anywhere and enters the two statements below as the argument `hrel`.

## Which half is discharged, and which is not

`Stacks.Groupoids.IsEtaleEquivalenceRelation` has three fields: étaleness of the source map,
étaleness of the target map, and `CategoryTheory.IsEquivalenceRelation` of the pair.

The two étaleness fields are **discharged here with no hypothesis beyond the affineness of the
two charts**, by
`AlgebraicGeometry.Space.SquareZeroExtension.etale_toScheme_map_chartSiteDiagram_map`, which is
`…etale_chartSpec_map_of_isAffine` — the étaleness of the arrows of the chart diagram — read on
the morphisms of the big fppf site that
`AlgebraicGeometry.Space.SquareZeroExtension.chartSiteDiagram` produces.  The passage from the
represented pair to the pair of schemes over `S` is
`AlgebraicGeometry.Space.isEtaleEquivalenceRelation_of_yoneda`.

The equivalence-relation field is **not** discharged, and the gap is not an oversight.  It splits
into two unrelated demands, of which exactly one is met.

`CategoryTheory.TransitiveRelation` asks for a limiting pullback cone of the two projections
together with a composition arrow out of it, hence for `𝒜` to turn a fibre product of charts into
a tensor product of sections, `𝒜(R₀ ×_{U₀} R₀) = 𝒜(R₀) ⊗_{𝒜(U₀)} 𝒜(R₀)`: a square with `𝒜` at
all four corners, indexed by a cospan of the small étale site.  **That square is available** for
affine charts, as
`AlgebraicGeometry.Space.SquareZeroExtension.isPushout_A_map_of_isPullback_of_isAffine`, whose
`Spec` is the cone itself,
`AlgebraicGeometry.Space.SquareZeroExtension.isPullback_chartSpec_map_of_isPullback_of_isAffine`.

What is **not proved here** is `CategoryTheory.JointlyMono₂`, which all three of
`CategoryTheory.ReflexiveRelation`, `CategoryTheory.SymmetricRelation` and
`CategoryTheory.TransitiveRelation` extend: it asks that `Spec(𝒜(R₀))` be a subobject of
`Spec(𝒜(U₀)) ×_S Spec(𝒜(U₀))`, a product over the *base*.  A cospan of the small étale site
never has the base as its vertex, so no square of the chart diagram bears on it, and in
particular the two transfer routes of
`StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer` are both unavailable:
`CategoryTheory.jointlyMono₂_map` wants `PreservesLimitsOfShape (Discrete WalkingPair)` of the
diagram, which would say it carries a fibre product over a chart to a product over the base,
and `CategoryTheory.isEquivalenceRelation_of_map_of_iso` *reflects* along a fully faithful
functor, which is the opposite direction.

**That does not close the question; the route below is not carried out here.**  Joint
monicity is not owed by a square of the chart diagram at all.  Between affine charts
`j' = ⟨Spec(𝒜(p)), Spec(𝒜(q))⟩ : Spec(𝒜(R₀)) ⟶ Spec(𝒜(U₀)) ×_S Spec(𝒜(U₀))` is a morphism of
*affine schemes*, and for a morphism of schemes
`AlgebraicGeometry.universallyInjective_unramified_tfae` — [Stacks Project, Tag 05VH] — derives
`Mono` from unramifiedness together with universal injectivity.  Its two inputs are each within
reach of the library: `j'` is unramified by left cancellation against the étaleness of its
first projection, which is `…etale_chartSpec_map_of_isAffine`; and `j'` is universally injective
because `U₀ ×_S U₀ ⟶ Spec(𝒜(U₀)) ×_S Spec(𝒜(U₀))` is itself a thickening — the ideal generated
by the two copies of the square-zero ideal of `𝒜` is nilpotent — so `j'` has the points and the
residue fields of `j : R₀ ⟶ U₀ ×_S U₀`, which is universally injective because it is a
monomorphism, by `AlgebraicGeometry.Space.universallyInjective_of_mono`.  Note that the
corresponding step at the level of algebraic spaces is *not* available —
`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism` records that the converse half of
[Stacks Project, Tag 05W6] is missing — which is why the argument has to be run on the affine
charts, where Tag 05VH applies.  Neither input is proved here.

Granted joint monicity, `CategoryTheory.ReflexiveRelation.map`,
`CategoryTheory.SymmetricRelation.map` and `CategoryTheory.TransitiveRelation.map` would carry
the equivalence relation of the kernel pair `R₀ = U₀ ×_X U₀` along the diagram, the last of them
consuming the cone above.

The lemma
`AlgebraicGeometry.Space.SquareZeroExtension.isPullback_reductionChartSpec_app_of_isAffine` is a
third square again — `𝒪_X` at two of its four corners, indexed by a single arrow `U ⟶ V`, saying
that the thickening of `U` is the base change of the thickening of `V`.  The chart-pair square is
not the groupoid square and the groupoid square is not a corollary of it.

The other route to the same field is [Stacks Project, Tag 0262] part (1),
`AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback`, which needs the pair to be the
kernel pair of a chart of some presheaf; taking that presheaf to be the ambient space is
circular, since the ambient space is what the quotient is being formed to produce.  Only the
reflexivity and symmetry *equations* are free: the diagonal `U₀ ⟶ R₀` and the flip of `R₀` are
arrows of the small étale site, so the functoriality of `chartSiteDiagram` carries them to the
charts of the extension.  They are not recorded separately here because they are instances of
`CategoryTheory.Functor.map_comp` and because without joint monicity they cannot be packaged into
the field that consumes them.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.isEtaleEquivalenceRelation_chartSiteDiagram_map`:
  a pair of arrows of the small étale site between affine charts is an **étale** equivalence
  relation on the charts of the extension as soon as it is an equivalence relation at all.
* `AlgebraicGeometry.Space.SquareZeroExtension.isAlgebraicSpace_quotient_chartSiteDiagram_map`:
  consequently its quotient sheaf is an algebraic space over `S`, by
  [Stacks Project, Tag 02WW].

## Implementation notes

**What the hypotheses are, and which of them are artefacts.**  Beyond `hrel`, the two statements
below carry: terminality of the base scheme `S`, which is what gives the charts of the extension
their structure morphisms — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSiteObject` for why
nothing in the datum supplies them over a general base; the containment `hcon` of every chart,
which is this development's size cutoff and is **not a hypothesis of
[Stacks Project, Tag 05ZT]**, whose algebraic spaces are sheaves on a site containing every
scheme — over an affine chart it is discharged from a bound on the sections of `ℐ` by
`…contains_chartSpec_obj_of_mk_ideal_lt_cutoff`, so a route through `R₀ ⇉ U₀` needs that bound at
the relation chart `R₀` as much as at the covering chart `U₀`; and the affineness of `R₀` and of
`U₀`.

**Affineness of the relation chart is a real restriction.**  Every proved fact about the chart
diagram — the étaleness of its arrows, the surjectivity of the reduction on sections, the kernel
base change, the cartesian square — holds only over an affine chart, because the sections of `𝒜`
over a non-affine chart do not determine it.  For `R₀ = U₀ ×_X U₀` affineness is not automatic:
it is étale over `U₀`, and it is affine as soon as the diagonal of `X` is, which is a condition on
`X` and not on the extension.  So the statements below are restricted to that case and do not
cover a general algebraic space.

**No `@[stacks]` attribute.**  Tag 05ZT concludes that the datum is realized by a first-order
thickening `X ⊂ X'` over `Y` together with an isomorphism `𝒪_{X'} ≅ 𝒜`.  Neither statement here
produces a thickening or identifies a structure sheaf, and both rest on `hrel`, on the cutoff
containment and on a terminal base; a conditional statement at hypotheses that are not the
source's is not the tag, and nothing here claims any part of it.  Tag 02WW is not reasserted
either: it is applied, and its tag sits on
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW), the quotient of an étale
  equivalence relation.
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS), étale equivalence
  relations.
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262), the kernel pair of an
  atlas, the other route to the equivalence-relation condition.
* [Stacks Project, Tag 05VH](https://stacks.math.columbia.edu/tag/05VH), monicity of a morphism
  of schemes from unramifiedness and universal injectivity, the open route to joint monicity.
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6), its counterpart for
  algebraic spaces, whose relevant half is missing, which is why Tag 05VH is applied on charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **A pair of arrows of the small étale site between affine charts is an étale equivalence
relation on the charts of the extension as soon as it is an equivalence relation.**

The two étaleness fields of `Stacks.Groupoids.IsEtaleEquivalenceRelation` are
`AlgebraicGeometry.Space.SquareZeroExtension.etale_toScheme_map_chartSiteDiagram_map`, which asks
nothing beyond the affineness of the two charts.  The remaining field is the argument `hrel`,
which is **not proved anywhere in this development**: it is joint monicity of the pair together
with the reflexivity, symmetry and transitivity witnesses.  The transitivity cone is available —
it is
`AlgebraicGeometry.Space.SquareZeroExtension.isPullback_chartSpec_map_of_isPullback_of_isAffine` —
and the joint monicity is not.  The module documentation of this file sets out why no square of
the chart diagram supplies it, and why that is *not* an obstruction: between affine charts the
pair lands in a product of affine schemes, where
`AlgebraicGeometry.universallyInjective_unramified_tfae` — [Stacks Project, Tag 05VH] — gives
monicity from unramifiedness and universal injectivity.  That route is open and unattempted; it
is the reason `hrel` is an argument here rather than a recorded impossibility. -/
theorem isEtaleEquivalenceRelation_chartSiteDiagram_map (hterm : IsTerminal S)
    (hcon : ∀ U : SmallEtale B S hS X.1, B.Contains ((chartSpec B S hS E).obj U))
    {R₀ U₀ : SmallEtale B S hS X.1} (p q : R₀ ⟶ U₀)
    (hR₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj R₀)))
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U₀)))
    (hrel : IsEquivalenceRelation
      (yoneda.map ((chartSiteDiagram B S hS E hterm hcon).map q))
      (yoneda.map ((chartSiteDiagram B S hS E hterm hcon).map p))) :
    IsEtaleEquivalenceRelation (relation B S hS
      ((chartSiteDiagram B S hS E hterm hcon).map p)
      ((chartSiteDiagram B S hS E hterm hcon).map q)) :=
  isEtaleEquivalenceRelation_of_yoneda B S hS _ _ (Iso.refl _) (by simpa using hrel)
    (etale_toScheme_map_chartSiteDiagram_map B S hS E hterm hcon q hR₀ hU₀)
    (etale_toScheme_map_chartSiteDiagram_map B S hS E hterm hcon p hR₀ hU₀)

/-- **The quotient of the charts of the extension by such a pair is an algebraic space over
`S`.**

This is [Stacks Project, Tag 02WW] in the form
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`, applied to
`…isEtaleEquivalenceRelation_chartSiteDiagram_map`.  It is **not** the ambient space of
[Stacks Project, Tag 05ZT]: `hrel` is undischarged, the containment `hcon` is this development's
size cutoff rather than a hypothesis of the source, the base scheme is required to be terminal,
and nothing here identifies the structure sheaf of the quotient with `𝒜` or exhibits `X` inside
it as a first-order thickening. -/
theorem isAlgebraicSpace_quotient_chartSiteDiagram_map
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (hterm : IsTerminal S)
    (hcon : ∀ U : SmallEtale B S hS X.1, B.Contains ((chartSpec B S hS E).obj U))
    {R₀ U₀ : SmallEtale B S hS X.1} (p q : R₀ ⟶ U₀)
    (hR₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj R₀)))
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U₀)))
    (hrel : IsEquivalenceRelation
      (yoneda.map ((chartSiteDiagram B S hS E hterm hcon).map q))
      (yoneda.map ((chartSiteDiagram B S hS E hterm hcon).map p))) :
    IsAlgebraicSpace B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (relation B S hS ((chartSiteDiagram B S hS E hterm hcon).map p)
          ((chartSiteDiagram B S hS E hterm hcon).map q))).obj :=
  let := isEtaleEquivalenceRelation_chartSiteDiagram_map B S hS E hterm hcon p q hR₀ hU₀ hrel
  isAlgebraicSpace_quotient_unconditional B S hS _ _

end SquareZeroExtension

end AlgebraicGeometry.Space

end

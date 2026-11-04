module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit

/-!
# Étaleness tested on every square of étale charts (Stacks 03XT, condition (7))

Étaleness of a morphism `f : X ⟶ Y` of algebraic spaces over `S`, in the sense of Tag 03FR,
is equivalent to the universal chart test: for *every* commuting square of étale scheme
charts of `f`, the scheme morphism between the charts is étale. That universal test is the
predicate `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, which is Tag 03MJ,
condition (1), instantiated at `AlgebraicGeometry.Etale`.

Only one implication has content. The chart test is by construction about an arbitrary
square, whereas Tag 03FS, condition (4), only provides *some* square with a surjective
source chart; the step from the latter to the former is descent along a surjective étale
chart.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`: **Stacks 03XT**,
  condition (7).

## Implementation notes

Both directions are assembled from results in the library. For the forward direction, étaleness of
`f` makes `p ≫ f` an étale chart of `Y` alongside `q`, and Tag 03EC
(`AlgebraicGeometry.Space.etale_of_etale_charts`) recognises the morphism between two étale
charts of one algebraic space as étale; no surjectivity is needed, so this direction holds
for every square. For the converse, an atlas of `Y` is lifted to a commuting square with
surjective étale source chart by Tag 02X1
(`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`), the hypothesis is
applied to that one square, and Tag 03FS, condition (4)
(`AlgebraicGeometry.Space.isEtale_iff_exists_etale_chart_square`) concludes.

The statement is phrased with `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` rather than
with the quantifier written out, so that the Tag 03MJ lemmas — in particular
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart` — apply to it directly.
Spelling the quantifier out gives the same proposition with the commutativity hypothesis and
the two étaleness hypotheses of the square in the other order.

## References

* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 03XT, condition (7).** A morphism of algebraic spaces over `S` is étale if and
only if, for every commuting square of étale scheme charts of it, the morphism of schemes
between the charts is étale. -/
theorem isEtale_iff_holdsOnEveryEtaleChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsEtale B S hS f ↔
      HoldsOnEveryEtaleChart B S hS
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) f := by
  refine ⟨fun hf U V p q α hp hq hcomm =>
    etale_of_etale_charts B S hS (p ≫ f) q (hf U p hp) hq α hcomm, fun hcharts => ?_⟩
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hqSurj hqEtale
  exact (isEtale_iff_exists_etale_chart_square B S hS hX hY f).2
    ⟨U, V, p, q, α, hcomm, hpSurj, hpEtale, hqEtale,
      hcharts U V p q α hpEtale hqEtale hcomm.symm⟩

end AlgebraicGeometry.Space

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Unramified morphisms of algebraic spaces and formal unramifiedness on charts

A morphism of algebraic spaces over `S` is unramified exactly when it is locally of finite
type and the scheme morphism in every commuting square of étale scheme charts is formally
unramified.

## Main results

* `AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts`
  splits unramifiedness of a morphism of algebraic spaces into local finite type and formal
  unramifiedness of its étale charts.

## Implementation notes

Both `AlgebraicGeometry.Space.IsUnramified` of Tag 03ZH and
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` of Tag 03XF are every-chart conditions of
Tag 03MJ, so the statement is the scheme-level equivalence
`AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified` of Tag 02HE
on every chart. Formal unramifiedness of the chart morphism is Mathlib's
`AlgebraicGeometry.FormallyUnramified`, written `_root_.AlgebraicGeometry.FormallyUnramified`
because inside the namespace `AlgebraicGeometry.Space` the predicate on morphisms of schemes is
meant, not the one on morphisms of algebraic spaces. No algebraicity hypothesis on the source or
target is imposed.

This is the chart-level half of the equivalence of conditions (1) and (3) of Tag 04GA. The
comparison of formal unramifiedness on charts with `AlgebraicGeometry.Space.FormallyUnramified`
of Tag 049S is Tag 04G8 and is not part of this file, so nothing here carries a
`@[stacks 04GA]` attribute.

## References

* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
* [Stacks Project, Tag 04GA](https://stacks.math.columbia.edu/tag/04GA)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of algebraic spaces is unramified exactly when it is locally of finite type
and formally unramified on every étale chart.**

This is the chart-level form of the equivalence of conditions (1) and (3) of
[Stacks Project, Tag 04GA]; passing from the chart condition to
`AlgebraicGeometry.Space.FormallyUnramified` is [Stacks Project, Tag 04G8]. -/
theorem isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsUnramified B S hS f ↔
      (IsLocallyOfFiniteType B S hS f ∧
        HoldsOnEveryEtaleChart B S hS
          (@_root_.AlgebraicGeometry.FormallyUnramified.{u} :
            MorphismProperty Scheme.{u}) f) := by
  simp only [IsUnramified, IsLocallyOfFiniteType, HoldsOnEveryEtaleChart,
    unramified_iff_locallyOfFiniteType_and_formallyUnramified, imp_and, forall_and]

end AlgebraicGeometry.Space

end

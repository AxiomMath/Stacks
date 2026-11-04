module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Restricting a support statement to an étale scheme chart

Let `X` be an algebraic space over a scheme `S` and let `W` be an étale scheme chart of `X`.  The
support (Stacks 04KA) of the restriction of an `𝒪_X`-module `M` to `W` is the preimage of the
support of `M`, by `AlgebraicGeometry.Space.supportOfSheaf_chartToSpace`.  This file records the
direction of that equality which needs no surjectivity of the chart: a support statement on `X`
restricts to every étale scheme chart.

## Main results

* `AlgebraicGeometry.Space.disjoint_chart_supportOfSheaf_of_disjoint`: if the support of `M` is
  disjoint from a set `U` of points of `X`, then the support of the restriction of `M` to any
  étale scheme chart `W` is disjoint from the preimage of `U`.  It is the converse of
  `AlgebraicGeometry.Space.disjoint_supportOfSheaf_of_chart_surjective`, which descends such a
  statement along a chart surjective on points.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Descent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The descent of a support statement along an étale scheme chart is reversible**, and the
converse direction needs no surjectivity: if the support of an `𝒪_X`-module `M` is disjoint from
a set `U` of points of `X`, then the support of its restriction to any étale scheme chart `W` is
disjoint from the preimage of `U`.

Both directions are the single equality
`AlgebraicGeometry.Space.supportOfSheaf_chartToSpace`, which identifies the support of the
restriction with the preimage of the support; this direction is then `Disjoint.preimage`. -/
theorem disjoint_chart_supportOfSheaf_of_disjoint (W : SmallEtale B S hS X.1)
    (M : Modules.{u, u} B S hS X.1 X.2) (U : Set (points B S hS X.1))
    (hdisj : Disjoint (supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj M)) U) :
    Disjoint
      (supportOfSheaf B S hS (chartSpace B S hS X W).1
        ((SheafOfModules.toSheaf
            (structureRingSheaf B S hS (chartSpace B S hS X W))).obj
          ((etaleModulePullback B S hS
            (chartToSpace B S hS X W) (isEtale_chartToSpace B S hS X W)).obj M)))
      (pointsMap B S hS (chartSpace B S hS X W).1
        (chartToSpace B S hS X W).hom ⁻¹' U) := by
  rw [Set.disjoint_left] at hdisj ⊢
  intro x hx hxU
  exact hdisj ((supportOfSheaf_chartToSpace B S hS X W M).subset hx) hxU

end Descent

end AlgebraicGeometry.Space

end

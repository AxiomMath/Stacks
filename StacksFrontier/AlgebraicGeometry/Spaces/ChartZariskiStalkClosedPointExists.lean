module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion

/-!
# A small étale neighbourhood carrying a point with no proper open neighbourhood

Let `u` be a point of an étale scheme chart of an algebraic space whose only open neighbourhood
is `⊤`. By Stacks 05VN every point of an étale scheme chart is the point under a lift of some
geometric point (`AlgebraicGeometry.Space.exists_geometricPoint_chartLift`), and that lift is a
small étale neighbourhood of the geometric point whose chart point is `u`, again with `⊤` as its
only open neighbourhood.

The hypothesis holds at the closed point of the spectrum of a local ring
(`AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing`), and more generally at a point to which
every point specializes (`TopCat.Presheaf.forall_eq_top_of_specializes`).

## Main results

* `AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_forall_eq_top`: **an étale scheme
  chart carrying a point with no proper open neighbourhood is the chart of a small étale
  neighbourhood of some geometric point whose chart point is that point.**

## References

* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An étale scheme chart carrying a point with no proper open neighbourhood is the chart of
a small étale neighbourhood of a geometric point whose chart point is that point.** -/
theorem exists_smallEtaleNeighborhood_forall_eq_top (hX : IsAlgebraicSpace B S hS X)
    (U : SmallEtale B S hS X) (u : chartScheme U)
    (hu : ∀ O : (chartScheme U).Opens, u ∈ O → O = ⊤) :
    ∃ (y : GeometricPoint B S hS X) (W : SmallEtaleNeighborhood y),
      ∀ O : (chartScheme W.chart).Opens, chartPoint B S hS X W ∈ O → O = ⊤ := by
  obtain ⟨ybar, q, hq, hpt⟩ := exists_geometricPoint_chartLift B S hS hX U u
  exact ⟨ybar, ⟨U, q, hq⟩, fun O hO => hu O (hpt ▸ hO)⟩

end AlgebraicGeometry.Space

end

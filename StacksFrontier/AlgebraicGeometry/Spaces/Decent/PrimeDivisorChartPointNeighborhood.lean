module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorOfCodimensionOnePoint

/-!
# A point of an étale chart, as a chart point of a small étale neighbourhood and as the generic
point of a prime divisor

Let `X` be an algebraic space over a scheme `S` and let `W` be an étale scheme chart of `X`. The
two statements below read a point `u` of the scheme `chartScheme W` in the two ways the proof of
Stacks 0EPX reads it.

* Every such `u` is the chart point of a small étale neighbourhood of some geometric point of
  `X` built on `W` itself. This is
  `AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_chart_eq` (Stacks 05VN on the chart)
  with its hypothesis discharged — a point of `|X|` is the image of a geometric point
  (`AlgebraicGeometry.Space.exists_geometricRepresentative`), so no point of `|X|` need be given
  in advance — and with the neighbourhood exhibited as the triple on `W`, so that no transport
  along an equality of charts appears in the statement.
* When `u` has coheight one in `chartScheme W` the point of `|X|` it lies over is the generic
  point of a prime divisor of `X`. This is
  `AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one`
  with its `AlgebraicGeometry.Space.ChartPoint` hypothesis discharged by
  `AlgebraicGeometry.Space.chartPoint_chartSchemeToPoints`, so that the chart is a
  `AlgebraicGeometry.Space.SmallEtale` rather than a bare triple.

Both are packaging: neither proves anything the two cited results do not already say. They exist
because the consumer — the étale-local argument of Stacks 0EPX, which runs over the
codimension-one points of one trivializing chart and attaches to each a prime divisor of `X` and
a geometric point of `X` above it — holds the chart as an object of the small étale site and the
point as a point of its scheme.

## Main results

* `AlgebraicGeometry.Space.exists_geometricPoint_chartPoint_eq`
* `AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_chartSchemeToPoints`

## References

* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

include hX in
/-- **Every point of an étale scheme chart is the chart point of a small étale neighbourhood
built on that same chart.** The neighbourhood is exhibited as the triple on the given chart, so
its `chart` field is that chart by construction and the statement needs no transport along an
equality of charts — unlike
`AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_chart_eq`, of which this is the
transport-free form with its hypothesis discharged.

The geometric point is not given in advance: a point of `|X|` is the image of one
(`AlgebraicGeometry.Space.exists_geometricRepresentative`), the point `u` lies over the point of
`|X|` it determines (`AlgebraicGeometry.Space.chartPoint_chartSchemeToPoints`), and Stacks 05VN
(`AlgebraicGeometry.Space.exists_chartLift_of_chartPoint`) then lifts `u` itself. That first step
is also recorded in the conclusion: the geometric point produced lies over the point of `|X|`
determined by `u`, which is what identifies it with the generic point of the prime divisor
`AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_chartSchemeToPoints` attaches to a
coheight-one `u`. -/
theorem exists_geometricPoint_chartPoint_eq (W : SmallEtale B S hS X) (u : chartScheme W) :
    ∃ (xbar : GeometricPoint B S hS X) (p : xbar.val.siteObject ⟶ W.obj.left)
      (hp : W.obj.hom.app (op xbar.val.siteObject) p = xbar.val.value),
      chartPoint B S hS X (⟨W, p, hp⟩ : SmallEtaleNeighborhood xbar) = u ∧
        xbar.image = chartSchemeToPoints B S hS X W u := by
  obtain ⟨xbar, hxbar⟩ :=
    exists_geometricRepresentative B S hS X (chartSchemeToPoints B S hS X W u)
  have hcp : ChartPoint B S hS W.obj.left W.obj.hom u xbar.image := by
    rw [hxbar]
    exact chartPoint_chartSchemeToPoints B S hS ⟨X, hX⟩ W u
  obtain ⟨q, hq, hpt⟩ := exists_chartLift_of_chartPoint B S hS hX xbar W u hcp
  exact ⟨xbar, q, hq, hpt, hxbar⟩

variable (hdec : IsDecentSpace B S hS X)

include hX hdec in
/-- **A coheight-one point of an étale scheme chart lies over the generic point of a prime
divisor.** This is
`AlgebraicGeometry.Space.exists_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one`
for a chart presented as an object of the small étale site, the
`AlgebraicGeometry.Space.ChartPoint` hypothesis being
`AlgebraicGeometry.Space.chartPoint_chartSchemeToPoints`. -/
theorem exists_primeDivisor_genericPoint_eq_chartSchemeToPoints (W : SmallEtale B S hS X)
    (u : chartScheme W) (hcoh : Order.coheight u = 1) :
    ∃ Z : PrimeDivisor B S hS X,
      Z.genericPoint B S hS X = chartSchemeToPoints B S hS X W u :=
  exists_primeDivisor_genericPoint_eq_of_coheight_chartPoint_eq_one B S hS hX hdec
    W.obj.left W.obj.hom W.property u (chartSchemeToPoints B S hS X W u)
    (chartPoint_chartSchemeToPoints B S hS ⟨X, hX⟩ W u) hcoh

end AlgebraicGeometry.Space

end

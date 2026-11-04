module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Dimension.OpenGeneralizingMap

/-!
# The dimension of a decent algebraic space is the dimension of its point space

The dimension of an algebraic space `X` over a scheme `S` is defined through étale scheme
charts: `AlgebraicGeometry.Space.dimensionAtPoint` at a point is the local Krull dimension of
any étale chart above it, and `AlgebraicGeometry.Space.dimension` is the supremum of those.
When `X` is decent these agree with the purely topological dimensions of the point space
`|X|`, locally and globally. This is **Stacks 0A4J**.

## Main results

* `AlgebraicGeometry.Space.generalizingMap_pointsMap_of_hasFiniteChartFibers`: Stacks 03K2 as
  a lifting property of the map on points of an étale chart.
* `AlgebraicGeometry.Space.topologicalKrullDimAt_points_eq_dimensionAtPoint_of_isDecentSpace`:
  part (1), `dim_x |X| = dim_x X`, which is also the fourth clause of Stacks 0AC9.
* `AlgebraicGeometry.Space.topologicalKrullDim_points_eq_dimension_of_isDecentSpace`:
  part (2), `dim |X| = dim X`.

## Implementation notes

Fix an étale chart `a : h_U ⟶ X` by a scheme with a point above `x`. The induced map on
points `|a| : |h_U| → |X|` has four properties that together force the two local dimensions to
agree: it is continuous and open, every generization of a point of its image lifts through it
(Stacks 03K2, using that decency gives finite fibres above every point by Stacks 03JX `(α)`),
and it collapses no specialization of the chart (Stacks 03K5). Decency also makes `|X|` sober,
Stacks 03K6, and the chart's point space is homeomorphic to the scheme underlying `U`, hence
sober as well. Those four properties are exactly the hypotheses of
`Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_generalizingMap`, which does the work.

The same two tags, 03K5 and 03K2, are consumed in the same way by
`AlgebraicGeometry.Space.coheight_pointsMap_eq`, which concerns the coheight of a point in the
specialization order rather than the local dimension. Neither statement follows from the
other; the lifting property shared by the two proofs is the lemma below.

Part (2) follows from part (1) because both the topological Krull dimension and the dimension
of an algebraic space are the supremum over points of their local values.

## References

* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 0A4J](https://stacks.math.columbia.edu/tag/0A4J)
* [Stacks Project, Tag 0AC9](https://stacks.math.columbia.edu/tag/0AC9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03K2**, packaged as a lifting property of the map on points. If every point of an
algebraic space over `S` has finite fibres in its étale charts by affine schemes, then
generizations lift along the map on points of any étale chart by a scheme. -/
theorem generalizingMap_pointsMap_of_hasFiniteChartFibers (hX : IsAlgebraicSpace B S hS X)
    (hfib : HasFiniteChartFibersAtEveryPoint B S hS X) (U : BigFppfOver B S hS)
    (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ) :
    GeneralizingMap (pointsMap B S hS (yoneda.obj U) φ) := by
  intro u y huy
  obtain ⟨u', hu'u, hu'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX huy
    (fun V hV ψ hψ ↦ hfib y V hV ψ hψ) U φ hφ u rfl
  exact ⟨u', hu'u, hu'⟩

/-- **Stacks 0A4J, part (1)**, and the fourth clause of **Stacks 0AC9**. At every point of a
decent algebraic space over `S` the local Krull dimension of the point space agrees with the
dimension of the space at that point, as defined by étale scheme charts.

This equality is what makes conditions (1) and (4) of Stacks 0AC9 — vanishing of the two
dimensions at the point — equivalent for a decent space. -/
@[stacks 0A4J "part (1)", stacks 0AC9 "conditions (1) and (4) for decent spaces"]
theorem topologicalKrullDimAt_points_eq_dimensionAtPoint_of_isDecentSpace
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X) (x : points B S hS X) :
    topologicalKrullDimAt (points B S hS X) x = dimensionAtPoint B S hS X hX x := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  set f := pointsMap B S hS (yoneda.obj U) a with hfdef
  -- Both point spaces are sober: the target by Stacks 03K6, the chart because it is the
  -- point space of a scheme.
  have : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hdec
  have : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hdec
  have : QuasiSober (points B S hS (yoneda.obj U)) :=
    (schemePointsHomeomorph B S hS U).isOpenEmbedding.quasiSober
  have hfcont : Continuous f := continuous_pointsMap B S hS a
  have hfopen : IsOpenMap f := isOpenMap_pointsMap_of_presheafEtale B S hS a ha
  -- Stacks 03K5: the chart collapses no specialization.
  have hfnc : ∀ ⦃q r : points B S hS (yoneda.obj U)⦄, q ⤳ r → f q = f r → q = r := by
    intro q r hqr heq
    exact (eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX
      (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec) U a ha r q heq.symm
      hqr).symm
  -- Stacks 03K2: every generization of a point of the image lifts to the chart.
  have hflift : GeneralizingMap f := generalizingMap_pointsMap_of_hasFiniteChartFibers B S hS hX
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec) U a ha
  have hchart := dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hp
  calc topologicalKrullDimAt (points B S hS X) x
      = topologicalKrullDimAt (points B S hS X) (f (p.class B S hS (yoneda.obj U))) := by
        rw [hp]
    _ = topologicalKrullDimAt (points B S hS (yoneda.obj U))
          (p.class B S hS (yoneda.obj U)) :=
        (Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_generalizingMap f hfcont hfopen
          hflift hfnc (p.class B S hS (yoneda.obj U))).symm
    _ = topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) (schemePoint B S hS U p) :=
        topologicalKrullDimAt_eq_of_homeomorph (schemePointsHomeomorph B S hS U) _
    _ = dimensionAtPoint B S hS X hX x := hchart.symm

/-- **Stacks 0A4J, part (2).** The Krull dimension of the point space of a decent algebraic
space over `S` agrees with the dimension of the space, as defined by étale scheme charts. -/
@[stacks 0A4J "part (2)"]
theorem topologicalKrullDim_points_eq_dimension_of_isDecentSpace
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X) :
    topologicalKrullDim (points B S hS X) = dimension B S hS X hX := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim, dimension]
  simp_rw [← topologicalKrullDimAt_eq_localKrullDim]
  exact iSup_congr fun x ↦
    topologicalKrullDimAt_points_eq_dimensionAtPoint_of_isDecentSpace B S hS hX hdec x

end AlgebraicGeometry.Space

end

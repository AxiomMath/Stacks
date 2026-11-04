module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties

/-!
# Quasi-compactness of an algebraic space and the topology on its points

An algebraic space over `S` is quasi-compact, in the sense of Tag 03E3 that it admits a
surjective étale chart from a quasi-compact scheme, exactly when its space of points is
quasi-compact for the topology of Tag 03BX.

The forward implication is immediate: the point space of a represented presheaf is
homeomorphic to the representing scheme, and the point map of a surjective chart is a
continuous surjection. For the converse, an arbitrary atlas `U ⟶ F` is restricted to the
members of an affine open cover of `U`; each restriction is still an étale chart and is open
on points, so the resulting open sets cover `|F|`, finitely many suffice, and the coproduct
of the corresponding affines is a quasi-compact scheme which is still surjective on points.

## Main results

* `AlgebraicGeometry.Space.exists_pointsMap_yonedaMap_eq_of_mem_range`: a point of a
  represented presheaf lifts along a morphism of the site whenever its underlying scheme
  point is in the range of the underlying morphism of schemes.

**Stacks 03E4** itself, `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_compactSpace_points`,
and `AlgebraicGeometry.Space.compactSpace_points_yoneda` are stated in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactPointSpace.lean`, which this module imports:
that module owns the two one-directional halves of the equivalence, so the equivalence is one
line there.

## Implementation notes

Topological quasi-compactness is Mathlib's `CompactSpace`, which imposes no separation
condition. `AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an
instance and is made a local instance here, as in
`StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented`.

## References

* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


/-- A point of a represented presheaf lifts along a morphism `j : V ⟶ U` of the big fppf site
over `S` as soon as its underlying point of the scheme of `U` lies in the range of the
underlying morphism of schemes.

Both point sets are the point sets of the representing schemes, so this is surjectivity of
the scheme map onto its range transported along that identification. -/
theorem exists_pointsMap_yonedaMap_eq_of_mem_range {U V : BigFppfOver B S hS} (j : V ⟶ U)
    (x : points B S hS (yoneda.obj U))
    (hx : pointsToScheme B S hS U x ∈
      Set.range ((BigFppfOver.toScheme B S hS).map j)) :
    ∃ y : points B S hS (yoneda.obj V),
      pointsMap B S hS (yoneda.obj V) (yoneda.map j) y = x := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨(schemePointRepresentative B S hS V z).class B S hS (yoneda.obj V),
    injective_pointsToScheme B S hS U ?_⟩
  rw [pointsToScheme_pointsMap, show pointsToScheme B S hS V
    ((schemePointRepresentative B S hS V z).class B S hS (yoneda.obj V)) = z from
    schemePointRepresentative_point B S hS V z]
  exact hz


end AlgebraicGeometry.Space

end

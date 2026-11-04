module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Quasi-compactness of an algebraic space is quasi-compactness of its point space

This module declares nothing of its own. It is an import surface for the following results,
which are stated elsewhere:

* **Stacks 03E4**, that an algebraic space over `S` is quasi-compact exactly when its space of
  points is a compact space, is
  `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_compactSpace_points` in
  `StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactTopology.lean`. That module is deliberately
  NOT re-exported here: it declares `AlgebraicGeometry.Space.compactSpace_points_yoneda` with an
  instance binder where `StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactPointSpace.lean`
  declares the same name with an explicit hypothesis, so making both visible at once changes
  which one a bare application resolves to. The modules that need the equivalence import it
  directly.
* **Stacks 040W**, part (1), that the surjective image of a quasi-compact algebraic space is
  quasi-compact, is `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isSurjective`, and part (2),
  that quasi-compactness of a morphism descends across a surjection in a commuting triangle, is
  `AlgebraicGeometry.Space.isQuasiCompact_of_comp_surjective`; both are in
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/QuasiCompact.lean`.

## References

* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
-/

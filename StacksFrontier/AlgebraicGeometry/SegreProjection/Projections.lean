module

public import StacksFrontier.AlgebraicGeometry.SegreProjection.Substitution

/-!
# The Segre projections, III: the partially defined projections

`StacksFrontier/AlgebraicGeometry/SegreProjection/Substitution.lean` provides, for each variable
`y_j` of the second group, a graded ring homomorphism from the polynomial ring on the first group
into the Segre product.  Feeding it to `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` turns it
into a morphism of schemes on its domain of definition, which is what this file names.

## Main definitions

* `Stacks.AlgebraicGeometry.SegreProjection.projLeft R X Y j`: the morphism to `Proj` of the
  polynomial ring on `X` defined on the open where some `x_i * y_j` is invertible.
* `Stacks.AlgebraicGeometry.SegreProjection.projRight R X Y i`: the mirror image.

## Main results

* `Stacks.AlgebraicGeometry.SegreProjection.basicOpen_genSub_le_mapDomain_right`: the bridge to
  the standard affine cover `Stacks.AlgebraicGeometry.SegreCharts.affineOpenCoverGenSub`, whose
  chart at `(i, j)` lies in the domain of `projRight R X Y i` — the companion statement for
  `projLeft` being `Stacks.AlgebraicGeometry.SegreProjection.basicOpen_genSub_le_mapDomain`.

On a standard chart the morphism is described by
`Stacks.AlgebraicGeometry.ProjTwistChain.homOfLE_mapHom`: it is the morphism of affine schemes
attached to the map `R[x]_{(x_i)} → S_{(x_i y_j)}` of degree-zero homogeneous localisations, the
target of which is the chart ring computed in
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreChartRing.lean`.  No restatement of that
lemma is made here; it applies to `projLeft` by unfolding.

## Implementation notes

`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` requires the two rings to lie in a common
universe, and they do: with `R : Type u` and `X Y : Type v`, both the polynomial ring on `X` and
the Segre product inside the polynomial ring on `X ⊕ Y` are of type `Type (max u v)`.

Both gradings are definitions rather than instances in this development, so they are taken as
instance binders, as everywhere else in the Segre files.

## What is not done

These morphisms are **not** glued.  Gluing them into a single morphism out of the whole of `Proj`
of the Segre product needs their pairwise agreement on the overlaps of the domains; the
ring-level identity behind that agreement is
`Stacks.RingTheory.SegreProjection.substLeft_mul_comm`, but the passage from that identity to an
equality of morphisms of schemes — which runs through the degree-zero homogeneous localisations
at a product of two generators, and through `AlgebraicGeometry.Proj.SpecMap_awayMap_awayι` to
move between the charts `D₊(x_i)` and `D₊(x_i * x_{i'})` of the target — is not carried out.  Nor
is anything proved about the pair `(projLeft, projRight)` as a map to the product of the two
projective spaces.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.SegreProjection

universe u v

variable (R : Type u) [CommRing R] (X Y : Type v) [GradedAlgebra (grading R X Y)]

/-- **The `j`-th partial Segre projection to the first factor.**  On the open where some
`x_i * y_j` is invertible, the substitution `x_i ↦ x_i * y_j` induces a morphism from `Proj` of
the Segre product to `Proj` of the polynomial ring on `X`. -/
public def projLeft [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)] (j : Y) :
    (mapDomain (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
        (substLeftGraded R X Y j)).toScheme ⟶
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule X R) :=
  mapHom _ _ (substLeftGraded R X Y j)

/-- **The `i`-th partial Segre projection to the second factor**, the mirror image of
`Stacks.AlgebraicGeometry.SegreProjection.projLeft`. -/
public def projRight [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)] (i : X) :
    (mapDomain (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
        (substRightGraded R X Y i)).toScheme ⟶
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule Y R) :=
  mapHom _ _ (substRightGraded R X Y i)

/-- The chart at `x_i * y_j` of the standard affine cover lies in the domain of the partial
projection to the second factor at `x_i`; the companion statement for the first factor is
`Stacks.AlgebraicGeometry.SegreProjection.basicOpen_genSub_le_mapDomain`. -/
public theorem basicOpen_genSub_le_mapDomain_right (i : X) (j : Y) :
    AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) ≤
      mapDomain (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
        (substRightGraded R X Y i) := by
  rw [← substRightGraded_X R X Y i j]
  exact basicOpen_le_mapDomain _ _ _ one_pos
    (MvPolynomial.isHomogeneous_X R j : MvPolynomial.X j ∈ _)

end Stacks.AlgebraicGeometry.SegreProjection

end

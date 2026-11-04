module

public import StacksFrontier.AlgebraicGeometry.SegreGlue.Glue

/-!
# The inverse images of the standard opens under the two glued Segre projections

`StacksFrontier/AlgebraicGeometry/SegreGlue/Product.lean` records two open halves of Tag 01WD.
This file settles the second of them: that the standard charts `D₊(x_i y_j)` of the Segre product
are carried onto the cover of the product of the two projective spaces by the products
`D₊(x_i) × D₊(y_j)` of standard opens.

## Main results

* `Stacks.AlgebraicGeometry.SegreChartProduct.projLeftGlued_preimage_basicOpen`: the inverse image
  of `D₊(x_i)` under the glued projection to the first factor is the union over `k` of the charts
  `D₊(x_i y_k)`.  The mirror image is
  `Stacks.AlgebraicGeometry.SegreChartProduct.projRightGlued_preimage_basicOpen`.

* `Stacks.AlgebraicGeometry.SegreChartProduct.inf_iSup_basicOpen_genSub`: **the minor relation,
  globally.**  The intersection of those two unions is the single chart `D₊(x_i y_j)`.  The
  inclusion `⊆` is false for formal reasons and holds only by the two-by-two minor relation
  `(x_i y_k)(x_{i'} y_j) = (x_i y_j)(x_{i'} y_k)` of
  `Stacks.AlgebraicGeometry.SegreGlue.genSub_mul_genSub_comm`: a point at which some `x_i y_k` and
  some `x_{i'} y_j` are nonzero has their product nonzero, hence has `x_i y_j` nonzero.

* `Stacks.AlgebraicGeometry.SegreChartProduct.preimage_inf_basicOpen_eq`: putting the two
  together, the locus where the first projection meets `D₊(x_i)` and the second meets `D₊(y_j)` is
  exactly the chart `D₊(x_i y_j)`.  This is what the `IsIso` argument for
  `Stacks.AlgebraicGeometry.SegreGlue.segreProd` needs in order to match the chart cover of the
  source with the product cover of the target: by `CategoryTheory.Limits.pullback.lift_fst` and
  `CategoryTheory.Limits.pullback.lift_snd` the inverse image under `segreProd` of
  `pullback.fst ⁻¹ᵁ D₊(x_i) ⊓ pullback.snd ⁻¹ᵁ D₊(y_j)` is the left-hand side here.

## Implementation notes

The two auxiliary lemmas
`Stacks.AlgebraicGeometry.SegreChartProduct.inf_eq_inf_of_ι_preimage_eq` and
`Stacks.AlgebraicGeometry.SegreChartProduct.le_of_ι_preimage_eq_top` convert a statement about
inverse images along the inclusion of an open into a statement about the open itself; they are
`AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf` together with
`AlgebraicGeometry.Scheme.Opens.opensRange_ι`.  They are what lets the computation of
`Stacks.AlgebraicGeometry.ProjTwistChain.mapAwayHom_preimage_basicOpen`, which is a statement
about a chart, be assembled into a statement about the whole of `AlgebraicGeometry.Proj` of the
Segre product: the charts cover by
`Stacks.AlgebraicGeometry.SegreGlue.iSup_basicOpen_substLeftGraded_X_eq_top`, and
`TopologicalSpace.Opens` is a frame, so an open equals the union of its intersections with the
members of a cover.

Both gradings are definitions rather than instances in this development, so they are taken as
instance binders, as everywhere else in the Segre files.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.SegreProjection Stacks.AlgebraicGeometry.SegreGlue

namespace Stacks.AlgebraicGeometry.SegreChartProduct

universe u v

/-! ### Opens, and inverse images along the inclusion of an open -/

section OpensAux

variable {Z : Scheme.{u}}

/-- Two opens with the same inverse image along the inclusion of an open `U` meet `U` in the same
open. -/
public theorem inf_eq_inf_of_ι_preimage_eq {U V V' : Z.Opens}
    (h : U.ι ⁻¹ᵁ V = U.ι ⁻¹ᵁ V') : U ⊓ V = U ⊓ V' := by
  have h1 := Scheme.Hom.image_preimage_eq_opensRange_inf (f := U.ι) V
  have h2 := Scheme.Hom.image_preimage_eq_opensRange_inf (f := U.ι) V'
  rw [Scheme.Opens.opensRange_ι] at h1 h2
  rw [← h1, ← h2, h]

/-- An open whose inverse image along the inclusion of `U` is everything contains `U`. -/
public theorem le_of_ι_preimage_eq_top {U V : Z.Opens} (h : U.ι ⁻¹ᵁ V = ⊤) : U ≤ V := by
  have h' : U ⊓ V = U ⊓ ⊤ :=
    inf_eq_inf_of_ι_preimage_eq (by rw [h]; exact (Scheme.Hom.preimage_top U.ι).symm)
  rw [inf_top_eq] at h'
  exact inf_eq_right.mp (by rw [inf_comm]; exact h')

/-- An open lies below a union `⨆ k, V k` if, for the members `U p` of a cover of `Z`, its inverse
image along `(U p).ι` equals that of some `V (f p)`. -/
private theorem le_iSup_of_ι_preimage_eq {ι κ : Type*} {W : Z.Opens} {V : κ → Z.Opens}
    (U : ι → Z.Opens) (hU : ⨆ p, U p = ⊤) (f : ι → κ)
    (h : ∀ p, (U p).ι ⁻¹ᵁ W = (U p).ι ⁻¹ᵁ V (f p)) : W ≤ ⨆ k, V k := by
  rw [← top_inf_eq W, ← hU, iSup_inf_eq]
  refine iSup_le fun p => ?_
  rw [inf_eq_inf_of_ι_preimage_eq (h p)]
  exact inf_le_right.trans (le_iSup V (f p))

end OpensAux

/-! ### The inverse images of the standard opens -/

section Projections

variable (R : Type u) [CommRing R] (X Y : Type v) [GradedAlgebra (grading R X Y)]

section Left

variable [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)]

/-- The inverse image of `D₊(x_i)` under the glued projection to the first factor, computed on the
chart at `(i', j)`: it is the chart's intersection with `D₊(x_i y_j)`. -/
public theorem ι_preimage_projLeftGlued_preimage (i i' : X) (j : Y) :
    (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (substLeftGraded R X Y j (MvPolynomial.X i'))).ι ⁻¹ᵁ
        (projLeftGlued R X Y ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule X R) (MvPolynomial.X i)) =
      (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (substLeftGraded R X Y j (MvPolynomial.X i'))).ι ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (SegreCharts.genSub R X Y (i, j)) := by
  rw [← Scheme.Hom.comp_preimage, ι_projLeftGlued R X Y (i', j),
    mapAwayHom_preimage_basicOpen (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
      (substLeftGraded R X Y j) one_pos (X_mem R X i') one_pos (X_mem R X i),
    substLeftGraded_X R X Y j i]

/-- **The inverse image of a standard open under the glued projection to the first factor.**  It
is the union over `k` of the standard charts `D₊(x_i y_k)`. -/
public theorem projLeftGlued_preimage_basicOpen (i : X) :
    projLeftGlued R X Y ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule X R) (MvPolynomial.X i) =
      ⨆ k : Y, AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (SegreCharts.genSub R X Y (i, k)) := by
  refine le_antisymm ?_ (iSup_le fun k => ?_)
  · exact le_iSup_of_ι_preimage_eq _ (iSup_basicOpen_substLeftGraded_X_eq_top R X Y) Prod.snd
      fun p => ι_preimage_projLeftGlued_preimage R X Y i p.1 p.2
  · refine le_of_ι_preimage_eq_top ?_
    have h := ι_preimage_projLeftGlued_preimage R X Y i i k
    rw [substLeftGraded_X R X Y k i] at h
    rw [h]
    exact Scheme.Opens.ι_preimage_self _

end Left

section Right

variable [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)]

/-- The mirror image of
`Stacks.AlgebraicGeometry.SegreChartProduct.ι_preimage_projLeftGlued_preimage`. -/
public theorem ι_preimage_projRightGlued_preimage (i : X) (j k : Y) :
    (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (substRightGraded R X Y i (MvPolynomial.X k))).ι ⁻¹ᵁ
        (projRightGlued R X Y ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule Y R) (MvPolynomial.X j)) =
      (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (substRightGraded R X Y i (MvPolynomial.X k))).ι ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (SegreCharts.genSub R X Y (i, j)) := by
  rw [← Scheme.Hom.comp_preimage, ι_projRightGlued R X Y (i, k),
    mapAwayHom_preimage_basicOpen (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
      (substRightGraded R X Y i) one_pos (X_mem R Y k) one_pos (X_mem R Y j),
    substRightGraded_X R X Y i j]

/-- The mirror image of
`Stacks.AlgebraicGeometry.SegreChartProduct.projLeftGlued_preimage_basicOpen`. -/
public theorem projRightGlued_preimage_basicOpen (j : Y) :
    projRightGlued R X Y ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule Y R) (MvPolynomial.X j) =
      ⨆ i : X, AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (SegreCharts.genSub R X Y (i, j)) := by
  refine le_antisymm ?_ (iSup_le fun i => ?_)
  · exact le_iSup_of_ι_preimage_eq _ (iSup_basicOpen_substRightGraded_X_eq_top R X Y) Prod.fst
      fun p => ι_preimage_projRightGlued_preimage R X Y p.1 j p.2
  · refine le_of_ι_preimage_eq_top ?_
    have h := ι_preimage_projRightGlued_preimage R X Y i j j
    rw [substRightGraded_X R X Y i j] at h
    rw [h]
    exact Scheme.Opens.ι_preimage_self _

end Right

/-! ### The two unions meet in a single chart -/

/-- **The minor relation, globally.**  The union of the charts `D₊(x_i y_k)` over `k` meets the
union of the charts `D₊(x_{i'} y_j)` over `i'` in the single chart `D₊(x_i y_j)`.

The inclusion `≤` is where the two-by-two minor relation
`Stacks.AlgebraicGeometry.SegreGlue.genSub_mul_genSub_comm` is used, through
`Stacks.AlgebraicGeometry.SegreGlue.inf_basicOpen_genSub_le_swapLeft`: without it the statement is
false for formal reasons, since no containment between `D₊(x_i y_k) ⊓ D₊(x_{i'} y_j)` and
`D₊(x_i y_j)` holds for a general pair of degree-one elements. -/
public theorem inf_iSup_basicOpen_genSub (i : X) (j : Y) :
    (⨆ k : Y, AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (SegreCharts.genSub R X Y (i, k))) ⊓
      (⨆ i' : X, AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (SegreCharts.genSub R X Y (i', j))) =
      AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) := by
  refine le_antisymm ?_ (le_inf
    (le_iSup (fun k : Y => AlgebraicGeometry.Proj.basicOpen (grading R X Y)
      (SegreCharts.genSub R X Y (i, k))) j)
    (le_iSup (fun i' : X => AlgebraicGeometry.Proj.basicOpen (grading R X Y)
      (SegreCharts.genSub R X Y (i', j))) i))
  rw [iSup_inf_iSup]
  exact iSup_le fun p => inf_basicOpen_genSub_le_swapLeft R X Y i p.2 p.1 j

/-! ### The chart cover matches the product cover -/

variable [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)]

/-- **The chart cover of the Segre product matches the product cover of the target.**  The locus
where the glued projection to the first factor lands in `D₊(x_i)` and the glued projection to the
second factor lands in `D₊(y_j)` is exactly the standard chart `D₊(x_i y_j)`.

Composed with `CategoryTheory.Limits.pullback.lift_fst` and
`CategoryTheory.Limits.pullback.lift_snd` this computes the inverse image under
`Stacks.AlgebraicGeometry.SegreGlue.segreProd` of the product open
`D₊(x_i) × D₊(y_j)` of the target. -/
public theorem preimage_inf_basicOpen_eq (i : X) (j : Y) :
    (projLeftGlued R X Y ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule X R) (MvPolynomial.X i)) ⊓
      (projRightGlued R X Y ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule Y R) (MvPolynomial.X j)) =
      AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) := by
  rw [projLeftGlued_preimage_basicOpen R X Y i, projRightGlued_preimage_basicOpen R X Y j,
    inf_iSup_basicOpen_genSub R X Y i j]

end Projections

end Stacks.AlgebraicGeometry.SegreChartProduct

end

module

public import StacksFrontier.AlgebraicGeometry.SegreGlue.Overlap
public import StacksFrontier.AlgebraicGeometry.SegreProjection.Substitution

/-!
# The two-by-two minor relation, and the overlaps of the standard charts it controls

The partially defined Segre projections of
`StacksFrontier/AlgebraicGeometry/SegreProjection/Substitution.lean` are indexed by a choice of
variable of the second group, and the chart `D₊(x_i y_j)` of the standard cover lies only in the
domain of the one indexed by `y_j`.  Two charts `D₊(x_i y_j)` and `D₊(x_{i'} y_k)` therefore carry
two different substitutions, and for the pair to be comparable at all each substitution must be
defined on the overlap — which is *not* a formal matter, because `D₊(x_i y_j) ⊓ D₊(x_{i'} y_k)` is
not contained in `D₊(x_{i'} y_j)` for formal reasons.

It is contained in it, and the reason is the two-by-two minor relation

`(x_i y_j) · (x_{i'} y_k) = (x_i y_k) · (x_{i'} y_j)`,

which holds in the Segre product because both sides are the monomial `x_i x_{i'} y_j y_k`.  The
relation says the two standard opens `D₊((x_i y_j)(x_{i'} y_k))` and `D₊((x_i y_k)(x_{i'} y_j))`
are the *same* open, and each of the four generators is therefore invertible on it.

## Main results

* `Stacks.AlgebraicGeometry.SegreGlue.genSub_mul_genSub_comm`: the minor relation.

* `Stacks.AlgebraicGeometry.SegreGlue.inf_basicOpen_genSub_le_swapLeft` and
  `Stacks.AlgebraicGeometry.SegreGlue.inf_basicOpen_genSub_le_swapRight`: its geometric content.
  On `D₊(x_i y_j) ⊓ D₊(x_{i'} y_k)` the two *swapped* generators `x_i y_k` and `x_{i'} y_j` are
  invertible as well.

* `Stacks.AlgebraicGeometry.SegreGlue.crossComm_substLeftGraded` and
  `Stacks.AlgebraicGeometry.SegreGlue.crossComm_substRightGraded`: the substitutions satisfy
  `Stacks.AlgebraicGeometry.SegreGlue.CrossComm`, which is
  `Stacks.RingTheory.SegreProjection.substLeft_mul_comm` repackaged.

* `Stacks.AlgebraicGeometry.SegreGlue.inf_basicOpen_genSub_le_substLeft` and its three companions:
  the four open inclusions a comparison of the two charts needs.  The degree-two element
  `x_i x_{i'}` is the one at which both substitutions are defined on the overlap — that is the
  whole point of passing to degree two, since at degree one they are not.

## Implementation notes

The element `x_i * x_{i'}` is homogeneous of degree `1 + 1`, and the statements below are phrased
with the literal `2`; the two are the same numeral for `ℕ`, but the membership proof is produced by
`MvPolynomial.IsHomogeneous.mul`, which produces the sum, so
`Stacks.AlgebraicGeometry.SegreGlue.X_mul_X_mem` is stated once and reused.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection
open Stacks.AlgebraicGeometry.SegreProjection

namespace Stacks.AlgebraicGeometry.SegreGlue

universe u v

variable (R : Type u) [CommRing R] (X Y : Type v)

/-! ### Homogeneous elements of degree one and two -/

/-- A variable is homogeneous of degree one. -/
public theorem X_mem (i : X) :
    (MvPolynomial.X i : MvPolynomial X R) ∈ MvPolynomial.homogeneousSubmodule X R 1 :=
  MvPolynomial.isHomogeneous_X R i

/-- A product of two variables is homogeneous of degree two.  This is the element at which both
substitutions attached to an overlap of two standard charts are defined. -/
public theorem X_mul_X_mem (i i' : X) :
    (MvPolynomial.X i * MvPolynomial.X i' : MvPolynomial X R) ∈
      MvPolynomial.homogeneousSubmodule X R 2 :=
  (MvPolynomial.isHomogeneous_X R i).mul (MvPolynomial.isHomogeneous_X R i')

/-! ### The minor relation -/

/-- **The two-by-two minor relation.**  In the Segre product the four generators attached to a
two-by-two block of index pairs satisfy `(x_i y_j)(x_{i'} y_k) = (x_i y_k)(x_{i'} y_j)`: both
sides are the monomial `x_i x_{i'} y_j y_k`. -/
public theorem genSub_mul_genSub_comm (i i' : X) (j k : Y) :
    SegreCharts.genSub R X Y (i, j) * SegreCharts.genSub R X Y (i', k) =
      SegreCharts.genSub R X Y (i, k) * SegreCharts.genSub R X Y (i', j) := by
  apply Subtype.ext
  have hmul : ∀ a b : segre R X Y,
      ((a * b : segre R X Y) : MvPolynomial (X ⊕ Y) R) = (a : MvPolynomial (X ⊕ Y) R) * b :=
    fun _ _ => rfl
  rw [hmul, hmul]
  show gen R X Y (i, j) * gen R X Y (i', k) = gen R X Y (i, k) * gen R X Y (i', j)
  simp only [gen_eq]
  ring

/-! ### The substitutions cross-commute -/

/-- The substitutions at two variables of the second group cross-commute; this is
`Stacks.RingTheory.SegreProjection.substLeft_mul_comm`. -/
public theorem crossComm_substLeftGraded (j k : Y) :
    CrossComm (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
      (substLeftGraded R X Y j) (substLeftGraded R X Y k) :=
  fun _ _ _ ha hb => substLeft_mul_comm R X Y j k
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ha)
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hb)

/-- The mirror image of
`Stacks.AlgebraicGeometry.SegreGlue.crossComm_substLeftGraded`. -/
public theorem crossComm_substRightGraded (i i' : X) :
    CrossComm (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
      (substRightGraded R X Y i) (substRightGraded R X Y i') :=
  fun _ _ _ ha hb => substRight_mul_comm R X Y i i'
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ha)
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hb)

/-! ### The substitutions at a product of two variables -/

/-- The substitution at `y_j` sends the product `x_i x_{i'}` to the product
`(x_i y_j) (x_{i'} y_j)` of two generators of the Segre product. -/
public theorem substLeftGraded_X_mul_X (j : Y) (i i' : X) :
    substLeftGraded R X Y j (MvPolynomial.X i * MvPolynomial.X i') =
      SegreCharts.genSub R X Y (i, j) * SegreCharts.genSub R X Y (i', j) := by
  rw [map_mul, substLeftGraded_X, substLeftGraded_X]

/-- The substitution at `x_i` sends the product `y_j y_k` to the product
`(x_i y_j) (x_i y_k)` of two generators of the Segre product. -/
public theorem substRightGraded_X_mul_X (i : X) (j k : Y) :
    substRightGraded R X Y i (MvPolynomial.X j * MvPolynomial.X k) =
      SegreCharts.genSub R X Y (i, j) * SegreCharts.genSub R X Y (i, k) := by
  rw [map_mul, substRightGraded_X, substRightGraded_X]

/-! ### The overlap of two standard charts -/

section Overlaps

variable [GradedAlgebra (grading R X Y)] (i i' : X) (j k : Y)

/-- **The first geometric consequence of the minor relation.**  On the overlap of the charts at
`(i, j)` and at `(i', k)` the swapped generator `x_i y_k` is invertible. -/
public theorem inf_basicOpen_genSub_le_swapLeft :
    AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) ⊓
        AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i', k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, k)) := by
  rw [← AlgebraicGeometry.Proj.basicOpen_mul, genSub_mul_genSub_comm,
    AlgebraicGeometry.Proj.basicOpen_mul]
  exact inf_le_left

/-- **The second geometric consequence of the minor relation.**  On the same overlap the swapped
generator `x_{i'} y_j` is invertible. -/
public theorem inf_basicOpen_genSub_le_swapRight :
    AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) ⊓
        AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i', k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i', j)) := by
  rw [← AlgebraicGeometry.Proj.basicOpen_mul, genSub_mul_genSub_comm,
    AlgebraicGeometry.Proj.basicOpen_mul]
  exact inf_le_right

/-- The overlap lies in the open where the substitution at `y_j` is defined at `x_i x_{i'}`. -/
public theorem inf_basicOpen_genSub_le_substLeft :
    AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) ⊓
        AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i', k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
      (substLeftGraded R X Y j (MvPolynomial.X i * MvPolynomial.X i')) := by
  rw [substLeftGraded_X_mul_X, AlgebraicGeometry.Proj.basicOpen_mul]
  exact le_inf inf_le_left (inf_basicOpen_genSub_le_swapRight R X Y i i' j k)

/-- The overlap lies in the open where the substitution at `y_k` is defined at `x_i x_{i'}`. -/
public theorem inf_basicOpen_genSub_le_substLeft' :
    AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) ⊓
        AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i', k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
      (substLeftGraded R X Y k (MvPolynomial.X i * MvPolynomial.X i')) := by
  rw [substLeftGraded_X_mul_X, AlgebraicGeometry.Proj.basicOpen_mul]
  exact le_inf (inf_basicOpen_genSub_le_swapLeft R X Y i i' j k) inf_le_right

/-- The overlap lies in the open where the substitution at `x_i` is defined at `y_j y_k`. -/
public theorem inf_basicOpen_genSub_le_substRight :
    AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) ⊓
        AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i', k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
      (substRightGraded R X Y i (MvPolynomial.X j * MvPolynomial.X k)) := by
  rw [substRightGraded_X_mul_X, AlgebraicGeometry.Proj.basicOpen_mul]
  exact le_inf inf_le_left (inf_basicOpen_genSub_le_swapLeft R X Y i i' j k)

/-- The overlap lies in the open where the substitution at `x_{i'}` is defined at `y_j y_k`. -/
public theorem inf_basicOpen_genSub_le_substRight' :
    AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) ⊓
        AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i', k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
      (substRightGraded R X Y i' (MvPolynomial.X j * MvPolynomial.X k)) := by
  rw [substRightGraded_X_mul_X, AlgebraicGeometry.Proj.basicOpen_mul]
  exact le_inf (inf_basicOpen_genSub_le_swapRight R X Y i i' j k) inf_le_right

end Overlaps

end Stacks.AlgebraicGeometry.SegreGlue

end

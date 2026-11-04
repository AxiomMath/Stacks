module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniChartAlgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniDistinguishedBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniInvertibleChart

/-!
# The change of basis of the linear system as a substitution of the parameters

A change of basis of the linear system `V` induces an invertible pair of `k`-matrices `b, b'`
between the parameter index set of the family and `{0, …, n}`. On a chart the chart functions `g`
of the new basis, read in the reduced chart ring, are the image `g = b · f` of the chart equations
`f` of the standing basis. Under the hypotheses of [Stacks, Tag 0G4F] there is a chart on which
`g 0` is invertible and `g 1, g 2` carry the codimension datum.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.reducedChartEquation`: the chart equations of the standing basis
  read in the reduced chart ring and indexed by the parameters of the family.
* `Stacks.Bertini.FamilyDivisors.substMatrix` and `Stacks.Bertini.FamilyDivisors.substMatrixInv`:
  the two change-of-basis matrices.

## Main results

* `Stacks.Bertini.FamilyDivisors.substMatrix_mul_substMatrixInv` and
  `Stacks.Bertini.FamilyDivisors.substMatrixInv_mul_substMatrix`: they are mutually inverse.
* `Stacks.Bertini.FamilyDivisors.reducedChartEquation_substMatrix`: the chart function of a member
  of the new basis is the corresponding combination of the chart equations.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.exists_chart_substitution`: **the whole input of the
  two chart statements**, on a chart meeting `Z` on which the function of `v₁` is a unit.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v

namespace Stacks.Bertini.FamilyDivisors

variable {D : FamilyDivisors.{u, v}}

/-- **The chart equations in the reduced chart ring**, indexed by the parameters of the family. -/
def reducedChartEquation (c : D.Chart) (j : D.basisIndex) : reducedChartRing c.U :=
  Ideal.Quotient.mk _ (D.chartEquation c.triv j.down)

section Subst

variable {p : ℕ} (W : Module.Basis (Fin p) D.k D.V)

/-- **The matrix of a basis of the linear system against the standing basis**, with the parameter
index set on the right. -/
def substMatrix : Matrix (Fin p) D.basisIndex D.k :=
  fun i j ↦ D.basis.repr (W i) j.down

/-- The inverse of `Stacks.Bertini.FamilyDivisors.substMatrix`. -/
def substMatrixInv : Matrix D.basisIndex (Fin p) D.k :=
  fun j i ↦ W.repr (D.basis j.down) i

/-- The coordinates of two bases of a module against each other multiply to the identity. -/
private theorem sum_repr_mul_repr_eq_ite {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (W : Module.Basis ι D.k D.V) (B : Module.Basis κ D.k D.V) (i i' : ι) :
    ∑ j, B.repr (W i) j * W.repr (B j) i' = if i = i' then 1 else 0 := by
  simp_rw [mul_comm (B.repr (W i) _)]
  rw [W.sum_repr_mul_repr B (W i) i', Module.Basis.repr_self, Finsupp.single_apply]

/-- `Stacks.Bertini.FamilyDivisors.substMatrixInv` is a right inverse of
`Stacks.Bertini.FamilyDivisors.substMatrix`. -/
theorem substMatrix_mul_substMatrixInv : substMatrix W * substMatrixInv W = 1 := by
  classical
  ext i i'
  rw [Matrix.mul_apply, Matrix.one_apply]
  exact (Fintype.sum_equiv Equiv.ulift _ _ fun j ↦ rfl).trans
    (sum_repr_mul_repr_eq_ite W D.basis i i')

/-- `Stacks.Bertini.FamilyDivisors.substMatrixInv` is a left inverse of
`Stacks.Bertini.FamilyDivisors.substMatrix`. -/
theorem substMatrixInv_mul_substMatrix : substMatrixInv W * substMatrix W = 1 := by
  classical
  ext j j'
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [ULift.ext_iff]
  exact sum_repr_mul_repr_eq_ite D.basis W j.down j'.down

/-- **The chart function of a member of the new basis is the corresponding combination of the chart
equations**, read in the reduced chart ring, with coefficients given by
`Stacks.Bertini.FamilyDivisors.substMatrix`. -/
theorem reducedChartEquation_substMatrix (c : D.Chart) (i : Fin p) :
    letI := reducedChartAlgebra c.U
    Ideal.Quotient.mk _ (chartFunction c.triv (W i)) =
      ∑ j : D.basisIndex, algebraMap D.k (reducedChartRing c.U) (substMatrix W i j) *
        reducedChartEquation c j := by
  let := reducedChartAlgebra c.U
  rw [chartFunction_eq_sum c.triv (W i)]
  simp only [map_sum, map_mul]
  exact (Fintype.sum_equiv Equiv.ulift _ _ fun j ↦ rfl).symm

end Subst

namespace Hypotheses

variable (h : D.Hypotheses)

include h

/-- There is a trivializing affine chart, an invertible pair of `k`-matrices between the parameter
index set of the family and `{0, …, m + 2}`, and a tuple `g` of elements of the reduced chart ring
which is the image of the chart equations under that substitution, whose zeroth entry is invertible
and whose first and second entries carry the codimension datum. -/
@[stacks 0G4F "hypothesis (3) as the substitution datum of the chart statements"]
theorem exists_chart_substitution :
    ∃ (c : D.Chart) (m : ℕ) (b : Matrix (Fin (m + 3)) D.basisIndex D.k)
      (b' : Matrix D.basisIndex (Fin (m + 3)) D.k),
      b * b' = 1 ∧ b' * b = 1 ∧
      letI := reducedChartAlgebra c.U
      ∃ (g : Fin (m + 3) → reducedChartRing c.U) (w : reducedChartRing c.U),
        (∀ i, g i = ∑ j : D.basisIndex,
            algebraMap D.k (reducedChartRing c.U) (b i j) * reducedChartEquation c j) ∧
          w * g ⟨0, by omega⟩ = 1 ∧
          ∃ q : Ideal (reducedChartRing c.U),
            q ∈ (Ideal.span {g ⟨1, by omega⟩, g ⟨2, by omega⟩}).minimalPrimes ∧
              ringKrullDim (reducedChartRing c.U ⧸ q) + 2 =
                ringKrullDim (reducedChartRing c.U) := by
  obtain ⟨c, hZ, hunit⟩ := h.exists_chart_isUnit_chartFunction
  obtain ⟨m, W, hW₁, hW₂, hW₃⟩ := h.exists_basis_distinguished
  refine ⟨c, m, substMatrix W, substMatrixInv W, substMatrix_mul_substMatrixInv W,
    substMatrixInv_mul_substMatrix W, ?_⟩
  let := reducedChartAlgebra c.U
  obtain ⟨w, hw⟩ := (hunit.map (Ideal.Quotient.mk (nilradical Γ(c.U.toScheme, ⊤)))).exists_left_inv
  obtain ⟨q, hq, hqdim⟩ := h.exists_ringKrullDim_quotient_add_two_eq_reducedChart c hZ
  refine ⟨fun i ↦ Ideal.Quotient.mk _ (chartFunction c.triv (W i)), w,
    fun i ↦ reducedChartEquation_substMatrix W c i, ?_, q, ?_, hqdim⟩
  · show w * Ideal.Quotient.mk _ (chartFunction c.triv (W ⟨0, by omega⟩)) = 1
    rwa [hW₁]
  · show q ∈ (Ideal.span {Ideal.Quotient.mk _ (chartFunction c.triv (W ⟨1, by omega⟩)),
      Ideal.Quotient.mk _ (chartFunction c.triv (W ⟨2, by omega⟩))}).minimalPrimes
    rwa [hW₂, hW₃]

end Hypotheses

end Stacks.Bertini.FamilyDivisors

end

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import StacksFrontier.RingTheory.GradedAlgebra.WeightedPresentation

/-!
# The graded Jacobian of a weighted graded presentation

Let `k` be a field and `P` a graded `k`-algebra presented by weighted homogeneous polynomials:
weights `d : Fin n → ℕ`, homogeneous elements `x i ∈ P_{d i}`, and polynomials `F j` which are
weighted homogeneous of weighted degree `e j`. The *graded Jacobian* of such a presentation is
the `k`-linear map
`J : ∏_i P_{d i} → ∏_j P_{e j}`, `(J p)_j = ∑_i p_i · (∂F_j/∂X_i)(x)`,
and this file constructs it and shows that its cokernel is finite-dimensional whenever every
graded piece of `P` is.

The degree bookkeeping is the only delicate point and it is `ℕ`-subtraction: `∂F_j/∂X_i` is
weighted homogeneous of weighted degree `e j - d i`, so `p_i · (∂F_j/∂X_i)(x)` lies in
`P_{d i + (e j - d i)}`, which is `P_{e j}` only when `d i ≤ e j`. In the remaining case
`∂F_j/∂X_i` is zero, so the term vanishes and lies in `P_{e j}` trivially.

## Main results

* `MvPolynomial.IsWeightedHomogeneous.pderiv_eq_zero_of_lt'`: a partial derivative of a weighted
  homogeneous polynomial vanishes when the weight of the variable exceeds the weighted degree.
* `MvPolynomial.IsWeightedHomogeneous.pderiv_tsub`: the truncated-subtraction form of
  Mathlib's `MvPolynomial.IsWeightedHomogeneous.pderiv`, valid with no side condition.
* `GradedAlgebra.mul_aeval_pderiv_mem_grading`: each term of the graded Jacobian lies in the
  graded piece of the degree of the relation.
* `GradedAlgebra.gradedJacobian`: the graded Jacobian itself.
* `GradedAlgebra.gradedJacobian_apply_coe`: its defining formula.
* `GradedAlgebra.finiteDimensional_gradedJacobian_cokernel`: its cokernel is
  finite-dimensional.
* `GradedAlgebra.exists_gradedJacobian`: the two previous results packaged as an existential.

## Implementation notes

Mathlib's `MvPolynomial.IsWeightedHomogeneous.pderiv` already provides the differentiation step
in the side-condition-free form `n' + w i = n`, which avoids `ℕ`-subtraction; the two general
lemmas added here are the `ℕ`-specific complements it does not have, namely the vanishing
statement and the truncated form. They are stated for an arbitrary commutative semiring of
coefficients.

The Jacobian is assembled from term maps written as compositions of `LinearMap.proj`,
`Submodule.subtype`, `LinearMap.mulRight` and `LinearMap.codRestrict`, so that no linearity
proof has to be written by hand.

The cokernel statement needs no hypothesis relating the presentation to the grading beyond the
ones that make the Jacobian exist: the target `∏_j P_{e j}` is already finite-dimensional, so
every quotient of it is. The content of the result is therefore the existence of `J`, i.e. the
degree bookkeeping above.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] {φ : MvPolynomial σ R}

/-- A partial derivative of a weighted homogeneous polynomial vanishes as soon as the weight of
the variable differentiated against exceeds the weighted degree. -/
theorem IsWeightedHomogeneous.pderiv_eq_zero_of_lt' {w : σ → ℕ} {n : ℕ} {i : σ}
    (h : φ.IsWeightedHomogeneous w n) (hi : n < w i) : pderiv i φ = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  rcases eq_or_ne (φ.coeff (m + Finsupp.single i 1)) 0 with h0 | h0
  · rw [h0, zero_mul]
  · exfalso
    have hw := h h0
    rw [map_add, Finsupp.weight_single, one_smul] at hw
    omega

/-- The truncated-subtraction form of Mathlib's `IsWeightedHomogeneous.pderiv`: for natural
number weights the partial derivative of a weighted homogeneous polynomial of weighted degree
`n` is weighted homogeneous of weighted degree `n - w i`, with no side condition, because the
derivative vanishes in the case `n < w i`. -/
theorem IsWeightedHomogeneous.pderiv_tsub {w : σ → ℕ} {n : ℕ} {i : σ}
    (h : φ.IsWeightedHomogeneous w n) :
    (pderiv i φ).IsWeightedHomogeneous w (n - w i) := by
  rcases le_or_gt (w i) n with hi | hi
  · exact h.pderiv (Nat.sub_add_cancel hi)
  · rw [h.pderiv_eq_zero_of_lt' hi]
    exact isWeightedHomogeneous_zero _ _ _

end MvPolynomial

namespace GradedAlgebra

open MvPolynomial

universe u v

variable {k : Type u} {P : Type v} [Field k] [CommRing P] [Algebra k P]

/-- The product of a homogeneous element of degree `d i` with the value at `x` of the `i`-th
partial derivative of a weighted homogeneous polynomial of weighted degree `ej` lies in the
graded piece of degree `ej`. -/
theorem mul_aeval_pderiv_mem_grading (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n : ℕ} {x : Fin n → P} {d : Fin n → ℕ} (hx : ∀ i, x i ∈ grading (d i))
    {ej : ℕ} {G : MvPolynomial (Fin n) k} (hG : IsWeightedHomogeneous d G ej)
    (i : Fin n) {z : P} (hz : z ∈ grading (d i)) :
    z * aeval x (pderiv i G) ∈ grading ej := by
  rcases le_or_gt (d i) ej with hle | hlt
  · have h1 : aeval x (pderiv i G) ∈ grading (ej - d i) :=
      aeval_mem_grading_of_isWeightedHomogeneous grading hx hG.pderiv_tsub
    have h2 := SetLike.mul_mem_graded hz h1
    rwa [Nat.add_sub_cancel' hle] at h2
  · rw [hG.pderiv_eq_zero_of_lt' hlt, map_zero, mul_zero]
    exact (grading ej).zero_mem

/-- One term of the graded Jacobian: the `k`-linear map sending `p` to
`p_i · (∂F_j/∂X_i)(x)`, viewed in the graded piece of degree `e j`. -/
noncomputable def gradedJacobianTerm (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (i : Fin n) (j : Fin r) :
    ((i : Fin n) → grading (d i)) →ₗ[k] grading (e j) :=
  LinearMap.codRestrict (grading (e j))
    (LinearMap.mulRight k (aeval x (pderiv i (F j))) ∘ₗ
      (grading (d i)).subtype ∘ₗ LinearMap.proj i)
    fun p => mul_aeval_pderiv_mem_grading grading hx (hF j) i (p i).2

/-- The underlying element of `gradedJacobianTerm grading hx F hF i j p` in `P` is
`p_i · (∂F_j/∂X_i)(x)`. -/
@[simp]
theorem gradedJacobianTerm_apply_coe (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (i : Fin n) (j : Fin r)
    (p : (i : Fin n) → grading (d i)) :
    ((gradedJacobianTerm grading hx F hF i j p : grading (e j)) : P) =
      (p i : P) * aeval x (pderiv i (F j)) :=
  rfl

/-- **The graded Jacobian of a weighted graded presentation.** For weights `d`, homogeneous
elements `x i ∈ P_{d i}` and relations `F j` weighted homogeneous of weighted degree `e j`, this
is the `k`-linear map `∏_i P_{d i} → ∏_j P_{e j}` whose `j`-th coordinate is
`p ↦ ∑_i p_i · (∂F_j/∂X_i)(x)`. -/
noncomputable def gradedJacobian (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) :
    ((i : Fin n) → grading (d i)) →ₗ[k] ((j : Fin r) → grading (e j)) :=
  LinearMap.pi fun j => ∑ i : Fin n, gradedJacobianTerm grading hx F hF i j

/-- The defining formula of the graded Jacobian. -/
theorem gradedJacobian_apply_coe (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j))
    (p : (i : Fin n) → grading (d i)) (j : Fin r) :
    ((gradedJacobian grading hx F hF p j : grading (e j)) : P) =
      ∑ i : Fin n, (p i : P) * aeval x (pderiv i (F j)) := by
  rw [gradedJacobian, LinearMap.pi_apply, LinearMap.sum_apply]
  push_cast
  simp

/-- **The cokernel of the graded Jacobian is finite-dimensional** when every graded piece of `P`
is. The target `∏_j P_{e j}` is a finite product of finite-dimensional spaces, so this needs
nothing beyond the existence of the Jacobian. -/
theorem finiteDimensional_gradedJacobian_cokernel (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] [∀ i, Module.Finite k (grading i)]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) :
    FiniteDimensional k
      (((j : Fin r) → grading (e j)) ⧸ LinearMap.range (gradedJacobian grading hx F hF)) := by
  have : Module.Finite k ((j : Fin r) → grading (e j)) := inferInstance
  infer_instance

/-- **The graded Jacobian of a weighted graded presentation, with finite-dimensional cokernel.**
This is the second step of the Stacks proof of the tangent-space half of Tag 0DVZ, packaged as
an existential over the linear map. -/
theorem exists_gradedJacobian (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ i, Module.Finite k (grading i)]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) :
    ∃ J : ((i : Fin n) → grading (d i)) →ₗ[k] ((j : Fin r) → grading (e j)),
      (∀ (p : (i : Fin n) → grading (d i)) (j : Fin r),
        ((J p j : grading (e j)) : P) =
          ∑ i : Fin n, (p i : P) * aeval x (pderiv i (F j))) ∧
      FiniteDimensional k (((j : Fin r) → grading (e j)) ⧸ LinearMap.range J) :=
  ⟨gradedJacobian grading hx F hF, gradedJacobian_apply_coe grading hx F hF,
    finiteDimensional_gradedJacobian_cokernel grading hx F hF⟩

end GradedAlgebra

end

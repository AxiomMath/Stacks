module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import StacksFrontier.RingTheory.GradedAlgebra.GradedJacobianFunctor
public import StacksFrontier.RingTheory.GradedAlgebra.LiftRecordGraded

/-!
# The recorded relation vector as an element of `W ⊗[k] V`

Step (viii) of the proof of the tangent-space half of Stacks 0DVZ
(`examples-defos.tex:683`) reads the vector `(g_1, …, g_m)` of
`GradedAlgebra.existsUnique_lTensor_subtype_record` in

`W = Coker(P_{d_1} ⊕ … ⊕ P_{d_n} → P_{e_1} ⊕ … ⊕ P_{e_m})`,

the cokernel of the graded Jacobian, and asserts that the resulting element is independent of
the choice of lifted generators. The record itself lies in `∏_j (N ⊗[k] P_{e_j})` for
`N = I`, the square-zero ideal of the base; the value of
`GradedAlgebra.gradedJacobianCokernelFunctor` at a test module `V` is `W ⊗[k] V`. This file
builds the `k`-linear map between the two out of an identification `φ : N → V` of the ideal
with the test module, and proves the two statements the proof needs about it:

* it kills exactly the ambiguity the change-of-generators formula
  `GradedAlgebra.sub_eq_sum_lTensor_gradedJacobianEntry_of_lift_relation` produces, so the
  recorded element does not depend on the chosen lifts of the generators;
* it is natural in `V`: changing `φ` by a map `V → V'` changes the recorded element by the
  value of `GradedAlgebra.gradedJacobianCokernelFunctor` on that map, which is
  `W ⊗ (-)` applied to it.

## Main definitions

* `GradedAlgebra.recordSwap`: the comparison `N ⊗[k] M → M ⊗[k] V` along `φ : N → V`.
* `GradedAlgebra.gradedJacobianCokernelRecord`: the map
  `∏_j (N ⊗[k] P_{e_j}) → W ⊗[k] V`.

## Main results

* `GradedAlgebra.gradedJacobian_apply_eq_sum_gradedJacobianEntry`: the Jacobian is the matrix
  of its entries.
* `GradedAlgebra.gradedJacobianCokernelRecord_eq_of_sub_eq_sum`: two records differing by the
  image of the Jacobian have the same image, which is the independence of the choice of lifts.
* `GradedAlgebra.lTensor_gradedJacobianCokernelRecord`: naturality in the test module.

## Implementation notes

The family `∏_j (N ⊗[k] P_{e_j})` is assembled into `N ⊗[k] ∏_j P_{e_j}` by
`TensorProduct.piRight`, so that the vanishing statement becomes the single identity
`(mkQ ∘ J) ⊗ id = 0` rather than a double sum over the index pairs; the only bookkeeping left
is `gradedJacobian_apply_eq_sum_gradedJacobianEntry`, which says that the `j`-th coordinate of
the Jacobian at `p` is the sum over `i` of the `(i, j)` entries at `p i`.

Nothing here is tagged: this is step (viii) of 0DVZ's *proof*, and Stacks does not tag the
steps of a proof.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public noncomputable section

open MvPolynomial TensorProduct

namespace GradedAlgebra

universe u v

variable {k : Type u} {P : Type v} [Field k] [CommRing P] [Algebra k P]

/-- **The graded Jacobian is the matrix of its entries.** The `j`-th coordinate of
`gradedJacobian` at `p` is the sum over `i` of `gradedJacobianEntry i j` at `p i`. -/
theorem gradedJacobian_apply_eq_sum_gradedJacobianEntry (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j))
    (p : (i : Fin n) → ↥(grading (d i))) (j : Fin r) :
    gradedJacobian grading hx F hF p j =
      ∑ i : Fin n, gradedJacobianEntry grading hx F hF i j (p i) := by
  refine Subtype.ext ?_
  rw [gradedJacobian_apply_coe, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun i _ => (gradedJacobianEntry_apply_coe grading hx F hF i j _).symm

variable {N V V' : Type*} [AddCommGroup N] [Module k N] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']

/-- **The comparison `N ⊗[k] M → M ⊗[k] V` along a map `φ : N → V`**, sending `b ⊗ₜ m` to
`m ⊗ₜ φ b`. The records of Stacks 0DVZ arrive with the square-zero ideal on the left and the
graded piece on the right, whereas the functor
`GradedAlgebra.gradedJacobianCokernelFunctor` has the test module on the right. -/
def recordSwap (φ : N →ₗ[k] V) (M : Type*) [AddCommGroup M] [Module k M] :
    N ⊗[k] M →ₗ[k] M ⊗[k] V :=
  LinearMap.lTensor M φ ∘ₗ (TensorProduct.comm k N M).toLinearMap

/-- The defining formula of `recordSwap`. -/
@[simp]
theorem recordSwap_tmul (φ : N →ₗ[k] V) (M : Type*) [AddCommGroup M] [Module k M]
    (b : N) (m : M) : recordSwap φ M (b ⊗ₜ m) = m ⊗ₜ φ b := rfl

/-- `recordSwap` turns a map applied to the right factor into the same map applied to the left
factor: it exchanges `LinearMap.lTensor` for `LinearMap.rTensor`. -/
theorem recordSwap_comp_lTensor (φ : N →ₗ[k] V) {M M' : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup M'] [Module k M'] (f : M →ₗ[k] M') :
    recordSwap φ M' ∘ₗ LinearMap.lTensor N f = LinearMap.rTensor V f ∘ₗ recordSwap φ M := by
  refine TensorProduct.ext' fun b m => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul, recordSwap_tmul,
    recordSwap_tmul, LinearMap.rTensor_tmul]

/-- Postcomposing the identification `φ : N → V` with a map `V → V'` postcomposes
`recordSwap` with `W ⊗ (-)` applied to that map. -/
theorem lTensor_comp_recordSwap (φ : N →ₗ[k] V) (f : V →ₗ[k] V') (M : Type*) [AddCommGroup M]
    [Module k M] :
    LinearMap.lTensor M f ∘ₗ recordSwap φ M = recordSwap (f ∘ₗ φ) M := by
  refine TensorProduct.ext' fun b m => ?_
  rw [LinearMap.comp_apply, recordSwap_tmul, LinearMap.lTensor_tmul, recordSwap_tmul,
    LinearMap.comp_apply]

/-- **The recorded relation vector as an element of `W ⊗[k] V`.** Given an identification
`φ : N → V` of the module carrying the record with the test module, a family
`g j ∈ N ⊗[k] P_{e j}` is assembled into `N ⊗[k] ∏_j P_{e j}`, moved to
`(∏_j P_{e j}) ⊗[k] V` and pushed into the cokernel of the graded Jacobian. This is the map
Stacks 0DVZ describes by *"the image of the vector `(G_1, …, G_m)` in the `k`-vector space
`W`"*. -/
def gradedJacobianCokernelRecord (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (φ : N →ₗ[k] V) :
    ((j : Fin r) → N ⊗[k] ↥(grading (e j))) →ₗ[k]
      (((j : Fin r) → ↥(grading (e j))) ⧸ LinearMap.range (gradedJacobian grading hx F hF))
        ⊗[k] V :=
  LinearMap.rTensor V (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF))) ∘ₗ
    recordSwap φ ((j : Fin r) → ↥(grading (e j))) ∘ₗ
    (TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm.toLinearMap

/-- The assembled form of the Jacobian acts on an assembled family coordinatewise by the
entries of the Jacobian. -/
theorem piRight_lTensor_gradedJacobian (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j))
    (ξ : N ⊗[k] ((i : Fin n) → ↥(grading (d i)))) (j : Fin r) :
    TensorProduct.piRight k k N (fun j' : Fin r => ↥(grading (e j')))
        (LinearMap.lTensor N (gradedJacobian grading hx F hF) ξ) j =
      ∑ i : Fin n, LinearMap.lTensor N (gradedJacobianEntry grading hx F hF i j)
        (TensorProduct.piRight k k N (fun i' : Fin n => ↥(grading (d i'))) ξ i) := by
  induction ξ using TensorProduct.inductionOn with
  | tmul b p =>
      have hL : TensorProduct.piRight k k N (fun j' : Fin r => ↥(grading (e j')))
          (LinearMap.lTensor N (gradedJacobian grading hx F hF) (b ⊗ₜ p)) j =
          b ⊗ₜ gradedJacobian grading hx F hF p j := rfl
      rw [hL, gradedJacobian_apply_eq_sum_gradedJacobianEntry, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hR : TensorProduct.piRight k k N (fun i' : Fin n => ↥(grading (d i'))) (b ⊗ₜ p) i =
          b ⊗ₜ p i := rfl
      rw [hR, LinearMap.lTensor_tmul]
  | add ξ η hξ hη =>
      rw [map_add, map_add, Pi.add_apply, hξ, hη, map_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, map_add]

/-- **The recorded element does not depend on the choice of lifted generators.** Two record
families differing by the image of the graded Jacobian — which is exactly the difference the
change-of-generators formula
`GradedAlgebra.sub_eq_sum_lTensor_gradedJacobianEntry_of_lift_relation` produces — have the
same image in `W ⊗[k] V`, because the Jacobian dies in its own cokernel and `- ⊗ V` is a
functor. -/
theorem gradedJacobianCokernelRecord_eq_of_sub_eq_sum (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (φ : N →ₗ[k] V)
    {g g' : (j : Fin r) → N ⊗[k] ↥(grading (e j))}
    {p : (i : Fin n) → N ⊗[k] ↥(grading (d i))}
    (h : ∀ j, g' j - g j =
      -∑ i : Fin n, LinearMap.lTensor N (gradedJacobianEntry grading hx F hF i j) (p i)) :
    gradedJacobianCokernelRecord grading hx F hF φ g' =
      gradedJacobianCokernelRecord grading hx F hF φ g := by
  have hdiff : (TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm (g' - g) =
      -LinearMap.lTensor N (gradedJacobian grading hx F hF)
        ((TensorProduct.piRight k k N fun i : Fin n => ↥(grading (d i))).symm p) := by
    refine (TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).injective ?_
    rw [LinearEquiv.apply_symm_apply, map_neg]
    refine funext fun j => ?_
    rw [Pi.sub_apply, h j, Pi.neg_apply, piRight_lTensor_gradedJacobian grading hx F hF _ j]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_)
    rw [LinearEquiv.apply_symm_apply]
  have hzero : Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF)) ∘ₗ
      gradedJacobian grading hx F hF = 0 := by
    refine LinearMap.ext fun q => ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨q, rfl⟩
  have hcomp : LinearMap.rTensor V
        (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF))) ∘ₗ
      recordSwap φ ((j : Fin r) → ↥(grading (e j))) ∘ₗ
        LinearMap.lTensor N (gradedJacobian grading hx F hF) = 0 := by
    rw [recordSwap_comp_lTensor, ← LinearMap.comp_assoc, ← LinearMap.rTensor_comp, hzero,
      LinearMap.rTensor_zero, LinearMap.zero_comp]
  have hmap : gradedJacobianCokernelRecord grading hx F hF φ (g' - g) = 0 := by
    have hstep : gradedJacobianCokernelRecord grading hx F hF φ (g' - g) =
        -(LinearMap.rTensor V
            (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF))) ∘ₗ
          recordSwap φ ((j : Fin r) → ↥(grading (e j))) ∘ₗ
            LinearMap.lTensor N (gradedJacobian grading hx F hF))
          ((TensorProduct.piRight k k N fun i : Fin n => ↥(grading (d i))).symm p) := by
      rw [gradedJacobianCokernelRecord, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.comp_apply, LinearMap.comp_apply]
      rw [show (TensorProduct.piRight k k N
          fun j : Fin r => ↥(grading (e j))).symm.toLinearMap (g' - g) =
          (TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm (g' - g) from rfl,
        hdiff, map_neg, map_neg]
    rw [hstep, hcomp, LinearMap.zero_apply, neg_zero]
  rw [map_sub] at hmap
  exact sub_eq_zero.mp hmap

/-- **Naturality of the recorded element in the test module.** Postcomposing the identification
`φ : N → V` with a map `f : V → V'` postcomposes the record with the value of
`GradedAlgebra.gradedJacobianCokernelFunctor` on `f`, which is `W ⊗ f`. This is the shape in
which the naturality hypothesis of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` consumes it. -/
theorem lTensor_gradedJacobianCokernelRecord (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (φ : N →ₗ[k] V) (f : V →ₗ[k] V')
    (g : (j : Fin r) → N ⊗[k] ↥(grading (e j))) :
    LinearMap.lTensor
        (((j : Fin r) → ↥(grading (e j))) ⧸ LinearMap.range (gradedJacobian grading hx F hF)) f
        (gradedJacobianCokernelRecord grading hx F hF φ g) =
      gradedJacobianCokernelRecord grading hx F hF (f ∘ₗ φ) g := by
  have hA : ∀ ζ : ((j : Fin r) → ↥(grading (e j))) ⊗[k] V,
      LinearMap.lTensor (((j : Fin r) → ↥(grading (e j))) ⧸
          LinearMap.range (gradedJacobian grading hx F hF)) f
        (LinearMap.rTensor V
          (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF))) ζ) =
      LinearMap.rTensor V' (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF)))
        (LinearMap.lTensor ((j : Fin r) → ↥(grading (e j))) f ζ) := by
    intro ζ
    induction ζ using TensorProduct.inductionOn with
    | tmul q w =>
        rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
          LinearMap.rTensor_tmul]
    | add ζ η hζ hη => rw [map_add, map_add, hζ, hη, map_add, map_add]
  have e1 : gradedJacobianCokernelRecord grading hx F hF φ g =
      LinearMap.rTensor V (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF)))
        (recordSwap φ ((j : Fin r) → ↥(grading (e j)))
          ((TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm g)) := rfl
  have e2 : gradedJacobianCokernelRecord grading hx F hF (f ∘ₗ φ) g =
      LinearMap.rTensor V' (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF)))
        (recordSwap (f ∘ₗ φ) ((j : Fin r) → ↥(grading (e j)))
          ((TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm g)) := rfl
  have e3 : recordSwap (f ∘ₗ φ) ((j : Fin r) → ↥(grading (e j)))
        ((TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm g) =
      LinearMap.lTensor ((j : Fin r) → ↥(grading (e j))) f
        (recordSwap φ ((j : Fin r) → ↥(grading (e j)))
          ((TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm g)) := by
    rw [← LinearMap.comp_apply, lTensor_comp_recordSwap]
  rw [e1, e2, e3, hA]

end GradedAlgebra

end

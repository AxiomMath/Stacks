module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# The parity operator of an integer grading

Let `M` be a module with an internal `ℤ`-grading `ℳ : ℤ → Submodule R M`. Its *parity
operator* is the linear endomorphism acting on the degree-`n` piece as multiplication by the
Koszul sign `(-1)^n`. It is the device by which a degree-dependent sign in a graded
construction can be absorbed into a single globally defined linear map, so that the
construction itself needs no reference to the decomposition.

## Main definitions

* `DirectSum.gradedProjection`: the projection of a graded module onto one of its graded
  pieces, as a linear endomorphism.
* `DirectSum.parity`: the parity operator of an integer grading.

## Main results

* `DirectSum.gradedProjection_of_mem_same` and `DirectSum.gradedProjection_of_mem_ne`: the
  projection fixes its own graded piece and kills the others.
* `DirectSum.parity_apply_of_mem`: the parity operator multiplies a homogeneous element of
  degree `n` by `(-1)^n`.
* `DirectSum.parity_mem`: the parity operator preserves each graded piece.
* `DirectSum.linearMap_ext_of_mem`: two linear maps out of a graded module agree as soon as
  they agree on homogeneous elements. This is how every identity involving the parity operator
  below is proved, and it is what clients need in order to reason about it.

## Implementation notes

The operator is built as `DirectSum.toModule` of the signed inclusions of the graded pieces,
precomposed with `DirectSum.decomposeLinearEquiv`; `parity_apply_of_mem` is then the only
property of that construction a client should use.
-/

@[expose] public noncomputable section

universe u w

namespace DirectSum

variable {R : Type u} [Ring R] {M : Type w} [AddCommGroup M] [Module R M]

/-- Two linear maps out of a graded module that agree on homogeneous elements are equal. -/
theorem linearMap_ext_of_mem {ι : Type*} [DecidableEq ι] (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ] {N : Type*} [AddCommGroup N] [Module R N]
    {f g : M →ₗ[R] N} (h : ∀ (i : ι) (x : M), x ∈ ℳ i → f x = g x) : f = g := by
  classical
  ext x
  have hsum : (∑ i ∈ DFinsupp.support (DirectSum.decompose ℳ x),
      ((DirectSum.decompose ℳ x) i : M)) = x :=
    DirectSum.sum_support_decompose ℳ x
  rw [← hsum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => h i _ ((DirectSum.decompose ℳ x) i).2

section Projection

variable {ι : Type*} [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- The projection of a graded module onto its degree-`i` piece, as a linear endomorphism of
the module. -/
def gradedProjection (i : ι) : M →ₗ[R] M :=
  (ℳ i).subtype ∘ₗ (DirectSum.component R ι (fun j => ℳ j) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

/-- The projection computes the degree-`i` component of the decomposition. -/
theorem gradedProjection_apply (i : ι) (x : M) :
    gradedProjection ℳ i x = (DirectSum.decompose ℳ x i : M) := rfl

/-- The projection onto the degree-`i` piece lands in that piece. -/
theorem gradedProjection_mem (i : ι) (x : M) : gradedProjection ℳ i x ∈ ℳ i :=
  (DirectSum.decompose ℳ x i).2

/-- The projection onto the degree-`i` piece fixes that piece. -/
theorem gradedProjection_of_mem_same {i : ι} {x : M} (hx : x ∈ ℳ i) :
    gradedProjection ℳ i x = x := by
  rw [gradedProjection_apply, DirectSum.decompose_of_mem_same ℳ hx]

/-- The projection onto the degree-`i` piece kills every other piece. -/
theorem gradedProjection_of_mem_ne {i j : ι} {x : M} (hx : x ∈ ℳ j) (hij : j ≠ i) :
    gradedProjection ℳ i x = 0 := by
  rw [gradedProjection_apply, DirectSum.decompose_of_mem_ne ℳ hx hij]

end Projection

variable (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]

/-- The parity operator of an integer grading: multiplication by the Koszul sign `(-1)^n` on
the degree-`n` piece. -/
def parity : M →ₗ[R] M :=
  (DirectSum.toModule R ℤ M
      (fun n => ((n.negOnePow : ℤ) • ((ℳ n).subtype : ℳ n →ₗ[R] M))))
    ∘ₗ (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

/-- The parity operator multiplies a homogeneous element of degree `n` by `(-1)^n`. -/
theorem parity_apply_of_mem {n : ℤ} {x : M} (hx : x ∈ ℳ n) :
    parity ℳ x = (n.negOnePow : ℤ) • x := by
  classical
  rw [parity, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem ℳ hx]
  rw [show (DirectSum.of (fun i => ℳ i) n ⟨x, hx⟩)
      = DirectSum.lof R ℤ (fun i => ℳ i) n ⟨x, hx⟩ from rfl]
  rw [DirectSum.toModule_lof]
  rfl

/-- The parity operator preserves each graded piece. -/
theorem parity_mem {n : ℤ} {x : M} (hx : x ∈ ℳ n) : parity ℳ x ∈ ℳ n := by
  rw [parity_apply_of_mem ℳ hx]
  exact zsmul_mem hx _

end DirectSum

end

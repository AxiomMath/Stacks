module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The kernel of a coordinate row one of whose entries is a unit

Let `B` be a commutative ring, `ι` a finite index type and `x : ι → B` a family with `x i = 1`
for some index `i`. The `B`-linear functional `(g_j) ↦ ∑ x_j g_j` on `ι → B` is then split
surjective, and its kernel is free on the family `e_j - x_j e_i` indexed by `j ≠ i`: a vector in
the kernel is determined by its coordinates away from `i`, because the relation forces the
`i`-th coordinate to be `-∑_{j ≠ i} x_j g_j`.

## Main definitions

* `Stacks.LinearAlgebra.unitalRow`: the linear functional `(g_j) ↦ ∑ x_j g_j`.
* `Stacks.LinearAlgebra.kernelGen`: the vector `e_j - x_j e_i`.
* `Stacks.LinearAlgebra.kernelEquiv` and `Stacks.LinearAlgebra.kernelBasis`: the kernel of the
  functional, identified with the free module on the indices `j ≠ i`, and the corresponding
  basis.

## Main results

* `Stacks.LinearAlgebra.unitalRow_kernelGen`: the generators lie in the kernel.
* `Stacks.LinearAlgebra.surjective_unitalRow`: the functional is surjective, `e_i` being a
  preimage of `1`.
* `Stacks.LinearAlgebra.kernelBasis_apply_coe`: the basis of the kernel consists of the vectors
  `e_j - x_j e_i`.

## Implementation notes

The hypothesis is `x i = 1` rather than `IsUnit (x i)`, which is what the application supplies:
on the standard chart `D₊(T_i)` of projective space the coordinate row is `(T_0/T_i, …, T_n/T_i)`
and its `i`-th entry is literally `1`. Nothing below would break for a unit entry, at the cost of
dividing by it throughout.
-/

@[expose] public section

namespace Stacks.LinearAlgebra

variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Contraction with the row `(x_j)`, as a linear functional on `ι → B`. -/
def unitalRow (x : ι → B) : (ι → B) →ₗ[B] B where
  toFun g := ∑ j, x j * g j
  map_add' g h := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c g := by simp [Finset.mul_sum, smul_eq_mul, mul_left_comm]

omit [DecidableEq ι] in
@[simp] theorem unitalRow_apply (x g : ι → B) : unitalRow x g = ∑ j, x j * g j := rfl

variable {i : ι} {x : ι → B}

/-- The vector `e_j - x_j e_i`, which contracts to `x_j - x_j x_i` against the row `(x_j)`. -/
def kernelGen (x : ι → B) (i j : ι) : ι → B := Pi.single j 1 - x j • Pi.single i 1

omit [Fintype ι] in
/-- The `k`-th coordinate of the vector `e_j - x_j e_i`. -/
theorem kernelGen_apply (i j k : ι) :
    kernelGen x i j k = (if k = j then 1 else 0) - x j * (if k = i then 1 else 0) := by
  simp [kernelGen, Pi.single_apply, eq_comm]

/-- When `x i = 1` the vector `e_j - x_j e_i` lies in the kernel of contraction with `(x_j)`. -/
theorem unitalRow_kernelGen (hx : x i = 1) (j : ι) : unitalRow x (kernelGen x i j) = 0 := by
  simp only [unitalRow_apply, kernelGen_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq' Finset.univ, hx]

/-- Contraction of the standard basis vector `e_i` against the row `(x_j)` is the entry `x i`. -/
theorem unitalRow_single (x : ι → B) (i : ι) :
    unitalRow x (Pi.single i 1) = x i := by
  simp [unitalRow_apply, Pi.single_apply, eq_comm]

omit [DecidableEq ι] in
/-- Contraction with a row one of whose entries is `1` is surjective. -/
theorem surjective_unitalRow (hx : x i = 1) : Function.Surjective (unitalRow x) := by
  classical
  exact fun b =>
    ⟨b • Pi.single i 1, by rw [map_smul, unitalRow_single, hx, smul_eq_mul, mul_one]⟩

/-- The map assembling a family of coefficients indexed by `j ≠ i` into the combination
`∑ c_j (e_j - x_j e_i)` of kernel generators. -/
def kernelLift (x : ι → B) (i : ι) : ({j : ι // j ≠ i} → B) →ₗ[B] (ι → B) :=
  ∑ j : {j : ι // j ≠ i}, (LinearMap.proj j).smulRight (kernelGen x i j.1)

/-- The vector assembled from a family of coefficients is the combination `∑ c_j (e_j - x_j e_i)`
of kernel generators. -/
theorem kernelLift_apply (c : {j : ι // j ≠ i} → B) :
    kernelLift x i c = ∑ j : {j : ι // j ≠ i}, c j • kernelGen x i j.1 := by
  simp [kernelLift, LinearMap.sum_apply]

/-- Away from the index `i` the assembled vector has the given coefficient. -/
theorem kernelLift_apply_of_ne (c : {j : ι // j ≠ i} → B) {k : ι} (hk : k ≠ i) :
    kernelLift x i c k = c ⟨k, hk⟩ := by
  rw [kernelLift_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, kernelGen_apply, smul_eq_mul, hk, ite_false,
    mul_zero, sub_zero]
  rw [Finset.sum_eq_single_of_mem ⟨k, hk⟩ (Finset.mem_univ _)]
  · simp
  · intro b _ hb
    have hbk : k ≠ (b : ι) := fun h => hb (Subtype.ext h.symm)
    simp [hbk]

/-- At the index `i` the assembled vector is determined by the row and the coefficients. -/
theorem kernelLift_apply_self (c : {j : ι // j ≠ i} → B) :
    kernelLift x i c i = -∑ j : {j : ι // j ≠ i}, x j.1 * c j := by
  rw [kernelLift_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, kernelGen_apply, smul_eq_mul, ite_true]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : i ≠ (j : ι) := fun h => j.2 h.symm
  simp [hj, mul_comm]

/-- A combination of the kernel generators determines its coefficients. -/
theorem injective_kernelLift : Function.Injective (kernelLift x i) := fun c c' h =>
  funext fun j => by
    rw [← kernelLift_apply_of_ne c j.2, ← kernelLift_apply_of_ne c' j.2, h]

/-- A vector annihilated by contraction with a row whose `i`-th entry is `1` is the combination
of kernel generators read off from its coordinates away from `i`. -/
theorem eq_kernelLift_of_unitalRow_eq_zero (hx : x i = 1) {g : ι → B}
    (hg : unitalRow x g = 0) : g = kernelLift x i (fun j => g j.1) := by
  refine funext fun k => ?_
  by_cases hk : k = i
  · subst hk
    rw [kernelLift_apply_self, eq_neg_iff_add_eq_zero]
    have hsplit : ∑ j, x j * g j
        = x k * g k + ∑ j : {j : ι // j ≠ k}, x j.1 * g j.1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      congr 1
      exact Finset.sum_subtype _ (fun j => by simp) _
    rw [unitalRow_apply, hsplit, hx, one_mul] at hg
    exact hg
  · rw [kernelLift_apply_of_ne _ hk]

/-- **The kernel of contraction with a row whose `i`-th entry is `1` is free on the indices
`j ≠ i`**, the index `j` corresponding to the vector `e_j - x_j e_i`. -/
noncomputable def kernelEquiv (hx : x i = 1) :
    ({j : ι // j ≠ i} → B) ≃ₗ[B] LinearMap.ker (unitalRow x) :=
  LinearEquiv.ofBijective
    ((kernelLift x i).codRestrict _ fun c => by
      simp only [LinearMap.mem_ker, kernelLift_apply, map_sum, map_smul,
        unitalRow_kernelGen hx, smul_zero, Finset.sum_const_zero])
    ⟨fun c c' h => injective_kernelLift (congrArg Subtype.val h), fun g =>
      ⟨fun j => g.1 j.1, Subtype.ext (eq_kernelLift_of_unitalRow_eq_zero hx g.2).symm⟩⟩

@[simp] theorem kernelEquiv_apply_coe (hx : x i = 1) (c : {j : ι // j ≠ i} → B) :
    ((kernelEquiv hx) c : ι → B) = kernelLift x i c := rfl

/-- The basis of the kernel of contraction with the row `(x_j)` given by the vectors
`e_j - x_j e_i` for `j ≠ i`. -/
noncomputable def kernelBasis (hx : x i = 1) :
    Module.Basis {j : ι // j ≠ i} B (LinearMap.ker (unitalRow x)) :=
  (Pi.basisFun B {j : ι // j ≠ i}).map (kernelEquiv hx)

@[simp] theorem kernelBasis_apply_coe (hx : x i = 1) (j : {j : ι // j ≠ i}) :
    ((kernelBasis hx j : LinearMap.ker (unitalRow x)) : ι → B) = kernelGen x i j.1 := by
  have : kernelLift x i (Pi.single j 1) = kernelGen x i j.1 := by
    simp [kernelLift_apply, Pi.single_apply]
  simpa [kernelBasis, Pi.basisFun_apply] using this

end Stacks.LinearAlgebra

end

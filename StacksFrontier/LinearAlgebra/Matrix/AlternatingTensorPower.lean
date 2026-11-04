module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Perm

/-!
# The alternating vector in a tensor power, and the rank-one projector it spans

Let `R` be a commutative ring and `n` a finite type with `d = #n` elements. The `d`-fold tensor
power of the free module `R ^ n` is free on the index type `n → n`, and a square matrix `u` over
`R` acts on it by the Kronecker power `Matrix.tensorPow u`, whose `(f, g)` entry is
`∏ k, u (f k) (g k)`.

Inside that tensor power sits the **alternating vector** `Matrix.altVec`, whose coordinate at an
index `f : n → n` is the sign of `f` when `f` is a permutation and `0` otherwise; classically it
is `∑_σ sgn(σ) · e_{σ(1)} ⊗ ⋯ ⊗ e_{σ(d)}`, the image of a generator of the top exterior power
under its embedding as the sign-character part of the tensor power. The two identities that make
it useful are that `u` acts on it through its determinant,
`u^{⊗ d} · a = det(u) · a` and `aᵗ · u^{⊗ d} = det(u) · aᵗ`, and they are proved here by reading
each side as a determinant: the coordinate sum against `altVec` is a Leibniz expansion, so it is
the determinant of `u` with its rows (respectively columns) read along `f`, which is
`Matrix.det_permute` when `f` is a permutation and vanishes by `Matrix.det_zero_of_row_eq` when it
is not.

`Matrix.altProj` is the rank-one matrix `a · aᵗ`. It is the projector of the proof of
[Stacks, Tag 0A2L]: there, for an Azumaya algebra `A` which is étale locally `𝓗om(F, F)` with `F`
free of rank `d`, the composite `F^{⊗ d} → ∧^d F → F^{⊗ d}` is read as a section of `A^{⊗ d}`, and
the sections obtained from two different trivialisations have to agree.
`Matrix.tensorPow_mul_altProj_mul_tensorPow` is that agreement: the two trivialisations differ by
conjugation by an invertible `u` — on a small enough open set, where the invertible sheaf of
Tag 0A2K is trivial — and the projector is unchanged, because the determinants it picks up on the
two sides cancel.

Nothing here mentions exterior powers: what the argument of Tag 0A2L uses about the projector is
only that it factors through a rank-one free module as a split epimorphism followed by a split
monomorphism, and that is `Matrix.altVec_id`, which says that the coordinate of `altVec` at the
identity index is `1`.

## Main definitions

* `Matrix.altVec`: the alternating vector, the sign character read as a vector on `n → n`.
* `Matrix.tensorPow`: the `d`-fold Kronecker power of a square matrix, indexed by `n → n`.
* `Matrix.altProj`: the rank-one matrix `altVec * altVecᵗ`.

## Main results

* `Matrix.det_submatrix_left` and `Matrix.det_submatrix_right`: reading the rows, or the columns,
  of `u` along `f : n → n` multiplies the determinant by `Matrix.altVec f`.
* `Matrix.sum_tensorPow_mul_altVec` and `Matrix.sum_altVec_mul_tensorPow`: **the Kronecker power
  of `u` acts on the alternating vector through `det u`**, on either side.
* `Matrix.tensorPow_mul_altProj` and `Matrix.altProj_mul_tensorPow`: hence it multiplies the
  rank-one projector by `det u` on either side.
* **`Matrix.tensorPow_mul_altProj_mul_tensorPow`: the projector is invariant under conjugation by
  a Kronecker power.** This is the agreement of two trivialisations in Tag 0A2L.
* `Matrix.altProj_mul_altProj`: `p * p = d! • p`, the identity the source records for the
  projector.
* `Matrix.tensorPow_one` and `Matrix.tensorPow_mul`: the Kronecker power is multiplicative.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open Equiv Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]

/-- The alternating vector of the `#n`-fold tensor power of `R ^ n`, as a function on the index
type `n → n` of that tensor power: its coordinate at `f` is the sign of `f` if `f` is a
permutation, and `0` if it is not. -/
def altVec (f : n → n) : R :=
  ∑ σ : Equiv.Perm n, if (σ : n → n) = f then ((Equiv.Perm.sign σ : ℤ) : R) else 0

variable {R}

/-- A sum of coordinates against `Matrix.altVec` is a sum over the permutations. -/
theorem sum_mul_altVec (F : (n → n) → R) :
    ∑ g, F g * altVec R g = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : R) * F (σ : n → n) := by
  simp only [altVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.sum_eq_single_of_mem (σ : n → n) (Finset.mem_univ _)
    (fun g _ hg ↦ by rw [if_neg (Ne.symm hg), mul_zero]), if_pos rfl, mul_comm]

/-- The coordinate of the alternating vector at a permutation `σ` is the sign of `σ`. -/
@[simp]
theorem altVec_coe_perm (σ : Equiv.Perm n) :
    altVec R (σ : n → n) = ((Equiv.Perm.sign σ : ℤ) : R) := by
  rw [altVec, Finset.sum_eq_single_of_mem σ (Finset.mem_univ _)
    (fun τ _ hτ ↦ if_neg fun h ↦ hτ (Equiv.coe_fn_injective h)), if_pos rfl]

/-- The alternating vector vanishes at an index which is not a permutation. -/
theorem altVec_eq_zero_of_not_bijective {f : n → n} (hf : ¬ Function.Bijective f) :
    altVec R f = 0 :=
  Finset.sum_eq_zero fun σ _ ↦ if_neg fun h ↦ hf (by rw [← h]; exact σ.bijective)

/-- The coordinate of the alternating vector at the identity index is `1`. -/
@[simp]
theorem altVec_id : altVec R (id : n → n) = 1 := by
  simpa using altVec_coe_perm (R := R) (1 : Equiv.Perm n)

/-- **Reading the rows of `u` along `f` multiplies the determinant by the coordinate of the
alternating vector at `f`.** -/
theorem det_submatrix_left (u : Matrix n n R) (f : n → n) :
    (u.submatrix f id).det = altVec R f * u.det := by
  by_cases hf : Function.Bijective f
  · obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm n, (σ : n → n) = f := ⟨Equiv.ofBijective f hf, rfl⟩
    rw [altVec_coe_perm, Matrix.det_permute]
  · rw [altVec_eq_zero_of_not_bijective hf, zero_mul]
    have hinj : ¬ Function.Injective f := fun h ↦ hf ⟨h, Finite.surjective_of_injective h⟩
    rw [Function.not_injective_iff] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    refine Matrix.det_zero_of_row_eq hne ?_
    funext k
    simp [Matrix.submatrix_apply, hij]

/-- **Reading the columns of `u` along `g` multiplies the determinant by the coordinate of the
alternating vector at `g`.** -/
theorem det_submatrix_right (u : Matrix n n R) (g : n → n) :
    (u.submatrix id g).det = altVec R g * u.det := by
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix, det_submatrix_left, Matrix.det_transpose]

/-- The `#n`-fold Kronecker power of a square matrix, as a matrix indexed by the index type
`n → n` of the `#n`-fold tensor power of `R ^ n`. -/
def tensorPow (u : Matrix n n R) : Matrix (n → n) (n → n) R :=
  Matrix.of fun f g ↦ ∏ k, u (f k) (g k)

omit [DecidableEq n] in
/-- The `(f, g)` entry of `Matrix.tensorPow u` is `∏ k, u (f k) (g k)`. -/
@[simp]
theorem tensorPow_apply (u : Matrix n n R) (f g : n → n) :
    tensorPow u f g = ∏ k, u (f k) (g k) :=
  rfl

/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem tensorPow_one : tensorPow (1 : Matrix n n R) = 1 := by
  ext f g
  simp only [tensorPow_apply, Matrix.one_apply]
  by_cases h : f = g
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ : ∃ k, f k ≠ g k := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- The Kronecker power of a product is the product of the Kronecker powers. -/
theorem tensorPow_mul (u v : Matrix n n R) :
    tensorPow (u * v) = tensorPow u * tensorPow v := by
  ext f h
  simp only [tensorPow_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun g _ ↦ Finset.prod_mul_distrib

/-- **The Kronecker power of `u` carries the alternating vector to `det u` times itself**, acting
on coordinates from the left. -/
theorem sum_tensorPow_mul_altVec (u : Matrix n n R) (f : n → n) :
    ∑ g, tensorPow u f g * altVec R g = altVec R f * u.det := by
  rw [sum_mul_altVec, ← det_submatrix_left u f, ← Matrix.det_transpose (u.submatrix f id),
    Matrix.det_apply']
  exact Finset.sum_congr rfl fun σ _ ↦ by
    simp [Matrix.transpose_apply, Matrix.submatrix_apply]

/-- **The Kronecker power of `u` carries the alternating vector to `det u` times itself**, acting
on coordinates from the right. -/
theorem sum_altVec_mul_tensorPow (u : Matrix n n R) (g : n → n) :
    ∑ f, altVec R f * tensorPow u f g = altVec R g * u.det := by
  rw [show (∑ f, altVec R f * tensorPow u f g) = ∑ f, tensorPow u f g * altVec R f from
      Finset.sum_congr rfl fun f _ ↦ mul_comm _ _,
    sum_mul_altVec, ← det_submatrix_right u g, Matrix.det_apply']
  exact Finset.sum_congr rfl fun σ _ ↦ by
    simp [Matrix.submatrix_apply]

/-- The sum of the squares of the coordinates of the alternating vector is `d!`. -/
theorem sum_altVec_mul_altVec :
    ∑ g : n → n, altVec R g * altVec R g = (Nat.factorial (Fintype.card n) : R) := by
  rw [sum_mul_altVec]
  simp only [altVec_coe_perm]
  rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) ↦
    show ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul, mul_one]

variable (R)

/-- The rank-one projector spanned by the alternating vector: the matrix `a * aᵗ` on the index
type of the `#n`-fold tensor power. This is the projector `p` of [Stacks, Tag 0A2L]. -/
def altProj : Matrix (n → n) (n → n) R :=
  Matrix.of fun f g ↦ altVec R f * altVec R g

variable {R}

/-- The `(f, g)` entry of `Matrix.altProj R` is `altVec R f * altVec R g`. -/
@[simp]
theorem altProj_apply (f g : n → n) : altProj R f g = altVec R f * altVec R g :=
  rfl

/-- A matrix which acts on `altVec` by the scalar `c` multiplies the projector by `c`. -/
private theorem mul_altProj_eq_smul (M : Matrix (n → n) (n → n) R) (c : R)
    (h : ∀ f, ∑ g, M f g * altVec R g = altVec R f * c) : M * altProj R = c • altProj R := by
  ext f k
  simp only [Matrix.mul_apply, altProj_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, h]
  ring

/-- **The Kronecker power of `u` multiplies the projector by `det u`**, on the left. -/
theorem tensorPow_mul_altProj (u : Matrix n n R) :
    tensorPow u * altProj R = u.det • altProj R :=
  mul_altProj_eq_smul _ _ (sum_tensorPow_mul_altVec u)

/-- **The Kronecker power of `u` multiplies the projector by `det u`**, on the right. -/
theorem altProj_mul_tensorPow (u : Matrix n n R) :
    altProj R * tensorPow u = u.det • altProj R := by
  ext f h
  simp only [Matrix.mul_apply, altProj_apply, Matrix.smul_apply, smul_eq_mul]
  rw [show (∑ g, altVec R f * altVec R g * tensorPow u g h) =
      altVec R f * ∑ g, altVec R g * tensorPow u g h from by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ ↦ mul_assoc _ _ _]
  rw [sum_altVec_mul_tensorPow]
  ring

/-- **The projector is invariant under conjugation by a Kronecker power**: if `u * v = 1`, then
`tensorPow u * altProj R * tensorPow v = altProj R`. This is the step of [Stacks, Tag 0A2L] which
says that two trivialisations of an Azumaya algebra give the same section of its tensor power: they
differ by conjugation by an invertible matrix, and the determinants the projector picks up on the
two sides cancel. -/
theorem tensorPow_mul_altProj_mul_tensorPow {u v : Matrix n n R} (huv : u * v = 1) :
    tensorPow u * altProj R * tensorPow v = altProj R := by
  rw [tensorPow_mul_altProj, Matrix.smul_mul, altProj_mul_tensorPow, smul_smul, ← Matrix.det_mul,
    huv, Matrix.det_one, one_smul]

/-- **`p * p = d! • p` for the projector `p`**, the identity recorded in the proof of
[Stacks, Tag 0A2L]. -/
theorem altProj_mul_altProj :
    (altProj R : Matrix (n → n) (n → n) R) * altProj R =
      (Nat.factorial (Fintype.card n) : R) • altProj R := by
  refine mul_altProj_eq_smul _ _ fun f ↦ ?_
  simp only [altProj_apply, mul_assoc, ← Finset.mul_sum, sum_altVec_mul_altVec]

end Matrix

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixAlgebraSections
public import StacksFrontier.LinearAlgebra.Matrix.AlternatingProjectorImage

/-!
# Matrix units, Kronecker powers and the alternating data under base change

This file collects the pieces of pure matrix algebra that the proof of [Stacks, Tag 0A2L] needs
once the geometry has been stripped away. Throughout, `n` is a finite type with decidable
equality, `R` a commutative ring, and `Matrix.single a b 1` is the matrix unit `e_{ab}`.

The first group of results is about a **conjugated matrix unit**. For `u v : Matrix n n R` the
matrix `u * e_{ab} * v` has `(x, y)` entry `u x a * v b y`, because `e_{ab}` is the rank-one
matrix which reads off the `a`-th column on the left and the `b`-th row on the right. Taking the
`#n`-fold Kronecker power `Matrix.tensorPow`, whose `(f, g)` entry is `∏ i, u (f i) (g i)` and
whose index type is `n → n`, the same computation runs one index at a time: the `(k', l')` entry
of `u^{⊗} * e_{kl} * v^{⊗}` is the product over `i` of the `(k' i, l' i)` entries of the `n × n`
conjugated matrix units `u * e_{k i, l i} * v`. This is the entrywise form of the statement that
the Kronecker power of a conjugation is the conjugation by the Kronecker powers, restricted to
the matrix units which span everything.

The second group is **base change of the alternating data**. The alternating vector
`Matrix.altVec R f` is the sign of `f` when `f : n → n` is a permutation and `0` otherwise, and
its defining formula uses only the integers: it is a sum of terms `±1` and `0`. A ring
homomorphism therefore carries `Matrix.altVec R` to `Matrix.altVec R'` and, entrywise, the
rank-one projector `Matrix.altProj R = a · aᵗ` to `Matrix.altProj R'`. This is what lets the
projector of Tag 0A2L be compared across a restriction map of the structure sheaf, or across the
map to a stalk: it is literally the same matrix, written over a different ring.

The third group concerns `Stacks.Matrix.unitCombination W`, the `R`-linear map of matrices which
sends the matrix unit `e_{ce}` to a prescribed matrix `W (c, e)`. Three facts complete its
calculus: it does send `e_{ab}` to `W (a, b)`; it is **conjugation** by `u` and `v` as soon as
every `W k` is the corresponding conjugated matrix unit, which is how one recognises the
automorphism produced by Skolem--Noether as conjugation; and it commutes with a ring
homomorphism applied entrywise, which is how that recognition is transported along a restriction
map.

## Main results

* `Matrix.mul_single_mul_apply`: the entries of a conjugated matrix unit, `u x a * v b y`.
* `Matrix.tensorPow_mul_single_mul_tensorPow_apply`: **the same, Kronecker-wise**, as a product
  over the index type of the entries of the `n × n` conjugated matrix units.
* `Matrix.map_altVec` and `Matrix.map_altProj`: **the alternating vector and the alternating
  projector are defined by the same formula over any commutative ring.**
* `Stacks.Matrix.unitCombination_single`: the combination of the matrix units evaluated at a
  matrix unit.
* `Stacks.Matrix.unitCombination_eq_conj`: **the combination of the matrix units is conjugation**
  as soon as the images of the matrix units are the conjugated matrix units.
* `Stacks.Matrix.unitCombination_map`: the combination of the matrix units commutes with a ring
  homomorphism.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

universe u

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Conjugate

variable {R : Type*} [CommRing R]

/-- **The entries of a conjugated matrix unit.** Multiplying by `Matrix.single a b 1` on the
right of `u` reads off the `a`-th column of `u`, and on the left of `v` the `b`-th row of `v`. -/
theorem mul_single_mul_apply (u v : Matrix n n R) (a b x y : n) :
    (u * Matrix.single a b (1 : R) * v) x y = u x a * v b y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem b (Finset.mem_univ _)
    (fun q _ hq ↦ by rw [Matrix.mul_single_apply_of_ne (hbj := hq), zero_mul]),
    Matrix.mul_single_apply_same, mul_one]

/-- **The entries of a conjugated matrix unit, Kronecker-wise.** For `u v : Matrix n n R` and
index functions `k l : n → n`, the `(k', l')` entry of `tensorPow u * single k l 1 * tensorPow v`
is the product over `i` of the `(k' i, l' i)` entries of the `n × n` conjugated matrix units
`u * single (k i) (l i) 1 * v`. -/
theorem tensorPow_mul_single_mul_tensorPow_apply (u v : Matrix n n R) (k l k' l' : n → n) :
    (Matrix.tensorPow u * Matrix.single k l (1 : R) * Matrix.tensorPow v) k' l'
      = ∏ i, (u * Matrix.single (k i) (l i) (1 : R) * v) (k' i) (l' i) := by
  simp only [mul_single_mul_apply, Matrix.tensorPow_apply]
  rw [Finset.prod_mul_distrib]

end Conjugate

section BaseChange

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- The alternating vector is defined by the same formula over any commutative ring. -/
theorem map_altVec (φ : R →+* R') (f : n → n) :
    φ (Matrix.altVec R f) = Matrix.altVec R' f := by
  simp only [Matrix.altVec, map_sum, apply_ite φ, map_intCast, map_zero]

/-- The alternating projector is defined by the same formula over any commutative ring. -/
theorem map_altProj (φ : R →+* R') :
    (Matrix.altProj R (n := n)).map φ = Matrix.altProj R' := by
  ext f g
  rw [Matrix.map_apply, Matrix.altProj_apply, map_mul, map_altVec, map_altVec,
    Matrix.altProj_apply]

end BaseChange

end Matrix

namespace Stacks.Matrix

variable {K : Type*} [CommRing K] {I : Type*} [Fintype I] [DecidableEq I]
  (W : I × I → Matrix I I K)

/-- The combination of the matrix units, evaluated at a matrix unit, is that unit's image. -/
theorem unitCombination_single (a b : I) :
    unitCombination W (Matrix.single a b (1 : K)) = W (a, b) := by
  rw [unitCombination, Finset.sum_eq_single_of_mem a (Finset.mem_univ _)
    (fun c _ hc ↦ Finset.sum_eq_zero fun e _ ↦ by
      rw [Matrix.single_apply_of_row_ne (Ne.symm hc), zero_smul]),
    Finset.sum_eq_single_of_mem b (Finset.mem_univ _)
      (fun e _ he ↦ by rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm he), zero_smul]),
    Matrix.single_apply_same, one_smul]

/-- **The combination of the matrix units is conjugation** as soon as the images of the matrix
units are the conjugates of the matrix units. -/
theorem unitCombination_eq_conj {u v : Matrix I I K}
    (hW : ∀ k : I × I, W k = u * Matrix.single k.1 k.2 (1 : K) * v) (M : Matrix I I K) :
    unitCombination W M = u * M * v := by
  have key : ∀ c e : I, M c e • W (c, e) = u * Matrix.single c e (M c e) * v := fun c e ↦ by
    rw [hW (c, e), ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hM : u * M * v = ∑ c : I, ∑ e : I, u * Matrix.single c e (M c e) * v := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hM, unitCombination]
  exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun e _ ↦ key c e

omit [DecidableEq I] in
/-- The combination of the matrix units commutes with a ring homomorphism. -/
theorem unitCombination_map {K' : Type*} [CommRing K'] (φ : K →+* K') (M : Matrix I I K) :
    (unitCombination W M).map φ
      = unitCombination (fun k ↦ (W k).map φ) (M.map φ) := by
  ext a b
  rw [Matrix.map_apply, unitCombination_apply, unitCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun e _ ↦ by
    rw [map_mul, Matrix.map_apply, Matrix.map_apply]

end Stacks.Matrix

end

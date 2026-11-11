module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Upper band matrices and unipotent elements of `GL_n`

A square matrix `X` indexed by `Fin n` is supported in the upper band of width `d` when
`X p q = 0` as soon as `q < p + d`. Products of band matrices are band matrices whose widths add
up, and the entry of a product on the boundary of the band is a single product of entries. We
use this to compute the entries near the diagonal of `(1 + Y) t (1 + C)` for an upper triangular
`t` and band matrices `Y`, `C` of width `d ≥ 1`, and we define the unipotent element `1 + N` of
`GL_n` of a strictly upper triangular `N` and the diagonal element of `GL_n` of a family of
units.

## Main definitions

* `Stacks.Adeles.GeneralLinear.IsUpperBand` — `X p q = 0` for `q < p + d`.
* `Stacks.Adeles.GeneralLinear.unipotentOfBand` — `1 + N ∈ GL_n(R)` for `N` strictly upper
  triangular.
* `Stacks.Adeles.GeneralLinear.diagonalGL` — the diagonal matrix of a family of units.

## Main results

* `Stacks.Adeles.GeneralLinear.one_add_mul_mul_one_add_apply` — the entries of
  `(1 + Y) t (1 + C)` in the band of width `d + 1`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.Adeles.GeneralLinear

section Band

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `X` is supported in the upper band of width `d`: `X p q = 0` whenever `q < p + d`. -/
public def IsUpperBand (d : ℕ) (X : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ p q : Fin n, (q : ℕ) < p + d → X p q = 0

/-- A band of width `d` is a band of every smaller width. -/
public theorem IsUpperBand.mono {d e : ℕ} {X : Matrix (Fin n) (Fin n) R} (h : IsUpperBand d X)
    (he : e ≤ d) : IsUpperBand e X :=
  fun p q hpq => h p q (by omega)

/-- Band matrices of width `d` are closed under addition. -/
public theorem IsUpperBand.add {d : ℕ} {X Y : Matrix (Fin n) (Fin n) R} (hX : IsUpperBand d X)
    (hY : IsUpperBand d Y) : IsUpperBand d (X + Y) :=
  fun p q hpq => by rw [Matrix.add_apply, hX p q hpq, hY p q hpq, add_zero]

/-- The widths of band matrices add up under multiplication. -/
public theorem IsUpperBand.mul {d e : ℕ} {X Y : Matrix (Fin n) (Fin n) R} (hX : IsUpperBand d X)
    (hY : IsUpperBand e Y) : IsUpperBand (d + e) (X * Y) := by
  intro p q hpq
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < p + d
  · rw [hX p l hl, zero_mul]
  · rw [hY l q (by omega), mul_zero]

/-- On the boundary `q = p + d + e` of the band of a product, the entry of `X * Y` is the single
product `X p l * Y l q` with `l = p + d`. -/
public theorem IsUpperBand.mul_apply_of_eq {d e : ℕ} {X Y : Matrix (Fin n) (Fin n) R}
    (hX : IsUpperBand d X) (hY : IsUpperBand e Y) {p q l : Fin n} (hl : (l : ℕ) = p + d)
    (hq : (q : ℕ) = p + d + e) : (X * Y) p q = X p l * Y l q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single l (fun l' _ hl' => ?_) (fun h => absurd (Finset.mem_univ l) h)
  by_cases h : (l' : ℕ) < p + d
  · rw [hX p l' h, zero_mul]
  · have : (l : ℕ) ≠ l' := fun h' => hl' (Fin.ext h'.symm)
    rw [hY l' q (by omega), mul_zero]

/-- A matrix is a band matrix of width `0` exactly when it is upper triangular. -/
public theorem isUpperBand_zero_iff {X : Matrix (Fin n) (Fin n) R} :
    IsUpperBand 0 X ↔ ∀ p q : Fin n, q < p → X p q = 0 := by
  refine ⟨fun h p q hpq => h p q (by simpa using hpq), fun h p q hpq => h p q ?_⟩
  exact Fin.lt_def.2 (by simpa using hpq)

/-- The entries of `(1 + Y) t (1 + C)` in the band of width `d + 1`, for an upper triangular `t`
and band matrices `Y`, `C` of width `d ≥ 1`: `t p q + Y p q * t q q + t p p * C p q`. -/
public theorem one_add_mul_mul_one_add_apply {d : ℕ} (hd : 1 ≤ d)
    {Y t C : Matrix (Fin n) (Fin n) R} (ht : IsUpperBand 0 t) (hY : IsUpperBand d Y)
    (hC : IsUpperBand d C) {p q : Fin n} (hpq : (q : ℕ) < p + d + 1) :
    ((1 + Y) * t * (1 + C)) p q = t p q + Y p q * t q q + t p p * C p q := by
  have hexp : (1 + Y) * t * (1 + C) = t + Y * t + t * C + Y * t * C := by
    simp only [add_mul, mul_add, one_mul, mul_one]
    abel
  have hYtC : (Y * t * C) p q = 0 :=
    ((hY.mul ht).mul hC) p q (by omega)
  rw [hexp, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, hYtC, add_zero]
  rcases Nat.lt_or_ge (q : ℕ) (p + d) with h | h
  · rw [(hY.mul ht) p q (by omega), (ht.mul hC) p q (by omega), hY p q h, hC p q h]
    ring
  · have hq : (q : ℕ) = p + d := by omega
    rw [hY.mul_apply_of_eq ht (l := q) hq (by omega),
      ht.mul_apply_of_eq hC (l := p) (by omega) (by omega)]

end Band

section Unipotent

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `1 + N` is invertible for `N` strictly upper triangular. -/
public theorem isUnit_one_add_of_isUpperBand {N : Matrix (Fin n) (Fin n) R}
    (hN : IsUpperBand 1 N) : IsUnit (1 + N) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular]
  · rw [Finset.prod_eq_one fun i _ => by
      rw [Matrix.add_apply, Matrix.one_apply_eq, hN i i (by omega), add_zero]]
    exact isUnit_one
  · intro i j hij
    have hij : j < i := hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.ne_of_gt hij), zero_add]
    exact hN i j (by have := Fin.lt_def.1 hij; omega)

/-- The unipotent element `1 + N` of `GL_n(R)`, for `N` strictly upper triangular. -/
public def unipotentOfBand (N : Matrix (Fin n) (Fin n) R) (hN : IsUpperBand 1 N) :
    GL (Fin n) R :=
  (isUnit_one_add_of_isUpperBand hN).unit

/-- The matrix of `unipotentOfBand N hN` is `1 + N`. -/
@[simp]
public theorem coe_unipotentOfBand (N : Matrix (Fin n) (Fin n) R) (hN : IsUpperBand 1 N) :
    (unipotentOfBand N hN : Matrix (Fin n) (Fin n) R) = 1 + N := rfl

/-- Band matrices are mapped to band matrices by a ring homomorphism. -/
public theorem IsUpperBand.map {S : Type*} [CommRing S] {d : ℕ} {N : Matrix (Fin n) (Fin n) R}
    (hN : IsUpperBand d N) (f : R →+* S) : IsUpperBand d (N.map f) :=
  fun p q hpq => by rw [Matrix.map_apply, hN p q hpq, map_zero]

/-- The image of `1 + N` under a ring homomorphism is `1 + f(N)`. -/
public theorem coe_map_unipotentOfBand {S : Type*} [CommRing S] (f : R →+* S)
    (N : Matrix (Fin n) (Fin n) R) (hN : IsUpperBand 1 N) :
    (GeneralLinearGroup.map f (unipotentOfBand N hN) : Matrix (Fin n) (Fin n) S) =
      1 + N.map f := by
  ext i j
  rw [GeneralLinearGroup.map_apply, coe_unipotentOfBand, Matrix.add_apply, Matrix.add_apply,
    map_add, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- The diagonal element of `GL_n(R)` with diagonal entries the units `u i`. -/
public def diagonalGL (u : Fin n → Rˣ) : GL (Fin n) R where
  val := diagonal fun i => (u i : R)
  inv := diagonal fun i => ((u i)⁻¹ : Rˣ)
  val_inv := by rw [diagonal_mul_diagonal]; simp
  inv_val := by rw [diagonal_mul_diagonal]; simp

/-- The matrix of `diagonalGL u` is the diagonal matrix of the `u i`. -/
@[simp]
public theorem coe_diagonalGL (u : Fin n → Rˣ) :
    (diagonalGL u : Matrix (Fin n) (Fin n) R) = diagonal fun i => (u i : R) := rfl

/-- The image of a diagonal element under a ring homomorphism is diagonal. -/
public theorem coe_map_diagonalGL {S : Type*} [CommRing S] (f : R →+* S) (u : Fin n → Rˣ) :
    (GeneralLinearGroup.map f (diagonalGL u) : Matrix (Fin n) (Fin n) S) =
      diagonal fun i => f (u i) := by
  ext i j
  rw [GeneralLinearGroup.map_apply, coe_diagonalGL, diagonal_apply, diagonal_apply]
  split_ifs <;> simp

end Unipotent

end Stacks.Adeles.GeneralLinear

end

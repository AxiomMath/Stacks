module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# A matrix killing a family of vectors which is a basis at every residue field

Let `B` be a commutative ring, `D` a `β × r` matrix over `B` and `b₁, …, b_r ∈ Bʳ` vectors with
`D bⱼ = 0`. If at every maximal ideal `q` the images of the `bⱼ` in `κ(q)ʳ` are linearly
independent, then the `bⱼ` form a basis of `Bʳ` — the determinant of the matrix with columns
`bⱼ` lies in no maximal ideal — and therefore `D = 0`.

This is the algebraic step of the proof of [Stacks, Tag 0BDP] which shows that a base change along
which a vector bundle descends lands in the closed stratum cut out by a minimal local model of
the degree zero cohomology.

## Main results

* `Matrix.isUnit_det_of_linearIndependent_residueField`: the determinant is a unit.
* `Matrix.eq_zero_of_mulVec_eq_zero_of_linearIndependent_residueField`: `D = 0`.
-/

@[expose] public section

namespace Matrix

variable {B : Type*} [CommRing B] {r β : ℕ}

/-- A square matrix whose columns are linearly independent over every residue field at a maximal
ideal has a unit determinant. -/
theorem isUnit_det_of_linearIndependent_residueField (M : Matrix (Fin r) (Fin r) B)
    (h : ∀ (q : Ideal B) [q.IsMaximal],
      LinearIndependent q.ResidueField (fun j ↦ fun i ↦ algebraMap B q.ResidueField (M i j))) :
    IsUnit M.det := by
  by_contra hM
  obtain ⟨q, hq, hdet⟩ := exists_max_ideal_of_mem_nonunits hM
  have hunit : IsUnit (M.map (algebraMap B q.ResidueField)) :=
    linearIndependent_cols_iff_isUnit.1 (h q)
  have hmap : (M.map (algebraMap B q.ResidueField)).det = algebraMap B q.ResidueField M.det :=
    (RingHom.map_det (algebraMap B q.ResidueField) M).symm
  rw [isUnit_iff_isUnit_det, hmap, IsScalarTower.algebraMap_apply B (B ⧸ q) q.ResidueField,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hdet, map_zero] at hunit
  exact not_isUnit_zero hunit

/-- **A matrix killing a residuewise basis is zero.** If `D bⱼ = 0` for vectors `b₁, …, b_r` whose
images are linearly independent over the residue field at every maximal ideal, then `D = 0`. -/
theorem eq_zero_of_mulVec_eq_zero_of_linearIndependent_residueField
    (D : Matrix (Fin β) (Fin r) B) (b : Fin r → Fin r → B) (hb : ∀ j, D *ᵥ b j = 0)
    (h : ∀ (q : Ideal B) [q.IsMaximal],
      LinearIndependent q.ResidueField (fun j ↦ fun i ↦ algebraMap B q.ResidueField (b j i))) :
    D = 0 := by
  let M : Matrix (Fin r) (Fin r) B := Matrix.of fun i j ↦ b j i
  have hDM : D * M = 0 := by
    ext i j
    simpa [M, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hb j) i
  calc D = D * M * M⁻¹ := by
        rw [Matrix.mul_assoc,
          Matrix.mul_nonsing_inv M (isUnit_det_of_linearIndependent_residueField M h),
          Matrix.mul_one]
    _ = 0 := by rw [hDM, Matrix.zero_mul]

end Matrix

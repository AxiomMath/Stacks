module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Trace

/-!
# The trace of the top exterior power is the determinant

For a square matrix `A` of size `n` over a commutative ring `R`, the trace of the endomorphism
`⋀ⁿ A` of the top exterior power `⋀[R]^n (Fin n → R)` is `det A`.
-/

@[expose] public section

open Module

namespace exteriorPower

/-- The trace of the `n`-th exterior power of the endomorphism of `Rⁿ` given by an `n × n`
matrix `A` is the determinant of `A`. -/
theorem trace_map_toLin'_eq_det {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.trace R _ (exteriorPower.map n (Matrix.toLin' A)) = A.det := by
  let b := Pi.basisFun R (Fin n)
  let B := b.exteriorPower n
  rw [LinearMap.trace_eq_matrix_trace R B, Matrix.trace]
  let s : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp [Set.powersetCard.mem_iff]⟩
  have hs : ∀ t : Set.powersetCard (Fin n) n, t = s := fun t =>
    Subtype.ext (Finset.eq_univ_of_card _ (by simp [Set.powersetCard.mem_iff.1 t.prop]))
  rw [Fintype.sum_eq_single s (fun t ht => (ht (hs t)).elim), Matrix.diag_apply,
    LinearMap.toMatrix_apply, basis_repr_apply, basis_apply, ιMulti_family, map_apply_ιMulti,
    ιMultiDual_apply_ιMulti]
  let e : Fin n ≃ Fin n := Equiv.ofBijective _
    ((Set.powersetCard.ofFinEmbEquiv.symm s).injective.bijective_of_finite)
  have hmat : (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
      ((Matrix.toLin' A ∘ b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) i)) =
      (A.submatrix e e).transpose := by
    ext i j
    simp [b, e, Matrix.toLin'_apply, Matrix.mulVec_single]
  rw [hmat, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]

end exteriorPower

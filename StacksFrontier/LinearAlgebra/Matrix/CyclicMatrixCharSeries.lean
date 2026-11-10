module

public import StacksFrontier.Algebra.Module.Projective.Determinant.InducedCharSeries
public import StacksFrontier.LinearAlgebra.Matrix.CharSeriesTraceDetection

/-!
# The characteristic series of a cyclic matrix

For a ring map `φ : R → M_r(Λ)` and the cyclic matrix `C(d, g)` of size `d + 1` with `g` in the
corner, `det(1 - φ(C(d, g)) T) = det(1 - φ(g) T ^ (d + 1))`. This is the local factor at a closed
point of degree `d + 1` with Frobenius `g`, on the point side of the key lemma
`Stacks.CharSeriesTraceDetection.coeff_det_eq_of_trace_pow`. Blockwise, `φ(C(d, g))` is the
induced endomorphism of `φ(g)`, and the identity is
`ProjectiveDeterminant.det_one_sub_smul_inducedEnd`.
-/

@[expose] public noncomputable section

open PowerSeries Matrix

universe u v

namespace Stacks.CharSeriesTraceDetection

variable {R : Type u} [Ring R] {Λ : Type v} [CommRing Λ] {r : ℕ}
  (φ : R →+* Matrix (Fin r) (Fin r) Λ)

/-- The first row of the cyclic matrix `C(d, g)`: `g` in the last column, `0` elsewhere. -/
theorem cyclicMatrix_zero_apply (d : ℕ) (g : R) (j : Fin (d + 1)) :
    cyclicMatrix d g 0 j = if j = Fin.last d then g else 0 := by
  simp only [cyclicMatrix, Matrix.of_apply, Fin.val_zero, true_and]
  rw [ite_eq_right (by omega)]

/-- The row `k + 1` of the cyclic matrix `C(d, g)`: `1` in column `k`, `0` elsewhere. -/
theorem cyclicMatrix_succ_apply (d : ℕ) (g : R) (k : Fin d) (j : Fin (d + 1)) :
    cyclicMatrix d g k.succ j = if j = k.castSucc then 1 else 0 := by
  simp only [cyclicMatrix, Matrix.of_apply, Fin.val_succ, Fin.succ_ne_zero, false_and,
    ite_false]
  by_cases h : j = k.castSucc
  · rw [ite_eq_left (by rw [h]; simp), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (Fin.ext (by simp; omega))), ite_eq_right h]

/-- The identification of `(Fin (d + 1) → Fin r → S)` with `(Fin r × Fin (d + 1) → S)`. -/
def blockEquiv (S : Type*) [CommRing S] (r d : ℕ) :
    (Fin (d + 1) → Fin r → S) ≃ₗ[S] (Fin r × Fin (d + 1) → S) where
  toFun v p := v p.2 p.1
  invFun w k x := w (x, k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`det(1 - φ(C(d, g)) T) = det(1 - φ(g) T ^ (d + 1))`.** -/
theorem det_one_sub_X_smul_blockMap_cyclicMatrix (d : ℕ) (g : R) :
    (1 - (X : PowerSeries Λ) • (blockMap φ (Fin (d + 1)) (cyclicMatrix d g)).map
      (C (R := Λ))).det =
      (1 - (X : PowerSeries Λ) ^ (d + 1) • (φ g).map (C (R := Λ))).det := by
  nontriviality Λ
  classical
  let S := PowerSeries Λ
  let ψ : (Fin r → S) →ₗ[S] (Fin r → S) := Matrix.toLin' ((φ g).map (C (R := Λ)))
  let L : (Fin (d + 1) → Fin r → S) →ₗ[S] (Fin (d + 1) → Fin r → S) :=
    LinearMap.id - (X : S) • ProjectiveDeterminant.inducedEnd d ψ
  have hInd := ProjectiveDeterminant.det_one_sub_smul_inducedEnd (R := S) (M := Fin r → S) d ψ X
  -- the right-hand side
  have hR : (1 - (X : S) ^ (d + 1) • (φ g).map (C (R := Λ))).det =
      ProjectiveDeterminant.det (LinearMap.id - (X : S) ^ (d + 1) • ψ) := by
    rw [ProjectiveDeterminant.det_eq_linearMap_det_of_basis (Pi.basisFun S (Fin r)),
      ← LinearMap.det_toMatrix' ]
    congr 1
    rw [map_sub, LinearMap.toMatrix'_id, map_smul, LinearMap.toMatrix'_toLin']
  -- the left-hand side
  let b : Module.Basis (Fin (Fintype.card (Fin r × Fin (d + 1)))) S (Fin (d + 1) → Fin r → S) :=
    ((Pi.basisFun S (Fin r × Fin (d + 1))).map (blockEquiv S r d).symm).reindex
      (Fintype.equivFin _)
  have hL : (1 - (X : S) • (blockMap φ (Fin (d + 1)) (cyclicMatrix d g)).map (C (R := Λ))).det =
      ProjectiveDeterminant.det L := by
    rw [ProjectiveDeterminant.det_eq_linearMap_det_of_basis b,
      ← LinearMap.det_conj L (blockEquiv S r d), ← LinearMap.det_toMatrix']
    congr 1
    refine Matrix.ext fun p q => ?_
    rw [LinearMap.toMatrix'_apply]
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, map_sub, map_smul,
      Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul, LinearEquiv.apply_symm_apply, Pi.single_apply]
    congr 2
    obtain ⟨x, k⟩ := p
    obtain ⟨y, j⟩ := q
    change C (blockMap φ (Fin (d + 1)) (cyclicMatrix d g) (x, k) (y, j)) =
      ProjectiveDeterminant.inducedEnd d ψ ((blockEquiv S r d).symm (Pi.single (y, j) 1)) k x
    simp only [blockMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.of_apply]
    refine Fin.cases ?_ (fun k' => ?_) k
    · rw [ProjectiveDeterminant.inducedEnd_apply_zero, cyclicMatrix_zero_apply]
      simp only [ψ, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, blockEquiv,
        LinearEquiv.coe_symm_mk, Matrix.map_apply]
      by_cases hj : j = Fin.last d
      · subst hj
        rw [ite_eq_left rfl, Finset.sum_eq_single y]
        · simp
        · intro y' _ hy'
          rw [Pi.single_apply, ite_eq_right (fun h => hy' (congrArg Prod.fst h)), mul_zero]
        · simp
      · rw [ite_eq_right hj, map_zero, Matrix.zero_apply, map_zero]
        refine (Finset.sum_eq_zero fun y' _ => ?_).symm
        rw [Pi.single_apply, ite_eq_right (fun h => hj (congrArg Prod.snd h).symm), mul_zero]
    · rw [ProjectiveDeterminant.inducedEnd_apply_succ, cyclicMatrix_succ_apply]
      simp only [blockEquiv, LinearEquiv.coe_symm_mk, Pi.single_apply]
      by_cases hj : j = k'.castSucc
      · subst hj
        rw [ite_eq_left rfl, map_one, Matrix.one_apply]
        by_cases hxy : x = y
        · subst hxy; simp
        · rw [ite_eq_right hxy, map_zero, ite_eq_right (fun h => hxy (congrArg Prod.fst h))]
      · rw [ite_eq_right hj, map_zero, Matrix.zero_apply, map_zero,
          ite_eq_right (fun h => hj (congrArg Prod.snd h).symm)]
  rw [hL, hR, ← hInd]

end Stacks.CharSeriesTraceDetection

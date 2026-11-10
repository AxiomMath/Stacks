module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EigenvalueAlgebraicity
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Frobenius spectra under a twisted-equivariant perfect pairing

Poincaré duality for a smooth projective variety `X` of dimension `d` over a finite field with
`q` elements is a perfect pairing
`Hⁱ(X_k̄, ℱ) × H^{2d-i}(X_k̄, ℱ^∨) → ℚ_ℓ(-d)`,
equivariant for the geometric Frobenius `π_X^*`, which acts on the Tate twist `ℚ_ℓ(-d)` as
multiplication by `q ^ d`.  Read on the two cohomology groups, equivariance says
`⟨π_X^* a, π_X^* b⟩ = q ^ d ⟨a, b⟩`.

This file turns that equation into the statement about spectra the theorem of Deligne,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), uses: every eigenvalue `α` of the
Frobenius on the first group is matched with the eigenvalue `q ^ d / α` of the Frobenius on the
second.  Combined with the weight bound in both degrees this gives purity.

## Main results

* `Stacks.EtaleCohomology.hasEigenvalue_div_of_pairing`: if a left-nondegenerate pairing
  `B : V × W → K` satisfies `B (f v) (g w) = c * B v w` with `c ≠ 0` and `W` is
  finite-dimensional, every eigenvalue `α` of `f` gives the eigenvalue `c / α` of `g`.
* `Stacks.EtaleCohomology.isPureOfWeight_of_pairing`: mixedness of weight at most `i` for `f`
  and of weight at most `2 * d - i` for `g`, together with such a pairing with `c = q ^ d`, give
  purity of weight `i` for `f`.

## Implementation notes

Only nondegeneracy on the left and finite-dimensionality of the right-hand space are used; a
perfect pairing of finite-dimensional spaces has both.  No invertibility of `f` or `g` is
assumed: that eigenvalues of `f` are nonzero follows from the equation and `c ≠ 0`.

The scalar `q ^ d` is nonzero in the coefficient field as soon as there is a ring homomorphism
`ι` to `ℂ`, which is how the weights are measured, so no characteristic hypothesis is needed.
-/

@[expose] public section

open scoped Matrix

namespace Stacks.EtaleCohomology

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- **Eigenvalues under a twisted-equivariant pairing.**  Let `B : V × W → K` be a bilinear
pairing which is nondegenerate on the left, `W` finite-dimensional, and let `f`, `g` be
endomorphisms with `B (f v) (g w) = c * B v w` for a nonzero scalar `c`.  Then every eigenvalue
`α` of `f` is nonzero and `c / α` is an eigenvalue of `g`. -/
public theorem hasEigenvalue_div_of_pairing [FiniteDimensional K W]
    {B : V →ₗ[K] W →ₗ[K] K} (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    {f : Module.End K V} {g : Module.End K W} {c : K}
    (hfg : ∀ v w, B (f v) (g w) = c * B v w) (hc : c ≠ 0)
    {α : K} (hα : f.HasEigenvalue α) : g.HasEigenvalue (c / α) := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hfv : f v = α • v := hv.apply_eq_smul
  have hrel : ∀ w, α * B v (g w) = c * B v w := fun w => by
    rw [← hfg v w, hfv, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hα0 : α ≠ 0 := by
    rintro rfl
    refine hv0 (hB v fun w => ?_)
    have h := hrel w
    rw [zero_mul, eq_comm, mul_eq_zero] at h
    exact h.resolve_left hc
  by_contra hg
  have he : Module.End.eigenspace g (c / α) = ⊥ :=
    not_not.1 (Module.End.hasEigenvalue_iff.not.1 hg)
  rw [Module.End.eigenspace_def] at he
  have hsurj : Function.Surjective (g - (c / α) • (1 : Module.End K W)) :=
    LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 he)
  refine hv0 (hB v fun w => ?_)
  obtain ⟨u, rfl⟩ := hsurj w
  have hgu : B v (g u) = c / α * B v u := by
    rw [div_mul_eq_mul_div, eq_div_iff hα0, mul_comm, hrel u]
  simp [hgu]

/-- A natural number `q > 1` has nonzero image in `K` when `K` admits a ring map to `ℂ`, so
`(q : K) ^ d ≠ 0`. -/
private theorem zpow_natCast_ne_zero {q : ℕ} (ι : K →+* ℂ) (d : ℤ) (hq : 1 < q) :
    (q : K) ^ d ≠ 0 := by
  refine zpow_ne_zero d fun h => ?_
  have h' := congrArg ι h
  rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
  omega

/-- **Purity from a twisted-equivariant pairing.**  If the Frobenius `f` on `Hⁱ` is mixed of
weight at most `i`, the Frobenius `g` on the cohomology of the dual sheaf in degree `2 * d - i`
is mixed of weight at most `2 * d - i`, and a pairing `B`, nondegenerate on the left, satisfies
`B (f v) (g w) = q ^ d * B v w` — the Frobenius equivariance of Poincaré duality, `π_X^*` acting
on the Tate twist `K(-d)` by `q ^ d` — then `f` is pure of weight `i`. -/
public theorem isPureOfWeight_of_pairing [FiniteDimensional K W] {q : ℕ} {ι : K →+* ℂ}
    {i d : ℤ} {f : Module.End K V} {g : Module.End K W}
    (hf : IsMixedOfWeightLE q ι i f) (hg : IsMixedOfWeightLE q ι (2 * d - i) g)
    {B : V →ₗ[K] W →ₗ[K] K} (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hfg : ∀ v w, B (f v) (g w) = (q : K) ^ d * B v w) (hq : 1 < q) :
    IsPureOfWeight q ι i f := by
  exact isPureOfWeight_of_duality hf hg
    (fun α hα => hasEigenvalue_div_of_pairing hB hfg (zpow_natCast_ne_zero ι d hq) hα) hq

/-! ### All eigenvalues, read in `ℂ` -/

/-- The endomorphism `f` is pure of weight `w`, relative to `q` and an embedding `ι` of the
coefficient field in `ℂ`: every complex root of its characteristic polynomial read along `ι` is a
`q`-Weil number of weight `w`. This sees every eigenvalue of `f` in an algebraic closure of `K`,
as `Stacks.EtaleCohomology.IsCharpolyMixedOfWeightLE` does. -/
public def IsCharpolyPureOfWeight [FiniteDimensional K V] (q : ℕ) (ι : K →+* ℂ) (w : ℤ)
    (f : Module.End K V) : Prop :=
  ∀ z : ℂ, (f.charpoly.map ι).IsRoot z → IsWeilNumber q w z

/-- **Complex eigenvalues under a twisted-equivariant perfect pairing.**  Let `B : V × W → K` be a
perfect pairing of finite-dimensional spaces and `f`, `g` endomorphisms with
`B (f v) (g w) = c * B v w`, `c ≠ 0`.  Then for every embedding `ι : K →+* ℂ`, every complex root
`z` of the characteristic polynomial of `f` along `ι` is nonzero and `ι c / z` is a root of that
of `g`.  In the basis of `W` dual to a basis of `V` the matrices `A` of `f` and `C` of `g`
satisfy `Aᵀ C = c`, and `Aᵀ (ι c / z - C) = (ι c / z) (Aᵀ - z)` over `ℂ`. -/
public theorem isRoot_div_charpoly_of_isPerfPair [FiniteDimensional K V] [FiniteDimensional K W]
    {B : V →ₗ[K] W →ₗ[K] K} [B.IsPerfPair] {f : Module.End K V} {g : Module.End K W} {c : K}
    (hfg : ∀ v w, B (f v) (g w) = c * B v w) (hc : c ≠ 0) (ι : K →+* ℂ) {z : ℂ}
    (hz : (f.charpoly.map ι).IsRoot z) : z ≠ 0 ∧ (g.charpoly.map ι).IsRoot (ι c / z) := by
  classical
  let φ : W ≃ₗ[K] Module.Dual K V :=
    LinearEquiv.ofBijective B.flip (LinearMap.IsPerfPair.bijective_right B)
  let bV := Module.finBasis K V
  let bW : Module.Basis (Fin (Module.finrank K V)) K W := bV.dualBasis.map φ.symm
  have hbW : ∀ w k, bW.repr w k = B (bV k) w := fun w k => by
    simp only [bW, Module.Basis.map_repr, LinearEquiv.trans_apply, Module.Basis.dualBasis_repr]
    rfl
  have hpair : ∀ i j, B (bV i) (bW j) = if j = i then 1 else 0 := fun i j => by
    have : B (bV i) (bW j) = φ (bW j) (bV i) := rfl
    rw [this]
    simp only [bW, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      Module.Basis.dualBasis_apply_self]
    by_cases h : i = j <;> simp [h, eq_comm]
  set A := LinearMap.toMatrix bV bV f
  set C := LinearMap.toMatrix bW bW g
  have hAC : Aᵀ * C = Matrix.scalar _ c := by
    ext i j
    rw [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    have hsum : ∀ y : W, B (f (bV i)) y = ∑ k, A k i * B (bV k) y := fun y => by
      conv_lhs => rw [← bV.sum_repr (f (bV i))]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, A,
        LinearMap.toMatrix_apply]
    have := hsum (g (bW j))
    rw [hfg, hpair] at this
    simp only [Matrix.transpose_apply, C, LinearMap.toMatrix_apply, hbW]
    rw [← this]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  set A' := A.map ι
  set C' := C.map ι
  have hAC' : A'ᵀ * C' = Matrix.scalar _ (ι c) := by
    have := congrArg (fun M => M.map ι) hAC
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [this]
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  have hdetA : A'.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAC'
    rw [Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.scalar_apply,
      Matrix.det_diagonal, Finset.prod_const] at this
    exact pow_ne_zero _ ((map_ne_zero ι).2 hc) this.symm
  have hfA : f.charpoly.map ι = A'.charpoly := by
    rw [← LinearMap.charpoly_toMatrix f bV, ← Matrix.charpoly_map]
  have hgC : g.charpoly.map ι = C'.charpoly := by
    rw [← LinearMap.charpoly_toMatrix g bW, ← Matrix.charpoly_map]
  rw [hfA, Polynomial.IsRoot, Matrix.eval_charpoly] at hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_sub, Matrix.det_neg, mul_eq_zero] at hz
    exact hdetA (hz.resolve_left (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)))
  refine ⟨hz0, ?_⟩
  rw [hgC, Polynomial.IsRoot, Matrix.eval_charpoly]
  have key : A'ᵀ * (Matrix.scalar _ (ι c / z) - C') =
      (ι c / z) • (A'ᵀ - Matrix.scalar _ z) := by
    rw [Matrix.mul_sub, hAC', smul_sub]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    split_ifs with h
    · subst h; field_simp
    · ring
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_transpose] at hdet
  have hzA : (A'ᵀ - Matrix.scalar _ z).det = 0 := by
    have : A'ᵀ - Matrix.scalar _ z = -(Matrix.scalar _ z - A')ᵀ := by
      rw [Matrix.transpose_sub, Matrix.scalar_apply, Matrix.diagonal_transpose, neg_sub]
    rw [this, Matrix.det_neg, Matrix.det_transpose, hz, mul_zero]
  rw [hzA, mul_zero] at hdet
  exact (mul_eq_zero.1 hdet).resolve_left hdetA

/-- **Purity of all eigenvalues from a twisted-equivariant perfect pairing.**  If every complex
eigenvalue of the Frobenius `f` on `Hⁱ` has weight at most `i`, every complex eigenvalue of the
Frobenius `g` on the cohomology of the dual sheaf in degree `2 * d - i` has weight at most
`2 * d - i`, and a perfect pairing `B` satisfies `B (f v) (g w) = q ^ d * B v w`, then every
complex eigenvalue of `f` is a `q`-Weil number of weight exactly `i`. -/
public theorem isCharpolyPureOfWeight_of_isPerfPair [FiniteDimensional K V]
    [FiniteDimensional K W] {q : ℕ} {ι : K →+* ℂ} {i d : ℤ} {f : Module.End K V}
    {g : Module.End K W} (hf : IsCharpolyMixedOfWeightLE q ι i f)
    (hg : IsCharpolyMixedOfWeightLE q ι (2 * d - i) g) {B : V →ₗ[K] W →ₗ[K] K} [B.IsPerfPair]
    (hfg : ∀ v w, B (f v) (g w) = (q : K) ^ d * B v w) (hq : 1 < q) :
    IsCharpolyPureOfWeight q ι i f := by
  intro z hz
  obtain ⟨hz0, hroot⟩ := isRoot_div_charpoly_of_isPerfPair hfg (zpow_natCast_ne_zero ι d hq) ι hz
  obtain ⟨w, hwi, hw⟩ := hf z hz
  obtain ⟨w', hw'i, hw'⟩ := hg _ hroot
  have hmap : ι ((q : K) ^ d) = (q : ℂ) ^ d := by rw [map_zpow₀, map_natCast]
  rw [hmap] at hw'
  have hw'eq : w' = 2 * d - w := hw'.weight_unique (hw.zpow_div (lt_trans zero_lt_one hq) d) hq
  have hweq : w = i := le_antisymm hwi (by omega)
  exact hweq ▸ hw

end Stacks.EtaleCohomology

end

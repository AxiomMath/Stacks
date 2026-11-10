module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharPolynomial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRootsExact

/-!
# Eigenvalues from an identity of local factors

If the local factor `det(1 - A T)` of an invertible matrix is a finite product of local factors
`det(1 - B_x T ^ (d_x))`, then every eigenvalue `z` of `A` (over any field into which the
coefficients are mapped) has a power `z ^ (d_x)` which is an eigenvalue of some `B_x`: evaluate
both sides at `T = z⁻¹`.  If moreover every `B_x` has Frobenius weights at most `w` relative to
`q ^ (d_x)`, then `A` has weights at most `w` relative to `q`.

This reads the Frobenius weights of `H⁰(X_k̄, F ⊗ ℚ_ℓ)` for a zero-dimensional `X` off the identity
`L(X, F) = det(1 - π_X^* T | H⁰)⁻¹` of [Tag 03V0](https://stacks.math.columbia.edu/tag/03V0), the
L-function being the finite Euler product `∏_x det(1 - π_x T ^ (deg x) | F_x̄)⁻¹`, in the
zero-dimensional step of the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves.

## Main results

* `Stacks.EtaleCohomology.eval₂_localCharPolynomial`.
* `Stacks.EtaleCohomology.exists_isRoot_charpoly_pow_of_localCharSeries_eq_prod`.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_of_localCharSeries_eq_prod`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.EtaleCohomology

variable {K L : Type*} [Field K] [Field L] {n : Type*} [Fintype n] [DecidableEq n]

/-- Evaluating the polynomial local factor: `det(1 - A T ^ d)` at `T = t` along `ι` is
`det(1 - t ^ d A)`. -/
public theorem eval₂_localCharPolynomial (ι : K →+* L) (A : Matrix n n K) (d : ℕ) (t : L) :
    (localCharPolynomial A d).eval₂ ι t = (1 - t ^ d • A.map ι).det := by
  rw [localCharPolynomial, ← Polynomial.coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, localCharPolyMatrix_apply]
  split_ifs with hij <;> simp [Matrix.sub_apply, Matrix.smul_apply, hij] <;> ring

/-- `det(1 - c A) = c ^ n · charpoly(A)(c⁻¹)` for `c ≠ 0`. -/
private lemma det_one_sub_smul_eq (A : Matrix n n L) {c : L} (hc : c ≠ 0) :
    (1 - c • A).det = c ^ Fintype.card n * A.charpoly.eval c⁻¹ := by
  have hs : c • Matrix.scalar n c⁻¹ = (1 : Matrix n n L) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.one_apply, hij, hc]
  rw [Matrix.eval_charpoly, ← Matrix.det_smul, smul_sub, hs]

/-- **Eigenvalues from an identity of local factors.**  If
`det(1 - A T) = ∏_x det(1 - B_x T ^ (d_x))` with `A` invertible, then for every root `z` of the
characteristic polynomial of `A` read along `ι`, some `z ^ (d_x)` is a root of that of `B_x`. -/
public theorem exists_isRoot_charpoly_pow_of_localCharSeries_eq_prod (ι : K →+* L)
    (A : Matrix n n K) (hA : IsUnit A.det) {ιs : Type*} (s : Finset ιs) {m : ιs → Type*}
    [∀ x, Fintype (m x)] [∀ x, DecidableEq (m x)] (Bx : ∀ x, Matrix (m x) (m x) K) (d : ιs → ℕ)
    (h : localCharSeries A 1 = ∏ x ∈ s, localCharSeries (Bx x) (d x)) {z : L}
    (hz : (A.charpoly.map ι).IsRoot z) : ∃ x ∈ s, ((Bx x).charpoly.map ι).IsRoot (z ^ d x) := by
  have hpoly : localCharPolynomial A 1 = ∏ x ∈ s, localCharPolynomial (Bx x) (d x) := by
    apply Polynomial.coe_inj.1
    rw [coe_localCharPolynomial, h]
    have hm := map_prod (Polynomial.coeToPowerSeries.ringHom (R := K))
      (fun x => localCharPolynomial (Bx x) (d x)) s
    simp only [Polynomial.coeToPowerSeries.ringHom_apply] at hm
    rw [hm]
    exact Finset.prod_congr rfl fun x _ => (coe_localCharPolynomial (Bx x) (d x)).symm
  rw [← Matrix.charpoly_map, Polynomial.IsRoot] at hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.diagonal_zero, zero_sub, Matrix.det_neg,
      show (A.map ι).det = ι A.det from (RingHom.map_det ι A).symm] at hz
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ((map_ne_zero ι).2 hA.ne_zero) hz
  have hev := congrArg (fun P => P.eval₂ ι z⁻¹) hpoly
  simp only [eval₂_localCharPolynomial, Polynomial.eval₂_finsetProd, pow_one] at hev
  rw [det_one_sub_smul_eq _ (inv_ne_zero hz0), inv_inv, hz, mul_zero] at hev
  obtain ⟨x, hx, hx0⟩ := Finset.prod_eq_zero_iff.1 hev.symm
  refine ⟨x, hx, ?_⟩
  rw [← Matrix.charpoly_map, Polynomial.IsRoot]
  rw [det_one_sub_smul_eq _ (pow_ne_zero _ (inv_ne_zero hz0)), inv_pow, inv_inv] at hx0
  exact (mul_eq_zero.1 hx0).resolve_left (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hz0)))

/-- **Weights from an identity of local factors.**  In the situation of
`Stacks.EtaleCohomology.exists_isRoot_charpoly_pow_of_localCharSeries_eq_prod`, if every
characteristic root of `B_x` along `ι` has absolute value `(q ^ (d_x)) ^ (w' / 2)` with `w' ≤ b`,
every characteristic root of `A` has absolute value `q ^ (w' / 2)` with `w' ≤ b`. -/
public theorem isCharpolyNormMixedOfWeightLE_of_localCharSeries_eq_prod {q : ℕ} (ι : K →+* ℂ)
    {b : ℤ} (A : Matrix n n K) (hA : IsUnit A.det) {ιs : Type*} (s : Finset ιs) {m : ιs → Type*}
    [∀ x, Fintype (m x)] [∀ x, DecidableEq (m x)] (Bx : ∀ x, Matrix (m x) (m x) K) (d : ιs → ℕ)
    (hd : ∀ x ∈ s, d x ≠ 0)
    (h : localCharSeries A 1 = ∏ x ∈ s, localCharSeries (Bx x) (d x))
    (hB : ∀ x ∈ s, ∀ y : ℂ, ((Bx x).charpoly.map ι).IsRoot y →
      ∃ w' ≤ b, ‖y‖ = ((q ^ d x : ℕ) : ℝ) ^ ((w' : ℝ) / 2)) (z : ℂ)
    (hz : (A.charpoly.map ι).IsRoot z) : ∃ w' ≤ b, ‖z‖ = (q : ℝ) ^ ((w' : ℝ) / 2) := by
  obtain ⟨x, hx, hzx⟩ := exists_isRoot_charpoly_pow_of_localCharSeries_eq_prod ι A hA s Bx d h hz
  obtain ⟨w', hw', hzm⟩ := hB x hx _ hzx
  refine ⟨w', hw', ?_⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hrhs : ((q ^ d x : ℕ) : ℝ) ^ ((w' : ℝ) / 2) = ((q : ℝ) ^ ((w' : ℝ) / 2)) ^ d x := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0,
      ← Real.rpow_mul hq0, mul_comm]
  rw [norm_pow, hrhs] at hzm
  exact (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hq0 _) (hd x hx)).1 hzm

end Stacks.EtaleCohomology

end

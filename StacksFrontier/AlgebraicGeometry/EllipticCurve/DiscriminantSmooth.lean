module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Smooth.Locus
public import StacksFrontier.RingTheory.Smooth.PlaneHypersurface

/-!
# A Weierstrass curve with smooth affine equation has nonzero discriminant

Let `W` be a Weierstrass curve over a field `k`, with affine equation
`f = y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆ ∈ k[x, y]`.  If the plane curve `k[x, y] ⧸ (f)` is
smooth over `k`, then the discriminant `Δ` of `W` is nonzero.

## Main definitions

* `Stacks.WeierstrassDiscriminant.affineEquation`: the dehomogenization at `z = 1` of Mathlib's
  homogeneous Weierstrass polynomial, an element of `k[x, y] = MvPolynomial (Fin 2) k`.

## Main results

* `Stacks.WeierstrassDiscriminant.affineEquation_eq`: the affine equation written out.
* `Stacks.WeierstrassDiscriminant.exists_singular_of_Δ_eq_zero`: over an algebraically closed
  field a Weierstrass curve with `Δ = 0` has an affine point at which both partial derivatives of
  its equation vanish.
* `Stacks.WeierstrassDiscriminant.Δ_ne_zero_of_forall_isMaximal`: if every maximal ideal
  containing `f` misses one of `∂f/∂x`, `∂f/∂y`, then `Δ ≠ 0`.
* `Stacks.WeierstrassDiscriminant.Δ_ne_zero_of_smooth`: if `k[x, y] ⧸ (f)` is smooth over `k`,
  then `Δ ≠ 0`.
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks.WeierstrassDiscriminant

variable {k : Type u} [Field k]

/-- The affine equation `y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆` of a Weierstrass curve, the
dehomogenization at `z = 1` of its homogeneous cubic, in the variables `x = X 0`, `y = X 1`. -/
def affineEquation (W : WeierstrassCurve k) : MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, 1] W.toProjective.polynomial

/-- The affine equation of a Weierstrass curve, written out. -/
theorem affineEquation_eq (W : WeierstrassCurve k) :
    affineEquation W = X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1
      - (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆) := by
  simp [affineEquation, WeierstrassCurve.Projective.polynomial, MvPolynomial.algebraMap_eq]

/-- The partial derivative of the affine equation in `x`. -/
theorem pderiv_zero_affineEquation (W : WeierstrassCurve k) :
    pderiv 0 (affineEquation W) = C W.a₁ * X 1 - (3 * X 0 ^ 2 + 2 * C W.a₂ * X 0 + C W.a₄) := by
  simp only [Fin.isValue, affineEquation_eq, map_sub, map_add, Derivation.leibniz_pow,
    Nat.add_one_sub_one, pow_one, pderiv_X, ne_eq, one_ne_zero, not_false_eq_true,
    Pi.single_eq_of_ne, smul_eq_mul, mul_zero, Derivation.leibniz, Pi.single_eq_same, mul_one,
    derivation_C, add_zero, zero_add, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The partial derivative of the affine equation in `y`. -/
theorem pderiv_one_affineEquation (W : WeierstrassCurve k) :
    pderiv 1 (affineEquation W) = 2 * X 1 + C W.a₁ * X 0 + C W.a₃ := by
  simp [affineEquation_eq]

/-- The affine equation of a Weierstrass curve is nonzero. -/
theorem affineEquation_ne_zero (W : WeierstrassCurve k) : affineEquation W ≠ 0 := by
  intro h
  have := congrArg (fun p => (MvPolynomial.aeval ![(0 : Polynomial k), Polynomial.X] p).coeff 2) h
  simp [affineEquation_eq] at this

section Singular

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field in which `2 ≠ 0`, a Weierstrass curve with vanishing
discriminant has an affine point at which both partial derivatives of its equation vanish. -/
theorem exists_singular_of_two_ne_zero (h2 : (2 : K) ≠ 0) (W : WeierstrassCurve K)
    (hΔ : W.Δ = 0) :
    ∃ x y : K, W.toAffine.Equation x y ∧ W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 ∧
      2 * y + W.a₁ * x + W.a₃ = 0 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := h4
  obtain ⟨r, s, t, h3⟩ := (Cubic.splits_iff_roots_eq_three (φ := RingHom.id K) ha).mp
    (by simpa using IsAlgClosed.splits W.twoTorsionPolynomial.toPoly)
  have hd : ¬ (r ≠ s ∧ r ≠ t ∧ s ≠ t) := by
    rw [← Cubic.discr_ne_zero_iff_roots_ne ha h3, W.twoTorsionPolynomial_discr, hΔ, mul_zero]
    simp
  have hb := Cubic.b_eq_three_roots ha h3
  have hc := Cubic.c_eq_three_roots ha h3
  have hdd := Cubic.d_eq_three_roots ha h3
  simp only [RingHom.id_apply, WeierstrassCurve.twoTorsionPolynomial] at hb hc hdd
  obtain ⟨x, u, hb', hc', hd'⟩ : ∃ x u : K, W.b₂ = 4 * -(2 * x + u) ∧
      2 * W.b₄ = 4 * (x ^ 2 + 2 * x * u) ∧ W.b₆ = 4 * -(x ^ 2 * u) := by
    rcases eq_or_ne r s with hrs | hrs
    · subst hrs
      exact ⟨r, t, by linear_combination hb, by linear_combination hc, by linear_combination hdd⟩
    rcases eq_or_ne r t with hrt | hrt
    · subst hrt
      exact ⟨r, s, by linear_combination hb, by linear_combination hc, by linear_combination hdd⟩
    have hst : s = t := by tauto
    subst hst
    exact ⟨s, r, by linear_combination hb, by linear_combination hc, by linear_combination hdd⟩
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hb' hc' hd'
  have hy : 2 * (-(W.a₁ * x + W.a₃) / 2) + W.a₁ * x + W.a₃ = 0 := by
    field_simp
    ring
  set y := -(W.a₁ * x + W.a₃) / 2
  refine ⟨x, y, ?_, ?_, hy⟩
  · rw [WeierstrassCurve.Affine.equation_iff']
    refine eq_zero_of_ne_zero_of_mul_left_eq_zero h4 ?_
    linear_combination (2 * y + W.a₁ * x + W.a₃) * hy - x ^ 2 * hb' - x * hc' - hd'
  · refine eq_zero_of_ne_zero_of_mul_left_eq_zero h4 ?_
    linear_combination 2 * W.a₁ * hy - 2 * x * hb' - hc'

/-- Over an algebraically closed field in which `2 = 0`, a Weierstrass curve with vanishing
discriminant has an affine point at which both partial derivatives of its equation vanish. -/
theorem exists_singular_of_two_eq_zero (h2 : (2 : K) = 0) (W : WeierstrassCurve K)
    (hΔ : W.Δ = 0) :
    ∃ x y : K, W.toAffine.Equation x y ∧ W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 ∧
      2 * y + W.a₁ * x + W.a₃ = 0 := by
  rcases W with ⟨a₁, a₂, a₃, a₄, a₆⟩
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at hΔ
  simp only [WeierstrassCurve.Affine.equation_iff']
  rcases eq_or_ne a₁ 0 with ha₁ | ha₁
  · subst ha₁
    have ha₃ : a₃ = 0 := by
      refine pow_eq_zero_iff (n := 4) (by norm_num) |>.mp ?_
      linear_combination hΔ - (-216 * a₆ ^ 2 - 32 * a₄ ^ 3 - 108 * a₃ ^ 2 * a₆ -
        14 * a₃ ^ 4 + 144 * a₂ * a₄ * a₆ + 36 * a₂ * a₃ ^ 2 * a₄ + 8 * a₂ ^ 2 * a₄ ^ 2 -
        32 * a₂ ^ 3 * a₆ - 8 * a₂ ^ 3 * a₃ ^ 2) * h2
    subst ha₃
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-a₄) (n := 2) (by norm_num)
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) (n := 2)
      (by norm_num)
    refine ⟨x, y, by linear_combination hy, by linear_combination -hx - (x ^ 2 + a₂ * x) * h2,
      by linear_combination y * h2⟩
  · obtain ⟨x, hx⟩ : ∃ x, a₃ = a₁ * x := ⟨a₃ / a₁, by field_simp⟩
    obtain ⟨y, hy⟩ : ∃ y, a₄ = a₁ * y - x ^ 2 := ⟨(x ^ 2 + a₄) / a₁, by field_simp; ring⟩
    subst hx hy
    refine ⟨x, y, ?_, by linear_combination -(x ^ 2 + a₂ * x) * h2,
      by linear_combination (y + a₁ * x) * h2⟩
    refine eq_zero_of_ne_zero_of_mul_left_eq_zero (pow_ne_zero 6 ha₁) ?_
    linear_combination hΔ - (32 * x ^ 6 - 216 * a₆ ^ 2 - 144 * a₂ * a₆ * x ^ 2 +
      8 * a₂ ^ 2 * x ^ 4 - 32 * a₂ ^ 3 * a₆ - 96 * a₁ * x ^ 4 * y +
      144 * a₁ * a₂ * a₆ * y - 16 * a₁ * a₂ ^ 2 * x ^ 2 * y + 96 * a₁ ^ 2 * x ^ 2 * y ^ 2 -
      48 * a₁ ^ 2 * x ^ 5 - 144 * a₁ ^ 2 * a₆ * x ^ 2 - 32 * a₁ ^ 2 * a₂ * x ^ 4 +
      72 * a₁ ^ 2 * a₂ * a₆ * x + 8 * a₁ ^ 2 * a₂ ^ 2 * y ^ 2 - 8 * a₁ ^ 2 * a₂ ^ 2 * x ^ 3 -
      24 * a₁ ^ 2 * a₂ ^ 2 * a₆ - 8 * a₁ ^ 2 * a₂ ^ 3 * x ^ 2 - 32 * a₁ ^ 3 * y ^ 3 +
      96 * a₁ ^ 3 * x ^ 3 * y + 36 * a₁ ^ 3 * a₆ * y + 28 * a₁ ^ 3 * a₂ * x ^ 2 * y +
      8 * a₁ ^ 3 * a₂ ^ 2 * x * y - 48 * a₁ ^ 4 * x * y ^ 2 + 2 * a₁ ^ 4 * x ^ 4 +
      18 * a₁ ^ 4 * a₆ * x + 4 * a₁ ^ 4 * a₂ * y ^ 2 + 14 * a₁ ^ 4 * a₂ * x ^ 3 -
      6 * a₁ ^ 4 * a₂ * a₆ - 4 * a₁ ^ 4 * a₂ ^ 2 * x ^ 2 - 16 * a₁ ^ 5 * x ^ 2 * y +
      4 * a₁ ^ 5 * a₂ * x * y) * h2

/-- Over an algebraically closed field, a Weierstrass curve with `Δ = 0` has an affine point on it
at which both partial derivatives `a₁y - (3x² + 2a₂x + a₄)` and `2y + a₁x + a₃` of its equation
vanish. -/
theorem exists_singular_of_Δ_eq_zero (W : WeierstrassCurve K) (hΔ : W.Δ = 0) :
    ∃ x y : K, W.toAffine.Equation x y ∧ W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0 ∧
      2 * y + W.a₁ * x + W.a₃ = 0 :=
  (em ((2 : K) = 0)).elim (exists_singular_of_two_eq_zero · W hΔ)
    (exists_singular_of_two_ne_zero · W hΔ)

end Singular

/-- If every maximal ideal of `k[x, y]` containing the affine equation of `W` misses one of its two
partial derivatives, then the discriminant of `W` is nonzero. -/
theorem Δ_ne_zero_of_forall_isMaximal {W : WeierstrassCurve k}
    (h : ∀ m : Ideal (MvPolynomial (Fin 2) k), m.IsMaximal → affineEquation W ∈ m →
      ∃ i, MvPolynomial.pderiv i (affineEquation W) ∉ m) : W.Δ ≠ 0 := by
  intro hΔ
  obtain ⟨x, y, hE, hX, hY⟩ := exists_singular_of_Δ_eq_zero (W.baseChange (AlgebraicClosure k))
    (by rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, hΔ, map_zero])
  rw [WeierstrassCurve.Affine.equation_iff'] at hE
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hE hX hY
  let φ : MvPolynomial (Fin 2) k →+* AlgebraicClosure k := (aeval ![x, y]).toRingHom
  have hφ : φ.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (C : k →+* MvPolynomial (Fin 2) k) φ ?_
    have hcomp : φ.comp C = algebraMap k (AlgebraicClosure k) := by
      ext a
      simp [φ]
    rw [hcomp]
    exact fun a => Algebra.IsIntegral.isIntegral (R := k) a
  have hm : (RingHom.ker φ).IsMaximal :=
    RingHom.ker_eq_comap_bot φ ▸ Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφ ⊥
  obtain ⟨i, hi⟩ := h _ hm (by simpa [φ, affineEquation_eq] using hE)
  apply hi
  rw [RingHom.mem_ker]
  fin_cases i
  · simpa [φ, pderiv_zero_affineEquation] using hX
  · simpa [φ, pderiv_one_affineEquation] using hY

/-- If `k[x, y] ⧸ (y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆)` is smooth over `k`, then the
discriminant of `W` is nonzero. -/
theorem Δ_ne_zero_of_smooth {W : WeierstrassCurve k}
    [Algebra.Smooth k (MvPolynomial (Fin 2) k ⧸ Ideal.span {affineEquation W})] : W.Δ ≠ 0 := by
  refine Δ_ne_zero_of_forall_isMaximal fun m hm hfm => ?_
  have hfu : ¬ IsUnit (affineEquation W) := fun hu =>
    hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hfm hu)
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {affineEquation W})) ≤ m := by
    rwa [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
  have hQ := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
  obtain ⟨i, hi⟩ := (Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem (affineEquation_ne_zero W)
    hfu (m.map (Ideal.Quotient.mk _))).mp inferInstance
  exact ⟨i, by rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, sup_of_le_left hker] at hi⟩

end Stacks.WeierstrassDiscriminant

end

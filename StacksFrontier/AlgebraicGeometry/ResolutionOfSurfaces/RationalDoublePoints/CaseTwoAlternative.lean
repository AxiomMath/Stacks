module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChangeOfGenerators

/-!
# Reaching case II of the rational double point discussion

The discussion of rational double points splits into two cases according to the quadratic form

`q = Σᵢ≤ⱼ āᵢⱼ tᵢtⱼ ∈ κ[t₁, t₂, t₃]`

attached to the quadratic relation `Σ aᵢⱼ xᵢxⱼ = Σ aᵢⱼₖ xᵢxⱼxₖ` among three generators of the
maximal ideal: case II is the case that `q` is an element of `κ*` times the square of a linear
form, and case I is everything else.

This file shows that if the dehomogenization `q(1, y₂, y₃)` lies in the square of an ideal of
`κ[y₂, y₃]` of colength greater than one, then `q` is a nonzero scalar times the square of a
nonzero linear form, and derives the normal form `x₃² = Σ aᵢⱼₖ xᵢxⱼxₖ` of case II.

## Main results

* `AlgebraicGeometry.sum_quadratic_congr_of_symm`: a quadratic expression in three ring elements
  depends on its coefficient matrix only through the diagonal and the sums `aₚᵩ + aᵩₚ`.
* `AlgebraicGeometry.coeffs_of_eq_smul_sq_affineLinear`: the six coefficients of a scalar multiple
  of the square of an affine linear polynomial in two variables.
* `AlgebraicGeometry.ne_zero_of_eq_smul_sq_affineLinear`: such a polynomial with a nonzero
  coefficient has a nonzero scalar and a nonzero linear part.
* `AlgebraicGeometry.exists_rankOne_of_dehomogenized_mem_sq`: the quadratic form is `c · (Σ lₚtₚ)²`
  once its dehomogenization lies in the square of an ideal of colength greater than one.
* `AlgebraicGeometry.exists_sq_eq_cubicExpansion_of_rankOne_residue`: the case II normal form
  `x₃² = Σ aᵢⱼₖ xᵢxⱼxₖ` from that rank one hypothesis, for the residues of a quadratic relation
  over a local ring.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BGD](https://stacks.math.columbia.edu/tag/0BGD)
-/

@[expose] public section

open IsLocalRing MvPolynomial

universe u

namespace AlgebraicGeometry

/-! ### Symmetrizing the coefficient matrix of a quadratic expression -/

/-- A quadratic expression in three ring elements depends on its coefficient matrix only through
the diagonal entries and the sums `aₚᵩ + aᵩₚ` of the off-diagonal ones. -/
public theorem sum_quadratic_congr_of_symm {R : Type*} [CommRing R] (x : Fin 3 → R)
    (a a' : Fin 3 → Fin 3 → R) (hdiag : ∀ p, a p p = a' p p)
    (hoff : ∀ p q, p < q → a p q + a q p = a' p q + a' q p) :
    ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, a' p q * (x p * x q) := by
  have h01 := hoff 0 1 (by decide)
  have h02 := hoff 0 2 (by decide)
  have h12 := hoff 1 2 (by decide)
  simp only [Fin.sum_univ_three]
  linear_combination (x 0 * x 0) * hdiag 0 + (x 1 * x 1) * hdiag 1 + (x 2 * x 2) * hdiag 2 +
    (x 0 * x 1) * h01 + (x 0 * x 2) * h02 + (x 1 * x 2) * h12

/-! ### The coefficients of a scalar times the square of an affine linear polynomial -/

/-- Equality of two elements of `Fin 2 →₀ ℕ` is equality of their two values. -/
private theorem finsupp_fin_two_eq_iff (m n : Fin 2 →₀ ℕ) : m = n ↔ m 0 = n 0 ∧ m 1 = n 1 := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]

/-- The six-term quadratic polynomial in two variables, written with its monomials. -/
private theorem sixTerm_eq_monomialSum {k : Type*} [Field k] (a b c d e f : k) :
    (C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
        C e * X 0 * X 1 + C f * X 1 ^ 2 : MvPolynomial (Fin 2) k) =
      monomial 0 a + monomial (Finsupp.single 0 1) b + monomial (Finsupp.single 1 1) c +
        monomial (Finsupp.single 0 2) d +
        monomial (Finsupp.single 0 1 + Finsupp.single 1 1) e +
        monomial (Finsupp.single 1 2) f := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.C_apply, MvPolynomial.C_apply,
    MvPolynomial.C_apply, MvPolynomial.C_apply, MvPolynomial.C_apply, MvPolynomial.C_apply,
    MvPolynomial.monomial_pow, MvPolynomial.monomial_pow, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
  norm_num [Finsupp.smul_single, MvPolynomial.C_mul_monomial]

/-- A scalar times the square of an affine linear polynomial in two variables, expanded into the
six-term form. -/
private theorem smul_sq_affineLinear_eq {k : Type*} [Field k] (j g h i : k) :
    (C j * (C g + C h * X 0 + C i * X 1) ^ 2 : MvPolynomial (Fin 2) k) =
      C (j * g ^ 2) + C (2 * (j * g * h)) * X 0 + C (2 * (j * g * i)) * X 1 +
        C (j * h ^ 2) * X 0 ^ 2 + C (2 * (j * h * i)) * X 0 * X 1 +
        C (j * i ^ 2) * X 1 ^ 2 := by
  simp only [map_mul, map_pow, map_ofNat]
  ring

/-- The six coefficients of a scalar multiple of the square of an affine linear polynomial in two
variables. Together they say that the homogeneous quadratic form
`a t₁² + b t₁t₂ + c t₁t₃ + d t₂² + e t₂t₃ + f t₃²` is `j · (g t₁ + h t₂ + i t₃)²`. -/
public theorem coeffs_of_eq_smul_sq_affineLinear {k : Type*} [Field k] (a b c d e f j g h i : k)
    (hid : (C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
        C e * X 0 * X 1 + C f * X 1 ^ 2 : MvPolynomial (Fin 2) k) =
      C j * (C g + C h * X 0 + C i * X 1) ^ 2) :
    a = j * g ^ 2 ∧ b = 2 * (j * g * h) ∧ c = 2 * (j * g * i) ∧
      d = j * h ^ 2 ∧ e = 2 * (j * h * i) ∧ f = j * i ^ 2 := by
  rw [smul_sq_affineLinear_eq, sixTerm_eq_monomialSum, sixTerm_eq_monomialSum] at hid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  [have hco := congrArg (MvPolynomial.coeff (0 : Fin 2 →₀ ℕ)) hid;
    have hco := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1)) hid;
    have hco := congrArg (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)) hid;
    have hco := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)) hid;
    have hco := congrArg
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)) hid;
    have hco := congrArg (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 2)) hid] <;>
  · simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial] at hco
    norm_num [finsupp_fin_two_eq_iff] at hco
    linear_combination hco

/-- A scalar multiple of the square of an affine linear polynomial in two variables which has a
nonzero coefficient has a nonzero scalar, and its linear polynomial has a nonzero coefficient. -/
public theorem ne_zero_of_eq_smul_sq_affineLinear {k : Type*} [Field k] (a b c d e f j g h i : k)
    (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0)
    (hid : (C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
        C e * X 0 * X 1 + C f * X 1 ^ 2 : MvPolynomial (Fin 2) k) =
      C j * (C g + C h * X 0 + C i * X 1) ^ 2) :
    j ≠ 0 ∧ (g ≠ 0 ∨ h ≠ 0 ∨ i ≠ 0) := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    coeffs_of_eq_smul_sq_affineLinear a b c d e f j g h i hid
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp at hnonzero
  · by_contra! ⟨rfl, rfl, rfl⟩
    simp at hnonzero

/-! ### The quadratic form is of rank one -/

/-- If some entry on or above the diagonal of a `3 × 3` matrix is nonzero, then one of `a 0 0`,
`a 0 1`, `a 0 2`, `a 1 1`, `a 1 2` and `a 2 2` is nonzero. -/
public theorem ne_zero_of_exists_ne_zero {k : Type*} [Field k] (a : Fin 3 → Fin 3 → k)
    (hunit : ∃ p q, p ≤ q ∧ a p q ≠ 0) :
    a 0 0 ≠ 0 ∨ a 0 1 ≠ 0 ∨ a 0 2 ≠ 0 ∨ a 1 1 ≠ 0 ∨ a 1 2 ≠ 0 ∨ a 2 2 ≠ 0 := by
  obtain ⟨p, q, hpq, hne⟩ := hunit
  fin_cases p <;> fin_cases q <;> simp_all

/-- An identity `a + b X₀ + c X₁ + d X₀² + e X₀X₁ + f X₁² = j (g + h X₀ + i X₁)²` among
polynomials in variables indexed by `ℕ` also holds among polynomials in variables indexed by
`Fin 2`. -/
private theorem eq_smul_sq_affineLinear_finTwo_of_nat {k : Type*} [Field k]
    (a b c d e f j g h i : k)
    (hid : (C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
        C e * X 0 * X 1 + C f * X 1 ^ 2 : MvPolynomial ℕ k) =
      C j * (C g + C h * X 0 + C i * X 1) ^ 2) :
    (C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
        C e * X 0 * X 1 + C f * X 1 ^ 2 : MvPolynomial (Fin 2) k) =
      C j * (C g + C h * X 0 + C i * X 1) ^ 2 := by
  set φ : MvPolynomial ℕ k →+* MvPolynomial (Fin 2) k :=
    (MvPolynomial.aeval (R := k) fun n : ℕ =>
      if n = 0 then (X 0 : MvPolynomial (Fin 2) k) else if n = 1 then X 1 else 0).toRingHom
    with hφ
  have hX0 : φ (X 0) = X 0 := by simp [hφ]
  have hX1 : φ (X 1) = X 1 := by simp [hφ]
  have hC : ∀ t : k, φ (C t) = C t := fun t => by simp [hφ]
  simpa only [map_add, map_mul, map_pow, hX0, hX1, hC] using congrArg φ hid

/-- If the dehomogenization of the quadratic form with upper triangular matrix `a` is a scalar
times the square of an affine linear polynomial, and some entry of `a` is nonzero, then the form
is `c · (Σ lₚtₚ)²` for a nonzero `c` and a nonzero `l`: `a` has `c lₚ²` on the diagonal and
`2 c lₚlᵩ` above it. -/
public theorem exists_rankOne_of_eq_smul_sq_affineLinear {k : Type*} [Field k]
    (a : Fin 3 → Fin 3 → k)
    (hnonzero : a 0 0 ≠ 0 ∨ a 0 1 ≠ 0 ∨ a 0 2 ≠ 0 ∨ a 1 1 ≠ 0 ∨ a 1 2 ≠ 0 ∨ a 2 2 ≠ 0)
    (j g h i : k)
    (hid : (C (a 0 0) + C (a 0 1) * X 0 + C (a 0 2) * X 1 + C (a 1 1) * X 0 ^ 2 +
        C (a 1 2) * X 0 * X 1 + C (a 2 2) * X 1 ^ 2 : MvPolynomial (Fin 2) k) =
      C j * (C g + C h * X 0 + C i * X 1) ^ 2) :
    ∃ (c : k) (l : Fin 3 → k), c ≠ 0 ∧ l ≠ 0 ∧
      (∀ p, a p p = c * l p * l p) ∧ (∀ p q, p < q → a p q = 2 * (c * l p * l q)) := by
  obtain ⟨hc00, hc01, hc02, hc11, hc12, hc22⟩ := coeffs_of_eq_smul_sq_affineLinear
    (a 0 0) (a 0 1) (a 0 2) (a 1 1) (a 1 2) (a 2 2) j g h i hid
  obtain ⟨hj, hl⟩ := ne_zero_of_eq_smul_sq_affineLinear
    (a 0 0) (a 0 1) (a 0 2) (a 1 1) (a 1 2) (a 2 2) j g h i hnonzero hid
  refine ⟨j, ![g, h, i], hj, fun hz => by simp_all, fun p => ?_, fun p q hpq => ?_⟩
  · fin_cases p <;> simp [hc00, hc11, hc22, pow_two, mul_assoc]
  · fin_cases p <;> fin_cases q <;> simp_all

/-- Let `a` be the matrix of a quadratic
form in three variables over a field, with a nonzero entry on or above the diagonal. Suppose the
dehomogenization

`q(1, y₂, y₃) = a₁₁ + a₁₂y₂ + a₁₃y₃ + a₂₂y₂² + a₂₃y₂y₃ + a₃₃y₃²`

lies in the square of an ideal `I ⊆ k[y₂, y₃]` of colength greater than one. Then the form is
`c · (Σ lₚtₚ)²` for a nonzero scalar `c` and a nonzero linear form `l`. -/
public theorem exists_rankOne_of_dehomogenized_mem_sq {k : Type*} [Field k]
    (a : Fin 3 → Fin 3 → k) (hunit : ∃ p q, p ≤ q ∧ a p q ≠ 0)
    (I : Ideal (MvPolynomial (Fin 2) k))
    (hcolength : 1 < Module.rank k (MvPolynomial (Fin 2) k ⧸ I))
    (hmem : (C (a 0 0) + C (a 0 1) * X 0 + C (a 0 2) * X 1 + C (a 1 1) * X 0 ^ 2 +
      C (a 1 2) * X 0 * X 1 + C (a 2 2) * X 1 ^ 2 : MvPolynomial (Fin 2) k) ∈ I ^ 2) :
    ∃ (c : k) (l : Fin 3 → k), c ≠ 0 ∧ l ≠ 0 ∧
      (∀ p, a p p = c * l p * l p) ∧ (∀ p q, p < q → a p q = 2 * (c * l p * l q)) := by
  have hnonzero := ne_zero_of_exists_ne_zero a hunit
  obtain ⟨j, g, h, i, hi⟩ := eq_smul_sq_affineLinear_of_mem_ideal_sq I
    (a 0 0) (a 0 1) (a 0 2) (a 1 1) (a 1 2) (a 2 2) hnonzero hmem hcolength
  exact exists_rankOne_of_eq_smul_sq_affineLinear a hnonzero j g h i
    (eq_smul_sq_affineLinear_finTwo_of_nat _ _ _ _ _ _ j g h i hi)

/-! ### The normal form of case II from a rank one quadratic form -/

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Let `x₁, x₂, x₃` generate the maximal ideal of a local ring and
satisfy a quadratic relation `Σ aₚᵩ xₚxᵩ = Σ aₚᵩᵣ xₚxᵩxᵣ` with `a` upper triangular, and suppose
the quadratic form the residues of `a` present is `c · (Σ lₚtₚ)²` for a nonzero scalar `c` and a
nonzero linear form `l`, that is, the residues of `a` are `c lₚ²` on the diagonal and `2 c lₚlᵩ`
above it. Then after a change of the generators the relation reads `x₃² = Σ aₚᵩᵣ xₚxᵩxᵣ`. -/
public theorem exists_sq_eq_cubicExpansion_of_rankOne_residue (x : Fin 3 → A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A)
    (hupper : ∀ p q, q < p → a p q = 0)
    (hrel : ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r))
    (c : ResidueField A) (hc : c ≠ 0) (l : Fin 3 → ResidueField A) (hl : l ≠ 0)
    (hdiag : ∀ p, residue A (a p p) = c * l p * l p)
    (hoff : ∀ p q, p < q → residue A (a p q) = 2 * (c * l p * l q)) :
    ∃ (x' : Fin 3 → A) (b' : Fin 3 → Fin 3 → Fin 3 → A),
      Ideal.span (Set.range x') = maximalIdeal A ∧
        x' 2 * x' 2 = ∑ p, ∑ q, ∑ r, b' p q r * (x' p * x' q * x' r) := by
  obtain ⟨a', ha'⟩ := exists_map_residue_eq (A := A) (Matrix.of fun p q => c * l p * l q)
  have ha'res : ∀ p q, residue A (a' p q) = c * l p * l q := fun p q =>
    congrFun (congrFun ha' p) q
  obtain ⟨s, hsdiag, hslt, hsgt⟩ :
      ∃ s : Fin 3 → Fin 3 → A, (∀ p, s p p = a' p p) ∧
        (∀ p q, p < q → s p q = a' p q + a' q p) ∧ (∀ p q, q < p → s p q = 0) := by
    refine ⟨fun p q => if p = q then a' p p else if p < q then a' p q + a' q p else 0,
      fun p => by simp, fun p q hpq => ?_, fun p q hpq => ?_⟩
    · simp [ne_of_lt hpq, hpq]
    · simp [ne_of_gt hpq, asymm hpq]
  have hsym : ∑ p, ∑ q, a' p q * (x p * x q) = ∑ p, ∑ q, s p q * (x p * x q) := by
    refine sum_quadratic_congr_of_symm x a' s (fun p => (hsdiag p).symm) fun p q hpq => ?_
    rw [hslt p q hpq, hsgt q p hpq]
    ring
  have hdiff : ∀ p q, a p q - s p q ∈ maximalIdeal A := by
    intro p q
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    rcases lt_trichotomy p q with hlt | heq | hgt
    · rw [hslt p q hlt, map_add, ha'res p q, ha'res q p, mul_right_comm c (l q) (l p),
        hoff p q hlt, two_mul]
    · subst heq
      rw [hsdiag p, ha'res p p, hdiag p]
    · rw [hsgt p q hgt, hupper p q hgt]
  obtain ⟨b'', hb''⟩ := exists_quadraticRelation_sub x hspan a s b hdiff hrel
  exact exists_span_eq_and_sq_eq_cubicExpansion x hspan a' b'' c hc l hl ha'res
    (hsym.trans hb'')

end AlgebraicGeometry

end

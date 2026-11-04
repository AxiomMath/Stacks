module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseTwoAlternative
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GoodCoordinate

/-!
# The dichotomy of Section 54.12, and what each case yields

Section 54.12 attaches to a rational double point a quadratic form

`q = Σᵢ≤ⱼ āᵢⱼ tᵢtⱼ ∈ κ[t₁, t₂, t₃]`,

the reduction of a quadratic relation `Σ aᵢⱼ xᵢxⱼ = Σ aᵢⱼₖ xᵢxⱼxₖ` among three generators of the
maximal ideal, and distinguishes case II, where `q` is an element of `κ*` times the square of a
linear form, from case I, where it is not. In case II the generators can be changed so that the
relation reads `x₃² = Σ aᵢⱼₖ xᵢxⱼxₖ`. In case I a singular point of the blowup whose residue field
is strictly larger than `κ` would put the form in case II, so every singular point of the
exceptional curve is `κ`-rational. Generators are indexed from `0`: the source's `x₁` has index `0`
and its `x₃` has index `2`.

## Main results

* `AlgebraicGeometry.isScalarSqLinear_of_upperTriangular`: an upper triangular coefficient matrix
  presented as `aₚₚ = c lₚ²`, `aₚᵩ = 2 c lₚlᵩ` satisfies `AlgebraicGeometry.IsScalarSqLinear`.
* `AlgebraicGeometry.isScalarSqLinear_of_dehomogenized_mem_sq`: if the dehomogenization
  `q(1, y₂, y₃)` lies in the square of an ideal of colength greater than one, the form is in
  case II.
* `AlgebraicGeometry.rank_le_one_of_not_isScalarSqLinear`: **the Claim of Section 54.12.** In
  case I an ideal whose square contains `q(1, y₂, y₃)` has colength at most one.
* `AlgebraicGeometry.exists_sq_eq_cubicExpansion_of_isScalarSqLinear`: **the normal form of
  case II.**
* `AlgebraicGeometry.IsScalarSqLinear.restrictFirstVar` and
  `AlgebraicGeometry.IsGoodCoordinateForm.not_isScalarSqLinear`: setting a variable to zero in a
  scalar times the square of a linear form leaves one, so a good coordinate exists only in case I.
* `AlgebraicGeometry.isGoodCoordinateForm_of_upperTriangular`: the good coordinate of the source,
  for an upper triangular form in case I whose first row vanishes.
* `AlgebraicGeometry.exists_generators_and_quadraticRelation`: from the dimension formula
  `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1` at `n = 1, 2`, three generators of the maximal ideal and the quadratic
  relation they satisfy.
* `AlgebraicGeometry.exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear`: **the dichotomy.**
  Either the singularity admits generators in the case II normal form `x₃² = Σ aᵢⱼₖ xᵢxⱼxₖ`, or it
  admits generators whose quadratic relation is in case I.

## References

* [Stacks Project, Tag 0BGB](https://stacks.math.columbia.edu/tag/0BGB)
* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
* [Stacks Project, Tag 0BGD](https://stacks.math.columbia.edu/tag/0BGD)
-/

@[expose] public section

open IsLocalRing MvPolynomial

universe u

namespace AlgebraicGeometry

/-! ### The upper triangular presentation of case II -/

/-- An upper triangular coefficient matrix given in the source's presentation of case II —
`aₚₚ = c lₚ²` on the diagonal and `aₚᵩ = 2 c lₚlᵩ` above it — presents a quadratic form which is a
scalar times the square of a linear form. The entries below the diagonal vanish, so the sums
`aₚᵩ + aᵩₚ` which `AlgebraicGeometry.IsScalarSqLinear` constrains are the entries above it. -/
public theorem isScalarSqLinear_of_upperTriangular {k : Type*} [CommRing k] {n : ℕ}
    {a : Fin n → Fin n → k} (hupper : ∀ p q, q < p → a p q = 0) (c : k) (l : Fin n → k)
    (hdiag : ∀ p, a p p = c * l p * l p)
    (hoff : ∀ p q, p < q → a p q = 2 * (c * l p * l q)) :
    IsScalarSqLinear a :=
  ⟨c, l, hdiag, fun p q hpq => by rw [hoff p q hpq, hupper q p hpq, add_zero]⟩

/-! ### Case II from a singular point of the exceptional curve -/

/-- **Case II from a singular point of the exceptional curve.** Let `a` be the upper triangular
coefficient matrix of the quadratic form of the singularity, with a nonzero entry on or above the
diagonal, and suppose the dehomogenization

`q(1, y₂, y₃) = a₁₁ + a₁₂y₂ + a₁₃y₃ + a₂₂y₂² + a₂₃y₂y₃ + a₃₃y₃²`

lies in the square of an ideal `I ⊆ k[y₂, y₃]` of colength greater than one. Then the form is in
case II. -/
public theorem isScalarSqLinear_of_dehomogenized_mem_sq {k : Type*} [Field k]
    (a : Fin 3 → Fin 3 → k) (hupper : ∀ p q, q < p → a p q = 0)
    (hunit : ∃ p q, p ≤ q ∧ a p q ≠ 0) (I : Ideal (MvPolynomial (Fin 2) k))
    (hcolength : 1 < Module.rank k (MvPolynomial (Fin 2) k ⧸ I))
    (hmem : (C (a 0 0) + C (a 0 1) * X 0 + C (a 0 2) * X 1 + C (a 1 1) * X 0 ^ 2 +
      C (a 1 2) * X 0 * X 1 + C (a 2 2) * X 1 ^ 2 : MvPolynomial (Fin 2) k) ∈ I ^ 2) :
    IsScalarSqLinear a := by
  obtain ⟨c, l, -, -, hdiag, hoff⟩ :=
    exists_rankOne_of_dehomogenized_mem_sq a hunit I hcolength hmem
  exact isScalarSqLinear_of_upperTriangular hupper c l hdiag hoff

/-- **The Claim of Section 54.12.** Suppose the quadratic form of the singularity is in case I:
its upper triangular coefficient matrix has a nonzero entry on or above the diagonal and is not a
scalar times the square of a linear form. Then any ideal `I ⊆ k[y₂, y₃]` whose square contains the
dehomogenization `q(1, y₂, y₃)` has colength at most one. -/
public theorem rank_le_one_of_not_isScalarSqLinear {k : Type*} [Field k]
    (a : Fin 3 → Fin 3 → k) (hupper : ∀ p q, q < p → a p q = 0)
    (hunit : ∃ p q, p ≤ q ∧ a p q ≠ 0) (hcase : ¬ IsScalarSqLinear a)
    (I : Ideal (MvPolynomial (Fin 2) k))
    (hmem : (C (a 0 0) + C (a 0 1) * X 0 + C (a 0 2) * X 1 + C (a 1 1) * X 0 ^ 2 +
      C (a 1 2) * X 0 * X 1 + C (a 2 2) * X 1 ^ 2 : MvPolynomial (Fin 2) k) ∈ I ^ 2) :
    Module.rank k (MvPolynomial (Fin 2) k ⧸ I) ≤ 1 :=
  le_of_not_gt fun hcon =>
    hcase (isScalarSqLinear_of_dehomogenized_mem_sq a hupper hunit I hcon hmem)

/-! ### Setting a variable to zero, and good coordinates -/

variable {k : Type*} [CommRing k] {n : ℕ}

/-- Setting the first variable to zero in a quadratic form which is a scalar times the square of a
linear form leaves one: the linear form loses its first term. -/
public theorem IsScalarSqLinear.restrictFirstVar {a : Fin (n + 1) → Fin (n + 1) → k}
    (h : IsScalarSqLinear a) :
    IsScalarSqLinear (AlgebraicGeometry.restrictFirstVar a) := by
  obtain ⟨c, l, hdiag, hoff⟩ := h
  exact ⟨c, fun p => l p.succ, fun p => hdiag p.succ,
    fun p q hpq => hoff p.succ q.succ (Fin.succ_lt_succ_iff.mpr hpq)⟩

/-- **A good coordinate exists only in case I.** If the quadratic form were a scalar times the
square of a linear form, so would be the form obtained by setting the first variable to zero, and
then the first generator would not be a good coordinate. -/
public theorem IsGoodCoordinateForm.not_isScalarSqLinear {a : Fin (n + 1) → Fin (n + 1) → k}
    (h : IsGoodCoordinateForm a) : ¬ IsScalarSqLinear a :=
  fun hcon => h hcon.restrictFirstVar

/-- **A good coordinate exists, for an upper triangular form.** If the quadratic form is not a
scalar times the square of a linear form — the source's case I — and the coefficients of the first
row vanish, then the first generator is a good coordinate. -/
public theorem isGoodCoordinateForm_of_upperTriangular {a : Fin (n + 1) → Fin (n + 1) → k}
    (hupper : ∀ p q, q < p → a p q = 0) (hrow : ∀ q, a 0 q = 0)
    (ha : ¬ IsScalarSqLinear a) : IsGoodCoordinateForm a :=
  isGoodCoordinateForm_of_not_isScalarSqLinear hrow
    (fun p => by
      rcases eq_or_ne p 0 with rfl | hp
      exacts [hrow 0, hupper p 0 (Fin.pos_iff_ne_zero.2 hp)])
    ha

/-- The good coordinate of the source for a ternary form, with its three conditions written out:
the coefficients of `t₁²`, `t₁t₂` and `t₁t₃` vanish. -/
public theorem isGoodCoordinateForm_of_upperTriangular_fin_three
    {a : Fin 3 → Fin 3 → k} (hupper : ∀ p q, q < p → a p q = 0)
    (h00 : a 0 0 = 0) (h01 : a 0 1 = 0) (h02 : a 0 2 = 0)
    (ha : ¬ IsScalarSqLinear a) : IsGoodCoordinateForm a :=
  isGoodCoordinateForm_of_upperTriangular hupper
    (fun q => by fin_cases q <;> assumption)
    ha

/-! ### The normal form of case II -/

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **The normal form of case II.** Let `x₁, x₂, x₃` generate the maximal ideal of a local ring
and satisfy a quadratic relation `Σ aₚᵩ xₚxᵩ = Σ aₚᵩᵣ xₚxᵩxᵣ` with `a` upper triangular and one
entry on or above the diagonal a unit, and suppose the quadratic form the residues of `a` present
is in case II. Then after a change of the generators the relation reads `x₃² = Σ aₚᵩᵣ xₚxᵩxᵣ`. -/
public theorem exists_sq_eq_cubicExpansion_of_isScalarSqLinear (x : Fin 3 → A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A)
    (hupper : ∀ p q, q < p → a p q = 0)
    (hunit : ∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal A)
    (hrel : ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r))
    (hcase : IsScalarSqLinear fun p q => residue A (a p q)) :
    ∃ (x' : Fin 3 → A) (b' : Fin 3 → Fin 3 → Fin 3 → A),
      Ideal.span (Set.range x') = maximalIdeal A ∧
        x' 2 * x' 2 = ∑ p, ∑ q, ∑ r, b' p q r * (x' p * x' q * x' r) := by
  obtain ⟨p, q, hpq, hne⟩ := hunit
  obtain ⟨c, l, hc, hl, hdiag, hoff⟩ := hcase.exists_ne_zero_of_upperTriangular
    (fun p q hqp => by rw [hupper p q hqp, map_zero])
    ⟨p, q, hpq, fun h => hne ((residue_eq_zero_iff (a p q)).mp h)⟩
  exact exists_sq_eq_cubicExpansion_of_rankOne_residue x hspan a b hupper hrel c hc l hl hdiag hoff

/-! ### The quadratic form of the singularity, and the dichotomy -/

/-- **The quadratic relation of Section 54.12.** Given the source's dimension formula
`dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1` at `n = 1` and `n = 2`, the maximal ideal of a Noetherian local ring is
generated by three elements, and the six products `xₚxᵩ` with `p ≤ q`, outnumbering
`dim_κ(𝔪²/𝔪³) = 5`, satisfy a relation modulo `𝔪³` whose coefficient matrix is upper triangular
with one entry on or above the diagonal a unit. -/
public theorem exists_generators_and_quadraticRelation [IsNoetherianRing A]
    (h1 : Module.finrank (ResidueField A) (gradedPiece A 1) = 3)
    (h2 : Module.finrank (ResidueField A) (gradedPiece A 2) = 5) :
    ∃ (x : Fin 3 → A) (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A),
      Ideal.span (Set.range x) = maximalIdeal A ∧ (∀ p q, q < p → a p q = 0) ∧
        (∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal A) ∧
        ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r) := by
  obtain ⟨x, hspan⟩ := exists_span_eq_maximalIdeal_of_finrank_cotangentSpace
    (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) (finrank_gradedPiece_one.symm.trans h1)
  obtain ⟨a, b, hupper, hunit, hrel⟩ :=
    exists_quadraticRelation_cubicExpansion (by rw [h2]; norm_num) x hspan
  exact ⟨x, a, b, hspan, hupper, hunit, hrel⟩

/-- **The dichotomy of Section 54.12.** Given the source's dimension formula at `n = 1` and
`n = 2`, a Noetherian local ring falls into one of two cases. In case II there are generators
`x₁, x₂, x₃` of the maximal ideal with `x₃² = Σ aₚᵩᵣ xₚxᵩxᵣ`, the normal form from which the
source's case II analysis proceeds. In case I there are generators satisfying a quadratic relation
whose coefficient matrix is upper triangular with a unit entry and whose quadratic form is not a
scalar times the square of a linear form. -/
public theorem exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear [IsNoetherianRing A]
    (h1 : Module.finrank (ResidueField A) (gradedPiece A 1) = 3)
    (h2 : Module.finrank (ResidueField A) (gradedPiece A 2) = 5) :
    (∃ (x : Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A),
        Ideal.span (Set.range x) = maximalIdeal A ∧
          x 2 * x 2 = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r)) ∨
      ∃ (x : Fin 3 → A) (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A),
        Ideal.span (Set.range x) = maximalIdeal A ∧ (∀ p q, q < p → a p q = 0) ∧
          (∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal A) ∧
          (∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r)) ∧
          ¬ IsScalarSqLinear fun p q => residue A (a p q) := by
  obtain ⟨x, a, b, hspan, hupper, hunit, hrel⟩ := exists_generators_and_quadraticRelation h1 h2
  by_cases hcase : IsScalarSqLinear fun p q => residue A (a p q)
  · exact Or.inl
      (exists_sq_eq_cubicExpansion_of_isScalarSqLinear x hspan a b hupper hunit hrel hcase)
  · exact Or.inr ⟨x, a, b, hspan, hupper, hunit, hrel, hcase⟩

end AlgebraicGeometry

end

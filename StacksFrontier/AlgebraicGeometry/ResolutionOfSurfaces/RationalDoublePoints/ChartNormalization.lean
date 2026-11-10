module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpResidueField

/-!
# Moving the singular point of the blowup to the origin of the first chart

Section 54.12 of the source attaches to a rational double point the quadratic form

`q = Σᵢ≤ⱼ āᵢⱼ tᵢtⱼ ∈ κ[t₁, t₂, t₃]`

of a quadratic relation `Σ aᵢⱼ xᵢxⱼ = Σ aᵢⱼₖ xᵢxⱼxₖ` among three generators of the maximal
ideal, and then, in case I, performs a step which the rest of the discussion rests on: it chooses
the generators so that the singular point of the blowup is the origin of the chart `A[𝔪/x₁]`.
There the point is cut out by `(y₂, y₃)`, and singularity forces `q(1, y₂, y₃) ∈ (y₂, y₃)²`, that
is

`ā₁₁ = ā₁₂ = ā₁₃ = 0`,

the vanishing of the first row and column of the quadratic form. That vanishing is what makes
`x₁` a good coordinate, by `AlgebraicGeometry.isGoodCoordinateForm_of_upperTriangular_fin_three`,
and it is the same normalization that makes the point `κ`-rational.

This file performs the coordinate change. The input is a point of the first chart, given as a
proper ideal `I ⊆ κ[y₂, y₃]` whose square contains the dehomogenization `q(1, y₂, y₃)`; the
output is a new system of generators of the maximal ideal whose quadratic relation has a
vanishing first row, so that its first generator is a good coordinate. Nothing is assumed about
the point beyond that membership: in case I the Claim of the source,
`AlgebraicGeometry.bijective_algebraMap_quotient_of_not_isScalarSqLinear`, already forces the
point to be `κ`-rational, hence to be cut out by `(y₂ - c₂, y₃ - c₃)`, and the substitution

`t₁ = s₁,  t₂ = c₂ s₁ + s₂,  t₃ = c₃ s₁ + s₃`

moves it to the origin.

## Main definitions

* `AlgebraicGeometry.chartTranslation`: the matrix of that substitution. It is unipotent lower
  triangular, so its determinant is `1` and it is invertible over any commutative ring; the
  inverse substitution is `AlgebraicGeometry.chartTranslation (-u) (-v)`.

## Main results

* `AlgebraicGeometry.isScalarSqLinear_congr`: whether a coefficient matrix presents a scalar
  times the square of a linear form depends only on its diagonal entries and on the sums
  `aₚᵩ + aᵩₚ` — the data the quadratic expression itself sees.
* `AlgebraicGeometry.exists_eval_eq_zero_of_bijective_algebraMap_quotient`: an ideal of
  `κ[y₂, y₃]` with quotient `κ` is contained in the kernel of an evaluation, so it is the ideal
  of a `κ`-rational point.
* `AlgebraicGeometry.exists_chartPoint_of_not_isScalarSqLinear`: **the `κ`-rational point of the
  chart, with the three identities it satisfies.** In case I, an ideal whose square contains
  `q(1, y₂, y₃)` produces `c₂, c₃ ∈ κ` at which `q(1, y₂, y₃)` and both its partial derivatives
  vanish. The source reads this as: the singular point of the exceptional curve is `κ`-rational
  and is a singular point of the curve.
* `AlgebraicGeometry.transportForm_chartTranslation_entries`: the nine coefficients of the
  quadratic form after the substitution.
* `AlgebraicGeometry.exists_quadraticRelation_vanishing_first_row`: **the chart normalization.**
  From the point and its three identities, new generators of the maximal ideal whose quadratic
  relation is upper triangular with a unit entry, has `ā₁₁ = ā₁₂ = ā₁₃ = 0` — indeed `a₁₁ = a₁₂ =
  a₁₃ = 0` on the nose — and whose first generator is therefore a good coordinate. The remaining
  four coefficients are unchanged, so the binary form `q(0, t₂, t₃)` is the same before and after
  the move; this is the source's remark that the good coordinate condition does not see the
  coefficients carrying `t₁`.
* `AlgebraicGeometry.exists_isGoodCoordinateForm_of_dehomogenized_mem_sq`: **a good coordinate
  exists, unconditionally in case I.** The same statement with the point replaced by the ideal
  it is cut out by, which is the form the geometry supplies.

## Implementation notes

The vanishing of the first *column* is not asked of the transported matrix, and could not be: in
characteristic two the two off-diagonal entries `ā₁ⱼ` and `āⱼ₁` are not separately determined by
the quadratic form, and the partial derivative of the dehomogenization controls only their sum.
The transported matrix is therefore replaced by its upper triangular symmetrization, which
presents the same quadratic expression by
`AlgebraicGeometry.sum_quadratic_congr_of_symm`, and whose first row has vanishing residues; the
residues are then cleared to honest zeros by
`AlgebraicGeometry.exists_quadraticRelation_sub`, the source's remark that a quadratic term whose
coefficient lies in `𝔪` can be subsumed into the cubic side.

A unit entry on or above the diagonal is not a hypothesis of the normalization but a conclusion
of it: if the three coefficients `a₂₂, a₂₃, a₃₃` all had vanishing residues, the binary form
`q(0, t₂, t₃)` would be zero, hence a scalar times the square of a linear form, and the first
generator would not be a good coordinate.

The dimension formula `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) = 2n + 1` plays no role here; the quadratic relation is a
hypothesis. Which `n` plays the role of the source's `x₁` is fixed by the indexing, as in
`RationalDoublePoints/CaseDichotomy.lean`: the good coordinate condition looks at the form with
the variable of index `0` set to zero.

No `@[stacks]` attribute is attached. The step this file formalizes is unnumbered in the source —
it sits inside the discussion that Tag 0BGE's proof refers to — and the membership
`q(1, y₂, y₃) ∈ I²`, which the source derives from singularity of the blowup at the point cut out
by `I`, is a hypothesis here rather than a consequence; so with that hypothesis added these
statements say less than the source does.

## References

* [Stacks Project, Tag 0BGB](https://stacks.math.columbia.edu/tag/0BGB)
* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
* [Stacks Project, Tag 0BGD](https://stacks.math.columbia.edu/tag/0BGD)
* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace AlgebraicGeometry

/-! ### A quadratic form sees only the diagonal and the off-diagonal sums -/

/-- Whether a coefficient matrix presents a quadratic form which is a scalar times the square of
a linear form depends only on its diagonal entries and on the sums `aₚᵩ + aᵩₚ`: those are the
only combinations the conditions of `AlgebraicGeometry.IsScalarSqLinear` constrain, and by
`AlgebraicGeometry.sum_quadratic_congr_of_symm` they are also the only ones the quadratic
expression sees. -/
public theorem isScalarSqLinear_congr {k : Type*} [CommRing k] {n : ℕ}
    {a a' : Fin n → Fin n → k} (hdiag : ∀ p, a p p = a' p p)
    (hoff : ∀ p q, p < q → a p q + a q p = a' p q + a' q p) :
    IsScalarSqLinear a ↔ IsScalarSqLinear a' :=
  ⟨fun ⟨c, l, hd, ho⟩ => ⟨c, l, fun p => (hdiag p).symm.trans (hd p),
      fun p q hpq => (hoff p q hpq).symm.trans (ho p q hpq)⟩,
    fun ⟨c, l, hd, ho⟩ => ⟨c, l, fun p => (hdiag p).trans (hd p),
      fun p q hpq => (hoff p q hpq).trans (ho p q hpq)⟩⟩

/-! ### The substitution moving a point of the first chart to the origin -/

/-- **The coordinate change of Section 54.12.** The matrix of the linear substitution
`t₁ = s₁`, `t₂ = u s₁ + s₂`, `t₃ = v s₁ + s₃`, which moves the point `(1 : u : v)` of the first
chart to the origin `(1 : 0 : 0)`. It is unipotent lower triangular, and
`AlgebraicGeometry.chartTranslation (-u) (-v)` is its inverse. -/
public def chartTranslation {R : Type*} [CommRing R] (u v : R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; u, 1, 0; v, 0, 1]

/-- The substitution moving a point of the first chart to the origin has determinant `1`. -/
public theorem det_chartTranslation {R : Type*} [CommRing R] (u v : R) :
    (chartTranslation u v).det = 1 := by
  simp [chartTranslation, Matrix.det_fin_three]

/-- The substitution moving a point of the first chart to the origin is invertible over any
commutative ring. -/
public theorem isUnit_det_chartTranslation {R : Type*} [CommRing R] (u v : R) :
    IsUnit (chartTranslation u v).det := by
  simp [det_chartTranslation]

/-- The three rows of the substitution, applied to a family of ring elements. The first row is
the first standard basis vector, so the substitution fixes the first element and translates the
other two by multiples of it. -/
public theorem sum_chartTranslation_mul {R : Type*} [CommRing R] (u v : R) (z : Fin 3 → R) :
    (∑ p, chartTranslation u v 0 p * z p = z 0) ∧
      (∑ p, chartTranslation u v 1 p * z p = u * z 0 + z 1) ∧
      (∑ p, chartTranslation u v 2 p * z p = v * z 0 + z 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [chartTranslation, Fin.sum_univ_three]

/-- Every element of `Fin 3` is `0`, `1` or `2`. -/
private theorem fin_three_cases (r : Fin 3) : r = 0 ∨ r = 1 ∨ r = 2 := by
  revert r
  decide

/-- A ring homomorphism carries the substitution of a point to the substitution of the image
point. -/
public theorem map_chartTranslation {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u v : R) (i p : Fin 3) :
    f (chartTranslation u v i p) = chartTranslation (f u) (f v) i p := by
  rcases fin_three_cases i with rfl | rfl | rfl <;>
    rcases fin_three_cases p with rfl | rfl | rfl <;> simp [chartTranslation]

/-- **The coefficients of the quadratic form after the substitution.** For an upper triangular
coefficient matrix, the nine coefficients of the transported form. The three carrying the first
variable are the dehomogenization `q(1, u, v)` and its two partial derivatives, split between the
entry above the diagonal and the one below it; the remaining four are unchanged, which is why the
binary form `q(0, t₂, t₃)` — and hence the good coordinate condition — survives the
substitution. -/
public theorem transportForm_chartTranslation_entries {R : Type*} [CommRing R] (u v : R)
    (a : Fin 3 → Fin 3 → R) (hupper : ∀ p q, q < p → a p q = 0) :
    (∑ i, ∑ j, a i j * (chartTranslation u v i 0 * chartTranslation u v j 0)
        = a 0 0 + a 0 1 * u + a 0 2 * v + a 1 1 * (u * u) + a 1 2 * (u * v)
          + a 2 2 * (v * v)) ∧
      (∑ i, ∑ j, a i j * (chartTranslation u v i 0 * chartTranslation u v j 1)
        = a 0 1 + a 1 1 * u) ∧
      (∑ i, ∑ j, a i j * (chartTranslation u v i 1 * chartTranslation u v j 0)
        = a 1 1 * u + a 1 2 * v) ∧
      (∑ i, ∑ j, a i j * (chartTranslation u v i 0 * chartTranslation u v j 2)
        = a 0 2 + a 1 2 * u + a 2 2 * v) ∧
      (∑ i, ∑ j, a i j * (chartTranslation u v i 2 * chartTranslation u v j 0)
        = a 2 2 * v) ∧
      (∑ i, ∑ j, a i j * (chartTranslation u v i 1 * chartTranslation u v j 1) = a 1 1) ∧
      (∑ i, ∑ j, a i j * (chartTranslation u v i 1 * chartTranslation u v j 2) = a 1 2) ∧
      (∑ i, ∑ j, a i j * (chartTranslation u v i 2 * chartTranslation u v j 1) = a 2 1) ∧
      (∑ i, ∑ j, a i j * (chartTranslation u v i 2 * chartTranslation u v j 2) = a 2 2) := by
  have h10 := hupper 1 0 (by decide)
  have h20 := hupper 2 0 (by decide)
  have h21 := hupper 2 1 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [chartTranslation, Fin.sum_univ_three, h10, h20, h21]
  ring

/-- The substitution moving a point of the first chart to the origin keeps a quadratic form in
case I: if the image of `a` under a ring homomorphism to a field is not a scalar times the square
of a linear form, neither is the image of the transported matrix. -/
public theorem not_isScalarSqLinear_map_transport_chartTranslation {R K : Type*} [CommRing R]
    [Field K] (f : R →+* K) (a : Fin 3 → Fin 3 → R) (u v : R)
    (hcase : ¬ IsScalarSqLinear fun p q => f (a p q)) :
    ¬ IsScalarSqLinear fun p q =>
      f (∑ i, ∑ j, a i j * (chartTranslation u v i p * chartTranslation u v j q)) := by
  intro hcon
  have heq : (fun p q =>
      f (∑ i, ∑ j, a i j * (chartTranslation u v i p * chartTranslation u v j q)))
      = transportForm (fun i j => f (a i j)) fun i p => chartTranslation (f u) (f v) i p := by
    funext p q
    simp only [transportForm_apply, map_sum, map_mul, map_chartTranslation]
  rw [heq] at hcon
  exact hcase ((isScalarSqLinear_transportForm_matrix_iff _ _
    (isUnit_det_chartTranslation (f u) (f v))).mp hcon)

/-! ### The `κ`-rational point of the chart -/

/-- **An ideal of `κ[y₂, y₃]` with quotient `κ` is the ideal of a `κ`-rational point.** Composing
the inverse of the structure map with the quotient map gives a `κ`-algebra homomorphism to `κ`
which kills the ideal, and every such homomorphism is an evaluation. -/
public theorem exists_eval_eq_zero_of_bijective_algebraMap_quotient {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin 2) k))
    (hbij : Function.Bijective (algebraMap k (MvPolynomial (Fin 2) k ⧸ I))) :
    ∃ c : Fin 2 → k, ∀ f ∈ I, eval c f = 0 := by
  let e : k ≃ₐ[k] (MvPolynomial (Fin 2) k ⧸ I) := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  let φ : MvPolynomial (Fin 2) k →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k I)
  refine ⟨φ ∘ X, fun f hf => ?_⟩
  have hzero : φ f = 0 := by
    have hq : (Ideal.Quotient.mkₐ k I) f = 0 := by
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hf
    change e.symm ((Ideal.Quotient.mkₐ k I) f) = 0
    rw [hq, map_zero]
  have hun := AlgHom.congr_fun (aeval_unique φ) f
  rw [show eval (φ ∘ X) f = aeval (φ ∘ X) f from rfl, ← hun, hzero]

/-- A derivation of a commutative algebra maps the square of an ideal into the ideal: this is the
Leibniz rule applied to products of two elements of the ideal. -/
theorem _root_.Derivation.map_mem_of_mem_ideal_sq {R S : Type*} [CommSemiring R] [CommRing S]
    [Algebra R S] (D : Derivation R S S) (I : Ideal S) {p : S} (hp : p ∈ I ^ 2) : D p ∈ I := by
  rw [pow_two] at hp
  induction hp using Submodule.mul_induction_on' with
  | mem_mul_mem p hp q hq =>
      rw [D.leibniz]
      exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_right _ hq)
  | add p hp q hq ihp ihq =>
      simpa only [map_add] using I.add_mem ihp ihq

/-- **The `κ`-rational point of the chart, and the three identities it satisfies.** Suppose the
quadratic form of the singularity is in case I: its upper triangular coefficient matrix has a
nonzero entry on or above the diagonal and is not a scalar times the square of a linear form. Let
`I` be a proper ideal of `κ[y₂, y₃]` whose square contains the dehomogenization `q(1, y₂, y₃)` —
which is what the source derives from singularity of the blowup at the point of the exceptional
curve cut out by `I`. Then `I` is the ideal of a `κ`-rational point `(c₂, c₃)`, by the Claim of
Section 54.12, and at that point `q(1, y₂, y₃)` vanishes together with both of its partial
derivatives: the point is a singular point of the exceptional curve.

These three identities are exactly the data
`AlgebraicGeometry.exists_quadraticRelation_vanishing_first_row` needs in order to move the point
to the origin. -/
public theorem exists_chartPoint_of_not_isScalarSqLinear {k : Type*} [Field k]
    (a : Fin 3 → Fin 3 → k) (hupper : ∀ p q, q < p → a p q = 0)
    (hunit : ∃ p q, p ≤ q ∧ a p q ≠ 0) (hcase : ¬ IsScalarSqLinear a)
    (I : Ideal (MvPolynomial (Fin 2) k)) (hI : I ≠ ⊤)
    (hmem : (C (a 0 0) + C (a 0 1) * X 0 + C (a 0 2) * X 1 + C (a 1 1) * X 0 ^ 2 +
      C (a 1 2) * X 0 * X 1 + C (a 2 2) * X 1 ^ 2 : MvPolynomial (Fin 2) k) ∈ I ^ 2) :
    ∃ c : Fin 2 → k,
      a 0 0 + a 0 1 * c 0 + a 0 2 * c 1 + a 1 1 * (c 0 * c 0) + a 1 2 * (c 0 * c 1)
          + a 2 2 * (c 1 * c 1) = 0 ∧
        a 0 1 + 2 * (a 1 1 * c 0) + a 1 2 * c 1 = 0 ∧
        a 0 2 + a 1 2 * c 0 + 2 * (a 2 2 * c 1) = 0 := by
  obtain ⟨c, hc⟩ := exists_eval_eq_zero_of_bijective_algebraMap_quotient I
    (bijective_algebraMap_quotient_of_not_isScalarSqLinear a hupper hunit hcase I hI hmem)
  have hD := fun i : Fin 2 => hc _ ((MvPolynomial.pderiv i).map_mem_of_mem_ideal_sq I hmem)
  refine ⟨c, ?_, ?_, ?_⟩
  · have h := hc _ (Ideal.pow_le_self (by norm_num) hmem)
    simp only [map_add, map_mul, map_pow, eval_C, eval_X] at h
    linear_combination h
  all_goals
    simp [mul_comm, mul_left_comm, mul_assoc] at hD
  · linear_combination hD.1
  · linear_combination hD.2

/-! ### The chart normalization -/

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- The generators translated by the substitution moving a point of the first chart to the origin
again generate the maximal ideal, and the substitution recovers the old generators from them. -/
public theorem exists_span_eq_chartTranslation (x : Fin 3 → A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A) (u v : A) :
    ∃ y : Fin 3 → A, Ideal.span (Set.range y) = maximalIdeal A ∧
      y 0 = x 0 ∧ y 1 = x 1 - u * x 0 ∧ y 2 = x 2 - v * x 0 ∧
      ∀ i, x i = ∑ p, chartTranslation u v i p * y p := by
  obtain ⟨y, hy0, hy1, hy2⟩ : ∃ y : Fin 3 → A,
      y 0 = x 0 ∧ y 1 = x 1 - u * x 0 ∧ y 2 = x 2 - v * x 0 :=
    ⟨fun p => if p = 0 then x 0 else if p = 1 then x 1 - u * x 0 else x 2 - v * x 0,
      by simp, by simp, by simp⟩
  have hyM : ∀ i, y i = ∑ p, chartTranslation (-u) (-v) i p * x p := by
    intro i
    obtain ⟨e0, e1, e2⟩ := sum_chartTranslation_mul (-u) (-v) x
    rcases fin_three_cases i with rfl | rfl | rfl
    · rw [e0, hy0]
    · rw [e1, hy1]
      ring
    · rw [e2, hy2]
      ring
  refine ⟨y, (span_range_eq_of_isUnit_det x y (chartTranslation (-u) (-v))
    (isUnit_det_chartTranslation _ _) hyM).trans hspan, hy0, hy1, hy2, fun i => ?_⟩
  obtain ⟨e0, e1, e2⟩ := sum_chartTranslation_mul u v y
  rcases fin_three_cases i with rfl | rfl | rfl
  · rw [e0, hy0]
  · rw [e1, hy0, hy1]
    ring
  · rw [e2, hy0, hy2]
    ring

/-- **Clearing the first row.** If the residues of `T₁₁`, `T₁₂ + T₂₁` and `T₁₃ + T₃₁` vanish, a
quadratic relation with coefficient matrix `T` among generators of the maximal ideal can be
rewritten with an upper triangular matrix whose first row is zero and whose other entries are those
of the upper triangular symmetrization of `T`; that matrix is in case I whenever `T` is. -/
public theorem exists_quadraticRelation_clear_first_row (y : Fin 3 → A)
    (hspan : Ideal.span (Set.range y) = maximalIdeal A)
    (T : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A)
    (hrel : ∑ p, ∑ q, T p q * (y p * y q) = ∑ p, ∑ q, ∑ r, b p q r * (y p * y q * y r))
    (hT00 : residue A (T 0 0) = 0) (hT01 : residue A (T 0 1) + residue A (T 1 0) = 0)
    (hT02 : residue A (T 0 2) + residue A (T 2 0) = 0) :
    ∃ (a' : Fin 3 → Fin 3 → A) (b' : Fin 3 → Fin 3 → Fin 3 → A),
      (∀ p q, q < p → a' p q = 0) ∧ a' 0 0 = 0 ∧ a' 0 1 = 0 ∧ a' 0 2 = 0 ∧
        a' 1 1 = T 1 1 ∧ a' 1 2 = T 1 2 + T 2 1 ∧ a' 2 2 = T 2 2 ∧
        (∑ p, ∑ q, a' p q * (y p * y q) = ∑ p, ∑ q, ∑ r, b' p q r * (y p * y q * y r)) ∧
        ((¬ IsScalarSqLinear fun p q => residue A (T p q)) →
          ¬ IsScalarSqLinear fun p q => residue A (a' p q)) := by
  obtain ⟨s, hs00, hs01, hs02, hs10, hs11, hs12, hs20, hs21, hs22⟩ :
      ∃ s : Fin 3 → Fin 3 → A, s 0 0 = T 0 0 ∧ s 0 1 = T 0 1 + T 1 0 ∧
        s 0 2 = T 0 2 + T 2 0 ∧ s 1 0 = 0 ∧ s 1 1 = T 1 1 ∧ s 1 2 = T 1 2 + T 2 1 ∧
        s 2 0 = 0 ∧ s 2 1 = 0 ∧ s 2 2 = T 2 2 :=
    ⟨fun p q => if p = 0 ∧ q = 0 then T 0 0 else if p = 0 ∧ q = 1 then T 0 1 + T 1 0
        else if p = 0 ∧ q = 2 then T 0 2 + T 2 0 else if p = 1 ∧ q = 1 then T 1 1
        else if p = 1 ∧ q = 2 then T 1 2 + T 2 1 else if p = 2 ∧ q = 2 then T 2 2 else 0,
      by simp⟩
  obtain ⟨a', ha'00, ha'01, ha'02, ha'10, ha'11, ha'12, ha'20, ha'21, ha'22⟩ :
      ∃ a' : Fin 3 → Fin 3 → A, a' 0 0 = 0 ∧ a' 0 1 = 0 ∧ a' 0 2 = 0 ∧ a' 1 0 = 0 ∧
        a' 1 1 = T 1 1 ∧ a' 1 2 = T 1 2 + T 2 1 ∧ a' 2 0 = 0 ∧ a' 2 1 = 0 ∧ a' 2 2 = T 2 2 :=
    ⟨fun p q => if p = 1 ∧ q = 1 then T 1 1 else if p = 1 ∧ q = 2 then T 1 2 + T 2 1
        else if p = 2 ∧ q = 2 then T 2 2 else 0,
      by simp⟩
  have hupper : ∀ p q, q < p → a' p q = 0 := by
    intro p q hpq
    rcases fin_three_cases p with rfl | rfl | rfl <;>
      rcases fin_three_cases q with rfl | rfl | rfl <;>
      first | exact absurd hpq (by decide) | assumption
  have hsym : ∑ p, ∑ q, T p q * (y p * y q) = ∑ p, ∑ q, s p q * (y p * y q) := by
    refine sum_quadratic_congr_of_symm y T s (fun p => ?_) fun p q hpq => ?_
    · rcases fin_three_cases p with rfl | rfl | rfl
      exacts [hs00.symm, hs11.symm, hs22.symm]
    · rcases fin_three_cases p with rfl | rfl | rfl <;>
        rcases fin_three_cases q with rfl | rfl | rfl <;>
        first
        | exact absurd hpq (by decide)
        | simp only [hs01, hs10, hs02, hs20, hs12, hs21, add_zero]
  have hdiff : ∀ p q, s p q - a' p q ∈ maximalIdeal A := by
    intro p q
    rcases fin_three_cases p with rfl | rfl | rfl <;> rcases fin_three_cases q with rfl | rfl | rfl
    · rw [hs00, ha'00, sub_zero, ← residue_eq_zero_iff]
      exact hT00
    · rw [hs01, ha'01, sub_zero, ← residue_eq_zero_iff, map_add]
      exact hT01
    · rw [hs02, ha'02, sub_zero, ← residue_eq_zero_iff, map_add]
      exact hT02
    all_goals simp [hs10, hs11, hs12, hs20, hs21, hs22, ha'10, ha'11, ha'12, ha'20, ha'21, ha'22]
  obtain ⟨b', hb'⟩ := exists_quadraticRelation_sub y hspan s a' b hdiff (hsym.symm.trans hrel)
  refine ⟨a', b', hupper, ha'00, ha'01, ha'02, ha'11, ha'12, ha'22, hb', fun hcase hcon =>
    hcase ((isScalarSqLinear_congr (fun p => ?_) fun p q hpq => ?_).mp hcon)⟩
  · rcases fin_three_cases p with rfl | rfl | rfl <;> simp [ha'00, ha'11, ha'22, hT00]
  · rcases fin_three_cases p with rfl | rfl | rfl <;>
    rcases fin_three_cases q with rfl | rfl | rfl <;>
      first
      | exact absurd hpq (by decide)
      | simp [ha'01, ha'10, ha'02, ha'20, ha'12, ha'21, hT01, hT02]

/-- Every element of `Fin 2` is `0` or `1`. -/
private theorem fin_two_cases (r : Fin 2) : r = 0 ∨ r = 1 := by
  revert r
  decide

/-- If the first generator is a good coordinate for the residues of a coefficient matrix with
vanishing `(3, 2)` entry, some entry on or above the diagonal is a unit. -/
public theorem exists_notMem_maximalIdeal_of_isGoodCoordinateForm_fin_three
    {a : Fin 3 → Fin 3 → A}
    (h21 : a 2 1 = 0) (hgood : IsGoodCoordinateForm fun p q => residue A (a p q)) :
    ∃ p q : Fin 3, p ≤ q ∧ a p q ∉ maximalIdeal A := by
  have e1 : (0 : Fin 2).succ = (1 : Fin 3) := by decide
  have e2 : (1 : Fin 2).succ = (2 : Fin 3) := by decide
  by_contra! hcon
  refine hgood ⟨0, 0, fun p => ?_, fun p q hpq => ?_⟩
  · rw [restrictFirstVar_apply, (residue_eq_zero_iff _).mpr (hcon _ _ le_rfl)]
    ring
  · rcases fin_two_cases p with rfl | rfl
    · rcases fin_two_cases q with rfl | rfl
      · exact absurd hpq (by decide)
      · rw [restrictFirstVar_apply, restrictFirstVar_apply, e1, e2, h21, map_zero,
          (residue_eq_zero_iff _).mpr (hcon 1 2 (by decide))]
        ring
    · rcases fin_two_cases q with rfl | rfl
      exacts [absurd hpq (by decide), absurd hpq (by decide)]


/-- **The chart normalization of Section 54.12.** Let `x₁, x₂, x₃` generate the maximal ideal of
a local ring and satisfy a quadratic relation `Σ aₚᵩ xₚxᵩ = Σ aₚᵩᵣ xₚxᵩxᵣ` with `a` upper
triangular, and suppose the quadratic form the residues of `a` present is in case I. Suppose given
a point `(c₂, c₃)` of the first chart at which the dehomogenization `q(1, y₂, y₃)` vanishes
together with both of its partial derivatives — which is what
`AlgebraicGeometry.exists_chartPoint_of_not_isScalarSqLinear` produces from a singular point of
the exceptional curve.

Then after the change of generators `x'₁ = x₁`, `x'₂ = x₂ - c₂x₁`, `x'₃ = x₃ - c₃x₁` moving that
point to the origin of the chart, the relation has an upper triangular coefficient matrix whose
first row vanishes — `a₁₁ = a₁₂ = a₁₃ = 0`, the source's `ā₁₁ = ā₁₂ = ā₁₃ = 0` and more — one of
whose entries on or above the diagonal is a unit, whose remaining four coefficients are those of
the old matrix, and whose first generator is therefore a good coordinate. The new generators
are recorded explicitly: `x'₁ = x₁`, `x'₂ = x₂ - u x₁`, `x'₃ = x₃ - v x₁` with `ū = c₂`, `v̄ = c₃`,
so that on the chart `A[𝔪/x₁]`, which only depends on `x₁`, the point becomes `y'₂ = y'₃ = 0`.

This is the step the source performs when it says one may choose the generators so that the
singular point of the blowup is the origin of the first chart. -/
public theorem exists_quadraticRelation_vanishing_first_row (x : Fin 3 → A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A)
    (hupper : ∀ p q, q < p → a p q = 0)
    (hrel : ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r))
    (hcase : ¬ IsScalarSqLinear fun p q => residue A (a p q))
    (c : Fin 2 → ResidueField A)
    (hconst : residue A (a 0 0) + residue A (a 0 1) * c 0 + residue A (a 0 2) * c 1 +
      residue A (a 1 1) * (c 0 * c 0) + residue A (a 1 2) * (c 0 * c 1) +
      residue A (a 2 2) * (c 1 * c 1) = 0)
    (hlin₂ : residue A (a 0 1) + 2 * (residue A (a 1 1) * c 0) + residue A (a 1 2) * c 1 = 0)
    (hlin₃ : residue A (a 0 2) + residue A (a 1 2) * c 0 + 2 * (residue A (a 2 2) * c 1) = 0) :
    ∃ (x' : Fin 3 → A) (a' : Fin 3 → Fin 3 → A) (b' : Fin 3 → Fin 3 → Fin 3 → A),
      Ideal.span (Set.range x') = maximalIdeal A ∧ (∀ p q, q < p → a' p q = 0) ∧
        a' 0 0 = 0 ∧ a' 0 1 = 0 ∧ a' 0 2 = 0 ∧
        (∀ p q : Fin 2, a' p.succ q.succ = a p.succ q.succ) ∧
        (∃ p q, p ≤ q ∧ a' p q ∉ maximalIdeal A) ∧
        (∑ p, ∑ q, a' p q * (x' p * x' q) = ∑ p, ∑ q, ∑ r, b' p q r * (x' p * x' q * x' r)) ∧
        (IsGoodCoordinateForm fun p q => residue A (a' p q)) ∧
        x' 0 = x 0 ∧ ∃ u v : A, residue A u = c 0 ∧ residue A v = c 1 ∧
          x' 1 = x 1 - u * x 0 ∧ x' 2 = x 2 - v * x 0 := by
  obtain ⟨u, hu⟩ := residue_surjective (R := A) (c 0)
  obtain ⟨v, hv⟩ := residue_surjective (R := A) (c 1)
  obtain ⟨y, hspan', hy0, hy1, hy2, hx⟩ := exists_span_eq_chartTranslation x hspan u v
  obtain ⟨b', hb'⟩ := exists_quadraticRelation_changeOfGenerators x y hspan'
    (chartTranslation u v) hx a b hrel
  obtain ⟨T, hT⟩ : ∃ T : Fin 3 → Fin 3 → A, ∀ p q, T p q =
      ∑ i, ∑ j, a i j * (chartTranslation u v i p * chartTranslation u v j q) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨e00, e01, e10, e02, e20, e11, e12, e21, e22⟩ :=
    transportForm_chartTranslation_entries u v a hupper
  have hrelT : ∑ p, ∑ q, T p q * (y p * y q)
      = ∑ p, ∑ q, ∑ r, b' p q r * (y p * y q * y r) :=
    Eq.trans (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hT p q]) hb'
  have hT00 : residue A (T 0 0) = 0 := by
    rw [hT, e00]
    simp only [map_add, map_mul, hu, hv]
    linear_combination hconst
  have hT01 : residue A (T 0 1) + residue A (T 1 0) = 0 := by
    rw [hT, hT, e01, e10]
    simp only [map_add, map_mul, hu, hv]
    linear_combination hlin₂
  have hT02 : residue A (T 0 2) + residue A (T 2 0) = 0 := by
    rw [hT, hT, e02, e20]
    simp only [map_add, map_mul, hu, hv]
    linear_combination hlin₃
  obtain ⟨a', b'', hupper', ha'00, ha'01, ha'02, ha'11, ha'12, ha'22, hb'', hcase'⟩ :=
    exists_quadraticRelation_clear_first_row y hspan' T b' hrelT hT00 hT01 hT02
  have h21 : a 2 1 = 0 := hupper 2 1 (by decide)
  have h21' : a' 2 1 = 0 := hupper' 2 1 (by decide)
  have hgood : IsGoodCoordinateForm fun p q => residue A (a' p q) :=
    isGoodCoordinateForm_of_upperTriangular_fin_three
      (fun p q hpq => by rw [hupper' p q hpq, map_zero])
      (by rw [ha'00, map_zero]) (by rw [ha'01, map_zero]) (by rw [ha'02, map_zero])
      (hcase' (by simpa only [hT] using
        not_isScalarSqLinear_map_transport_chartTranslation (residue A) a u v hcase))
  have e1 : (0 : Fin 2).succ = (1 : Fin 3) := by decide
  have e2 : (1 : Fin 2).succ = (2 : Fin 3) := by decide
  have hrestrict : ∀ p q : Fin 2, a' p.succ q.succ = a p.succ q.succ := by
    intro p q
    rcases fin_two_cases p with rfl | rfl <;> rcases fin_two_cases q with rfl | rfl
    · rw [e1, ha'11, hT, e11]
    · rw [e1, e2, ha'12, hT, e12, hT, e21, h21, add_zero]
    · rw [e2, e1, h21', h21]
    · rw [e2, ha'22, hT, e22]
  exact ⟨y, a', b'', hspan', hupper', ha'00, ha'01, ha'02, hrestrict,
    exists_notMem_maximalIdeal_of_isGoodCoordinateForm_fin_three h21' hgood, hb'', hgood,
    hy0, u, v, hu, hv, hy1, hy2⟩

/-- **A good coordinate exists, unconditionally in case I.** Let `x₁, x₂, x₃` generate the
maximal ideal of a local ring and satisfy a quadratic relation with upper triangular coefficient
matrix `a` having a unit entry on or above the diagonal, and suppose the quadratic form the
residues of `a` present is not a scalar times the square of a linear form — the source's case I.
Let `I` be a proper ideal of `κ[y₂, y₃]` whose square contains the dehomogenization
`q(1, y₂, y₃)`, which is what the source derives from singularity of the blowup at the point of
the exceptional curve cut out by `I`.

Then there are generators of the maximal ideal whose quadratic relation is again upper triangular
with a unit entry, whose first row vanishes, whose other coefficients are unchanged, and whose
first generator is a good coordinate.

This is `AlgebraicGeometry.exists_quadraticRelation_vanishing_first_row` with the point of the
chart replaced by the ideal cutting it out. It discharges the hypothesis `hrow` of
`AlgebraicGeometry.isGoodCoordinateForm_of_not_isScalarSqLinear`: the source arranges that
vanishing by moving the singular point of the blowup to the origin of the first chart, and this
is that move. -/
public theorem exists_isGoodCoordinateForm_of_dehomogenized_mem_sq (x : Fin 3 → A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A)
    (hupper : ∀ p q, q < p → a p q = 0)
    (hunit : ∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal A)
    (hrel : ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r))
    (hcase : ¬ IsScalarSqLinear fun p q => residue A (a p q))
    (I : Ideal (MvPolynomial (Fin 2) (ResidueField A))) (hI : I ≠ ⊤)
    (hmem : (C (residue A (a 0 0)) + C (residue A (a 0 1)) * X 0 +
      C (residue A (a 0 2)) * X 1 + C (residue A (a 1 1)) * X 0 ^ 2 +
      C (residue A (a 1 2)) * X 0 * X 1 +
      C (residue A (a 2 2)) * X 1 ^ 2 : MvPolynomial (Fin 2) (ResidueField A)) ∈ I ^ 2) :
    ∃ (x' : Fin 3 → A) (a' : Fin 3 → Fin 3 → A) (b' : Fin 3 → Fin 3 → Fin 3 → A),
      Ideal.span (Set.range x') = maximalIdeal A ∧ (∀ p q, q < p → a' p q = 0) ∧
        a' 0 0 = 0 ∧ a' 0 1 = 0 ∧ a' 0 2 = 0 ∧
        (∀ p q : Fin 2, a' p.succ q.succ = a p.succ q.succ) ∧
        (∃ p q, p ≤ q ∧ a' p q ∉ maximalIdeal A) ∧
        (∑ p, ∑ q, a' p q * (x' p * x' q) = ∑ p, ∑ q, ∑ r, b' p q r * (x' p * x' q * x' r)) ∧
        IsGoodCoordinateForm fun p q => residue A (a' p q) := by
  obtain ⟨c, hconst, hlin₂, hlin₃⟩ := exists_chartPoint_of_not_isScalarSqLinear
    (fun p q => residue A (a p q))
    (fun p q hpq => by rw [hupper p q hpq, map_zero])
    (by
      obtain ⟨p, q, hpq, hne⟩ := hunit
      exact ⟨p, q, hpq, fun h => hne ((residue_eq_zero_iff _).mp h)⟩)
    hcase I hI hmem
  obtain ⟨x', a', b', h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ :=
    exists_quadraticRelation_vanishing_first_row x hspan a b hupper hrel hcase c
      hconst hlin₂ hlin₃
  exact ⟨x', a', b', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end AlgebraicGeometry

end

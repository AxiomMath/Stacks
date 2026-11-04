module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChangeOfGenerators

/-!
# The two cases of the rational double point discussion, and good coordinates

Section 54.12 of the source attaches to a rational double point the quadratic form

`q = Σᵢ≤ⱼ āᵢⱼ tᵢtⱼ ∈ κ[t₁, t₂, t₃]`

of a quadratic relation `Σ aᵢⱼ xᵢxⱼ = Σ aᵢⱼₖ xᵢxⱼxₖ` among three generators of the maximal
ideal, and splits the argument in two according to it: *case II* is the case that `q` is an
element of `κ*` times the square of a linear form, and *case I* is everything else. In case I
the source singles out an element `x₁` of the maximal ideal and calls it a **good coordinate**
when, for any (equivalently, some) completion of `x₁` to a system of generators `x₁, x₂, x₃`,
the binary form `q(0, t₂, t₃)` is not a scalar times a square. This file formalizes those two
notions and the facts the source needs about them.

## Main definitions

* `AlgebraicGeometry.IsScalarSqLinear`: the coefficient matrix of a quadratic form presents it
  as a scalar times the square of a linear form. This is the source's case II; case I is the
  negation.
* `AlgebraicGeometry.transportForm`: the coefficient matrix of a quadratic form after a linear
  substitution.
* `AlgebraicGeometry.restrictFirstVar`: the coefficient matrix of `q(0, t₂, …, tₙ)`, the form
  obtained by setting the first variable to zero.
* `AlgebraicGeometry.IsGoodCoordinateForm`: the good coordinate condition, that the restricted
  form is not a scalar times a square.

## Main results

* `AlgebraicGeometry.sum_sum_eq_zero_of_alternating`: a double sum whose terms vanish on the
  diagonal and cancel in pairs is zero. Every computation below is an instance of this, and it
  is the reason they are all valid in characteristic two.
* `AlgebraicGeometry.sum_quadratic_eq_mul_sq`: the coefficient conditions of
  `IsScalarSqLinear` say exactly that `Σᵢⱼ aᵢⱼ tᵢtⱼ = c · (Σᵢ lᵢtᵢ)²`, in every
  characteristic. This is the bridge between the matrix form of the definition and the source's
  "a square of a linear form times an element of `κ*`".
* `AlgebraicGeometry.IsScalarSqLinear.exists_ne_zero_of_upperTriangular`: for a nonzero upper
  triangular presentation the scalar and the linear form are automatically nonzero, so the
  definition agrees with the source's reading, and matches the hypotheses of
  `AlgebraicGeometry.exists_sq_eq_cubicExpansion_of_rankOne_residue`.
* `AlgebraicGeometry.isScalarSqLinear_smul_iff` and
  `AlgebraicGeometry.isScalarSqLinear_transportForm_iff`: the condition is unchanged by scaling
  the form by a nonzero scalar and by an invertible linear substitution. The quadratic form of a
  rational double point is well defined only up to both, so this is what makes case I and
  case II properties of the singularity.
* `AlgebraicGeometry.isGoodCoordinateForm_of_not_isScalarSqLinear`: **a good coordinate
  exists.** In case I, a system of generators for which the coefficients carrying the first
  variable vanish — which is what the source arranges by moving the singular point of the
  blowup to the origin of the first chart — has `x₁` as a good coordinate. That move is
  `AlgebraicGeometry.exists_quadraticRelation_vanishing_first_row` in
  `RationalDoublePoints/ChartNormalization.lean`, which produces such a system of generators, so
  the vanishing is available rather than assumed.
* `AlgebraicGeometry.IsGoodCoordinateForm.of_restrictFirstVar_eq`: **good coordinates
  propagate.** Being a good coordinate depends on the quadratic form only through
  `q(0, t₂, t₃)`, so it survives any change of the form which leaves that binary form alone.
  The blowup step is such a change: the source's `q'` differs from `q` only in the coefficients
  carrying `t₁`.
* `AlgebraicGeometry.isGoodCoordinateForm_transportForm_iff_of_first_row`: **the notion does not
  depend on the choice of `x₂, x₃`.** A change of generators fixing `x₁` restricts to an
  invertible substitution of the remaining variables, along which the restricted form is
  transported, and the condition is invariant.

## Implementation notes

The quadratic form is carried by its coefficient matrix rather than by a polynomial, because
that is the shape in which the surrounding files produce and consume it:
`AlgebraicGeometry.exists_quadraticRelation` produces an upper triangular matrix,
`AlgebraicGeometry.exists_rankOne_of_dehomogenized_mem_sq` produces exactly the two coefficient
conditions of `IsScalarSqLinear`, and
`AlgebraicGeometry.exists_quadraticRelation_changeOfGenerators` produces exactly
`transportForm`. The conditions are imposed on the diagonal entries and on the sums
`aₚᵩ + aᵩₚ`, which are what the quadratic expression `Σᵢⱼ aᵢⱼ tᵢtⱼ` sees; on an upper triangular
matrix they read `aₚₚ = c lₚ²` and `aₚᵩ = 2c lₚlᵩ` for `p < q`, which is the source's
presentation.

Neither the scalar nor the linear form is required to be nonzero in the definition. For the
ternary form `q` of a rational double point that is no loss, because `q ≠ 0`; but the binary
form `q(0, t₂, t₃)` can vanish, and when it does `x₁` must not count as a good coordinate — the
line `t₁ = 0` is then a component of `E` and carries a rational singular point. Requiring a
nonzero linear form would make the zero form good and the propagation false.

Setting the first variable to zero is a submatrix along `Fin.succ`, so the restricted form of a
form in `n + 1` variables is a form in `n` variables and the two can be discussed at once.

## References

* [Stacks Project, Tag 0BGB](https://stacks.math.columbia.edu/tag/0BGB)
* [Stacks Project, Tag 0BGD](https://stacks.math.columbia.edu/tag/0BGD)
* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
-/

@[expose] public section

open IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Alternating double sums -/

/-- A double sum over a finite index type vanishes when its terms vanish on the diagonal and
cancel in pairs. Every identity in this file reduces to this one, and it is why they all hold in
characteristic two: the alternative argument, that the sum equals its own negative, only
controls twice the sum. -/
public theorem sum_sum_eq_zero_of_alternating {R : Type*} [AddCommGroup R] {ι : Type*}
    [Fintype ι] (f : ι → ι → R) (hdiag : ∀ p, f p p = 0)
    (hswap : ∀ p q, f p q + f q p = 0) :
    ∑ p, ∑ q, f p q = 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun z : ι × ι => f z.1 z.2)]
  refine Finset.sum_ninvolution (fun z : ι × ι => (z.2, z.1)) (fun z => hswap z.1 z.2)
    (fun z hz hcon => hz ?_) (fun _ => Finset.mem_univ _) (fun _ => rfl)
  have h1 : z.2 = z.1 := congrArg Prod.fst hcon
  show f z.1 z.2 = 0
  rw [h1]
  exact hdiag z.1

/-! ### A quadratic form which is a scalar times the square of a linear form -/

/-- **Case II of Section 54.12.** The quadratic form `Σᵢⱼ aᵢⱼ tᵢtⱼ` presented by the coefficient
matrix `a` is a scalar times the square of a linear form: there are `c` and `l` with
`aₚₚ = c lₚ²` and `aₚᵩ + aᵩₚ = 2 c lₚlᵩ` for `p < q`, which by
`AlgebraicGeometry.sum_quadratic_eq_mul_sq` is the same as `Σᵢⱼ aᵢⱼ tᵢtⱼ = c (Σᵢ lᵢtᵢ)²`. On an
upper triangular matrix, the presentation the source uses, the second condition reads
`aₚᵩ = 2 c lₚ lᵩ`.

Case I of the source's dichotomy is the negation of this condition. -/
public def IsScalarSqLinear {k : Type*} [CommRing k] {n : ℕ} (a : Fin n → Fin n → k) : Prop :=
  ∃ (c : k) (l : Fin n → k), (∀ p, a p p = c * l p * l p) ∧
    ∀ p q, p < q → a p q + a q p = 2 * (c * l p * l q)

variable {k : Type*} [CommRing k] {n : ℕ}

/-- The product of two linear forms, times a scalar, expanded as a double sum. -/
private theorem mul_sum_mul_sum_eq_sum_sum {R : Type*} [CommRing R] (c : R) (l x y : Fin n → R) :
    c * (∑ i, l i * x i) * (∑ j, l j * y j) = ∑ i, ∑ j, (c * l i * l j) * (x i * y j) := by
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- If `a` satisfies the coefficient conditions of `IsScalarSqLinear` with witnesses `c`, `l`, then
`a` and `c lᵢ lⱼ` have the same double sum against any symmetric weight. -/
private theorem sum_sum_mul_eq_of_scalarSq_coeffs {R : Type*} [CommRing R] (a : Fin n → Fin n → R)
    (c : R) (l : Fin n → R) (hdiag : ∀ p, a p p = c * l p * l p)
    (hoff : ∀ p q, p < q → a p q + a q p = 2 * (c * l p * l q)) (w : Fin n → Fin n → R)
    (hw : ∀ i j, w i j = w j i) :
    ∑ i, ∑ j, a i j * w i j = ∑ i, ∑ j, (c * l i * l j) * w i j := by
  have hd : ∀ i j, (a i j - c * l i * l j) + (a j i - c * l j * l i) = 0 := by
    intro i j
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · linear_combination hoff i j hlt
    · rw [hdiag i]; ring
    · linear_combination hoff j i hgt
  have hzero : ∑ i, ∑ j, (a i j - c * l i * l j) * w i j = 0 := by
    refine sum_sum_eq_zero_of_alternating _ (fun i => by rw [hdiag i]; ring) fun i j => ?_
    rw [hw j i]
    linear_combination w i j * hd i j
  simp only [sub_mul, Finset.sum_sub_distrib] at hzero
  exact sub_eq_zero.mp hzero

/-- The coefficient conditions defining `AlgebraicGeometry.IsScalarSqLinear` say exactly that the
quadratic expression they present is a scalar times the square of a linear form. This holds in
every characteristic, and connects the coefficient form of the definition with the source's
description of case II. -/
public theorem sum_quadratic_eq_mul_sq {R : Type*} [CommRing R] (a : Fin n → Fin n → R)
    (c : R) (l : Fin n → R) (hdiag : ∀ p, a p p = c * l p * l p)
    (hoff : ∀ p q, p < q → a p q + a q p = 2 * (c * l p * l q)) (t : Fin n → R) :
    ∑ p, ∑ q, a p q * (t p * t q) = c * (∑ p, l p * t p) ^ 2 := by
  rw [pow_two, ← mul_assoc, mul_sum_mul_sum_eq_sum_sum]
  exact sum_sum_mul_eq_of_scalarSq_coeffs a c l hdiag hoff _ fun i j => mul_comm _ _

/-- The quadratic expression presented by a matrix satisfying
`AlgebraicGeometry.IsScalarSqLinear` is a scalar times the square of a linear form, with the
same witnesses. -/
public theorem IsScalarSqLinear.exists_sum_eq_mul_sq {a : Fin n → Fin n → k}
    (h : IsScalarSqLinear a) :
    ∃ (c : k) (l : Fin n → k), ∀ t : Fin n → k,
      ∑ p, ∑ q, a p q * (t p * t q) = c * (∑ p, l p * t p) ^ 2 := by
  obtain ⟨c, l, hdiag, hoff⟩ := h
  exact ⟨c, l, fun t => sum_quadratic_eq_mul_sq a c l hdiag hoff t⟩

/-- An upper triangular coefficient matrix satisfying `AlgebraicGeometry.IsScalarSqLinear` has,
over a field, the presentation the source uses: `aₚₚ = c lₚ²` and `aₚᵩ = 2 c lₚlᵩ` for `p < q`.
Moreover, if the matrix is nonzero then the scalar and the linear form are nonzero, so the
condition is the source's "an element of `κ*` times the square of a linear form". These are the
hypotheses of `AlgebraicGeometry.exists_sq_eq_cubicExpansion_of_rankOne_residue`, which turns
case II into the normal form `x₃² = Σ aᵢⱼₖ xᵢxⱼxₖ`. -/
public theorem IsScalarSqLinear.exists_ne_zero_of_upperTriangular {K : Type*} [Field K]
    {a : Fin n → Fin n → K} (hupper : ∀ p q, q < p → a p q = 0)
    (hne : ∃ p q, p ≤ q ∧ a p q ≠ 0) (h : IsScalarSqLinear a) :
    ∃ (c : K) (l : Fin n → K), c ≠ 0 ∧ l ≠ 0 ∧ (∀ p, a p p = c * l p * l p) ∧
      ∀ p q, p < q → a p q = 2 * (c * l p * l q) := by
  obtain ⟨c, l, hdiag, hoff⟩ := h
  have hoff' : ∀ p q, p < q → a p q = 2 * (c * l p * l q) := by
    intro p q hpq
    rw [← hoff p q hpq, hupper q p hpq, add_zero]
  have hkey : c = 0 ∨ l = 0 → False := by
    intro h
    obtain ⟨p, q, hpq, hzero⟩ := hne
    refine hzero ?_
    rcases eq_or_lt_of_le hpq with rfl | hlt
    · rw [hdiag p]; rcases h with h | h <;> simp [h]
    · rw [hoff' p q hlt]; rcases h with h | h <;> simp [h]
  exact ⟨c, l, fun hc => hkey (Or.inl hc), fun hl => hkey (Or.inr hl), hdiag, hoff'⟩

/-- Scaling a quadratic form preserves the condition of being a scalar times the square of a
linear form. -/
public theorem IsScalarSqLinear.smul {a : Fin n → Fin n → k} (d : k)
    (h : IsScalarSqLinear a) : IsScalarSqLinear fun p q => d * a p q := by
  obtain ⟨c, l, hdiag, hoff⟩ := h
  refine ⟨d * c, l, fun p => ?_, fun p q hpq => ?_⟩
  · show d * a p p = d * c * l p * l p
    rw [hdiag p]; ring
  show d * a p q + d * a q p = 2 * (d * c * l p * l q)
  rw [← mul_add, hoff p q hpq]
  ring

/-- Over a field, scaling a quadratic form by a nonzero scalar does not change whether it is a
scalar times the square of a linear form. The quadratic form of a rational double point is well
defined only up to an element of `κ*`, so this is part of what makes case I and case II
properties of the singularity. -/
public theorem isScalarSqLinear_smul_iff {K : Type*} [Field K] (a : Fin n → Fin n → K) {d : K}
    (hd : d ≠ 0) : IsScalarSqLinear (fun p q => d * a p q) ↔ IsScalarSqLinear a := by
  refine ⟨fun h => ?_, fun h => h.smul d⟩
  have hback := h.smul d⁻¹
  have heq : (fun p q => d⁻¹ * (d * a p q)) = a := by
    funext p q
    field_simp
  rwa [heq] at hback

/-! ### Linear substitutions -/

/-- The coefficient matrix of a quadratic form after the linear substitution `tᵢ = Σₚ Nᵢₚ sₚ`.
This is the matrix `AlgebraicGeometry.exists_quadraticRelation_changeOfGenerators` produces for
a change of the generators of the maximal ideal. -/
public def transportForm (a : Fin n → Fin n → k) (N : Fin n → Fin n → k) :
    Fin n → Fin n → k :=
  fun p q => ∑ i, ∑ j, a i j * (N i p * N j q)

/-- The `(p, q)` coefficient of `transportForm a N` is `∑ i, ∑ j, a i j * (N i p * N j q)`. -/
@[simp]
public theorem transportForm_apply (a N : Fin n → Fin n → k) (p q : Fin n) :
    transportForm a N p q = ∑ i, ∑ j, a i j * (N i p * N j q) := rfl

/-- A quadratic form which is a scalar times the square of a linear form stays one after any
linear substitution: the linear form is substituted into. -/
public theorem IsScalarSqLinear.transportForm {a : Fin n → Fin n → k}
    (N : Fin n → Fin n → k) (h : IsScalarSqLinear a) :
    IsScalarSqLinear (AlgebraicGeometry.transportForm a N) := by
  obtain ⟨c, l, hdiag, hoff⟩ := h
  refine ⟨c, fun p => ∑ i, l i * N i p, fun p => ?_, fun p q _ => ?_⟩
  · rw [transportForm_apply, mul_sum_mul_sum_eq_sum_sum]
    exact sum_sum_mul_eq_of_scalarSq_coeffs a c l hdiag hoff _ fun i j => mul_comm _ _
  · have h := sum_sum_mul_eq_of_scalarSq_coeffs a c l hdiag hoff
      (fun i j => N i p * N j q + N i q * N j p) fun i j => by ring
    simp only [mul_add, Finset.sum_add_distrib] at h
    rw [transportForm_apply, transportForm_apply]
    simp only [← mul_sum_mul_sum_eq_sum_sum] at h
    linear_combination h

/-- Transporting a quadratic form along two linear substitutions in turn transports it along
their composite. -/
public theorem transportForm_transportForm (a N M : Fin n → Fin n → k) :
    transportForm (transportForm a N) M
      = transportForm a fun i r => ∑ p, N i p * M p r := by
  funext r v
  have hL : ∀ p q : Fin n, transportForm a N p q * (M p r * M q v)
      = ∑ i, ∑ j, a i j * (N i p * N j q) * (M p r * M q v) := by
    intro p q
    rw [transportForm_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
  have hR : ∀ i j : Fin n,
      a i j * ((∑ p, N i p * M p r) * ∑ q, N j q * M q v)
        = ∑ p, ∑ q, a i j * (N i p * N j q) * (M p r * M q v) := by
    intro i j
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [transportForm_apply, transportForm_apply]
  calc ∑ p, ∑ q, transportForm a N p q * (M p r * M q v)
      = ∑ p, ∑ q, ∑ i, ∑ j, a i j * (N i p * N j q) * (M p r * M q v) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hL p q
    _ = ∑ i, ∑ j, ∑ p, ∑ q, a i j * (N i p * N j q) * (M p r * M q v) :=
        sum_comm_four _
    _ = ∑ i, ∑ j, a i j * ((∑ p, N i p * M p r) * ∑ q, N j q * M q v) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hR i j).symm

/-- Transporting a quadratic form along the identity substitution does nothing. -/
public theorem transportForm_one (a : Fin n → Fin n → k) :
    transportForm a (fun i p => if i = p then 1 else 0) = a := by
  funext p q
  rw [transportForm_apply,
    Finset.sum_eq_single_of_mem p (Finset.mem_univ p) (fun i _ hi => by simp [hi]),
    Finset.sum_eq_single_of_mem q (Finset.mem_univ q) (fun j _ hj => by simp [hj])]
  simp

/-- The condition of being a scalar times the square of a linear form is unchanged by a linear
substitution which has a right inverse. Together with
`AlgebraicGeometry.isScalarSqLinear_smul_iff` this says that case I and case II of the source's
dichotomy depend only on the singularity, the quadratic form being well defined up to an element
of `κ*` and a change of the generators of the maximal ideal. -/
public theorem isScalarSqLinear_transportForm_iff (a N N' : Fin n → Fin n → k)
    (hNN' : (fun i r => ∑ p, N i p * N' p r) = fun i p : Fin n => if i = p then 1 else 0) :
    IsScalarSqLinear (transportForm a N) ↔ IsScalarSqLinear a := by
  have hcomp : transportForm (transportForm a N) N' = a := by
    rw [transportForm_transportForm, hNN', transportForm_one]
  refine ⟨fun h => ?_, fun h => h.transportForm _⟩
  rw [← hcomp]
  exact h.transportForm _

/-- Over a field, the condition of being a scalar times the square of a linear form is unchanged
by a linear substitution given by an invertible matrix. -/
public theorem isScalarSqLinear_transportForm_matrix_iff {K : Type*} [Field K]
    (a : Fin n → Fin n → K) (N : Matrix (Fin n) (Fin n) K) (hN : IsUnit N.det) :
    IsScalarSqLinear (transportForm a fun i p => N i p) ↔ IsScalarSqLinear a :=
  isScalarSqLinear_transportForm_iff a (fun i p => N i p) (fun p r => N⁻¹ p r) (by
    funext i r
    show ∑ p, N i p * N⁻¹ p r = if i = r then 1 else 0
    rw [show ∑ p, N i p * N⁻¹ p r = (N * N⁻¹) i r from Matrix.mul_apply.symm,
      Matrix.mul_nonsing_inv N hN, Matrix.one_apply])

/-! ### Setting the first variable to zero -/

/-- The coefficient matrix of the quadratic form `q(0, t₂, …, tₙ₊₁)` obtained by setting the
first variable to zero: the submatrix on the remaining indices. -/
public def restrictFirstVar (a : Fin (n + 1) → Fin (n + 1) → k) : Fin n → Fin n → k :=
  fun p q => a p.succ q.succ

omit [CommRing k] in
/-- The `(p, q)` coefficient of `restrictFirstVar a` is `a p.succ q.succ`. -/
@[simp]
public theorem restrictFirstVar_apply (a : Fin (n + 1) → Fin (n + 1) → k) (p q : Fin n) :
    restrictFirstVar a p q = a p.succ q.succ := rfl

/-- **A good coordinate.** For a quadratic form `q(t₁, …, tₙ₊₁)` attached to a system of
generators `x₁, …, xₙ₊₁` of the maximal ideal, the first generator is a good coordinate when
`q(0, t₂, …, tₙ₊₁)` is not a scalar times the square of a linear form. -/
public def IsGoodCoordinateForm (a : Fin (n + 1) → Fin (n + 1) → k) : Prop :=
  ¬ IsScalarSqLinear (restrictFirstVar a)

/-- **Good coordinates propagate.** Being a good coordinate depends on the quadratic form only
through the form obtained by setting the first variable to zero. The source's blowup step
changes only the coefficients carrying `t₁`, so this is what carries a good coordinate from a
rational double point to the singular point of its blowup. -/
public theorem IsGoodCoordinateForm.of_restrictFirstVar_eq {a a' : Fin (n + 1) → Fin (n + 1) → k}
    (h : ∀ p q : Fin n, a' p.succ q.succ = a p.succ q.succ) (ha : IsGoodCoordinateForm a) :
    IsGoodCoordinateForm a' := by
  refine fun hcon => ha ?_
  obtain ⟨c, l, hdiag, hoff⟩ := hcon
  refine ⟨c, l, fun p => ?_, fun p q hpq => ?_⟩
  · rw [restrictFirstVar_apply, ← h p p]
    simpa using hdiag p
  · rw [restrictFirstVar_apply, restrictFirstVar_apply, ← h p q, ← h q p]
    simpa using hoff p q hpq

/-- Over a field, scaling the quadratic form by a nonzero scalar does not change whether the
first generator is a good coordinate. -/
public theorem isGoodCoordinateForm_smul_iff {K : Type*} [Field K]
    (a : Fin (n + 1) → Fin (n + 1) → K) {d : K} (hd : d ≠ 0) :
    IsGoodCoordinateForm (fun p q => d * a p q) ↔ IsGoodCoordinateForm a := by
  have heq : restrictFirstVar (fun p q => d * a p q)
      = fun p q => d * restrictFirstVar a p q := by
    funext p q
    rfl
  unfold IsGoodCoordinateForm
  rw [heq]
  exact not_congr (isScalarSqLinear_smul_iff _ hd)

/-- **A good coordinate exists.** If the quadratic form is not a scalar times the square of a
linear form — the source's case I — and the coefficients carrying the first variable all vanish,
then the first generator is a good coordinate: setting the first variable to zero does not
change such a form.

The source arranges the vanishing by choosing the generators so that the singular point of the
blowup is the origin of the first chart, where singularity forces `q(1, y₂, y₃) ∈ (y₂, y₃)²`,
that is `ā₁₁ = ā₁₂ = ā₁₃ = 0`. That choice of generators is made by
`AlgebraicGeometry.exists_quadraticRelation_vanishing_first_row`. -/
public theorem isGoodCoordinateForm_of_not_isScalarSqLinear
    {a : Fin (n + 1) → Fin (n + 1) → k} (hrow : ∀ q, a 0 q = 0) (hcol : ∀ p, a p 0 = 0)
    (ha : ¬ IsScalarSqLinear a) : IsGoodCoordinateForm a := by
  refine fun hcon => ha ?_
  obtain ⟨c, l, hdiag, hoff⟩ := hcon
  refine ⟨c, Fin.cons 0 l, fun p => ?_, fun p q hpq => ?_⟩
  · induction p using Fin.cases with
    | zero => rw [hrow 0]; simp
    | succ p => simpa using hdiag p
  · induction p using Fin.cases with
    | zero => rw [hrow q, hcol q]; simp
    | succ p =>
        induction q using Fin.cases with
        | zero =>
            exfalso
            rw [Fin.lt_def, Fin.val_succ, Fin.val_zero] at hpq
            omega
        | succ q =>
            have hpq' : p < q := by
              rw [Fin.lt_def, Fin.val_succ, Fin.val_succ] at hpq
              rw [Fin.lt_def]
              omega
            simpa using hoff p q hpq'

/-- **The good coordinate condition does not depend on the choice of the other generators.** A
change of generators fixing the first one expresses the old generators in terms of the new ones
by a matrix whose first row is the first standard basis vector. The restriction of the
transported form to the vanishing of the first variable is then the transport of the restriction
along the submatrix on the remaining indices, and the condition is invariant under invertible
substitutions.

This is the source's remark that the notion of good coordinate does not depend on the `x₂, x₃`
used to compute the quadratic form. -/
public theorem isGoodCoordinateForm_transportForm_iff_of_first_row {K : Type*} [Field K]
    (a : Fin (n + 1) → Fin (n + 1) → K) (N : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hrow : ∀ q, N 0 q = if (0 : Fin (n + 1)) = q then 1 else 0)
    (hM : IsUnit (N.submatrix Fin.succ Fin.succ).det) :
    IsGoodCoordinateForm (transportForm a fun i p => N i p) ↔ IsGoodCoordinateForm a := by
  have hzero : ∀ p : Fin n, N 0 p.succ = 0 := by
    intro p
    rw [hrow p.succ, ite_eq_right fun h : (0 : Fin (n + 1)) = p.succ => (Fin.succ_ne_zero p) h.symm]
  have hres : restrictFirstVar (transportForm a fun i p => N i p)
      = transportForm (restrictFirstVar a)
        (fun i p => (N.submatrix Fin.succ Fin.succ) i p) := by
    funext p q
    rw [restrictFirstVar_apply, transportForm_apply, transportForm_apply,
      Fin.sum_univ_succ (f := fun i => ∑ j, a i j * (N i p.succ * N j q.succ)),
      show (∑ j, a 0 j * (N 0 p.succ * N j q.succ)) = 0 from by simp [hzero p], zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_succ (f := fun j => a i.succ j * (N i.succ p.succ * N j q.succ)),
      show a i.succ 0 * (N i.succ p.succ * N 0 q.succ) = 0 from by simp [hzero q], zero_add]
    exact Finset.sum_congr rfl fun j _ => by simp [Matrix.submatrix_apply]
  unfold IsGoodCoordinateForm
  rw [hres]
  exact not_congr (isScalarSqLinear_transportForm_matrix_iff _ _ hM)

/-- **Case I and case II do not depend on the order of the generators.** Reindexing the
coefficient matrix by a permutation of the variables preserves the property of presenting a
scalar times the square of a linear form. -/
public theorem isScalarSqLinear_comp_perm_iff {k : Type*} [CommRing k] {n : ℕ}
    (a : Fin n → Fin n → k) (σ : Equiv.Perm (Fin n)) :
    IsScalarSqLinear (fun p q => a (σ p) (σ q)) ↔ IsScalarSqLinear a := by
  have key : ∀ (b : Fin n → Fin n → k) (τ : Equiv.Perm (Fin n)), IsScalarSqLinear b →
      IsScalarSqLinear (fun p q => b (τ p) (τ q)) := by
    rintro b τ ⟨c, l, hdiag, hoff⟩
    refine ⟨c, l ∘ τ, fun p => hdiag (τ p), fun p q hpq => ?_⟩
    have hne : τ p ≠ τ q := fun h => (ne_of_lt hpq) (τ.injective h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hoff _ _ hlt
    · simp only [Function.comp_apply]
      rw [add_comm, hoff _ _ hgt]
      ring
  refine ⟨fun h => ?_, key a σ⟩
  have h' := key _ σ.symm h
  simpa using h'

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CoordinatePredicates
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpSingularPoints
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartRingSpec
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StrictBaseChange

/-!
# Case II of a rational double point: unit-special coordinates

Section 54.12 of the source resolves a rational double point in case II by tracking one element
`x₁` of the maximal ideal along the blowups. This file proves the chart computation behind that
step, for a corrected form of the shape the source tracks.

## The source's shape is not stable, and the corrected one

The source asserts that if `x₃² + x₁(a x₂² + b x₂x₃ + c x₃²) ∈ 𝔪⁴` for generators `x₁, x₂, x₃` of
the maximal ideal (`AlgebraicGeometry.IsSpecialCoordinate`), then every singular point of the
blowup which is not in case I is the point `y₂ = y₃ = 0` of the chart at `x₁`, where the same
shape holds again for the image of `x₁`. This is false: for the `D₆` singularity
`z² + y x² + y⁵` and `x₁ = y` the only singular point of the blowup is the `D₄` point
`Z² + yX² + y³` of the chart at `y`; it is not in case I (its graded ring is `κ[y, X, Z]/(Z²)`),
and the image of `y` is not a special coordinate there, since the cubic part of the relation
would have to be `y` times a scalar multiple of a square, while it is `y(X² + y²)`. The term
`y³` comes from the part of the relation lying in `𝔪⁴`, which the source drops. Likewise the
source's claim that a point of case II of the blowup of a case II singularity carries a special
coordinate fails for `E₈ → E₇`.

What is stable is the shape `x₃² + x₁·Q(x₁, x₂, x₃) ∈ 𝔪⁴` for an arbitrary quadratic expression
`Q` whose coefficient of `x₂²` is a unit, `AlgebraicGeometry.IsUnitSpecialCoordinate`. The
variant in which that coefficient is not a unit is `AlgebraicGeometry.IsTripleRootCoordinate`:
it is what the case II points of multiplicity three (the triple roots of the cubic on the double
line) carry, and along which the tracked element changes from one blowup to the next. Chains of
such points are not treated here.

## Main definitions

* `AlgebraicGeometry.IsUnitSpecialCoordinate`
* `AlgebraicGeometry.IsTripleRootCoordinate`

## Main results

* `RationalDoublePointSituation.isCaseOne_or_isUnitSpecialCoordinate_stalk_blowUp`: for a
  unit-special coordinate `e` of the ring of a Situation 0BGC, every singular point of the blowup
  in the maximal ideal is in case I, or `e` cuts out the exceptional divisor there, the residue
  field is unchanged, and the image of `e` is again unit-special.
* `AlgebraicGeometry.isCaseOne_or_isUnitSpecialCoordinate_of_chart`: the same computation at an
  abstract local ring of a chart, in pure commutative algebra; its pieces are
  `AlgebraicGeometry.isCaseOne_or_isUnitSpecialCoordinate_of_chartZero` (the chart at `x₁`),
  `AlgebraicGeometry.isCaseOne_or_isUnitSpecialCoordinate_of_chartOne` (the chart at `x₂`) and
  `AlgebraicGeometry.isCaseOne_or_isUnitSpecialCoordinate_of_sq` (completing the square).
* `AlgebraicGeometry.exists_chartData_blowUp`: the local ring at a point of the blowup of
  `Spec(A)` in its maximal ideal is a localization of a chart `A[𝔪/x_j]`, read in the stalk.

## Implementation notes

The map from `A` to the local ring at `x` is `AlgebraicGeometry.blowUpStalkHom`, which unfolds to
`((Scheme.ΓSpecIso _).inv ≫ (blowUpToBase _).appTop ≫ germ ⊤ x trivial).hom`.

No `@[stacks]` attribute is attached: this is one step of the discussion preceding Tag 0BGE, in a
corrected form, not a tag.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u

namespace AlgebraicGeometry

section Defs

variable (B : Type u) [CommRing B] [IsLocalRing B]

/-- `e` is a unit-special coordinate of the local ring `B`: there are generators `e = x₁, x₂, x₃`
of the maximal ideal and a quadratic expression `Q = Σ qᵢⱼ xᵢxⱼ` whose coefficient of `x₂²` is a
unit, with `x₃² + x₁·Q ∈ 𝔪⁴`. -/
def IsUnitSpecialCoordinate (e : B) : Prop :=
  ∃ (x : Fin 3 → B) (q : Fin 3 → Fin 3 → B), x 0 = e ∧
    Ideal.span (Set.range x) = maximalIdeal B ∧ q 1 1 ∉ maximalIdeal B ∧
    x 2 * x 2 + x 0 * ∑ i, ∑ j, q i j * (x i * x j) ∈ maximalIdeal B ^ 4

/-- `e` is a triple-root coordinate of the local ring `B`: there are generators `e = x₁, x₂, x₃`
of the maximal ideal and a quadratic expression `Q = Σ qᵢⱼ xᵢxⱼ` whose coefficient of `x₂²` lies
in the maximal ideal, with `x₃² + x₁·Q ∈ 𝔪⁴`. -/
def IsTripleRootCoordinate (e : B) : Prop :=
  ∃ (x : Fin 3 → B) (q : Fin 3 → Fin 3 → B), x 0 = e ∧
    Ideal.span (Set.range x) = maximalIdeal B ∧ q 1 1 ∈ maximalIdeal B ∧
    x 2 * x 2 + x 0 * ∑ i, ∑ j, q i j * (x i * x j) ∈ maximalIdeal B ^ 4

end Defs

/-! ### Generalities -/

/-- The range of a family indexed by `Fin 3`. -/
theorem range_fin_three {α : Type*} (f : Fin 3 → α) : Set.range f = {f 0, f 1, f 2} := by
  ext a
  simp [Fin.exists_fin_succ, eq_comm]

/-- `1` does not lie in the maximal ideal of a local ring. -/
theorem one_notMem_maximalIdeal' (C : Type*) [CommRing C] [IsLocalRing C] :
    (1 : C) ∉ maximalIdeal C :=
  fun h => (IsLocalRing.mem_maximalIdeal _).mp h isUnit_one

/-- A quadratic form in three variables with no `t₂²` term, a nonzero `t₃²` term and a nonzero
`t₁t₂` term is not a scalar times the square of a linear form. -/
theorem not_isScalarSqLinear_of_coeff {k : Type*} [Field k] (a : Fin 3 → Fin 3 → k)
    (h11 : a 1 1 = 0) (h22 : a 2 2 ≠ 0) (h01 : a 0 1 + a 1 0 ≠ 0) : ¬ IsScalarSqLinear a := by
  rintro ⟨c, l, hd, ho⟩
  have hc : c ≠ 0 := by
    rintro rfl
    exact h22 (by simpa using hd 2)
  have hl : l 1 = 0 := by
    have h' : c * (l 1 * l 1) = 0 := by rw [← mul_assoc, ← hd 1, h11]
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hc)
  exact h01 (by rw [ho 0 1 (by decide), hl]; ring)

/-- If `w * w + t * z = t ^ 2 * c₀` with `t` in the maximal ideal, then `w` is in it too. -/
private theorem mem_maximalIdeal_of_mul_self_add {C : Type*} [CommRing C] [IsLocalRing C]
    {t w z c₀ : C} (ht : t ∈ maximalIdeal C) (h : w * w + t * z = t ^ 2 * c₀) :
    w ∈ maximalIdeal C := by
  have hww : w * w ∈ maximalIdeal C := by
    have : w * w = t ^ 2 * c₀ - t * z := by linear_combination h
    rw [this]
    exact sub_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ht 2 two_pos))
      (Ideal.mul_mem_right _ _ ht)
  exact ((IsLocalRing.maximalIdeal.isMaximal C).isPrime.mem_or_mem hww).elim id id

section Local

variable {B C : Type*} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
  (φ : B →+* C) [IsLocalHom φ]

/-- Two evaluations of a polynomial at families congruent modulo an ideal are congruent. -/
theorem MvPolynomial.eval₂_sub_eval₂_mem {σ : Type*} (I : Ideal C) (Y Y' : σ → C)
    (h : ∀ i, Y i - Y' i ∈ I) (P : MvPolynomial σ B) :
    MvPolynomial.eval₂ φ Y P - MvPolynomial.eval₂ φ Y' P ∈ I := by
  rw [← Ideal.Quotient.eq, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  exact Ideal.Quotient.eq.mpr (h i)

/-- Substituting polynomials in one variable into a polynomial in several variables, then
evaluating, is evaluating at the values of the substituted polynomials. -/
theorem eval₂_eval₂_C {σ : Type*} (s : σ → B[X]) (v : C) (P : MvPolynomial σ B) :
    (MvPolynomial.eval₂ Polynomial.C s P).eval₂ φ v =
      MvPolynomial.eval₂ φ (fun i => (s i).eval₂ φ v) P := by
  simpa [Function.comp_def] using
    MvPolynomial.eval₂_comp_left (Polynomial.eval₂RingHom φ v) Polynomial.C s P

/-- The residue of the value at `v` of a polynomial is the value of its reduction at the residue
of `v`. -/
theorem residue_eval₂ (v : C) (P : B[X]) :
    residue C (P.eval₂ φ v) =
      (P.map (residue B)).eval₂ (ResidueField.map φ) (residue C v) := by
  rw [Polynomial.eval₂_map, ResidueField.map_comp_residue, Polynomial.hom_eval₂]

/-- A polynomial whose coefficients lie in the maximal ideal has its values in any ideal
containing the image of the maximal ideal. -/
theorem eval₂_mem_of_map_residue_eq_zero {I : Ideal C} (hφm : ∀ b ∈ maximalIdeal B, φ b ∈ I)
    (v : C) {P : B[X]} (hP : P.map (residue B) = 0) : P.eval₂ φ v ∈ I := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine Ideal.sum_mem _ fun n _ => Ideal.mul_mem_right _ _ (hφm _ ?_)
  rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.coeff_map, hP, Polynomial.coeff_zero]

/-- The map from polynomials over the residue field of `B` to the residue field of `C` sending
the variable to the residue of `v`. -/
abbrev residuePolyEval (v : C) : (ResidueField B)[X] →+* ResidueField C :=
  Polynomial.eval₂RingHom (ResidueField.map φ) (residue C v)

/-- **The maximal ideal at a point of a chart.** Let `C` be local over `B`, the image of the
maximal ideal of `B` lying in `t·C`, and suppose that every element of `C` becomes, after
multiplication by a unit, a polynomial in `v` over `B` modulo `w`. If the kernel of the
evaluation at `v` of polynomials over the residue field is generated by `g`, and `G` lifts `g`,
then the maximal ideal of `C` is generated by `t`, `G(v)` and `w`. -/
theorem maximalIdeal_eq_span_of_ker {t v w : C} (ht : t ∈ maximalIdeal C)
    (hw : w ∈ maximalIdeal C) (hφm : ∀ b ∈ maximalIdeal B, φ b ∈ Ideal.span {t})
    (hloc : ∀ c : C, ∃ (b : C) (P : B[X]), IsUnit b ∧ b * c - P.eval₂ φ v ∈ Ideal.span {w})
    {g : (ResidueField B)[X]} (hker : RingHom.ker (residuePolyEval φ v) = Ideal.span {g})
    {G : B[X]} (hG : G.map (residue B) = g) :
    maximalIdeal C = Ideal.span {t, G.eval₂ φ v, w} := by
  set J := Ideal.span ({t, G.eval₂ φ v, w} : Set C)
  have htJ : t ∈ J := Ideal.subset_span (by simp)
  have hGJ : G.eval₂ φ v ∈ J := Ideal.subset_span (by simp)
  have hwJ : Ideal.span {w} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (by simp))
  have htJ' : Ideal.span {t} ≤ J := (Ideal.span_singleton_le_iff_mem _).mpr htJ
  refine le_antisymm (fun d hd => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨b, P, hb, hP⟩ := hloc d
    have hPm : P.eval₂ φ v ∈ maximalIdeal C := by
      have : P.eval₂ φ v = b * d - (b * d - P.eval₂ φ v) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ hd)
        ((Ideal.span_singleton_le_iff_mem _).mpr hw hP)
    have hker' : P.map (residue B) ∈ RingHom.ker (residuePolyEval φ v) := by
      rw [RingHom.mem_ker]
      show (P.map (residue B)).eval₂ (ResidueField.map φ) (residue C v) = 0
      rw [← residue_eval₂, IsLocalRing.residue_eq_zero_iff]
      exact hPm
    rw [hker, Ideal.mem_span_singleton'] at hker'
    obtain ⟨k, hk⟩ := hker'
    obtain ⟨K, hK⟩ := Polynomial.map_surjective (residue B) IsLocalRing.residue_surjective k
    have hdiff : (P - K * G).map (residue B) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hK, hG, hk, sub_self]
    have h1 := eval₂_mem_of_map_residue_eq_zero φ hφm v hdiff
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul] at h1
    have hPJ : P.eval₂ φ v ∈ J := by
      have : P.eval₂ φ v = (P.eval₂ φ v - K.eval₂ φ v * G.eval₂ φ v) +
        K.eval₂ φ v * G.eval₂ φ v := by ring
      rw [this]
      exact add_mem (htJ' h1) (Ideal.mul_mem_left _ _ hGJ)
    have hbdJ : b * d ∈ J := by
      have : b * d = P.eval₂ φ v + (b * d - P.eval₂ φ v) := by ring
      rw [this]
      exact add_mem hPJ (hwJ hP)
    have : d = ↑hb.unit⁻¹ * (b * d) := by
      rw [← mul_assoc, hb.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hbdJ
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ht
    · refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
      rw [residue_eval₂, hG]
      exact (show g ∈ RingHom.ker (residuePolyEval φ v) from
        hker ▸ Ideal.mem_span_singleton_self g)
    · exact hw

/-- **The residue field at a point of a chart at which the coordinate is rational.** If every
element of `C` is, up to a unit, a polynomial in `v` modulo `w` — the unit being itself such a
polynomial — and the residue of `v` comes from the residue field of `B`, then the residue field
of `C` is that of `B`. -/
theorem surjective_residue_comp_of_residue_eq {v w : C} (hw : w ∈ maximalIdeal C)
    (hloc : ∀ c : C, ∃ (b : C) (P Q : B[X]), IsUnit b ∧
      b * c - P.eval₂ φ v ∈ Ideal.span {w} ∧ b - Q.eval₂ φ v ∈ Ideal.span {w})
    {μ : ResidueField B} (hμ : residue C v = ResidueField.map φ μ) :
    Function.Surjective ((residue C).comp φ) := by
  have hres : ∀ (c : C) (P : B[X]), c - P.eval₂ φ v ∈ Ideal.span {w} →
      residue C c = ResidueField.map φ ((P.map (residue B)).eval μ) := by
    intro c P hc
    have h1 : residue C c = residue C (P.eval₂ φ v) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hw hc
    rw [h1, residue_eval₂, hμ, Polynomial.eval₂_at_apply]
  intro z
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨b, P, Q, hb, hP, hQ⟩ := hloc c
  have hbc := hres _ _ hP
  have hb' := hres _ _ hQ
  have hb0 : residue C b ≠ 0 := (hb.map (residue C)).ne_zero
  obtain ⟨b₀, hb₀⟩ := IsLocalRing.residue_surjective
    ((P.map (residue B)).eval μ / (Q.map (residue B)).eval μ)
  refine ⟨b₀, ?_⟩
  show residue C (φ b₀) = residue C c
  rw [← ResidueField.map_residue, hb₀, map_div₀, ← hbc, ← hb', map_mul]
  field_simp

end Local

/-! ### The chart at the first generator -/

section ChartZero

variable {B C : Type*} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
  (φ : B →+* C) [IsLocalHom φ]

/-- If the images of generators of the maximal ideal lie in `t·C`, so does the image of the whole
maximal ideal. -/
theorem map_mem_span_of_generators {x : Fin 3 → B}
    (hx : Ideal.span (Set.range x) = maximalIdeal B) {t : C}
    (hxt : ∀ i, φ (x i) ∈ Ideal.span {t}) : ∀ b ∈ maximalIdeal B, φ b ∈ Ideal.span {t} := by
  intro b hb
  rw [← hx] at hb
  have : Ideal.map φ (Ideal.span (Set.range x)) ≤ Ideal.span {t} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hxt i
  exact this (Ideal.mem_map_of_mem φ hb)

/-- The quadratic part `q(1, Y, 0)` of a quadratic expression, as a polynomial in `Y`. -/
def chartQuadPoly (q : Fin 3 → Fin 3 → B) : B[X] :=
  Polynomial.C (q 0 0) + Polynomial.C (q 0 1 + q 1 0) * Polynomial.X +
    Polynomial.C (q 1 1) * Polynomial.X ^ 2

/-- The dehomogenized quadratic expression `q(1, v, w)` is `q(1, v, 0)` plus `w` times a linear
expression. -/
theorem sum_quadratic_chartZero (q : Fin 3 → Fin 3 → B) (v w : C) :
    ∑ i, ∑ j, φ (q i j) * (![1, v, w] i * ![1, v, w] j) =
      (chartQuadPoly q).eval₂ φ v +
        w * (φ (q 0 2 + q 2 0) + φ (q 1 2 + q 2 1) * v + φ (q 2 2) * w) := by
  simp only [Fin.sum_univ_three, chartQuadPoly, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow, map_add]
  simp
  ring

/-- A ring map between local rings sends elements outside the maximal ideal outside the maximal
ideal. -/
theorem notMem_maximalIdeal_map {b : B} (hb : b ∉ maximalIdeal B) : φ b ∉ maximalIdeal C :=
  fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm
    ((IsLocalRing.notMem_maximalIdeal.mp hb).map φ)


/-- **Completing the square at a rational point of the double line.** Let `t, v, w` generate the
maximal ideal of `C`, with `w² + t·(c·v² + α·t·v + β·t + w·(L₀ + d·v + f·w)) = t²·c₀` and `c` a
unit. Then `C` is in case I, or `t` is a unit-special coordinate of `C`: if the quadratic form
`w² + (β - c₀)·t² + L₀·t·w` is a scalar times a square, it is `(w + λt)²`, and `w + λt` replaces
`w`. -/
theorem isCaseOne_or_isUnitSpecialCoordinate_of_sq {C : Type*} [CommRing C] [IsLocalRing C]
    {t v w c d f α' β' L₀ c₀ : C} (hc : c ∉ maximalIdeal C) (ht : t ∈ maximalIdeal C)
    (hv'm : v ∈ maximalIdeal C) (hwm : w ∈ maximalIdeal C)
    (hgen' : maximalIdeal C = Ideal.span {t, v, w})
    (hrel2 : w * w + t * (c * v ^ 2 + α' * t * v + β' * t +
        w * (L₀ + d * v + f * w)) = t ^ 2 * c₀) :
    IsCaseOne C ∨ IsUnitSpecialCoordinate C t := by
  set a : Fin 3 → Fin 3 → C := ![![β' - c₀, 0, L₀], ![0, 0, 0], ![0, 0, 1]] with ha
  set X3 : Fin 3 → C := ![t, v, w] with hX3
  have hspan3 : Ideal.span (Set.range X3) = maximalIdeal C := by
    rw [range_fin_three]; exact hgen'.symm
  have hm2 : ∀ {a b : C}, a ∈ maximalIdeal C → b ∈ maximalIdeal C →
      a * b ∈ maximalIdeal C ^ 2 := fun ha hb => by
    rw [sq]; exact Ideal.mul_mem_mul ha hb
  have hrelI : ∑ p, ∑ r, a p r * (X3 p * X3 r) ∈ maximalIdeal C ^ 3 := by
    have : ∑ p, ∑ r, a p r * (X3 p * X3 r) = -(t * (c * (v * v) +
        α' * (t * v) + (d * (w * v) + f * (w * w)))) := by
      simp only [ha, hX3, Fin.sum_univ_three]
      simp
      linear_combination hrel2
    rw [this, pow_succ']
    refine neg_mem (Ideal.mul_mem_mul ht ?_)
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ (hm2 hv'm hv'm))
      (Ideal.mul_mem_left _ _ (hm2 ht hv'm))) (add_mem (Ideal.mul_mem_left _ _ (hm2 hwm hv'm))
        (Ideal.mul_mem_left _ _ (hm2 hwm hwm)))
  by_cases hF : IsScalarSqLinear (fun p r => residue C (a p r))
  swap
  · left
    refine ⟨X3, a, hspan3, ?_, ⟨2, 2, le_rfl, ?_⟩, hrelI, hF⟩
    · intro p r hpr
      fin_cases p <;> fin_cases r <;> simp [ha] at hpr ⊢
    · simp [ha]
  right
  obtain ⟨c', l, hd, ho⟩ := hF
  have hd0 := hd 0
  have hd2 := hd 2
  have ho02 := ho 0 2 (by decide)
  simp only [ha] at hd0 hd2 ho02
  simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, map_sub,
    Matrix.cons_val, Matrix.cons_val_one, map_one, map_zero, add_zero] at hd0 hd2 ho02
  set lam₀ := c' * l 0 * l 2 with hlam₀
  obtain ⟨lam, hlam⟩ := IsLocalRing.residue_surjective lam₀
  set W := w + lam * t with hW
  set δ₁ := L₀ - 2 * lam with hδ₁
  set δ₂ := lam ^ 2 - lam * L₀ + β' - c₀ with hδ₂
  have hδ₁m : δ₁ ∈ maximalIdeal C := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [hδ₁, map_sub, map_mul, map_ofNat, hlam]
    linear_combination ho02
  have hδ₂m : δ₂ ∈ maximalIdeal C := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [hδ₂, map_sub, map_add, map_mul, map_pow, hlam]
    linear_combination (-lam₀) * ho02 + hd0 + (c' * l 0 * l 0) * hd2
  have hWm : W ∈ maximalIdeal C := add_mem hwm (Ideal.mul_mem_left _ _ ht)
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = δ₂ + α' * v - d * lam * v -
      2 * f * lam * W + f * lam ^ 2 * t := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = δ₁ + d * v + f * W := ⟨_, rfl⟩
  have hid : W * W + t * (c * (v * v) + t * a₁ + W * b₁) = 0 := by
    simp only [ha₁, hb₁, hδ₁, hδ₂, hW]
    linear_combination hrel2
  set Y3 : Fin 3 → C := ![t, v, W] with hY3
  have hspanY : Ideal.span (Set.range Y3) = maximalIdeal C := by
    rw [range_fin_three]
    apply le_antisymm
    · rw [Ideal.span_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨ht, hv'm, hWm⟩
    · rw [hgen', Ideal.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Ideal.subset_span (by simp [hY3])
      · exact Ideal.subset_span (by simp [hY3])
      · have : y = W - lam * t := by rw [hW]; ring
        rw [this]
        exact sub_mem (Ideal.subset_span (by simp [hY3]))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp [hY3])))
  have ha₁m : a₁ ∈ maximalIdeal C := by
    simp only [ha₁]
    exact add_mem (sub_mem (sub_mem (add_mem hδ₂m (Ideal.mul_mem_left _ _ hv'm))
      (Ideal.mul_mem_left _ _ hv'm)) (Ideal.mul_mem_left _ _ hWm))
      (Ideal.mul_mem_left _ _ ht)
  have hb₁m : b₁ ∈ maximalIdeal C := by
    simp only [hb₁]
    exact add_mem (add_mem hδ₁m (Ideal.mul_mem_left _ _ hv'm)) (Ideal.mul_mem_left _ _ hWm)
  obtain ⟨ca, hca⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp
    (show a₁ ∈ Submodule.span C (Set.range Y3) by rw [← Ideal.span, hspanY]; exact ha₁m)
  obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp
    (show b₁ ∈ Submodule.span C (Set.range Y3) by rw [← Ideal.span, hspanY]; exact hb₁m)
  simp only [Fin.sum_univ_three, smul_eq_mul, hY3] at hca hcb
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hca hcb
  refine ⟨Y3, ![ca, ![0, c, 0], cb], rfl, hspanY, ?_, ?_⟩
  · simpa using hc
  · have : Y3 2 * Y3 2 + Y3 0 * ∑ i, ∑ j, ![ca, ![0, c, 0], cb] i j *
        (Y3 i * Y3 j) = 0 := by
      simp only [hY3, Fin.sum_univ_three]
      simp
      linear_combination hid + t * t * hca + t * W * hcb
    rw [this]
    exact zero_mem _


/-- **The local computation at a point of the chart at `x₁` of the blowup of a unit-special
coordinate.** Let `x₁, x₂, x₃` generate the maximal ideal of `B`, with
`x₃² + x₁·Σ qᵢⱼxᵢxⱼ ∈ 𝔪⁴` and `q₂₂` a unit, and let `C` be a two-dimensional Noetherian local ring
over `B` which is not regular, in which `xᵢ = x₁·yᵢ` with `y = (1, v, w)`, the relation having
become `w² + x₁·Σ qᵢⱼyᵢyⱼ = x₁²·c₀`, and every element of which is, up to a unit, a polynomial in
`v` over `B` modulo `w`. Then either `C` is in case I, or the residue field of `C` is that of `B`
and the image of `x₁` is a unit-special coordinate of `C`. -/
theorem isCaseOne_or_isUnitSpecialCoordinate_of_chartZero
    [IsNoetherianRing C] (hdimC : ringKrullDim C = 2) (hsing : ¬ IsRegularLocalRing C)
    {x : Fin 3 → B} (hx : Ideal.span (Set.range x) = maximalIdeal B)
    {q : Fin 3 → Fin 3 → B} (hq : q 1 1 ∉ maximalIdeal B)
    {v w c₀ : C} (hv : φ (x 1) = φ (x 0) * v) (hw : φ (x 2) = φ (x 0) * w)
    (hrel : w * w + φ (x 0) * ∑ i, ∑ j, φ (q i j) * (![1, v, w] i * ![1, v, w] j) =
      φ (x 0) ^ 2 * c₀)
    (hloc : ∀ c : C, ∃ (b : C) (P Q : B[X]), IsUnit b ∧
      b * c - P.eval₂ φ v ∈ Ideal.span {w} ∧ b - Q.eval₂ φ v ∈ Ideal.span {w}) :
    IsCaseOne C ∨ (Ideal.map φ (maximalIdeal B) = Ideal.span {φ (x 0)} ∧
      Function.Surjective ((residue C).comp φ) ∧ IsUnitSpecialCoordinate C (φ (x 0))) := by
  classical
  set t := φ (x 0) with ht_def
  have hx0 : x 0 ∈ maximalIdeal B := hx ▸ Ideal.subset_span ⟨0, rfl⟩
  have ht : t ∈ maximalIdeal C := map_nonunit φ _ hx0
  have hφm : ∀ b ∈ maximalIdeal B, φ b ∈ Ideal.span {t} := by
    refine map_mem_span_of_generators φ hx fun i => ?_
    fin_cases i
    · exact Ideal.mem_span_singleton_self _
    · show φ (x 1) ∈ _
      rw [hv]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · show φ (x 2) ∈ _
      rw [hw]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [sum_quadratic_chartZero φ q v w] at hrel
  have hmapm : Ideal.map φ (maximalIdeal B) = Ideal.span {t} := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun b hb => hφm b hb) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem φ hx0
  set L := φ (q 0 2 + q 2 0) + φ (q 1 2 + q 2 1) * v + φ (q 2 2) * w with hL
  set H := chartQuadPoly q with hH
  have hwm : w ∈ maximalIdeal C := mem_maximalIdeal_of_mul_self_add ht hrel
  have hloc1 : ∀ c : C, ∃ (b : C) (P : B[X]), IsUnit b ∧
      b * c - P.eval₂ φ v ∈ Ideal.span {w} :=
    fun c => let ⟨b, P, _, hb, hP, _⟩ := hloc c; ⟨b, P, hb, hP⟩
  set θ := residuePolyEval φ v with hθ
  obtain ⟨g, hg⟩ : ∃ g, RingHom.ker θ = Ideal.span {g} :=
    ⟨Submodule.IsPrincipal.generator (RingHom.ker θ), (Ideal.span_singleton_generator _).symm⟩
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (residue B) IsLocalRing.residue_surjective g
  have hgen := maximalIdeal_eq_span_of_ker φ ht hwm hφm hloc1 hg hG
  have hHres : ∀ P : B[X], θ (P.map (residue B)) = residue C (P.eval₂ φ v) :=
    fun P => (residue_eval₂ φ v P).symm
  have hmem_ker : ∀ P : (ResidueField B)[X], θ P = 0 → g ∣ P := by
    intro P hP
    have : P ∈ RingHom.ker θ := hP
    rwa [hg, Ideal.mem_span_singleton] at this
  have hhexp : H.map (residue B) = Polynomial.C (residue B (q 0 0)) +
      Polynomial.C (residue B (q 0 1 + q 1 0)) * Polynomial.X +
        Polynomial.C (residue B (q 1 1)) * Polynomial.X ^ 2 := by
    simp [hH, chartQuadPoly]
  set h := H.map (residue B) with hh
  have hh2 : h.coeff 2 ≠ 0 := by
    rw [hhexp]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow]
    simpa using (IsLocalRing.residue_eq_zero_iff _).not.mpr hq
  by_cases hdiv : g ∣ h
  swap
  · -- the point is not on the double line's special locus: `C` is regular
    exfalso
    have hHu : H.eval₂ φ v ∉ maximalIdeal C := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hHres]
      exact fun h0 => hdiv (hmem_ker _ h0)
    have hu : IsUnit (H.eval₂ φ v + w * L - t * c₀) := by
      refine IsLocalRing.notMem_maximalIdeal.mp fun hm => hHu ?_
      have : H.eval₂ φ v = (H.eval₂ φ v + w * L - t * c₀) - (w * L - t * c₀) := by ring
      rw [this]
      exact sub_mem hm (sub_mem (Ideal.mul_mem_right _ _ hwm) (Ideal.mul_mem_right _ _ ht))
    have htw : t ∈ Ideal.span {w} := by
      have hrel' : t * (H.eval₂ φ v + w * L - t * c₀) = -(w * w) := by
        linear_combination hrel
      have : t = -(w * (w * ↑hu.unit⁻¹)) := by
        calc t = t * (H.eval₂ φ v + w * L - t * c₀) * ↑hu.unit⁻¹ := by
                rw [mul_assoc, hu.mul_val_inv, mul_one]
          _ = _ := by rw [hrel']; ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self w))
    apply hsing
    refine isRegularLocalRing_of_maximalIdeal_eq_span_pair hdimC
      (u := G.eval₂ φ v) (v := w) ?_
    rw [hgen]
    apply le_antisymm
    · rw [Ideal.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact (Ideal.span_mono (by simp)) htw
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
    · exact Ideal.span_mono (by intro y hy; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy ⊢; tauto)
  obtain ⟨k, hk⟩ := hdiv
  by_cases hdiv2 : g * g ∣ h
  swap
  · -- a simple root: case I
    left
    have hgk : ¬ g ∣ k := fun ⟨k', hk'⟩ => hdiv2 ⟨k', by rw [hk, hk', mul_assoc]⟩
    obtain ⟨K, hK⟩ := Polynomial.map_surjective (residue B) IsLocalRing.residue_surjective k
    have hKu : K.eval₂ φ v ∉ maximalIdeal C := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hHres, hK]
      exact fun h0 => hgk (hmem_ker _ h0)
    have hdiff : (H - G * K).map (residue B) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hG, hK, ← hh, hk, sub_self]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp
      (eval₂_mem_of_map_residue_eq_zero φ hφm v hdiff)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul] at hs
    refine ⟨![t, G.eval₂ φ v, w], ![![s - c₀, K.eval₂ φ v, L], ![0, 0, 0], ![0, 0, 1]],
      ?_, ?_, ⟨2, 2, le_rfl, ?_⟩, ?_, ?_⟩
    · rw [range_fin_three]
      exact hgen.symm
    · intro p r hpr
      fin_cases p <;> fin_cases r <;> simp_all
    · simp
    · have : ∑ p, ∑ r, ![![s - c₀, K.eval₂ φ v, L], ![0, 0, 0], ![0, 0, 1]] p r *
          (![t, G.eval₂ φ v, w] p * ![t, G.eval₂ φ v, w] r) = 0 := by
        simp only [Fin.sum_univ_three]
        simp
        linear_combination hrel + t * hs
      rw [this]
      exact zero_mem _
    · apply not_isScalarSqLinear_of_coeff
      · simp
      · simp
      · simpa using IsLocalRing.notMem_maximalIdeal.mp hKu
  · -- a double root: a rational point, and either case I or unit-special again
    have hh0 : h ≠ 0 := fun h0 => hh2 (by rw [h0, Polynomial.coeff_zero])
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hh0 (by rw [hk, zero_mul])
    have hgnu : ¬ IsUnit g := by
      intro hu
      have h1 : (1 : (ResidueField B)[X]) ∈ RingHom.ker θ := by
        rw [hg, Ideal.mem_span_singleton]; exact hu.dvd
      exact one_ne_zero ((map_one θ).symm.trans (RingHom.mem_ker.mp h1))
    have hdeg : g.natDegree = 1 := by
      have h1 : (g * g).natDegree ≤ h.natDegree := Polynomial.natDegree_le_of_dvd hdiv2 hh0
      rw [Polynomial.natDegree_mul hg0 hg0] at h1
      have h2 : h.natDegree ≤ 2 := by
        rw [hhexp]; compute_degree
      have h3 : g.natDegree ≠ 0 := fun h0 => hgnu
        (Polynomial.isUnit_iff_degree_eq_zero.mpr
          (by rw [Polynomial.degree_eq_natDegree hg0, h0]; rfl))
      omega
    set α := g.coeff 1 with hα_def
    have hα : α ≠ 0 := by
      have : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
      rwa [Polynomial.leadingCoeff, hdeg] at this
    set μ := -(g.coeff 0) / α with hμ_def
    have hgX : g = Polynomial.C α * (Polynomial.X - Polynomial.C μ) := by
      have hαμ : α * μ = -(g.coeff 0) := by rw [hμ_def]; field_simp
      calc g = Polynomial.C (g.coeff 1) * Polynomial.X + Polynomial.C (g.coeff 0) :=
            Polynomial.eq_X_add_C_of_natDegree_le_one hdeg.le
        _ = Polynomial.C α * (Polynomial.X - Polynomial.C μ) := by
            rw [mul_sub, ← Polynomial.C_mul, hαμ, Polynomial.C_neg]; ring
    have hkerμ : RingHom.ker θ = Ideal.span {Polynomial.X - Polynomial.C μ} := by
      rw [hg, hgX, Ideal.span_singleton_mul_left_unit
        (Polynomial.isUnit_C.mpr (IsUnit.mk0 α hα))]
    have hμ : residue C v = ResidueField.map φ μ := by
      have : Polynomial.X - Polynomial.C μ ∈ RingHom.ker θ := by
        rw [hkerμ]; exact Ideal.mem_span_singleton_self _
      rw [RingHom.mem_ker, map_sub] at this
      simpa [hθ, sub_eq_zero] using this
    have hsurj := surjective_residue_comp_of_residue_eq φ hwm hloc hμ
    obtain ⟨m, hm⟩ : (Polynomial.X - Polynomial.C μ) * (Polynomial.X - Polynomial.C μ) ∣ h :=
      dvd_trans ⟨Polynomial.C α * Polynomial.C α, by rw [hgX]; ring⟩ hdiv2
    have he0 : residue B (q 0 0) + residue B (q 0 1 + q 1 0) * μ +
        residue B (q 1 1) * μ ^ 2 = 0 := by
      have := congrArg (Polynomial.eval μ) hm
      rw [hhexp] at this
      simp at this
      rw [map_add]
      linear_combination this
    have he1 : residue B (q 0 1 + q 1 0) + 2 * residue B (q 1 1) * μ = 0 := by
      have := congrArg (fun p => (Polynomial.derivative p).eval μ) hm
      simp only [hhexp] at this
      simp [Polynomial.derivative_mul] at this
      rw [map_add]
      linear_combination this
    obtain ⟨μ', hμ'⟩ := IsLocalRing.residue_surjective μ
    have hgen' := maximalIdeal_eq_span_of_ker φ ht hwm hφm hloc1 hkerμ
      (G := Polynomial.X - Polynomial.C μ') (by simp [hμ'])
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hgen'
    set v' := v - φ μ' with hv'
    have hv'm : v' ∈ maximalIdeal C := hgen' ▸ Ideal.subset_span (by simp)
    have hα0 : q 0 1 + q 1 0 + 2 * q 1 1 * μ' ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [map_add, map_mul, map_ofNat, hμ'] at he1 ⊢
      linear_combination he1
    have hβ0 : q 0 0 + (q 0 1 + q 1 0) * μ' + q 1 1 * μ' ^ 2 ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [map_add, map_mul, map_pow, hμ'] at he0 ⊢
      linear_combination he0
    obtain ⟨α', hα'⟩ := Ideal.mem_span_singleton'.mp (hφm _ hα0)
    obtain ⟨β', hβ'⟩ := Ideal.mem_span_singleton'.mp (hφm _ hβ0)
    have hHv : H.eval₂ φ v = φ (q 1 1) * v' ^ 2 + φ (q 0 1 + q 1 0 + 2 * q 1 1 * μ') * v' +
        φ (q 0 0 + (q 0 1 + q 1 0) * μ' + q 1 1 * μ' ^ 2) := by
      simp only [hH, chartQuadPoly, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow, hv', map_add, map_mul,
        map_pow, map_ofNat]
      ring
    set L₀ := φ (q 0 2 + q 2 0 + (q 1 2 + q 2 1) * μ') with hL₀
    have hLv : L = L₀ + φ (q 1 2 + q 2 1) * v' + φ (q 2 2) * w := by
      simp only [hL, hL₀, hv', map_add, map_mul]; ring
    have hrel2 : w * w + t * (φ (q 1 1) * v' ^ 2 + α' * t * v' + β' * t +
        w * (L₀ + φ (q 1 2 + q 2 1) * v' + φ (q 2 2) * w)) = t ^ 2 * c₀ := by
      have := hrel
      rw [hHv, hLv, ← hα', ← hβ'] at this
      linear_combination this
    exact (isCaseOne_or_isUnitSpecialCoordinate_of_sq (t := t) (v := v') (w := w)
      (notMem_maximalIdeal_map φ hq) ht hv'm hwm hgen' hrel2).imp_right
        fun h => ⟨hmapm, hsurj, h⟩

end ChartZero

/-! ### The other two charts, and the three charts together -/

section Charts

variable {B C : Type*} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
  (φ : B →+* C) [IsLocalHom φ]

/-- Changing the chart coordinate `u` into its inverse: an element which is, up to a unit, a
polynomial in `u` modulo `w` is, up to another unit, a polynomial in `u⁻¹` modulo `w`. -/
theorem exists_polynomial_invOf {u w w' : C} [Invertible u]
    (hww' : Ideal.span {w} = Ideal.span {w'})
    (hloc : ∀ c : C, ∃ (b : C) (P Q : B[X]), IsUnit b ∧
      b * c - P.eval₂ φ u ∈ Ideal.span {w} ∧ b - Q.eval₂ φ u ∈ Ideal.span {w}) :
    ∀ c : C, ∃ (b : C) (P Q : B[X]), IsUnit b ∧
      b * c - P.eval₂ φ (⅟u) ∈ Ideal.span {w'} ∧ b - Q.eval₂ φ (⅟u) ∈ Ideal.span {w'} := by
  intro c
  obtain ⟨b, P, Q, hb, hP, hQ⟩ := hloc c
  have hinv : ∀ n : ℕ, (⅟u) ^ n * u ^ n = 1 := fun n => by
    rw [← mul_pow, invOf_mul_self, one_pow]
  have key : ∀ (R : B[X]) (n : ℕ) (y : C), (⅟u) ^ (R.natDegree + n) * y -
      (Polynomial.X ^ n * R.reverse).eval₂ φ (⅟u) =
      (⅟u) ^ (R.natDegree + n) * (y - R.eval₂ φ u) := fun R n y => by
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, ← eval₂_reverse_mul_pow φ u R, pow_add]
    linear_combination ((⅟u) ^ n * R.reverse.eval₂ φ (⅟u)) * hinv R.natDegree
  refine ⟨(⅟u) ^ (P.natDegree + Q.natDegree) * b, Polynomial.X ^ Q.natDegree * P.reverse,
    Polynomial.X ^ P.natDegree * Q.reverse, ((isUnit_of_invertible (⅟u)).pow _).mul hb,
    ?_, ?_⟩ <;> rw [← hww']
  · rw [mul_assoc, key P Q.natDegree (b * c)]
    exact Ideal.mul_mem_left _ _ hP
  · rw [add_comm, key Q P.natDegree b]
    exact Ideal.mul_mem_left _ _ hQ

/-- From a presentation of the elements of `C` as fractions of polynomials in a family `Y` to
one by polynomials in one element `v` modulo another `w`. -/
theorem exists_polynomial_of_mvPolynomial {σ : Type*} {Y : σ → C} {v w : C} (s : σ → B[X])
    (hs : ∀ i, Y i - (s i).eval₂ φ v ∈ Ideal.span {w})
    (hloc : ∀ c : C, ∃ (b : C) (P Q : MvPolynomial σ B), IsUnit b ∧
      b * c = MvPolynomial.eval₂ φ Y P ∧ b = MvPolynomial.eval₂ φ Y Q) :
    ∀ c : C, ∃ (b : C) (P Q : B[X]), IsUnit b ∧
      b * c - P.eval₂ φ v ∈ Ideal.span {w} ∧ b - Q.eval₂ φ v ∈ Ideal.span {w} := by
  intro c
  obtain ⟨b, P, Q, hb, hP, hQ⟩ := hloc c
  refine ⟨b, MvPolynomial.eval₂ Polynomial.C s P, MvPolynomial.eval₂ Polynomial.C s Q, hb,
    ?_, ?_⟩
  · rw [hP, eval₂_eval₂_C]
    exact MvPolynomial.eval₂_sub_eval₂_mem φ _ _ _ hs P
  · rw [hQ, eval₂_eval₂_C]
    exact MvPolynomial.eval₂_sub_eval₂_mem φ _ _ _ hs Q

/-- **The local computation at a point of the chart at `x₂` of the blowup of a unit-special
coordinate.** In the notation of
`AlgebraicGeometry.isCaseOne_or_isUnitSpecialCoordinate_of_chartZero`, now with `xᵢ = x₂·yᵢ` and
`y = (u, 1, w)`: if `u` lies in the maximal ideal the ring is in case I, and otherwise the point
lies in the chart at `x₁` as well and the computation there applies. -/
theorem isCaseOne_or_isUnitSpecialCoordinate_of_chartOne
    [IsNoetherianRing C] (hdimC : ringKrullDim C = 2) (hsing : ¬ IsRegularLocalRing C)
    {x : Fin 3 → B} (hx : Ideal.span (Set.range x) = maximalIdeal B)
    {q : Fin 3 → Fin 3 → B} (hq : q 1 1 ∉ maximalIdeal B)
    {u w c₀ : C} (hu : φ (x 0) = φ (x 1) * u) (hw : φ (x 2) = φ (x 1) * w)
    (hrel : w * w + φ (x 1) * (u * ∑ i, ∑ j, φ (q i j) * (![u, 1, w] i * ![u, 1, w] j)) =
      φ (x 1) ^ 2 * c₀)
    (hloc : ∀ c : C, ∃ (b : C) (P Q : B[X]), IsUnit b ∧
      b * c - P.eval₂ φ u ∈ Ideal.span {w} ∧ b - Q.eval₂ φ u ∈ Ideal.span {w}) :
    IsCaseOne C ∨ (Ideal.map φ (maximalIdeal B) = Ideal.span {φ (x 0)} ∧
      Function.Surjective ((residue C).comp φ) ∧ IsUnitSpecialCoordinate C (φ (x 0))) := by
  classical
  set t := φ (x 1) with ht_def
  have hx1 : x 1 ∈ maximalIdeal B := hx ▸ Ideal.subset_span ⟨1, rfl⟩
  have ht : t ∈ maximalIdeal C := map_nonunit φ _ hx1
  have hwm : w ∈ maximalIdeal C := mem_maximalIdeal_of_mul_self_add ht hrel
  by_cases hum : u ∈ maximalIdeal C
  · left
    have hφm : ∀ b ∈ maximalIdeal B, φ b ∈ Ideal.span {t} := by
      refine map_mem_span_of_generators φ hx fun i => ?_
      fin_cases i
      · show φ (x 0) ∈ _
        rw [hu]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      · exact Ideal.mem_span_singleton_self _
      · show φ (x 2) ∈ _
        rw [hw]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have hu0 : residue C u = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hum
    have hw0 : residue C w = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hwm
    have hker : RingHom.ker (residuePolyEval φ u) = Ideal.span {Polynomial.X} := by
      ext P
      rw [RingHom.mem_ker, Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
      simp only [residuePolyEval, Polynomial.coe_eval₂RingHom, hu0, Polynomial.eval₂_at_zero]
      exact map_eq_zero_iff _ (ResidueField.map φ).injective
    have hloc1 : ∀ c : C, ∃ (b : C) (P : B[X]), IsUnit b ∧
        b * c - P.eval₂ φ u ∈ Ideal.span {w} :=
      fun c => let ⟨b, P, _, hb, hP, _⟩ := hloc c; ⟨b, P, hb, hP⟩
    have hgen := maximalIdeal_eq_span_of_ker φ ht hwm hφm hloc1 hker (G := Polynomial.X)
      (Polynomial.map_X _)
    simp only [Polynomial.eval₂_X] at hgen
    have hTm : (∑ i, ∑ j, φ (q i j) * (![u, 1, w] i * ![u, 1, w] j)) - φ (q 1 1) ∈
        maximalIdeal C := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp [Fin.sum_univ_three, hu0, hw0]
    refine ⟨![t, u, w], ![![-c₀, φ (q 1 1), 0], ![0, 0, 0], ![0, 0, 1]], ?_, ?_,
      ⟨2, 2, le_rfl, ?_⟩, ?_, ?_⟩
    · rw [range_fin_three]
      exact hgen.symm
    · intro p r hpr
      fin_cases p <;> fin_cases r <;> simp at hpr ⊢
    · simp
    · have : ∑ p, ∑ r, ![![-c₀, φ (q 1 1), 0], ![0, 0, 0], ![0, 0, 1]] p r *
          (![t, u, w] p * ![t, u, w] r) =
          -(t * (u * ((∑ i, ∑ j, φ (q i j) * (![u, 1, w] i * ![u, 1, w] j)) - φ (q 1 1)))) := by
        simp [Fin.sum_univ_three] at hrel ⊢
        linear_combination hrel
      rw [this, pow_succ', sq]
      exact neg_mem (Ideal.mul_mem_mul ht (Ideal.mul_mem_mul hum hTm))
    · apply not_isScalarSqLinear_of_coeff
      · simp
      · simp
      · simpa using IsLocalRing.notMem_maximalIdeal.mp (notMem_maximalIdeal_map φ hq)
  · have hu' : IsUnit u := IsLocalRing.notMem_maximalIdeal.mp hum
    let := hu'.invertible
    have huv : u * ⅟u = 1 := mul_invOf_self u
    have hYe : (![1, ⅟u, w * ⅟u] : Fin 3 → C) = fun i => ⅟u * ![u, 1, w] i := by
      funext i
      fin_cases i
      · simp
      · simp
      · simp [mul_comm]
    have hsum : ∑ i, ∑ j, φ (q i j) * (![1, ⅟u, w * ⅟u] i * ![1, ⅟u, w * ⅟u] j) =
        (⅟u) ^ 2 * ∑ i, ∑ j, φ (q i j) * (![u, 1, w] i * ![u, 1, w] j) := by
      rw [hYe, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    refine isCaseOne_or_isUnitSpecialCoordinate_of_chartZero φ hdimC hsing hx hq
      (v := ⅟u) (w := w * ⅟u) (c₀ := (⅟u) ^ 4 * c₀) ?_ ?_ ?_
      (exists_polynomial_invOf φ (Ideal.span_singleton_mul_right_unit
        (isUnit_of_invertible (⅟u)) w).symm hloc)
    · rw [hu, mul_assoc, huv, mul_one]
    · rw [hw, hu]
      linear_combination (-(t * w)) * huv
    · rw [hsum, hu]
      linear_combination (⅟u) ^ 2 * hrel - t ^ 2 * (⅟u) ^ 2 * c₀ * (u * ⅟u + 1) * huv

/-- **The local computation at a point of the blowup of a unit-special coordinate lying over the
closed point, in any of the three charts.** Let `C` be a two-dimensional Noetherian local domain
over `B` which is not regular, in which `xₖ = x_j·Yₖ` for one index `j` with `Y_j = 1`, the image
of `x_j` being nonzero and lying in the maximal ideal, and every element of which is a fraction
of polynomials in the `Yₖ` with a unit denominator. Then either `C` is in case I, or the maximal
ideal of `B` generates the ideal of `C` generated by the image of `x₁`, the residue field of `C`
is that of `B`, and the image of `x₁` is a unit-special coordinate of `C`. -/
theorem isCaseOne_or_isUnitSpecialCoordinate_of_chart [IsDomain C] [IsNoetherianRing C]
    (hdimC : ringKrullDim C = 2) (hsing : ¬ IsRegularLocalRing C)
    {x : Fin 3 → B} (hx : Ideal.span (Set.range x) = maximalIdeal B)
    {q : Fin 3 → Fin 3 → B} (hq : q 1 1 ∉ maximalIdeal B)
    (hrel : x 2 * x 2 + x 0 * ∑ i, ∑ j, q i j * (x i * x j) ∈ maximalIdeal B ^ 4)
    (j : Fin 3) (Y : Fin 3 → C) (hYj : Y j = 1) (hY : ∀ k, φ (x k) = φ (x j) * Y k)
    (hxj : φ (x j) ≠ 0)
    (hloc : ∀ c : C, ∃ (b : C) (P Q : MvPolynomial (Fin 3) B), IsUnit b ∧
      b * c = MvPolynomial.eval₂ φ Y P ∧ b = MvPolynomial.eval₂ φ Y Q) :
    IsCaseOne C ∨ (Ideal.map φ (maximalIdeal B) = Ideal.span {φ (x 0)} ∧
      Function.Surjective ((residue C).comp φ) ∧ IsUnitSpecialCoordinate C (φ (x 0))) := by
  classical
  set t := φ (x j) with ht_def
  have hφm : ∀ b ∈ maximalIdeal B, φ b ∈ Ideal.span {t} :=
    map_mem_span_of_generators φ hx fun k => by
      rw [hY k]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hxjm : x j ∈ maximalIdeal B := hx ▸ Ideal.subset_span ⟨j, rfl⟩
  have ht : t ∈ maximalIdeal C := map_nonunit φ _ hxjm
  obtain ⟨r, hr⟩ : ∃ r, φ (x 2 * x 2 + x 0 * ∑ i, ∑ k, q i k * (x i * x k)) = t ^ 4 * r := by
    have hle : Ideal.map φ (maximalIdeal B ^ 4) ≤ Ideal.span {t ^ 4} := by
      rw [Ideal.map_pow, ← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hφm) 4
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hle (Ideal.mem_map_of_mem φ hrel))
    exact ⟨r, by rw [← hr, mul_comm]⟩
  have hrelC : Y 2 * Y 2 + t * (Y 0 * ∑ i, ∑ k, φ (q i k) * (Y i * Y k)) = t ^ 2 * r := by
    have h1 : t ^ 2 * (Y 2 * Y 2 + t * (Y 0 * ∑ i, ∑ k, φ (q i k) * (Y i * Y k))) =
        t ^ 2 * (t ^ 2 * r) := by
      rw [show t ^ 2 * (t ^ 2 * r) = t ^ 4 * r by ring, ← hr]
      simp only [map_add, map_mul, hY, Fin.sum_univ_three]
      ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hxj) h1
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · have hYe : Y = ![1, Y 1, Y 2] := by
      funext i; fin_cases i <;> simp [hYj]
    rw [hYe] at hrelC
    simp only [Matrix.cons_val_zero, one_mul, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at hrelC
    refine isCaseOne_or_isUnitSpecialCoordinate_of_chartZero φ hdimC hsing hx hq
      (v := Y 1) (w := Y 2) (c₀ := r) (hY 1) (hY 2) (by rw [← hYe, hYe] at *; simpa using hrelC) ?_
    refine exists_polynomial_of_mvPolynomial φ ![1, Polynomial.X, 0] (fun i => ?_) hloc
    fin_cases i
    · simp [hYj]
    · simp
    · simp
  · have hYe : Y = ![Y 0, 1, Y 2] := by
      funext i; fin_cases i <;> simp [hYj]
    refine isCaseOne_or_isUnitSpecialCoordinate_of_chartOne φ hdimC hsing hx hq
      (u := Y 0) (w := Y 2) (c₀ := r) (hY 0) (hY 2) ?_ ?_
    · rw [hYe] at hrelC
      simpa using hrelC
    refine exists_polynomial_of_mvPolynomial φ ![Polynomial.X, 1, 0] (fun i => ?_) hloc
    fin_cases i
    · simp
    · simp [hYj]
    · simp
  · exfalso
    rw [hYj] at hrelC
    exact one_notMem_maximalIdeal' C (mem_maximalIdeal_of_mul_self_add ht hrelC)

end Charts

/-! ### The local ring at a point of an affine chart of the blowup -/

section ChartData

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **The affine blowup algebra `A[𝔪/x_j]` is generated over `A` by the fractions `x_k/x_j`.** -/
theorem adjoin_range_affineBlowupFraction_eq_top {x : Fin 3 → A}
    (hx : Ideal.span (Set.range x) = maximalIdeal A) (j : Fin 3)
    (hxm : ∀ k, x k ∈ maximalIdeal A) :
    Algebra.adjoin A (Set.range fun k => affineBlowupFraction (maximalIdeal A) (x j)
      (Localization.Away (x j)) (hxm k)) = ⊤ := by
  set S := Localization.Away (x j)
  refine Subalgebra.map_injective
    (f := (affineBlowupAlgebra (maximalIdeal A) (x j) S).val) Subtype.val_injective ?_
  rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨i, rfl⟩
    exact (affineBlowupFraction (maximalIdeal A) (x j) S (hxm i)).2
  · rintro z ⟨y, hy, rfl⟩
    have hcf : ∀ i, algebraMap A S (x j) *
        ((affineBlowupFraction (maximalIdeal A) (x j) S (hxm i) : _) : S) =
        algebraMap A S (x i) := fun i => by
      rw [mul_comm]
      exact IsLocalization.mk'_spec S (x i) ⟨x j, Submonoid.mem_powers (x j)⟩
    rw [← hx, Ideal.span, Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, hc⟩ := hy
    have hkey : IsLocalization.mk' S y ⟨x j, Submonoid.mem_powers (x j)⟩
        = ∑ i, algebraMap A S (c i) *
          ((affineBlowupFraction (maximalIdeal A) (x j) S (hxm i) : _) : S) := by
      refine (IsLocalization.Away.algebraMap_isUnit (S := S) (x j)).mul_left_cancel ?_
      rw [IsLocalization.mk'_spec' S y ⟨x j, Submonoid.mem_powers (x j)⟩, ← hc,
        map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, map_mul, ← hcf i]
      ring
    rw [hkey]
    exact sum_mem fun i _ => mul_mem (Subalgebra.algebraMap_mem _ _)
      (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- **The data of a point of the chart at `x_j`, read in a local ring isomorphic to the local ring
of the chart ring there.** Let `R` be isomorphic to `A[𝔪/x_j]`, `D` its localization at a prime,
and `C ≅ D`, with `φ : A → C` the composite. Then the images `Yₖ` of the fractions `xₖ/x_j`
satisfy `Y_j = 1` and `xₖ = x_j·Yₖ` in `C`, the image of `x_j` is not zero, and every element of
`C` is a fraction of polynomials over `A` in the `Yₖ` with a unit denominator. -/
theorem exists_chartData {x : Fin 3 → A} (hx : Ideal.span (Set.range x) = maximalIdeal A)
    (j : Fin 3) {R D C : Type*} [CommRing R] [CommRing D] [CommRing C] [Algebra R D]
    (E : affineBlowupAlgebra (maximalIdeal A) (x j) (Localization.Away (x j)) ≃+* R)
    (pz : Ideal R) [pz.IsPrime] [IsLocalization.AtPrime D pz] (e : D ≃+* C) (φ : A →+* C)
    (hφ : ∀ b, φ b = e (algebraMap R D (E (algebraMap A _ b)))) :
    ∃ Y : Fin 3 → C, Y j = 1 ∧ (∀ k, φ (x k) = φ (x j) * Y k) ∧ φ (x j) ≠ 0 ∧
      ∀ c : C, ∃ (b : C) (P Q : MvPolynomial (Fin 3) A), IsUnit b ∧
        b * c = MvPolynomial.eval₂ φ Y P ∧ b = MvPolynomial.eval₂ φ Y Q := by
  classical
  set S := Localization.Away (x j)
  have hxm : ∀ k, x k ∈ maximalIdeal A := fun k => hx ▸ Ideal.subset_span ⟨k, rfl⟩
  set fr : Fin 3 → affineBlowupAlgebra (maximalIdeal A) (x j) S :=
    fun k => affineBlowupFraction (maximalIdeal A) (x j) S (hxm k) with hfr_def
  set κ : affineBlowupAlgebra (maximalIdeal A) (x j) S →+* C :=
    (e.toRingHom.comp (algebraMap R D)).comp E.toRingHom with hκ
  have hφκ : ∀ b, φ b = κ (algebraMap A _ b) := hφ
  have hκeval : ∀ P : MvPolynomial (Fin 3) A, κ (MvPolynomial.aeval fr P) =
      MvPolynomial.eval₂ φ (fun k => κ (fr k)) P := by
    intro P
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    congr 1
    ext b
    exact (hφκ b).symm
  have hgen : ∀ a : affineBlowupAlgebra (maximalIdeal A) (x j) S,
      ∃ P : MvPolynomial (Fin 3) A, MvPolynomial.aeval fr P = a := by
    intro a
    have : a ∈ Algebra.adjoin A (Set.range fr) := by
      rw [adjoin_range_affineBlowupFraction_eq_top hx j hxm]; trivial
    rwa [Algebra.adjoin_range_eq_range_aeval] at this
  refine ⟨fun k => κ (fr k), ?_, fun k => ?_, ?_, fun c => ?_⟩
  · have : fr j = 1 := by
      apply Subtype.ext
      show IsLocalization.mk' S (x j) ⟨x j, Submonoid.mem_powers (x j)⟩ = 1
      exact IsLocalization.mk'_self' (M := Submonoid.powers (x j)) S
        (x := ⟨x j, Submonoid.mem_powers (x j)⟩)
    simp only [this, map_one]
  · rw [hφκ, hφκ, ← map_mul, algebraMap_mul_affineBlowupFraction]
  · intro h0
    rw [hφκ] at h0
    simp only [hκ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_eq_zero_iff _ e.injective] at h0
    obtain ⟨⟨m, hm⟩, hm0⟩ := (IsLocalization.map_eq_zero_iff pz.primeCompl D _).mp h0
    simp only at hm0
    have : E.symm m = 0 := by
      have h1 : algebraMap A _ (x j) * E.symm m = 0 := by
        rw [mul_comm]
        apply E.injective
        rw [map_mul, E.apply_symm_apply, map_zero, hm0]
      exact (Stacks.Blowup.isRegular_algebraMap_affineBlowupAlgebra (maximalIdeal A) (x j)
        S).left (show _ * _ = _ * _ by rw [h1, mul_zero])
    rw [map_eq_zero_iff _ E.symm.injective] at this
    exact hm (this ▸ pz.zero_mem)
  · obtain ⟨d, rfl⟩ := e.surjective c
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective pz.primeCompl d
    obtain ⟨a₁, rfl⟩ := E.surjective r
    obtain ⟨a₂, ha₂⟩ := E.surjective s
    obtain ⟨P, rfl⟩ := hgen a₁
    obtain ⟨Q, hQ⟩ := hgen a₂
    refine ⟨e (algebraMap R D s), P, Q,
      (IsLocalization.map_units D s).map e, ?_, ?_⟩
    · rw [← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm,
        IsLocalization.mk'_mul_cancel_right, ← hκeval]
      rfl
    · rw [← hκeval, hQ, ← ha₂]
      rfl

end ChartData

/-! ### The blowup of a rational double point at a unit-special coordinate -/

section BlowUp

open CategoryTheory TopologicalSpace

/-- The ring map from a ring `A` to the local ring at a point of a scheme over `Spec(A)`:
`A ≅ Γ(Spec A)`, then the global sections, then the germ. -/
abbrev stalkHomOfSpec {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (x : X) : A →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom

/-- The ring map from a local ring `A` to the local ring at a point of the blowup of `Spec(A)` in
its maximal ideal. -/
abbrev blowUpStalkHom (A : Type u) [CommRing A] [IsLocalRing A]
    (x : blowUp (maximalIdealSheaf A)) :
    A →+* (blowUp (maximalIdealSheaf A)).presheaf.stalk x :=
  stalkHomOfSpec (blowUpToBase (maximalIdealSheaf A)) x

/-- `AlgebraicGeometry.stalkHomOfSpec` factors through the stalk map at the image point. -/
theorem stalkHomOfSpec_apply {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (x : X) (b : A) :
    stalkHomOfSpec f x b = (f.stalkMap x).hom
      (((Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).presheaf.germ ⊤ (f x) trivial).hom b) := by
  have h1 : (Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).presheaf.germ ⊤ (f x) trivial) ≫
        f.stalkMap x := by
    rw [Category.assoc]
    exact (congrArg ((Scheme.ΓSpecIso (.of A)).inv ≫ ·)
      (Scheme.Hom.germ_stalkMap f ⊤ x trivial)).symm
  exact congrArg (fun h => h.hom b) h1

/-- The sections over the whole space of the maximal ideal sheaf of `Spec(A)`. -/
theorem ideal_top_maximalIdealSheaf (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (maximalIdeal A).map (Scheme.ΓSpecIso (.of A)).inv.hom := by
  simp

/-- The map from `A` to the local ring at a point of a scheme over `Spec(A)` seen in an open
`j : Spec B ⟶ X`, given the compatibility of `j` with a ring map `Γ(Spec A) ⟶ B`. Stated for an
abstract scheme and chart, so that no concrete chart ring is unfolded. -/
theorem stalkHomOfSpec_comp_stalkMap {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) {B : CommRingCat.{u}} (j : Spec B ⟶ X) (w : Spec B)
    (q : (Spec (.of A)).presheaf.obj (Opposite.op ⊤) ⟶ B)
    (h : (Spec (.of A)).presheaf.germ ⊤ (f (j w)) trivial ≫ f.stalkMap (j w) ≫ j.stalkMap w =
      q ≫ StructureSheaf.toStalk B w) (b : A) :
    (j.stalkMap w).hom (stalkHomOfSpec f (j w) b) =
      (StructureSheaf.toStalk B w).hom (q.hom ((Scheme.ΓSpecIso (.of A)).inv.hom b)) := by
  rw [stalkHomOfSpec_apply]
  have h3 := congrArg (fun h => h.hom ((Scheme.ΓSpecIso (.of A)).inv.hom b)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
  exact h3.trans rfl

/-- The chart data at a point of the chart at `x_j` of the blowup of `Spec(A)` in its maximal
ideal. -/
theorem exists_chartData_blowupChartι (A : Type u) [CommRing A] [IsLocalRing A] {x : Fin 3 → A}
    (hx : Ideal.span (Set.range x) = maximalIdeal A) (j : Fin 3)
    (hg : (Scheme.ΓSpecIso (.of A)).inv.hom (x j) ∈
      (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩)
    (z : Spec (.of (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩))) :
    ∃ Y : Fin 3 → (blowUp (maximalIdealSheaf A)).presheaf.stalk
        (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩ z), Y j = 1 ∧
      (∀ k, blowUpStalkHom A
          (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩ z) (x k) =
        blowUpStalkHom A
          (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩ z) (x j) * Y k) ∧
      blowUpStalkHom A
        (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩ z) (x j) ≠ 0 ∧
      ∀ c, ∃ (b : (blowUp (maximalIdealSheaf A)).presheaf.stalk
          (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩ z))
        (P Q : MvPolynomial (Fin 3) A), IsUnit b ∧
        b * c = MvPolynomial.eval₂ (blowUpStalkHom A
          (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩ z)) Y P ∧
        b = MvPolynomial.eval₂ (blowUpStalkHom A
          (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩ z)) Y Q := by
  have hEx := exists_ringEquiv_blowupChartRing_ofIdealTop A (maximalIdeal A) (x j) ⟨_, hg⟩ rfl
  obtain ⟨E, hE⟩ := hEx
  have : z.asIdeal.IsPrime := z.isPrime
  let : Algebra (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩)
      ((Spec (.of (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
        ⟨_, hg⟩))).presheaf.stalk z) := StructureSheaf.stalkAlgebra _ z
  have : IsLocalization.AtPrime ((Spec (.of (blowupChartRing (maximalIdealSheaf A)
      ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩))).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ z
  have hkey := germ_comp_stalkMap_blowupChartι (I := maximalIdealSheaf A)
    (U := ⟨⊤, isAffineOpen_top _⟩) (a := ⟨_, hg⟩) z (TopologicalSpace.Opens.mem_top _)
  have h1 := stalkHomOfSpec_comp_stalkMap (blowUpToBase (maximalIdealSheaf A)) _ z _ hkey
  let e := (asIso ((blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩).stalkMap
    z)).symm.commRingCatIsoToRingEquiv
  have hφ : ∀ b, blowUpStalkHom A
      (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg⟩ z) b =
      e (algebraMap _ _ (E (algebraMap A _ b))) := by
    intro b
    refine Eq.trans ?_ (congrArg (fun r => e (algebraMap _ _ r)) (hE b)).symm
    exact e.symm_apply_eq.mp (h1 b)
  exact exists_chartData hx j E z.asIdeal e _ hφ

/-- **The chart data at a point of the blowup of `Spec(A)` in its maximal ideal.** For generators
`x₁, x₂, x₃` of the maximal ideal, every point lies in the chart at some `x_j`, and the local ring
there carries the data `AlgebraicGeometry.exists_chartData` describes, with
`AlgebraicGeometry.blowUpStalkHom` as the map from `A`. -/
theorem exists_chartData_blowUp (A : Type u) [CommRing A] [IsLocalRing A] {x : Fin 3 → A}
    (hx : Ideal.span (Set.range x) = maximalIdeal A) (w : blowUp (maximalIdealSheaf A)) :
    ∃ j : Fin 3, ∃ Y : Fin 3 → (blowUp (maximalIdealSheaf A)).presheaf.stalk w, Y j = 1 ∧
      (∀ k, blowUpStalkHom A w (x k) = blowUpStalkHom A w (x j) * Y k) ∧
      blowUpStalkHom A w (x j) ≠ 0 ∧
      ∀ c, ∃ (b : (blowUp (maximalIdealSheaf A)).presheaf.stalk w)
        (P Q : MvPolynomial (Fin 3) A), IsUnit b ∧
        b * c = MvPolynomial.eval₂ (blowUpStalkHom A w) Y P ∧
        b = MvPolynomial.eval₂ (blowUpStalkHom A w) Y Q := by
  have hxm : ∀ k, x k ∈ maximalIdeal A := fun k => hx ▸ Ideal.subset_span ⟨k, rfl⟩
  have hg : ∀ k, (Scheme.ΓSpecIso (.of A)).inv.hom (x k) ∈
      (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩ := fun k =>
    mem_ideal_ofIdealTop_isAffineOpen_top A (maximalIdeal A) (hxm k)
  have hspan : (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      Ideal.span (Set.range fun k => (Scheme.ΓSpecIso (.of A)).inv.hom (x k)) := by
    rw [ideal_top_maximalIdealSheaf, ← hx, Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨j, z, hz⟩ := exists_mem_range_blowupChartι (I := maximalIdealSheaf A)
    (U := ⟨⊤, isAffineOpen_top _⟩) (fun k => (Scheme.ΓSpecIso (.of A)).inv.hom (x k)) hg hspan
    w (TopologicalSpace.Opens.mem_top _)
  subst hz
  exact ⟨j, exists_chartData_blowupChartι A hx j (hg j) z⟩

/-- **[Stacks, Section 54.12], the final case, corrected.** Let `A` be the ring of a
Situation 0BGC and `e` a unit-special coordinate of `A`. At every singular point `x` of the
blowup of `Spec(A)` in its maximal ideal, either the local ring is in case I, or the maximal ideal
of `A` generates the ideal of `e` in `𝒪_{X, x}`, the residue field at `x` is that of `A`, and the
image of `e` is again a unit-special coordinate of `𝒪_{X, x}`. -/
theorem RationalDoublePointSituation.isCaseOne_or_isUnitSpecialCoordinate_stalk_blowUp
    (S : RationalDoublePointSituation.{u}) {e : S.A} (he : IsUnitSpecialCoordinate S.A e)
    (x : blowUp (maximalIdealSheaf S.A))
    (hx : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    IsCaseOne ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∨
      (Ideal.map (blowUpStalkHom S.A x) (IsLocalRing.maximalIdeal S.A) =
          Ideal.span {blowUpStalkHom S.A x e} ∧
        Function.Surjective
          ((residue ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)).comp
            (blowUpStalkHom S.A x)) ∧
        IsUnitSpecialCoordinate ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
          (blowUpStalkHom S.A x e)) := by
  obtain ⟨g, q, rfl, hspan, hq, hrel⟩ := he
  have hover := S.blowUpToBase_eq_closedPoint_of_mem_singularLocus x hx
  have hclosed := S.isClosed_singleton_of_mem_singularLocus_blowUp x hx
  have : IsLocalHom (blowUpStalkHom S.A x) :=
    isLocalHom_germ_appTop (blowUpToBase (maximalIdealSheaf S.A)) x hover
  have : IsLocallyNoetherian (blowUp (maximalIdealSheaf S.A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf S.A))
  have := S.isNormalDomain_stalk_blowUp x
  obtain ⟨j, Y, hYj, hY, hxj, hloc⟩ := exists_chartData_blowUp S.A hspan x
  exact isCaseOne_or_isUnitSpecialCoordinate_of_chart (blowUpStalkHom S.A x)
    (S.ringKrullDim_stalk_blowUp_eq_two x hclosed) hx hspan hq hrel j Y hYj hY hxj hloc

end BlowUp

end AlgebraicGeometry

end

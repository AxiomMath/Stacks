module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential

/-!
# The filtration of an even variable extension by the degree of the variable

Let `A` be a graded algebra with a differential and let `A⟨T⟩` be the algebra obtained by
adjoining a divided-power variable `T` of even degree `d`, as in Tag 09PM. Its elements are the
finite sums `∑ aₙ T⁽ⁿ⁾`, and this file equips it with the increasing filtration

`F⁰ ⊆ F¹ ⊆ F² ⊆ ⋯`, `Fᵖ = ⨁_{n ≤ p} A · T⁽ⁿ⁾`,

together with the two facts that make it a filtration of `A⟨T⟩` as a complex: each step is
carried into itself by the differential of Tag 09PM, and in a fixed total degree `m` the
filtration is exhaustive as soon as `p * d ≥ m`, since a monomial `aₙ T⁽ⁿ⁾` of total degree `m`
has `n * d ≤ m`.

The graded pieces are identified with the homogeneous pieces of `A`, shifted by the degree of
`T⁽ᵖ⁾`: in total degree `m` the quotient `Fᵖ / Fᵖ⁻¹` is `𝒜 (m - p * d)` through the coefficient
of `T⁽ᵖ⁾`, with inverse `a ↦ a T⁽ᵖ⁾`. This shift is what makes the first page of the spectral
sequence of the filtration a shift of the homology of `A`.

## Main definitions

* `DividedPowers.TateResolution.EvenVariableAlgebra.coeffFiltration` — the step `Fᵖ`, cut out by
  the vanishing of the coefficients of `T⁽ⁿ⁾` for `n > p`. The index is an integer, the negative
  steps being zero, as the index of a filtration of a complex has to be.
* `DividedPowers.TateResolution.EvenVariableAlgebra.coeffLinearMap` — the coefficient of `T⁽ⁿ⁾`,
  as a linear map.
* `DividedPowers.TateResolution.EvenVariableAlgebra.gradedPieceEquiv` — the identification of the
  graded piece of the filtration in total degree `m` with `𝒜 (m - p * d)`.

## Main results

* `DividedPowers.TateResolution.EvenVariableAlgebra.coeffFiltration_mono` and
  `DividedPowers.TateResolution.EvenVariableAlgebra.coeffFiltration_eq_bot` — the filtration is
  increasing, and vanishes in the negative steps.
* `DividedPowers.TateResolution.EvenVariableAlgebra.mem_coeffFiltration_of_mem_grade` — in total
  degree `m` the filtration is exhausted by the step `p` as soon as `m ≤ p * d`.
* `DividedPowers.TateResolution.evenPolynomialDifferential_coeff` — the coefficients of the
  differential of Tag 09PM: the coefficient of `T⁽ⁿ⁾` in `d x` is `dA` of the coefficient of
  `T⁽ⁿ⁾` in `x` plus the signed product of the coefficient of `T⁽ⁿ⁺¹⁾` with `f`.
* `DividedPowers.TateResolution.evenPolynomialDifferential_mem_coeffFiltration` — each step of
  the filtration is carried into itself by that differential.

## Implementation notes

The filtration is a condition on the coefficients, not a submodule of a direct sum: the
coefficients of an element of `A⟨T⟩` form a finitely supported family `ℕ →₀ A`, so `Fᵖ` is the
support condition `∀ n > p, x.coeff n = 0`. The scalars are left as a parameter `S`: the
statements are used both over the base ring of the grading and over a coefficient algebra sitting
in degree zero, and the condition does not refer to the scalars at all.

The coefficient formula for the differential is proved here from
`evenPolynomialDifferential_monomial` by induction on the coefficient expansion; it is the
identity that both the stability of the filtration and the first page of the spectral sequence of
the filtration are read off from.

## References

* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 0GZ6](https://stacks.math.columbia.edu/tag/0GZ6)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v w

namespace EvenVariableAlgebra

/-! ### The filtration -/

section Defs

variable {A : Type v} [Ring A]

/-- **The `p`-th step of the filtration of `A⟨T⟩` by the degree of the adjoined divided-power
variable**: the elements whose coefficient along `T⁽ⁿ⁾` vanishes for every `n` greater than `p`.
The index is an integer, so that the negative steps are zero and the filtration is indexed the
way a filtration of a complex is. -/
public def coeffFiltration (S : Type u) (A : Type v) [CommRing S] [Ring A] [Algebra S A]
    (p : ℤ) : Submodule S (EvenVariableAlgebra A) where
  carrier := {x | ∀ n : ℕ, p < (n : ℤ) → x.coeff n = 0}
  zero_mem' n _ := by simp
  add_mem' {x y} hx hy n hn := by
    rw [coeff_add, Finsupp.add_apply, hx n hn, hy n hn, add_zero]
  smul_mem' c x hx n hn := by
    rw [coeff_smul, Finsupp.smul_apply, hx n hn, smul_zero]

variable (S : Type u) [CommRing S] [Algebra S A]

/-- The coefficients of a difference. -/
@[simp]
public theorem coeff_sub (x y : EvenVariableAlgebra A) :
    (x - y).coeff = x.coeff - y.coeff := by
  rw [sub_eq_add_neg, coeff_add, coeff_neg, sub_eq_add_neg]

/-- Membership in a step of the filtration is the vanishing of the higher coefficients. -/
@[simp]
public theorem mem_coeffFiltration {p : ℤ} {x : EvenVariableAlgebra A} :
    x ∈ coeffFiltration S A p ↔ ∀ n : ℕ, p < (n : ℤ) → x.coeff n = 0 := Iff.rfl

/-- The filtration is increasing. -/
public theorem coeffFiltration_mono : Monotone (coeffFiltration S A) :=
  fun _ _ hpq _ hx n hn => hx n (lt_of_le_of_lt hpq hn)

/-- A monomial `a T⁽ⁿ⁾` lies in every step from `n` on. -/
public theorem monomial_mem_coeffFiltration {p : ℤ} {n : ℕ} (hn : (n : ℤ) ≤ p) (a : A) :
    monomial n a ∈ coeffFiltration S A p := by
  intro k hk
  rw [coeff_monomial, Finsupp.single_eq_of_ne (show k ≠ n by omega)]

/-- The negative steps of the filtration are zero: an element with no coefficients is zero. -/
public theorem coeffFiltration_eq_bot {p : ℤ} (hp : p < 0) : coeffFiltration S A p = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hx0 : x = 0 :=
    EvenVariableAlgebra.ext (Finsupp.ext fun n => by simpa using hx n (by omega))
  simp [hx0]

end Defs

/-! ### Exhaustiveness in a fixed total degree -/

section Grade

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (S : Type w) [CommRing S] [Algebra S A]

/-- **In a fixed total degree the filtration is exhaustive**: a homogeneous element of degree `m`
lies in the step `p` as soon as `m ≤ p * d`, because the coefficient of `T⁽ⁿ⁾` in an element of
degree `m` vanishes unless `n * d ≤ m`. -/
public theorem mem_coeffFiltration_of_mem_grade (𝒜 : ℕ → Submodule R A) {d m : ℕ} (hd : 0 < d)
    {p : ℤ} (hp : (m : ℤ) ≤ p * d) {x : EvenVariableAlgebra A} (hx : x ∈ grade 𝒜 d m) :
    x ∈ coeffFiltration S A p := by
  intro n hn
  have hlt : (m : ℤ) < (n : ℤ) * d := by
    have h1 : (p + 1) * (d : ℤ) ≤ (n : ℤ) * d :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    have h2 : (0 : ℤ) < d := by exact_mod_cast hd
    nlinarith
  have hnd : ¬ n * d ≤ m := fun h => not_le.2 hlt (by exact_mod_cast h)
  simpa [hnd] using (mem_grade_iff 𝒜 d m x).1 hx n

end Grade

/-! ### The coefficient maps and the graded pieces -/

section GradedPiece

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The coefficient of `T⁽ⁿ⁾`, as a linear map. -/
public def coeffLinearMap (S : Type w) (A : Type v) [CommRing S] [Ring A] [Algebra S A]
    (n : ℕ) : EvenVariableAlgebra A →ₗ[S] A where
  toFun x := x.coeff n
  map_add' x y := by rw [coeff_add, Finsupp.add_apply]
  map_smul' c x := by
    rw [coeff_smul, Finsupp.smul_apply]
    rfl

/-- `coeffLinearMap S A n` sends `x` to its coefficient of `T⁽ⁿ⁾`. -/
@[simp]
public theorem coeffLinearMap_apply (S : Type w) [CommRing S] [Algebra S A] (n : ℕ)
    (x : EvenVariableAlgebra A) : coeffLinearMap S A n x = x.coeff n := rfl

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : ℕ)

/-- The part of the filtration step `p` in total degree `m`. -/
public abbrev gradedStep (p : ℤ) (m : ℕ) : Submodule R (EvenVariableAlgebra A) :=
  coeffFiltration R A p ⊓ grade 𝒜 d m

omit [GradedAlgebra 𝒜] in
/-- The previous step is contained in the step. -/
public theorem gradedStep_pred_le (p : ℤ) (m : ℕ) :
    gradedStep 𝒜 d (p - 1) m ≤ gradedStep 𝒜 d p m :=
  inf_le_inf_right _ (coeffFiltration_mono R (by omega))

omit [GradedAlgebra 𝒜] in
/-- The coefficient of `T⁽ᵖ⁾` of an element of total degree `m` is homogeneous of degree
`m - p * d`. -/
public theorem coeff_mem_of_mem_gradedStep {p m : ℕ} (hpm : p * d ≤ m)
    {x : EvenVariableAlgebra A} (hx : x ∈ gradedStep 𝒜 d (p : ℤ) m) :
    x.coeff p ∈ 𝒜 (m - p * d) := by
  simpa [hpm] using (mem_grade_iff 𝒜 d m x).1 hx.2 p

/-- **The coefficient of `T⁽ᵖ⁾` on the filtration step `p` in total degree `m`**, as a linear map
to the homogeneous piece `𝒜 (m - p * d)` of the coefficient algebra. -/
public def gradedStepCoeff {p m : ℕ} (hpm : p * d ≤ m) :
    ↥(gradedStep 𝒜 d (p : ℤ) m) →ₗ[R] ↥(𝒜 (m - p * d)) :=
  LinearMap.codRestrict _ ((coeffLinearMap R A p).comp (gradedStep 𝒜 d (p : ℤ) m).subtype)
    fun x => coeff_mem_of_mem_gradedStep 𝒜 d hpm x.2

omit [GradedAlgebra 𝒜] in
/-- `gradedStepCoeff` sends `x` to its coefficient of `T⁽ᵖ⁾`. -/
@[simp]
public theorem gradedStepCoeff_apply {p m : ℕ} (hpm : p * d ≤ m)
    (x : ↥(gradedStep 𝒜 d (p : ℤ) m)) :
    (gradedStepCoeff 𝒜 d hpm x : A) = (x : EvenVariableAlgebra A).coeff p := rfl

omit [GradedAlgebra 𝒜] in
/-- A monomial `a T⁽ᵖ⁾` with `a` homogeneous of degree `m - p * d` lies on the filtration step
`p` in total degree `m`. -/
public theorem monomial_mem_gradedStep {p m : ℕ} (hpm : p * d ≤ m) {a : A}
    (ha : a ∈ 𝒜 (m - p * d)) : monomial p a ∈ gradedStep 𝒜 d (p : ℤ) m :=
  ⟨monomial_mem_coeffFiltration R le_rfl a, by
    simpa [hpm] using (monomial_mem_grade_iff 𝒜 d m p a).2 (by simpa [hpm] using ha)⟩

omit [GradedAlgebra 𝒜] in
/-- **The coefficient of `T⁽ᵖ⁾` is onto the homogeneous piece `𝒜 (m - p * d)`**, the monomial
`a T⁽ᵖ⁾` being a preimage of `a`. -/
public theorem surjective_gradedStepCoeff {p m : ℕ} (hpm : p * d ≤ m) :
    Function.Surjective (gradedStepCoeff 𝒜 d hpm) := fun a =>
  ⟨⟨monomial p (a : A), monomial_mem_gradedStep 𝒜 d hpm a.2⟩, Subtype.ext (by simp [monomial])⟩

omit [GradedAlgebra 𝒜] in
/-- **The coefficient of `T⁽ᵖ⁾` has the previous filtration step as its kernel**: an element of
the step `p` with vanishing coefficient along `T⁽ᵖ⁾` is exactly one of the step `p - 1`. -/
public theorem ker_gradedStepCoeff {p m : ℕ} (hpm : p * d ≤ m) :
    LinearMap.ker (gradedStepCoeff 𝒜 d hpm) =
      (gradedStep 𝒜 d ((p : ℤ) - 1) m).comap (gradedStep 𝒜 d (p : ℤ) m).subtype := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  refine ⟨fun hx => ⟨fun n hn => ?_, x.2.2⟩, fun hx => Subtype.ext (hx.1 p (by omega))⟩
  rcases eq_or_lt_of_le (show (p : ℤ) ≤ (n : ℤ) by omega) with h | h
  · obtain rfl : p = n := by exact_mod_cast h
    exact congrArg Subtype.val hx
  · exact x.2.1 n h

/-- **The graded piece of the filtration in total degree `m` is the homogeneous piece
`𝒜 (m - p * d)` of the coefficient algebra**, by the coefficient of `T⁽ᵖ⁾`. This is the degree
shift by `p * d` carried by the monomial `T⁽ᵖ⁾`, and it is what makes the first page of the
spectral sequence of the filtration a shift of the homology of `A`. -/
public def gradedPieceEquiv {p m : ℕ} (hpm : p * d ≤ m) :
    (↥(gradedStep 𝒜 d (p : ℤ) m) ⧸
        (gradedStep 𝒜 d ((p : ℤ) - 1) m).comap (gradedStep 𝒜 d (p : ℤ) m).subtype) ≃ₗ[R]
      ↥(𝒜 (m - p * d)) :=
  (Submodule.quotEquivOfEq _ _ (ker_gradedStepCoeff 𝒜 d hpm).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_gradedStepCoeff 𝒜 d hpm))

omit [GradedAlgebra 𝒜] in
/-- The graded piece identification sends the class of an element to its coefficient along
`T⁽ᵖ⁾`. -/
@[simp]
public theorem gradedPieceEquiv_mk {p m : ℕ} (hpm : p * d ≤ m)
    (x : ↥(gradedStep 𝒜 d (p : ℤ) m)) :
    (gradedPieceEquiv 𝒜 d hpm (Submodule.Quotient.mk x) : A) =
      (x : EvenVariableAlgebra A).coeff p := rfl

omit [GradedAlgebra 𝒜] in
/-- The inverse of the graded piece identification sends a homogeneous element `a` of degree
`m - p * d` to the class of the monomial `a T⁽ᵖ⁾`. -/
public theorem gradedPieceEquiv_symm_apply {p m : ℕ} (hpm : p * d ≤ m)
    {a : A} (ha : a ∈ 𝒜 (m - p * d)) :
    (gradedPieceEquiv 𝒜 d hpm).symm ⟨a, ha⟩ =
      Submodule.Quotient.mk ⟨monomial p a, monomial_mem_gradedStep 𝒜 d hpm ha⟩ :=
  (LinearEquiv.symm_apply_eq _).2
    (Subtype.ext (by
      rw [gradedPieceEquiv_mk]
      simp [monomial]))

end GradedPiece

end EvenVariableAlgebra

/-! ### Stability under the differential -/

section Differential

open EvenVariableAlgebra

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (dA : A →ₗ[R] A) (f : A)

/-- **Each step of the filtration is carried into itself by the differential of the even variable
extension of Tag 09PM.** The coefficient of `T⁽ⁿ⁾` in `d x` is built from the coefficients of
`T⁽ⁿ⁾` and `T⁽ⁿ⁺¹⁾` in `x`, both of which vanish above the step. -/
public theorem evenPolynomialDifferential_mem_coeffFiltration (S : Type w) [CommRing S]
    [Algebra S A] {p : ℤ} {x : EvenVariableAlgebra A} (hx : x ∈ coeffFiltration S A p) :
    evenPolynomialDifferential 𝒜 dA f x ∈ coeffFiltration S A p := by
  intro n hn
  rw [evenPolynomialDifferential_coeff 𝒜 dA f, hx n hn, hx (n + 1) (by push_cast; omega)]
  simp

end Differential

end DividedPowers.TateResolution

end

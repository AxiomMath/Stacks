module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Components
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowup
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# A regular model with an inseparable component: the algebra of the charts

Each chart of the model `X` of `Stacks.Models.InseparableModel` is `B = R[s][T] ⧸ (x T - y)` with
`(x, y)` one of `(π, s² - t)`, `(s² - t, π)`, `(1 - t s², π s²)`. In each case `x` and `y` are
coprime in the unique factorization domain `R[s]`, so `B` is a domain; `R[s] ⧸ (x, y)` is a field
(`κ`, `κ`, `k[s] ⧸ (1 - t s²)`), so `B ⧸ x B = (R[s] ⧸ (x, y))[T]` is regular and `B` is regular.

## Main results

* `Stacks.Models.InseparableModel.isDomain_chartRing`
* `Stacks.Models.InseparableModel.isRegularRing_chartRing`
* `Stacks.Models.InseparableModel.injective_algebraMap_chartRing`
* `Stacks.Models.InseparableModel.flat_chartRing`
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.Models.InseparableModel

/-! ### Reduction modulo `π` -/

/-- Reduction modulo `π` of the coefficients, `R[s] → k[s]`. -/
private abbrev red : R[X] →+* k[X] := mapRingHom (algebraMap R k)

private theorem red_surjective : Function.Surjective red :=
  map_surjective _ algebraMap_Rk_surjective

private theorem ker_red : RingHom.ker red = Ideal.span {C π} := by
  have h : RingHom.ker (algebraMap R k) = Ideal.span {π} := by
    rw [RingHom.algebraMap_toAlgebra, PowerSeries.ker_coeff_eq_max_ideal,
      PowerSeries.maximalIdeal_eq_span_X, π]
  rw [ker_mapRingHom, h, Ideal.map_span, Set.image_singleton]

private alias algebraMap_tR := algebraMap_Rk_tR

/-- If `q` reduces to an irreducible polynomial modulo `π`, then `(π, q)` is maximal in `R[s]`. -/
private theorem isMaximal_span_C_π (q : R[X]) (h : Irreducible (red q)) :
    (Ideal.span {C π, q}).IsMaximal := by
  have : Ideal.span {C π, q} = Ideal.comap red (Ideal.map red (Ideal.span {q})) := by
    rw [Ideal.comap_map_of_surjective _ red_surjective, ← RingHom.ker_eq_comap_bot, ker_red,
      Ideal.span_insert, sup_comm]
  rw [this, Ideal.map_span, Set.image_singleton]
  have := PrincipalIdealRing.isMaximal_of_irreducible h
  exact Ideal.comap_isMaximal_of_surjective _ red_surjective

private theorem irreducible_red_X_sq_sub : Irreducible (red (X ^ 2 - C tR)) := by
  have : red (X ^ 2 - C tR) = κpoly := by simp [κpoly, algebraMap_tR]
  rw [this]
  exact irreducible_κpoly

private theorem t_ne_zero : t ≠ 0 := RatFunc.X_ne_zero

private theorem irreducible_red_one_sub : Irreducible (red (1 - C tR * X ^ 2)) := by
  have : red (1 - C tR * X ^ 2) = 1 - C t * X ^ 2 := by simp [algebraMap_tR]
  rw [this]
  have hdeg : (1 - C t * X ^ 2 : k[X]).natDegree = 2 := by
    rw [sub_eq_neg_add, ← C_1, natDegree_add_C, natDegree_neg, natDegree_C_mul_X_pow _ _ t_ne_zero]
  refine irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) fun a ha => ?_
  simp only [IsRoot, eval_sub, eval_one, eval_mul, eval_C, eval_pow, eval_X] at ha
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  apply pow_two_ne_t a⁻¹
  field_simp
  linear_combination ha

/-- `R[s] ⧸ (x, y)` is a field. -/
private theorem isMaximal_span_chartX_chartY (c : Fin 3) :
    (Ideal.span {chartX c, chartY c}).IsMaximal := by
  fin_cases c
  · exact isMaximal_span_C_π _ irreducible_red_X_sq_sub
  · show (Ideal.span {X ^ 2 - C tR, C π}).IsMaximal
    rw [Set.pair_comm]
    exact isMaximal_span_C_π _ irreducible_red_X_sq_sub
  · show (Ideal.span {chartX 2, chartY 2}).IsMaximal
    have : Ideal.span {chartX 2, chartY 2} = Ideal.span {C π, 1 - C tR * X ^ 2} := by
      refine le_antisymm ?_ ?_
      · rw [Ideal.span_le, Set.pair_subset_iff]
        refine ⟨Ideal.subset_span (by simp [chartX]), Ideal.mem_span_pair.mpr ⟨X ^ 2, 0, ?_⟩⟩
        rw [show chartY 2 = C π * X ^ 2 from rfl]
        ring
      · rw [Ideal.span_le, Set.pair_subset_iff]
        refine ⟨Ideal.mem_span_pair.mpr ⟨C π, C tR, ?_⟩, Ideal.subset_span (by simp [chartX])⟩
        simp only [chartX, chartY]
        simp
        ring
    rw [this]
    exact isMaximal_span_C_π _ irreducible_red_one_sub

/-! ### The chart equation -/

private theorem π_ne_zero : π ≠ 0 := irreducible_π.ne_zero

private theorem prime_C_π : Prime (C π : R[X]) := prime_C_iff.mpr irreducible_π.prime

private theorem not_C_π_dvd_of_coeff {q : R[X]} {i : ℕ} (h : q.coeff i = 1) : ¬ C π ∣ q := by
  rw [C_dvd_iff_dvd_coeff]
  intro hd
  have := hd i
  rw [h] at this
  exact irreducible_π.not_isUnit (isUnit_of_dvd_one this)

private theorem chartX_ne_zero (c : Fin 3) : chartX c ≠ 0 := by
  fin_cases c
  · simpa [chartX] using π_ne_zero
  · intro h
    have := congrArg (coeff · 2) h
    simp [chartX] at this
  · intro h
    have := congrArg (coeff · 0) h
    simp [chartX, coeff_C] at this

private theorem isRelPrime_chartX_chartY (c : Fin 3) : IsRelPrime (chartX c) (chartY c) := by
  have h0 : IsRelPrime (C π) (X ^ 2 - C tR : R[X]) :=
    prime_C_π.irreducible.isRelPrime_iff_not_dvd.mpr
      (not_C_π_dvd_of_coeff (i := 2) (by simp))
  fin_cases c
  · exact h0
  · exact h0.symm
  · show IsRelPrime (1 - C tR * X ^ 2) (C π * X ^ 2)
    refine IsRelPrime.mul_right ?_ (IsRelPrime.pow_right ?_)
    · exact (prime_C_π.irreducible.isRelPrime_iff_not_dvd.mpr
        (not_C_π_dvd_of_coeff (i := 0) (by simp [coeff_C]))).symm
    · refine (irreducible_X.isRelPrime_iff_not_dvd.mpr ?_).symm
      rw [X_dvd_iff]
      simp [coeff_C]

/-- The chart equation as a linear polynomial in `T` over `R[s]`. -/
private theorem chartEq_eq_C_mul_X_add_C (c : Fin 3) :
    chartEq c = C (chartX c) * X + C (-chartY c) := by
  simp [chartEq, sub_eq_add_neg]

private theorem prime_chartEq (c : Fin 3) : Prime (chartEq c) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime, chartEq_eq_C_mul_X_add_C]
  exact irreducible_C_mul_X_add_C (chartX_ne_zero c) (isRelPrime_chartX_chartY c).neg_right

private theorem natDegree_chartEq (c : Fin 3) : (chartEq c).natDegree = 1 := by
  rw [chartEq_eq_C_mul_X_add_C, natDegree_linear (chartX_ne_zero c)]

/-- Each chart ring `R[s][T] ⧸ (x T - y)` is an integral domain. -/
theorem isDomain_chartRing (c : Fin 3) : IsDomain (chartRing c) := by
  rw [Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_prime (prime_chartEq c).ne_zero]
  exact prime_chartEq c

private theorem algebraMap_poly_chartRing (c : Fin 3) (f : R[X]) :
    algebraMap R[X] (chartRing c) f = Ideal.Quotient.mk (Ideal.span {chartEq c}) (C f) := by
  rw [IsScalarTower.algebraMap_apply R[X] R[X][X] (chartRing c), Ideal.Quotient.algebraMap_eq,
    algebraMap_eq]

private theorem injective_algebraMap_poly_chartRing (c : Fin 3) :
    Function.Injective (algebraMap R[X] (chartRing c)) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  rw [algebraMap_poly_chartRing, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hf
  by_contra hf0
  have := natDegree_le_of_dvd hf (C_ne_zero.mpr hf0)
  rw [natDegree_chartEq, natDegree_C] at this
  exact absurd this (by norm_num)

/-- The structure map `R → R[s][T] ⧸ (x T - y)` of each chart ring is injective. -/
theorem injective_algebraMap_chartRing (c : Fin 3) :
    Function.Injective (algebraMap R (chartRing c)) := by
  rw [IsScalarTower.algebraMap_eq R R[X] (chartRing c)]
  exact (injective_algebraMap_poly_chartRing c).comp (by rw [algebraMap_eq]; exact C_injective)

/-- Each chart ring `R[s][T] ⧸ (x T - y)` is flat over `R`. -/
theorem flat_chartRing (c : Fin 3) : Module.Flat R (chartRing c) := by
  have := isDomain_chartRing c
  have : Module.IsTorsionFree R (chartRing c) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (injective_algebraMap_chartRing c)
  infer_instance

/-- In the chart, `x T = y`. -/
private theorem chartX_mul_T (c : Fin 3) :
    Ideal.Quotient.mk (Ideal.span {chartEq c}) (C (chartX c)) *
        Ideal.Quotient.mk (Ideal.span {chartEq c}) X =
      Ideal.Quotient.mk (Ideal.span {chartEq c}) (C (chartY c)) := by
  rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- Every element of the chart times a power of `x` comes from `R[s]`. -/
private theorem exists_mul_chartX_pow (c : Fin 3) (b : chartRing c) :
    ∃ (n : ℕ) (a : R[X]), b * algebraMap R[X] (chartRing c) (chartX c) ^ n =
      algebraMap R[X] (chartRing c) a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [algebraMap_poly_chartRing]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨n, a, ha⟩ := hp
    obtain ⟨m, b, hb⟩ := hq
    refine ⟨n + m, a * chartX c ^ m + b * chartX c ^ n, ?_⟩
    simp only [map_add, map_mul, map_pow, pow_add] at ha hb ⊢
    linear_combination
      (Ideal.Quotient.mk (Ideal.span {chartEq c}) (C (chartX c)) ^ m) * ha +
      (Ideal.Quotient.mk (Ideal.span {chartEq c}) (C (chartX c)) ^ n) * hb
  | monomial n a =>
    refine ⟨n, a * chartY c ^ n, ?_⟩
    rw [← C_mul_X_pow_eq_monomial, C_mul, C_pow, map_mul, map_mul, map_pow, map_pow,
      ← chartX_mul_T]
    ring

/-- Each chart ring `R[s][T] ⧸ (x T - y)` is a regular ring. -/
theorem isRegularRing_chartRing (c : Fin 3) : IsRegularRing (chartRing c) := by
  have := isDomain_chartRing c
  set I := Ideal.span {chartX c, chartY c}
  have := isMaximal_span_chartX_chartY c
  let := Ideal.Quotient.field I
  set Φ : R[X][X] →+* (R[X] ⧸ I)[X] := mapRingHom (Ideal.Quotient.mk I)
  have hΦ : Function.Surjective Φ := map_surjective _ Ideal.Quotient.mk_surjective
  have hker : Ideal.span {chartEq c} ⊔ Ideal.span {C (chartX c)} = RingHom.ker Φ := by
    rw [ker_mapRingHom, Ideal.mk_ker, Ideal.map_span, Set.image_pair]
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_span_pair.mpr ⟨X, -1, by simp [chartEq]; ring⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    · rw [Ideal.span_le, Set.pair_subset_iff]
      refine ⟨Ideal.mem_sup_right (Ideal.subset_span rfl), ?_⟩
      have : C (chartY c) = X * C (chartX c) - chartEq c := by simp [chartEq]
      rw [this]
      exact sub_mem (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
        (Ideal.mem_sup_left (Ideal.subset_span rfl))
  have hJ : Ideal.span {algebraMap R[X] (chartRing c) (chartX c)} =
      (Ideal.span {C (chartX c)}).map (Ideal.Quotient.mk (Ideal.span {chartEq c})) := by
    rw [Ideal.map_span, Set.image_singleton, algebraMap_poly_chartRing]
  let e : chartRing c ⧸ Ideal.span {algebraMap R[X] (chartRing c) (chartX c)} ≃+*
      (R[X] ⧸ I)[X] :=
    ((Ideal.quotEquivOfEq hJ).trans (DoubleQuot.quotQuotEquivQuotSup _ _)).trans
      ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hΦ))
  have : IsRegularRing (chartRing c ⧸ Ideal.span {algebraMap R[X] (chartRing c) (chartX c)}) :=
    IsRegularRing.of_ringEquiv e.symm
  exact Stacks.Blowup.isRegularRing_of_quotient_away (injective_algebraMap_poly_chartRing c)
    (chartX c) (chartX_ne_zero c) (exists_mul_chartX_pow c)

end Stacks.Models.InseparableModel

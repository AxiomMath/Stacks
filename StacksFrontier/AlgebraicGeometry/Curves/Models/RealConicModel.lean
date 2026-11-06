module

public import StacksFrontier.AlgebraicGeometry.Curves.DegenerateConicBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurveDimension
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PlaneCurveModelBaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.RingTheory.NodalChart.Regularity

/-!
# The conic `T₁² + T₂² = πT₀²` over a discrete valuation ring

Let `R` be a discrete valuation ring with uniformizer `π` in which `2` is invertible, and let

`X = V(T₁² + T₂² - πT₀²) ⊆ ℙ²_R`.

For `R = ℝ[[π]]` this is the scheme of [Stacks, Tag 0CDL]. This file shows that `X` is regular,
from its three standard charts.

## Main definitions

* `Stacks.Models.RealConicModel.equation`: the form `T₁² + T₂² - πT₀²`.
* `Stacks.Models.RealConicModel.scheme`: the plane curve `X` it cuts out.

## Main results

* `Stacks.Models.RealConicModel.isRegular_scheme`: `X` is regular.

## Implementation notes

The chart rings are `R[Y₀, Y₁]/(Y₀² + Y₁² - π)` on `D₊(T₀)` and `R[Y₀, Y₁]/(1 + Y₁² - πY₀²)` on
`D₊(T₁)` and `D₊(T₂)`. Each is a hypersurface in the regular ring `R[Y₀, Y₁]`, and the hypersurface
criterion `Stacks.isRegularRing_quotient_span_singleton_of_forall_notMem_sq` asks that the
equation not lie in the square of the maximal ideal at any prime containing it. Away from the
point `(π, Y₀, Y₁)` of the first chart a partial derivative of the equation is a unit there,
because `2` is invertible; at that point the equation is `-π` modulo the square of the maximal
ideal, and `π` is not in that square (`Stacks.C_notMem_sq_localization_nodalOriginIdeal`).

## References

* [Stacks Project, Tag 0CDL](https://stacks.math.columbia.edu/tag/0CDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial IsLocalRing

universe u

namespace Stacks.Models.RealConicModel

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (π : R)

/-- The quadratic form `T₁² + T₂² - πT₀²`. -/
def equation : MvPolynomial (Fin 3) R := X 1 ^ 2 + X 2 ^ 2 - C π * X 0 ^ 2

/-- The form `T₁² + T₂² - πT₀²` is homogeneous of degree `2`. -/
theorem isHomogeneous_equation : (equation π).IsHomogeneous 2 := by
  refine IsHomogeneous.sub (IsHomogeneous.add ?_ ?_) ?_
  · simpa using (isHomogeneous_X R (1 : Fin 3)).pow 2
  · simpa using (isHomogeneous_X R (2 : Fin 3)).pow 2
  · simpa using (isHomogeneous_C (Fin 3) π).mul ((isHomogeneous_X R (0 : Fin 3)).pow 2)

/-- **The conic `X = V(T₁² + T₂² - πT₀²) ⊆ ℙ²_R`.** -/
abbrev scheme : Scheme.{u} := PlaneCurveModel.scheme (equation π) (isHomogeneous_equation π)

/-- The structure morphism `X ⟶ Spec R`. -/
abbrev toSpec : scheme π ⟶ Spec (CommRingCat.of R) :=
  PlaneCurveModel.toSpec (equation π) (isHomogeneous_equation π)

/-- The coordinate `T₀` does not divide `T₁² + T₂² - πT₀²`: the form is `1` at `(0 : 1 : 0)`. -/
theorem not_X_zero_dvd_equation [Nontrivial R] :
    ¬ (X 0 : MvPolynomial (Fin 3) R) ∣ equation π :=
  PlaneCurveModel.not_X_dvd_of_eval_ne_zero (equation π) (v := ![0, 1, 0]) rfl
    (by simp [equation])

/-! ### The chart equations -/

/-- The dehomogenization of `T₁² + T₂² - πT₀²` at `T₀` is `Y₀² + Y₁² - π`. -/
theorem dehomCoeff_equation_zero :
    Stacks.ProjectiveChart.dehomCoeff R 0 (equation π) = X 0 ^ 2 + X 1 ^ 2 - C π := by
  have h0 : finSuccEquiv' (0 : Fin 3) 0 = none := by decide
  have h1 : finSuccEquiv' (0 : Fin 3) 1 = some 0 := by decide
  have h2 : finSuccEquiv' (0 : Fin 3) 2 = some 1 := by decide
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval, equation]
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, h0, h1, h2,
    Option.elim_none, Option.elim_some, algebraMap_eq]
  ring

/-- The dehomogenization of `T₁² + T₂² - πT₀²` at `T₁` is `1 + Y₁² - πY₀²`. -/
theorem dehomCoeff_equation_one :
    Stacks.ProjectiveChart.dehomCoeff R 1 (equation π) = 1 + X 1 ^ 2 - C π * X 0 ^ 2 := by
  have h0 : finSuccEquiv' (1 : Fin 3) 0 = some 0 := by decide
  have h1 : finSuccEquiv' (1 : Fin 3) 1 = none := by decide
  have h2 : finSuccEquiv' (1 : Fin 3) 2 = some 1 := by decide
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval, equation]
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, h0, h1, h2,
    Option.elim_none, Option.elim_some, algebraMap_eq]
  ring

/-- The dehomogenization of `T₁² + T₂² - πT₀²` at `T₂` is `1 + Y₁² - πY₀²`. -/
theorem dehomCoeff_equation_two :
    Stacks.ProjectiveChart.dehomCoeff R 2 (equation π) = 1 + X 1 ^ 2 - C π * X 0 ^ 2 := by
  have h0 : finSuccEquiv' (2 : Fin 3) 0 = some 0 := by decide
  have h1 : finSuccEquiv' (2 : Fin 3) 1 = some 1 := by decide
  have h2 : finSuccEquiv' (2 : Fin 3) 2 = none := by decide
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval, equation]
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, h0, h1, h2,
    Option.elim_none, Option.elim_some, algebraMap_eq]
  ring

/-! ### Coefficients of the chart equations -/

/-- The coefficient of `Y₀²` in `Y₀² + Y₁² - a` is `1`. -/
theorem coeff_chart_zero (a : R) :
    (X 0 ^ 2 + X 1 ^ 2 - C a : MvPolynomial (Fin 2) R).coeff (Finsupp.single 0 2) = 1 := by
  have h : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 :=
    (Finsupp.single_ne_zero.mpr two_ne_zero).symm
  simp [coeff_X_pow, coeff_C, Finsupp.single_eq_single_iff, h]

/-- The coefficient of `Y₁²` in `1 + Y₁² - aY₀²` is `1`. -/
theorem coeff_chart_one (a : R) :
    (1 + X 1 ^ 2 - C a * X 0 ^ 2 : MvPolynomial (Fin 2) R).coeff (Finsupp.single 1 2) = 1 := by
  have h : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 :=
    (Finsupp.single_ne_zero.mpr two_ne_zero).symm
  simp [coeff_X_pow, coeff_C_mul, coeff_one, Finsupp.single_eq_single_iff, h]

/-! ### Regularity of the chart rings -/

/-- If a partial derivative of `f` is not in the prime `p`, then `f` is not in the square of the
maximal ideal of the localization at `p`. -/
private theorem notMem_sq_of_pderiv_notMem (i : Fin 2) {f : MvPolynomial (Fin 2) R}
    {p : Ideal (MvPolynomial (Fin 2) R)} [p.IsPrime] (h : pderiv (R := R) i f ∉ p) :
    algebraMap (MvPolynomial (Fin 2) R) (Localization.AtPrime p) f ∉
      maximalIdeal (Localization.AtPrime p) ^ 2 :=
  notMem_sq_of_derivation ((pderiv (R := R) i).restrictScalars ℤ) h

/-- If `2` is a unit, `2 * a ∈ p` implies `a ∈ p` for a prime `p`. -/
private theorem mem_of_two_mul_mem (h2 : IsUnit (2 : R)) {p : Ideal (MvPolynomial (Fin 2) R)}
    (hp : p.IsPrime) {a : MvPolynomial (Fin 2) R} (h : 2 * a ∈ p) : a ∈ p :=
  (hp.mem_or_mem h).resolve_left fun h' => hp.ne_top (Ideal.eq_top_of_isUnit_mem _ h'
    (by simpa only [map_ofNat] using h2.map (C : R →+* MvPolynomial (Fin 2) R)))

variable [IsDomain R] [IsDiscreteValuationRing R] {π}

omit [IsDiscreteValuationRing R] in
/-- At the origin `(π, Y₀, Y₁)` the equation `Y₀² + Y₁² - π` is not in the square of the maximal
ideal of the localization. -/
private theorem sum_sq_sub_C_notMem_sq_localization_nodalOriginIdeal (hπ : π ≠ 0)
    [(nodalOriginIdeal R π).IsPrime] :
    algebraMap (MvPolynomial (Fin 2) R) (Localization.AtPrime (nodalOriginIdeal R π))
        (X 0 ^ 2 + X 1 ^ 2 - C π)
      ∉ maximalIdeal (Localization.AtPrime (nodalOriginIdeal R π)) ^ 2 := by
  intro hsq
  refine C_notMem_sq_localization_nodalOriginIdeal (R := R) hπ ?_
  have hXX : algebraMap (MvPolynomial (Fin 2) R)
      (Localization.AtPrime (nodalOriginIdeal R π)) (X 0 * X 0 + X 1 * X 1)
      ∈ maximalIdeal (Localization.AtPrime (nodalOriginIdeal R π)) ^ 2 := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (nodalOriginIdeal R π), ← Ideal.map_pow]
    refine Ideal.mem_map_of_mem _ ?_
    rw [pow_two]
    exact add_mem (Ideal.mul_mem_mul (X_mem_nodalOriginIdeal π 0) (X_mem_nodalOriginIdeal π 0))
      (Ideal.mul_mem_mul (X_mem_nodalOriginIdeal π 1) (X_mem_nodalOriginIdeal π 1))
  have hCeq : algebraMap (MvPolynomial (Fin 2) R)
      (Localization.AtPrime (nodalOriginIdeal R π)) (C π) =
      algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime (nodalOriginIdeal R π)) (X 0 * X 0 + X 1 * X 1) -
      algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime (nodalOriginIdeal R π)) (X 0 ^ 2 + X 1 ^ 2 - C π) := by
    rw [← map_sub]
    congr 1
    ring
  rw [hCeq]
  exact sub_mem hXX hsq

/-- **`R[Y₀, Y₁]/(Y₀² + Y₁² - π)` is a regular ring.** At a prime not containing `Yᵢ` the partial
derivative `2Yᵢ` is a unit; a prime containing both coordinates and the equation contains `π`, so
it is the maximal ideal `(π, Y₀, Y₁)`, where the equation is `-π` modulo the square of the
maximal ideal. -/
theorem isRegularRing_chart_zero (hπ : Irreducible π) (h2 : IsUnit (2 : R)) :
    IsRegularRing (MvPolynomial (Fin 2) R ⧸ Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - C π :
      MvPolynomial (Fin 2) R)}) := by
  have hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  refine isRegularRing_quotient_span_singleton_of_forall_notMem_sq _ ?_
  intro p hp hfp
  have hderiv : ∀ i : Fin 2, X i ∉ p →
      algebraMap (MvPolynomial (Fin 2) R) (Localization.AtPrime p)
        (X 0 ^ 2 + X 1 ^ 2 - C π) ∉ maximalIdeal (Localization.AtPrime p) ^ 2 := by
    intro i hi
    refine notMem_sq_of_pderiv_notMem i fun hmem => hi (mem_of_two_mul_mem h2 hp ?_)
    rwa [show pderiv (R := R) i (X 0 ^ 2 + X 1 ^ 2 - C π) = 2 * X i by
      fin_cases i <;> simp [pderiv_X]] at hmem
  by_cases hx0 : X 0 ∈ p
  · by_cases hx1 : X 1 ∈ p
    · have hC : C π ∈ p := by
        rw [← show (X 0 * X 0 + X 1 * X 1 : MvPolynomial (Fin 2) R) - (X 0 ^ 2 + X 1 ^ 2 - C π) =
            C π by ring]
        exact sub_mem (add_mem (Ideal.mul_mem_right _ _ hx0) (Ideal.mul_mem_right _ _ hx1)) hfp
      have hle : nodalOriginIdeal R π ≤ p := by
        rw [nodalOriginIdeal, Ideal.span_le]
        rintro z (rfl | rfl | rfl) <;> assumption
      obtain rfl : nodalOriginIdeal R π = p :=
        (isMaximal_nodalOriginIdeal hmax).eq_of_le hp.ne_top hle
      exact sum_sq_sub_C_notMem_sq_localization_nodalOriginIdeal hπ.ne_zero
    · exact hderiv 1 hx1
  · exact hderiv 0 hx0

/-- **`R[Y₀, Y₁]/(1 + Y₁² - πY₀²)` is a regular ring.** At every prime containing the equation one
of the partial derivatives `2Y₁` and `-2πY₀` is a unit, since a prime containing `Y₁` and `πY₀`
contains `1 = (1 + Y₁² - πY₀²) - Y₁ · Y₁ + πY₀ · Y₀`. -/
theorem isRegularRing_chart_one (h2 : IsUnit (2 : R)) :
    IsRegularRing (MvPolynomial (Fin 2) R ⧸ Ideal.span {(1 + X 1 ^ 2 - C π * X 0 ^ 2 :
      MvPolynomial (Fin 2) R)}) := by
  refine isRegularRing_quotient_span_singleton_of_forall_notMem_sq _ ?_
  intro p hp hfp
  by_cases hx1 : X 1 ∈ p
  · by_cases hx0 : C π * X 0 ∈ p
    · exfalso
      refine hp.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
      rw [← show (1 + X 1 ^ 2 - C π * X 0 ^ 2 : MvPolynomial (Fin 2) R) - X 1 * X 1 +
          (C π * X 0) * X 0 = 1 by ring]
      exact add_mem (sub_mem hfp (Ideal.mul_mem_right _ _ hx1)) (Ideal.mul_mem_right _ _ hx0)
    · refine notMem_sq_of_pderiv_notMem 0 fun h => hx0 (mem_of_two_mul_mem h2 hp ?_)
      rwa [show pderiv (R := R) 0 (1 + X 1 ^ 2 - C π * X 0 ^ 2 : MvPolynomial (Fin 2) R) =
        -(2 * (C π * X 0)) by simp [pderiv_X]; ring, neg_mem_iff] at h
  · refine notMem_sq_of_pderiv_notMem 1 fun h => hx1 (mem_of_two_mul_mem h2 hp ?_)
    rwa [show pderiv (R := R) 1 (1 + X 1 ^ 2 - C π * X 0 ^ 2 : MvPolynomial (Fin 2) R) =
      2 * X 1 by simp [pderiv_X]] at h

/-! ### Flatness of the chart rings -/

/-- If some coefficient of `f` is a unit, `π ^ n * g ∈ (f)` implies `g ∈ (f)`. -/
private theorem mem_span_singleton_of_C_pow_mul_mem (hπ : Irreducible π)
    {f : MvPolynomial (Fin 2) R} {m : Fin 2 →₀ ℕ} (hm : IsUnit (f.coeff m)) (n : ℕ)
    {g : MvPolynomial (Fin 2) R}
    (hg : C (π ^ n) * g ∈ Ideal.span {f}) : g ∈ Ideal.span {f} := by
  have hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  let := Ideal.Quotient.field (Ideal.span {π})
  set q := Ideal.Quotient.mk (Ideal.span {π})
  have hf : MvPolynomial.map q f ≠ 0 := by
    intro h
    have hc := congrArg (fun p => p.coeff m) h
    simp only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    exact (hm.map q).ne_zero hc
  have hCπ : (C π : MvPolynomial (Fin 2) R) ≠ 0 := fun h => hπ.ne_zero (C_eq_zero.mp h)
  -- `π` is a nonzerodivisor modulo `f`.
  have hstep : ∀ g : MvPolynomial (Fin 2) R, C π * g ∈ Ideal.span {f} → g ∈ Ideal.span {f} := by
    intro g hg
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hg
    have h0 : MvPolynomial.map q h * MvPolynomial.map q f = 0 := by
      rw [← map_mul, hh, map_mul, map_C]
      simp [q]
    have hh0 : MvPolynomial.map q h = 0 := (mul_eq_zero.mp h0).resolve_right hf
    have hmem : h ∈ Ideal.map (C : R →+* MvPolynomial (Fin 2) R) (Ideal.span {π}) := by
      rwa [← Ideal.mk_ker (I := Ideal.span {π}), ← MvPolynomial.ker_map]
    rw [Ideal.map_span, Set.image_singleton] at hmem
    obtain ⟨h', rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    have : C π * g = C π * (h' * f) := by rw [← hh]; ring
    rw [mul_left_cancel₀ hCπ this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)
  induction n generalizing g with
  | zero => simpa using hg
  | succ n ih => exact ih (hstep _ (by rwa [← mul_assoc, ← map_mul, ← pow_succ']))

/-- **A hypersurface `R[Y₀, Y₁]/(f)` over a discrete valuation ring is flat** as soon as some
coefficient of `f` is a unit. It is torsion-free: if `πg ∈ (f)`, say `πg = fh`, then `f h ≡ 0`
modulo `π` with `f ≢ 0`, so `π ∣ h` and `g ∈ (f)`. -/
theorem flat_quotient_of_isUnit_coeff (hπ : Irreducible π) (f : MvPolynomial (Fin 2) R)
    {m : Fin 2 →₀ ℕ} (hm : IsUnit (f.coeff m)) :
    Module.Flat R (MvPolynomial (Fin 2) R ⧸ Ideal.span {f}) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  constructor
  intro r hr x y hxy
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr.ne_zero hπ
  rw [← sub_eq_zero]
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (x - y)
  have h0 : r • (x - y) = 0 := by rwa [smul_sub, sub_eq_zero]
  rw [← hg] at h0 ⊢
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h0
  have h1 : C (π ^ n) * (C (u : R) * g) ∈ Ideal.span {f} := by
    rwa [← mul_assoc, ← map_mul, mul_comm (π ^ n), ← hu]
  rw [Ideal.Quotient.eq_zero_iff_mem, show g = C ((u⁻¹ : Rˣ) : R) * (C (u : R) * g) by
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]]
  exact Ideal.mul_mem_left _ _ (mem_span_singleton_of_C_pow_mul_mem hπ hm n h1)

/-- **The conic is flat over `R`**, `π` being a uniformizer: each chart equation has a
coefficient equal to `1`. -/
theorem flat_toSpec (hπ : Irreducible π) : Flat (toSpec π) := by
  refine PlaneCurveModel.hasRingHomProperty_toSpec (P := @Flat) (Q := RingHom.Flat)
    (equation π) (isHomogeneous_equation π) 0 (not_X_zero_dvd_equation π) fun k => ?_
  rw [RingHom.flat_algebraMap_iff]
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [dehomCoeff_equation_zero]
    exact flat_quotient_of_isUnit_coeff hπ _ (m := Finsupp.single 0 2)
      (by rw [coeff_chart_zero]; exact isUnit_one)
  · rw [dehomCoeff_equation_one]
    exact flat_quotient_of_isUnit_coeff hπ _ (m := Finsupp.single 1 2)
      (by rw [coeff_chart_one]; exact isUnit_one)
  · rw [dehomCoeff_equation_two]
    exact flat_quotient_of_isUnit_coeff hπ _ (m := Finsupp.single 1 2)
      (by rw [coeff_chart_one]; exact isUnit_one)

/-! ### Regularity of the conic -/

/-- **The conic `X = V(T₁² + T₂² - πT₀²) ⊆ ℙ²_R` is regular**, for `π` a uniformizer of a discrete
valuation ring in which `2` is invertible. Its three standard charts have regular rings. -/
theorem isRegular_scheme (hπ : Irreducible π) (h2 : IsUnit (2 : R)) : IsRegular (scheme π) := by
  intro x
  have hx : x ∈ (⨆ k : Fin 3, PlaneCurveModel.chart (equation π) (isHomogeneous_equation π) k) := by
    rw [PlaneCurveModel.iSup_chart_eq_top]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨⟨_, PlaneCurveModel.isAffineOpen_chart (equation π) (isHomogeneous_equation π) k⟩, hk,
    ?_⟩
  have hreg : IsRegularRing (MvPolynomial (Fin 2) R ⧸
      Ideal.span {Stacks.ProjectiveChart.dehomCoeff R k (equation π)}) := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    · rw [dehomCoeff_equation_zero]
      exact isRegularRing_chart_zero hπ h2
    · rw [dehomCoeff_equation_one]
      exact isRegularRing_chart_one h2
    · rw [dehomCoeff_equation_two]
      exact isRegularRing_chart_one h2
  exact IsRegularRing.of_ringEquiv (PlaneCurveModel.chartEquiv (equation π)
    (isHomogeneous_equation π) 0 (not_X_zero_dvd_equation π) k)

/-! ### Change of coefficients -/

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The form `T₁² + T₂² - πT₀²` is compatible with a change of coefficients. -/
theorem map_equation {S : Type u} [CommRing S] (φ : R →+* S) (π : R) :
    MvPolynomial.map φ (equation π) = equation (φ π) := by
  simp [equation]

end Stacks.Models.RealConicModel

/-! ### The conic `T₁² + T₂² = 0` over a field -/

namespace Stacks.Models.RealConicModel

attribute [local instance] MvPolynomial.gradedAlgebra

section Field

variable (k : Type u) [Field k]

/-- Over a field in which `-1` is not a square, `T₁² + T₂²` is irreducible. It is the degenerate
conic `T₀² + T₁²` of `Stacks.Curves.DegenerateConic.conicForm` after the cyclic renaming
`T₀ ↦ T₁ ↦ T₂ ↦ T₀`. -/
theorem irreducible_equation_zero (hk : ∀ c : k, c ^ 2 ≠ -1) : Irreducible (equation (0 : k)) := by
  have h0 : finRotate 3 0 = 1 := by decide
  have h1 : finRotate 3 1 = 2 := by decide
  have hr : (MvPolynomial.renameEquiv k (finRotate 3)).toMulEquiv
      (Stacks.Curves.DegenerateConic.conicForm k) = equation (0 : k) := by
    show MvPolynomial.rename (finRotate 3) (Stacks.Curves.DegenerateConic.conicForm k) = _
    simp [Stacks.Curves.DegenerateConic.conicForm, equation, h0, h1]
  rw [← hr]
  exact (MulEquiv.irreducible_iff _).mpr (Stacks.Curves.DegenerateConic.conicForm_irreducible hk)

/-- The chart ring `k[Y₀, Y₁]/(Y₀² + Y₁²)` of `V(T₁² + T₂²)` on `D₊(T₀)`. -/
theorem dehomCoeff_equation_zero_zero :
    Stacks.ProjectiveChart.dehomCoeff k 0 (equation (0 : k)) = X 0 ^ 2 + X 1 ^ 2 := by
  rw [dehomCoeff_equation_zero, map_zero, sub_zero]

/-- The origin `(Y₀, Y₁)` of `k[Y₀, Y₁]`, as the ideal `(0, Y₀, Y₁)`. -/
private theorem isMaximal_origin : (nodalOriginIdeal k (0 : k)).IsMaximal :=
  isMaximal_nodalOriginIdeal
    (by rw [Ideal.span_singleton_eq_bot.mpr rfl]; exact Ideal.bot_isMaximal)

private theorem sum_sq_mem_origin_sq :
    (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) k) ∈ nodalOriginIdeal k (0 : k) ^ 2 :=
  add_mem (Ideal.pow_mem_pow (X_mem_nodalOriginIdeal 0 0) 2)
    (Ideal.pow_mem_pow (X_mem_nodalOriginIdeal 0 1) 2)

/-- **The affine conic `k[Y₀, Y₁]/(Y₀² + Y₁²)` is singular at the origin.** -/
theorem not_isRegular_spec_chart :
    ¬ IsRegular (Spec (CommRingCat.of (MvPolynomial (Fin 2) k ⧸
      Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) k)}))) := by
  have := (isMaximal_origin k).isPrime
  refine not_isRegular_spec_quotient_span_singleton_of_mem_sq (nodalOriginIdeal k 0) ?_ ?_
  · refine mem_nonZeroDivisors_of_ne_zero ?_
    refine (IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _
      (nodalOriginIdeal k 0).primeCompl_le_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ?_))
    intro h
    have h' := congrArg (fun p => p.coeff (Finsupp.single 0 2)) h
    simp [MvPolynomial.coeff_X_pow, Finsupp.single_eq_single_iff] at h'
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (nodalOriginIdeal k 0), ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (sum_sq_mem_origin_sq k)

private theorem not_X_zero_dvd_equation_zero :
    ¬ (X 0 : MvPolynomial (Fin 3) k) ∣ equation (0 : k) :=
  not_X_zero_dvd_equation 0

/-- The degenerate conic `V(T₁² + T₂²) ⊆ ℙ²_k` is nonempty: its chart on `D₊(T₀)` has the nonzero
ring `k[Y₀, Y₁]/(Y₀² + Y₁²)`. -/
theorem nonempty_scheme_zero : Nonempty (scheme (0 : k)) := by
  let U := PlaneCurveModel.chart (equation (0 : k)) (isHomogeneous_equation 0) 0
  have hU := PlaneCurveModel.isAffineOpen_chart (equation (0 : k)) (isHomogeneous_equation 0) 0
  have hne : Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) k)} ≠ ⊤ := by
    intro h
    refine (isMaximal_origin k).ne_top (top_le_iff.mp ?_)
    rw [← h, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_le_self two_ne_zero (sum_sq_mem_origin_sq k)
  have : Nontrivial (MvPolynomial (Fin 2) k ⧸
      Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) k)}) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have e := PlaneCurveModel.chartEquiv (equation (0 : k)) (isHomogeneous_equation 0) 0
    (not_X_zero_dvd_equation_zero k) 0
  rw [dehomCoeff_equation_zero_zero] at e
  have : Nontrivial Γ(scheme (0 : k), U) := e.symm.toEquiv.nontrivial
  obtain ⟨x⟩ : Nonempty U.toScheme := Nonempty.map hU.isoSpec.inv inferInstance
  exact ⟨x.1⟩

/-- **The degenerate conic `V(T₁² + T₂²) ⊆ ℙ²_k` is irreducible** when `-1` is not a square in
`k`: its homogeneous coordinate ring is a domain. -/
theorem irreducibleSpace_scheme_zero (hk : ∀ c : k, c ^ 2 ≠ -1) :
    IrreducibleSpace (scheme (0 : k)) := by
  have : (PlaneCurveModel.equationIdeal (equation (0 : k))
      (isHomogeneous_equation 0)).toIdeal.IsPrime :=
    (Ideal.span_singleton_prime (irreducible_equation_zero k hk).ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_equation_zero k hk))
  have : IsDomain (MvPolynomial (Fin 3) k ⧸
      (PlaneCurveModel.equationIdeal (equation (0 : k)) (isHomogeneous_equation 0)).toIdeal) :=
    Ideal.Quotient.isDomain _
  have := nonempty_scheme_zero k
  exact AlgebraicGeometry.irreducibleSpace_proj_of_isDomain _

/-- **The degenerate conic `V(T₁² + T₂²) ⊆ ℙ²_k` is singular**: it is not regular at the point
`(1 : 0 : 0)`, where its chart is `k[Y₀, Y₁]/(Y₀² + Y₁²)`. -/
theorem not_isRegular_scheme_zero : ¬ IsRegular (scheme (0 : k)) := by
  intro hreg
  let U := PlaneCurveModel.chart (equation (0 : k)) (isHomogeneous_equation 0) 0
  have hU := PlaneCurveModel.isAffineOpen_chart (equation (0 : k)) (isHomogeneous_equation 0) 0
  have e := PlaneCurveModel.chartEquiv (equation (0 : k)) (isHomogeneous_equation 0) 0
    (not_X_zero_dvd_equation_zero k) 0
  rw [dehomCoeff_equation_zero_zero] at e
  exact not_isRegular_spec_chart k (IsRegular.of_iso
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm
    (IsRegular.of_iso hU.isoSpec.symm (hreg.restrict U)))

end Field

/-! ### The special fibre -/

section SpecialFibre

variable {R : Type u} [CommRing R] (π : R) (k : Type u) [Field k] [Algebra R k]

/-- The special fibre `X ×_{Spec R} Spec k` of the conic, for a field `k` over `R`. -/
abbrev specialFiber : Scheme.{u} :=
  pullback (toSpec π) (Spec.map (CommRingCat.ofHom (algebraMap R k)))

/-- If `π` maps to zero in `k`, the fibre of `X` over `Spec k` is the degenerate conic
`V(T₁² + T₂²) ⊆ ℙ²_k`. -/
def specialFiberIso (hπ : algebraMap R k π = 0) : scheme (0 : k) ≅ specialFiber π k :=
  (PlaneCurveModel.schemeCongr (isHomogeneous_equation 0) ((isHomogeneous_equation π).map _)
      (by rw [map_equation, hπ])) ≪≫
    (PlaneCurveModel.isPullback_mapMap (equation π) (isHomogeneous_equation π)
      (algebraMap R k)).isoPullback

/-- **The special fibre is irreducible**, when `π` maps to zero in `k` and `-1` is not a square
in `k`. -/
theorem irreducibleSpace_specialFiber (hπ : algebraMap R k π = 0) (hk : ∀ c : k, c ^ 2 ≠ -1) :
    IrreducibleSpace (specialFiber π k) := by
  have := irreducibleSpace_scheme_zero k hk
  have h := (IrreducibleSpace.isIrreducible_univ (scheme (0 : k))).image
    (specialFiberIso π k hπ).hom.base (specialFiberIso π k hπ).hom.base.hom.continuous.continuousOn
  have hs : Function.Surjective (specialFiberIso π k hπ).hom := fun y =>
    ⟨(specialFiberIso π k hπ).inv y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
  rw [Set.image_univ_of_surjective hs] at h
  exact (irreducibleSpace_def _).mpr h

/-- **The special fibre is singular**, when `π` maps to zero in `k`. -/
theorem not_isRegular_specialFiber (hπ : algebraMap R k π = 0) :
    ¬ IsRegular (specialFiber π k) := fun h =>
  not_isRegular_scheme_zero k (IsRegular.of_iso (specialFiberIso π k hπ) h)

end SpecialFibre

/-! ### Splitting the form `T₁² + T₂²` -/

section Split

variable {S : Type u} [CommRing S] {i c : S}

/-- The substitution `T₀ ↦ T₀`, `T₁ ↦ T₁ + iT₂`, `T₂ ↦ T₁ - iT₂`. -/
def splitSubst (i : S) : Fin 3 → MvPolynomial (Fin 3) S :=
  ![X 0, X 1 + C i * X 2, X 1 - C i * X 2]

/-- The substitution `T₀ ↦ T₀`, `T₁ ↦ c(T₁ + T₂)`, `T₂ ↦ -ic(T₁ - T₂)`, inverse to `splitSubst i`
when `i² = -1` and `2c = 1`. -/
def splitSubstInv (i c : S) : Fin 3 → MvPolynomial (Fin 3) S :=
  ![X 0, C c * (X 1 + X 2), C (-(i * c)) * (X 1 - X 2)]

/-- `splitSubst i` sends `T₀` to `T₀`. -/
@[simp] theorem splitSubst_zero (i : S) : splitSubst i 0 = X 0 := rfl
/-- `splitSubst i` sends `T₁` to `T₁ + iT₂`. -/
@[simp] theorem splitSubst_one (i : S) : splitSubst i 1 = X 1 + C i * X 2 := rfl
/-- `splitSubst i` sends `T₂` to `T₁ - iT₂`. -/
@[simp] theorem splitSubst_two (i : S) : splitSubst i 2 = X 1 - C i * X 2 := rfl
/-- `splitSubstInv i c` sends `T₀` to `T₀`. -/
@[simp] theorem splitSubstInv_zero (i c : S) : splitSubstInv i c 0 = X 0 := rfl
/-- `splitSubstInv i c` sends `T₁` to `c(T₁ + T₂)`. -/
@[simp] theorem splitSubstInv_one (i c : S) : splitSubstInv i c 1 = C c * (X 1 + X 2) := rfl
/-- `splitSubstInv i c` sends `T₂` to `-ic(T₁ - T₂)`. -/
@[simp] theorem splitSubstInv_two (i c : S) :
    splitSubstInv i c 2 = C (-(i * c)) * (X 1 - X 2) := rfl

/-- Each image `splitSubst i j` is a linear form. -/
theorem isHomogeneous_splitSubst (i : S) (j : Fin 3) : (splitSubst i j).IsHomogeneous 1 := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · exact isHomogeneous_X _ _
  · exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)
  · exact (isHomogeneous_X _ _).sub (isHomogeneous_C_mul_X _ _)

/-- Each image `splitSubstInv i c j` is a linear form. -/
theorem isHomogeneous_splitSubstInv (i c : S) (j : Fin 3) :
    (splitSubstInv i c j).IsHomogeneous 1 := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · exact isHomogeneous_X _ _
  · have h := (isHomogeneous_C (Fin 3) c).mul ((isHomogeneous_X S 1).add (isHomogeneous_X S 2))
    rwa [zero_add] at h
  · have h := (isHomogeneous_C (Fin 3) (-(i * c))).mul
      ((isHomogeneous_X S 1).sub (isHomogeneous_X S 2))
    rwa [zero_add] at h

variable (hi : i ^ 2 = -1) (hc : 2 * c = 1)

include hi in
private theorem C_sq_eq : (C i : MvPolynomial (Fin 3) S) ^ 2 = -1 := by
  rw [← map_pow, hi, map_neg, map_one]

include hc in
private theorem C_two_mul : (C c : MvPolynomial (Fin 3) S) * 2 = 1 := by
  rw [mul_comm, show (2 : MvPolynomial (Fin 3) S) = C 2 from (map_ofNat C 2).symm, ← map_mul, hc,
    map_one]

include hi hc in
/-- When `i² = -1` and `2c = 1`, substituting `splitSubstInv i c` into `splitSubst i j` gives
`T_j`. -/
theorem aeval_splitSubstInv_splitSubst (j : Fin 3) :
    aeval (splitSubstInv i c) (splitSubst i j) = X j := by
  have h1 := C_sq_eq hi
  have h2 := C_two_mul hc
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · simp
  · simp only [splitSubst_one, map_add, map_mul, aeval_X, aeval_C, algebraMap_eq,
      splitSubstInv_one, splitSubstInv_two, map_neg]
    linear_combination (-(C c * (X 1 - X 2))) * h1 + X 1 * h2
  · simp only [splitSubst_two, map_sub, map_mul, aeval_X, aeval_C, algebraMap_eq,
      splitSubstInv_one, splitSubstInv_two, map_neg]
    linear_combination (C c * (X 1 - X 2)) * h1 + X 2 * h2

include hi hc in
/-- When `i² = -1` and `2c = 1`, substituting `splitSubst i` into `splitSubstInv i c j` gives
`T_j`. -/
theorem aeval_splitSubst_splitSubstInv (j : Fin 3) :
    aeval (splitSubst i) (splitSubstInv i c j) = X j := by
  have h2 := C_two_mul hc
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · simp
  · simp only [splitSubstInv_one, map_add, map_mul, aeval_X, aeval_C, algebraMap_eq,
      splitSubst_one, splitSubst_two]
    linear_combination X 1 * h2
  · simp only [splitSubstInv_two, map_sub, map_mul, aeval_X, aeval_C, algebraMap_eq,
      splitSubst_one, splitSubst_two, map_neg]
    linear_combination (-(2 * C c * X 2)) * C_sq_eq hi + X 2 * h2

include hi in
/-- The substitution `T₁ ↦ T₁ + iT₂`, `T₂ ↦ T₁ - iT₂` carries `T₁T₂ - πT₀²` to
`T₁² + T₂² - πT₀²`. -/
theorem aeval_splitSubst_nodal (π : S) :
    aeval (splitSubst i) (X 1 * X 2 - C π * X 0 ^ 2 : MvPolynomial (Fin 3) S) = equation π := by
  simp only [equation, map_sub, map_mul, map_pow, aeval_X, aeval_C, algebraMap_eq, splitSubst_zero,
    splitSubst_one, splitSubst_two]
  linear_combination (-(X 2 ^ 2 : MvPolynomial (Fin 3) S)) * C_sq_eq hi

include hi hc in
/-- The inverse substitution carries `T₁² + T₂² - πT₀²` to `T₁T₂ - πT₀²`. -/
theorem aeval_splitSubstInv_equation (π : S) :
    aeval (splitSubstInv i c) (equation π) =
      (X 1 * X 2 - C π * X 0 ^ 2 : MvPolynomial (Fin 3) S) := by
  simp only [equation, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_eq,
    splitSubstInv_zero, splitSubstInv_one, splitSubstInv_two, map_neg]
  linear_combination (C c ^ 2 * (X 1 - X 2) ^ 2) * C_sq_eq hi +
    X 1 * X 2 * (2 * C c + 1) * C_two_mul hc

end Split

/-! ### Base change to a ring containing a square root of `-1` -/

section BaseChangeSplit

variable {R S : Type u} [CommRing R] [CommRing S] (π : R) (φ : R →+* S) {i c : S}
  (hi : i ^ 2 = -1) (hc : 2 * c = 1)
  {G : MvPolynomial (Fin 3) S} (hG : G.IsHomogeneous 2)
  (hGeq : G = X 1 * X 2 - C (φ π) * X 0 ^ 2)

include hi hc hGeq in
/-- The substitution `splitSubstInv i c` carries `T₁² + T₂² - φ(π)T₀²` into the ideal of
`G = T₁T₂ - φ(π)T₀²`. -/
theorem splitSubstInv_mem :
    PlaneCurveModel.linearSubst (splitSubstInv i c) (isHomogeneous_splitSubstInv i c)
      (MvPolynomial.map φ (equation π)) ∈ (PlaneCurveModel.equationIdeal G hG).toIdeal := by
  rw [PlaneCurveModel.linearSubst_apply, map_equation, aeval_splitSubstInv_equation hi hc,
    ← hGeq]
  exact Ideal.subset_span rfl

include hi hGeq in
/-- The substitution `splitSubst i` carries `G = T₁T₂ - φ(π)T₀²` into the ideal of
`T₁² + T₂² - φ(π)T₀²`. -/
theorem splitSubst_mem :
    PlaneCurveModel.linearSubst (splitSubst i) (isHomogeneous_splitSubst i) G ∈
      (PlaneCurveModel.equationIdeal (MvPolynomial.map φ (equation π))
        ((isHomogeneous_equation π).map φ)).toIdeal := by
  rw [PlaneCurveModel.linearSubst_apply, hGeq, aeval_splitSubst_nodal hi, ← map_equation]
  exact Ideal.subset_span rfl

/-- The isomorphism `V(T₁T₂ - πT₀²) ≅ V(T₁² + T₂² - πT₀²)` over `S` induced by
`T₁ ↦ c(T₁ + T₂)`, `T₂ ↦ -ic(T₁ - T₂)`, where `i² = -1` and `2c = 1`. -/
def splitMap : PlaneCurveModel.scheme G hG ⟶
    PlaneCurveModel.scheme (MvPolynomial.map φ (equation π)) ((isHomogeneous_equation π).map φ) :=
  PlaneCurveModel.changeMap _ _
    (PlaneCurveModel.linearSubst_comp_eq_id _ _ _ _ (aeval_splitSubstInv_splitSubst hi hc))
    (splitSubstInv_mem π φ hi hc hG hGeq) (splitSubst_mem π φ hi hGeq)

/-- `splitMap` is an isomorphism. -/
theorem isIso_splitMap : IsIso (splitMap π φ hi hc hG hGeq) := by
  unfold splitMap
  exact PlaneCurveModel.isIso_changeMap _ _
    (PlaneCurveModel.linearSubst_comp_eq_id _ _ _ _ (aeval_splitSubst_splitSubstInv hi hc))
    (PlaneCurveModel.linearSubst_comp_eq_id _ _ _ _ (aeval_splitSubstInv_splitSubst hi hc))
    (splitSubstInv_mem π φ hi hc hG hGeq) (splitSubst_mem π φ hi hGeq)

/-- `splitMap` commutes with the structure morphisms to `Spec S`. -/
theorem splitMap_toSpec :
    splitMap π φ hi hc hG hGeq ≫
        PlaneCurveModel.toSpec (MvPolynomial.map φ (equation π))
          ((isHomogeneous_equation π).map φ) =
      PlaneCurveModel.toSpec G hG := by
  unfold splitMap
  exact PlaneCurveModel.changeMap_toSpec _ _
    (PlaneCurveModel.linearSubst_comp_eq_id _ _ _ _ (aeval_splitSubstInv_splitSubst hi hc))
    (splitSubstInv_mem π φ hi hc hG hGeq) (splitSubst_mem π φ hi hGeq)
    (PlaneCurveModel.linearSubst_C _ _)

/-- **The base change of `X = V(T₁² + T₂² - πT₀²)` along `φ : R →+* S` is
`V(T₁T₂ - φ(π)T₀²)`**, when `S` contains a square root `i` of `-1` and `2` is invertible in `S`,
because `T₁² + T₂² = (T₁ + iT₂)(T₁ - iT₂)` there. -/
theorem isPullback_split :
    IsPullback (splitMap π φ hi hc hG hGeq ≫
        PlaneCurveModel.mapMap (equation π) (isHomogeneous_equation π) φ)
      (PlaneCurveModel.toSpec G hG) (toSpec π) (Spec.map (CommRingCat.ofHom φ)) := by
  have := isIso_splitMap π φ hi hc hG hGeq
  refine (PlaneCurveModel.isPullback_mapMap (equation π) (isHomogeneous_equation π) φ).of_iso
    (asIso (splitMap π φ hi hc hG hGeq)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp,
      splitMap_toSpec]
  · simp
  · simp

end BaseChangeSplit

end Stacks.Models.RealConicModel

end

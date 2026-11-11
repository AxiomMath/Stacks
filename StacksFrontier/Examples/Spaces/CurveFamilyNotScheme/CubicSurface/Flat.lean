module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Charts
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurfaceIrreducible
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The cubic surface is integral and flat over the affine line

Every standard chart of the surface `Y : T₀³ + T₁³ + T₂³ - t T₀T₁T₂ = 0` of Stacks 0D5E is
`Spec k[t][x, y]/(f)` with `f = 1 + x³ + y³ - t x y`. As a polynomial in `t` over `k[x, y]`, `f` has
degree one, and its two coefficients `1 + x³ + y³` and `-x y` are coprime, since neither `x` nor
`y` divides `1 + x³ + y³`. So `f` is irreducible and the chart ring is a domain. It contains `k[t]`
(evaluation at the point `x = -1`, `y = 0`, which lies on every fibre, is a retraction), so it is
torsion-free, hence flat, over the principal ideal domain `k[t]`. Flatness of `Y ⟶ A¹_k` follows
chart by chart.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.irreducible_cubicChartEquation`: `f` is irreducible.
* `Stacks.Examples.CurveFamilyNotScheme.isDomain_cubicChartRing`: the chart ring is a domain.
* `Stacks.Examples.CurveFamilyNotScheme.algebraMap_cubicChartRing_injective`: it contains `k[t]`.
* `Stacks.Examples.CurveFamilyNotScheme.isIntegral_cubicSurface`: `Y` is integral, being
  irreducible (`Stacks.Examples.CurveFamilyNotScheme.irreducibleSpace_cubicSurface`) and covered
  by the spectra of domains.
* `Stacks.Examples.CurveFamilyNotScheme.flat_cubicSurfaceToLine`: `Y ⟶ A¹_k` is flat.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Stacks.AlgebraicGeometry.ProjPolyChart
  Stacks.RingTheory.HomogeneousQuotient

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ### Irreducibility of the chart equation -/

/-- The identification `k[t][T] ≃ (k[T])[t]` of polynomials over `k[t]` with polynomials in `t`
over the polynomial ring `k[T]`. -/
def polynomialCoeffEquiv (σ : Type*) :
    MvPolynomial σ (Polynomial k) ≃ₐ[k] Polynomial (MvPolynomial σ k) :=
  ((mapAlgEquiv σ (uniqueAlgEquiv k Unit).symm).trans (commAlgEquiv k σ Unit)).trans
    ((uniqueAlgEquiv (MvPolynomial σ k) Unit).restrictScalars k)

/-- `polynomialCoeffEquiv` sends a variable `Tᵢ` to the constant `Tᵢ`. -/
theorem polynomialCoeffEquiv_X (σ : Type*) (i : σ) :
    polynomialCoeffEquiv k σ (X i) = Polynomial.C (X i) := by
  simp [polynomialCoeffEquiv, mapAlgEquiv_apply]

/-- `polynomialCoeffEquiv` sends the constant `t` to the variable `t`. -/
theorem polynomialCoeffEquiv_C_X (σ : Type*) :
    polynomialCoeffEquiv k σ (C Polynomial.X) = Polynomial.X := by
  simp [polynomialCoeffEquiv, mapAlgEquiv_apply]

/-- The cubic `1 + x³ + y³` over `k`, the value of the chart equation at `t = 0`. -/
abbrev chartFermat : MvPolynomial (Fin 2) k :=
  1 + X 0 ^ 3 + X 1 ^ 3

/-- No coordinate divides `1 + x³ + y³`: it does not vanish at the origin. -/
theorem not_X_dvd_chartFermat (i : Fin 2) : ¬ (X i : MvPolynomial (Fin 2) k) ∣ chartFermat k := by
  rintro ⟨q, hq⟩
  have h := congrArg (eval (0 : Fin 2 → k)) hq
  simp at h

/-- The monomial `x y` and `1 + x³ + y³` are coprime. -/
theorem isRelPrime_X_mul_chartFermat :
    IsRelPrime (X 0 * X 1 : MvPolynomial (Fin 2) k) (chartFermat k) := by
  let _ := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial (Fin 2) k)
  have h (i : Fin 2) : IsRelPrime (X i : MvPolynomial (Fin 2) k) (chartFermat k) :=
    (MvPolynomial.X_prime (R := k) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
      (not_X_dvd_chartFermat k i)
  exact (h 0).mul_left (h 1)

/-- The image of the chart equation in `(k[x, y])[t]`: `(1 + x³ + y³) - x y t`. -/
theorem polynomialCoeffEquiv_cubicChartEquation :
    polynomialCoeffEquiv k (Fin 2) (cubicChartEquation k) =
      Polynomial.C (-(X 0 * X 1)) * Polynomial.X + Polynomial.C (chartFermat k) := by
  simp only [cubicChartEquation, map_add, map_sub, map_mul, map_pow, map_one,
    polynomialCoeffEquiv_X, polynomialCoeffEquiv_C_X, chartFermat, map_neg]
  ring

/-- **The chart equation `1 + x³ + y³ - t x y` is irreducible** in `k[t][x, y]`: it has degree
one in `t` with coprime coefficients. -/
theorem irreducible_cubicChartEquation : Irreducible (cubicChartEquation k) := by
  rw [← MulEquiv.irreducible_iff (polynomialCoeffEquiv k (Fin 2)).toMulEquiv]
  change Irreducible (polynomialCoeffEquiv k (Fin 2) (cubicChartEquation k))
  rw [polynomialCoeffEquiv_cubicChartEquation]
  refine Polynomial.irreducible_C_mul_X_add_C ?_ ?_
  · exact neg_ne_zero.mpr (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  · rw [neg_eq_neg_one_mul, isRelPrime_mul_unit_left_left isUnit_one.neg]
    exact isRelPrime_X_mul_chartFermat k

/-- **The chart ring `k[t][x, y]/(1 + x³ + y³ - t x y)` is a domain.** -/
instance isDomain_cubicChartRing : IsDomain (CubicChartRing k) := by
  have : (Ideal.span {cubicChartEquation k}).IsPrime :=
    (Ideal.span_singleton_prime (irreducible_cubicChartEquation k).ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_cubicChartEquation k))
  exact Ideal.Quotient.isDomain (Ideal.span {cubicChartEquation k})

/-! ### The chart ring contains `k[t]` -/

/-- Evaluation of the chart ring at the point `x = -1`, `y = 0`, which lies on every fibre. -/
def cubicChartEval : CubicChartRing k →+* Polynomial k :=
  Ideal.Quotient.lift _ (aeval (![-1, 0] : Fin 2 → Polynomial k)).toRingHom <| by
    intro a ha
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [cubicChartEquation]
    norm_num

/-- Evaluation at `x = -1`, `y = 0` is a retraction of the structure map. -/
theorem cubicChartEval_algebraMap (a : Polynomial k) :
    cubicChartEval k (algebraMap (Polynomial k) (CubicChartRing k) a) = a := by
  rw [← Ideal.Quotient.mk_algebraMap]
  simp [cubicChartEval, MvPolynomial.algebraMap_eq]

/-- The structure map `k[t] → k[t][x, y]/(1 + x³ + y³ - t x y)` is injective. -/
theorem algebraMap_cubicChartRing_injective :
    Function.Injective (algebraMap (Polynomial k) (CubicChartRing k)) :=
  Function.LeftInverse.injective (cubicChartEval_algebraMap k)

/-- The chart ring is nontrivial. -/
instance : Nontrivial (CubicChartRing k) :=
  (algebraMap_cubicChartRing_injective k).nontrivial

/-! ### Integrality -/

/-- **The cubic surface is reduced**: it is covered by the spectra of the chart rings, which are
domains. -/
instance isReduced_cubicSurface : IsReduced (cubicSurface k) := by
  have (y : cubicSurface k) : _root_.IsReduced ((cubicSurface k).presheaf.stalk y) := by
    have hy : y ∈ ⨆ j : Fin 3, (cubicChart k j).opensRange := by
      rw [iSup_opensRange_cubicChart]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hj
    exact isReduced_of_injective ((cubicChart k j).stalkMap z).hom
      (asIso ((cubicChart k j).stalkMap z)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

/-- **The cubic surface `Y` is integral**: it is irreducible
(`Stacks.Examples.CurveFamilyNotScheme.irreducibleSpace_cubicSurface`) and reduced. -/
instance isIntegral_cubicSurface : IsIntegral (cubicSurface k) := by
  have := irreducibleSpace_cubicSurface k
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-! ### Flatness -/

/-- The chart ring is torsion-free over `k[t]`. -/
instance : FaithfulSMul (Polynomial k) (CubicChartRing k) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_cubicChartRing_injective k)

/-- **The chart ring is flat over `k[t]`**: a torsion-free module over a principal ideal domain. -/
instance : Module.Flat (Polynomial k) (CubicChartRing k) :=
  IsDedekindDomain.flat_iff_torsion_eq_bot.mpr <| Submodule.isTorsionFree_iff_torsion_eq_bot.mp <|
    FaithfulSMul.to_isTorsionFree (Polynomial k) (CubicChartRing k)

/-- The plane curve model of the cubic surface is flat over the affine line. -/
instance flat_cubicModelToLine : Flat (cubicModelToLine k) := by
  refine Stacks.Models.PlaneCurveModel.hasRingHomProperty_toSpec (P := @Flat)
    (Q := RingHom.Flat) _ _ 0 (not_X_zero_dvd_cubicEquation k) fun j => ?_
  rw [dehomCoeff_cubicEquation, RingHom.flat_algebraMap_iff]
  infer_instance

/-- **The cubic surface is flat over the affine line.** -/
instance flat_cubicSurfaceToLine : Flat (cubicSurfaceToLine k) := by
  rw [← cubicSurfaceIso_hom_toSpec]
  infer_instance

end Stacks.Examples.CurveFamilyNotScheme

end

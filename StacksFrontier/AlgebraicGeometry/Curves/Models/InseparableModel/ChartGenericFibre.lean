module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ChartAlgebra
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Smooth.Basic

/-!
# A regular model with an inseparable component: the charts of the generic fibre

After inverting `π`, the coefficients `x, y` of each chart equation `x T - y` of the model of
`Stacks.Models.InseparableModel` generate the unit ideal of `K[s]` (`x = π`; `y = π`;
`x + (t/π) y = 1`), so `K ⊗_R R[s][T] ⧸ (x T - y)` is the localization `K[s][1/x]`: smooth over
`K`, a domain, of Krull dimension one.

## Main results

* `Stacks.Models.InseparableModel.smooth_tensor_chartRing`
* `Stacks.Models.InseparableModel.isDomain_tensor_chartRing`
* `Stacks.Models.InseparableModel.ringKrullDim_tensor_chartRing`
-/

@[expose] public noncomputable section

open TensorProduct

namespace Stacks.Models.InseparableModel

open Polynomial

/-- The coefficient `x` of a chart equation, over `K`. -/
abbrev chartXK (c : Fin 3) : K[X] := (chartX c).map (algebraMap R K)

/-- The coefficient `y` of a chart equation, over `K`. -/
abbrev chartYK (c : Fin 3) : K[X] := (chartY c).map (algebraMap R K)

/-- The localization `K[s][1/x]` of a chart. -/
abbrev chartLocK (c : Fin 3) : Type := Localization.Away (chartXK c)

/-- The uniformizer `π` stays nonzero in the fraction field `K`. -/
theorem algebraMap_RK_π_ne_zero : algebraMap R K π ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr irreducible_π.ne_zero

/-- The element `t` stays nonzero in the fraction field `K`. -/
theorem algebraMap_RK_tR_ne_zero : algebraMap R K tR ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ?_
  intro h
  have := congrArg (PowerSeries.constantCoeff (R := k)) h
  simp only [tR, PowerSeries.constantCoeff_C, map_zero] at this
  exact RatFunc.X_ne_zero this

/-- The constant coefficient of `x` is nonzero: `x(0)` is `π`, `-t` or `1`. -/
theorem chartXK_coeff_zero_ne_zero (c : Fin 3) : (chartXK c).coeff 0 ≠ 0 := by
  fin_cases c
  · simpa [chartX] using algebraMap_RK_π_ne_zero
  · simpa [chartX] using algebraMap_RK_tR_ne_zero
  · simp [chartX]

/-- The coefficient `x` of a chart equation is a nonzero polynomial over `K`. -/
theorem chartXK_ne_zero (c : Fin 3) : chartXK c ≠ 0 := fun h =>
  chartXK_coeff_zero_ne_zero c (by rw [h, coeff_zero])

/-- **`x` and `y` generate the unit ideal of `K[s]`.** -/
theorem exists_mul_chartXK_add_mul_chartYK (c : Fin 3) :
    ∃ a b : K[X], a * chartXK c + b * chartYK c = 1 := by
  have hπ := algebraMap_RK_π_ne_zero
  fin_cases c
  · exact ⟨C (algebraMap R K π)⁻¹, 0, by simp [chartXK, chartX, ← C_mul, hπ]⟩
  · exact ⟨0, C (algebraMap R K π)⁻¹, by simp [chartYK, chartY, ← C_mul, hπ]⟩
  · refine ⟨1, C (algebraMap R K tR / algebraMap R K π), ?_⟩
    change 1 * (1 - C tR * X ^ 2 : R[X]).map (algebraMap R K) +
      C _ * (C π * X ^ 2 : R[X]).map (algebraMap R K) = 1
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X]
    rw [one_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hπ]
    ring

section Maps

variable (c : Fin 3)

/-- `R → K → K[s][1/x]` is a scalar tower. -/
instance : IsScalarTower R K (chartLocK c) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K[X] (chartLocK c),
      IsScalarTower.algebraMap_apply K K[X] (chartLocK c)]
    rfl

/-- `R[s][T] → K[s][1/x]`, `T ↦ y/x`. -/
def toLocPoly : (R[X])[X] →ₐ[R] chartLocK c where
  __ := eval₂RingHom ((algebraMap K[X] (chartLocK c)).comp (mapRingHom (algebraMap R K)))
    (algebraMap K[X] (chartLocK c) (chartYK c) * IsLocalization.Away.invSelf (chartXK c))
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R K[X] (chartLocK c)]

/-- The chart equation `x T - y` maps to zero in `K[s][1/x]`. -/
theorem toLocPoly_chartEq : toLocPoly c (chartEq c) = 0 := by
  simp only [toLocPoly, chartEq, AlgHom.coe_mk, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_X, RingHom.coe_comp, Function.comp_apply, coe_mapRingHom]
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one, sub_self]

/-- `B → K[s][1/x]`. -/
def toLocB : chartRing c →ₐ[R] chartLocK c :=
  Ideal.Quotient.liftₐ _ (toLocPoly c) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, toLocPoly_chartEq, mul_zero]

/-- Evaluating `p ∈ R[s]` at the constant `s ∈ R[s][T]` gives the constant `p`. -/
theorem aeval_C_X (p : R[X]) : aeval (C X : (R[X])[X]) p = C p := by
  rw [show (C X : (R[X])[X]) = (CAlgHom : R[X] →ₐ[R] (R[X])[X]) X from rfl, aeval_algHom_apply,
    aeval_X_left_apply]
  rfl

/-! The comparison is carried out for an arbitrary `R`-algebra `B` identified with the chart
ring, so that the ring structure of `K ⊗_R B` is that of a tensor product of two variable
algebras. -/

variable {B : Type} [CommRing B] [Algebra R B] (e : chartRing c ≃ₐ[R] B)

/-- The class of `s` in `K ⊗_R B`. -/
abbrev sK : K ⊗[R] B :=
  Algebra.TensorProduct.includeRight (e (Ideal.Quotient.mk _ (C X)))

/-- The class of `T` in `K ⊗_R B`. -/
abbrev TK : K ⊗[R] B :=
  Algebra.TensorProduct.includeRight (e (Ideal.Quotient.mk _ X))

/-- `K[s] → K ⊗_R B`, `s ↦ s`. -/
def toTensorPoly : K[X] →ₐ[K] K ⊗[R] B := aeval (sK c e)

/-- On polynomials with coefficients in `R`, `K[s] → K ⊗_R B` is the class of the constant
polynomial in `B`. -/
theorem toTensorPoly_map (p : R[X]) :
    toTensorPoly c e (p.map (algebraMap R K)) =
      Algebra.TensorProduct.includeRight (e (Ideal.Quotient.mk _ (C p))) := by
  rw [toTensorPoly, aeval_map_algebraMap, sK, aeval_algHom_apply, aeval_algHom_apply,
    ← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, aeval_C_X]

/-- The chart equation holds in `K ⊗_R B`: `x T = y`. -/
theorem toTensorPoly_chartXK_mul_TK :
    toTensorPoly c e (chartXK c) * TK c e = toTensorPoly c e (chartYK c) := by
  rw [toTensorPoly_map, toTensorPoly_map, TK, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- `x` is a unit in `K ⊗_R B`: if `a x + b y = 1`, then `a + b T` is its inverse. -/
theorem isUnit_toTensorPoly_chartXK : IsUnit (toTensorPoly c e (chartXK c)) := by
  obtain ⟨a, b, hab⟩ := exists_mul_chartXK_add_mul_chartYK c
  refine IsUnit.of_mul_eq_one (toTensorPoly c e a + toTensorPoly c e b * TK c e) ?_
  calc toTensorPoly c e (chartXK c) * (toTensorPoly c e a + toTensorPoly c e b * TK c e)
      = toTensorPoly c e (a * chartXK c) +
          toTensorPoly c e b * (toTensorPoly c e (chartXK c) * TK c e) := by
        rw [map_mul]; ring
    _ = 1 := by rw [toTensorPoly_chartXK_mul_TK, ← map_mul, ← map_add, hab, map_one]

/-- `K[s][1/x] → K ⊗_R B`. -/
def fromLoc : chartLocK c →ₐ[K] K ⊗[R] B :=
  IsLocalization.Away.liftAlgHom (A := K) (S := chartLocK c) (P := K ⊗[R] B)
    (f := toTensorPoly c e) (chartXK c) (isUnit_toTensorPoly_chartXK c e)

/-- `K[s][1/x] → K ⊗_R B` restricts to `K[s] → K ⊗_R B` on `K[s]`. -/
theorem fromLoc_algebraMap (p : K[X]) :
    fromLoc c e (algebraMap K[X] (chartLocK c) p) = toTensorPoly c e p :=
  IsLocalization.Away.lift_eq (chartXK c) (isUnit_toTensorPoly_chartXK c e) p

/-- `K ⊗_R B → K[s][1/x]`. -/
def toLoc : K ⊗[R] B →ₐ[K] chartLocK c :=
  Algebra.TensorProduct.lift (Algebra.ofId K _) ((toLocB c).comp e.symm.toAlgHom)
    fun _ _ => Commute.all _ _

/-- On `B`, the map `K ⊗_R B → K[s][1/x]` is the inverse of `e` followed by the map from the chart
ring. -/
theorem toLoc_includeRight (b : B) :
    toLoc c e (Algebra.TensorProduct.includeRight b) = toLocB c (e.symm b) := by
  simp [toLoc]

/-- `K[s][1/x] → K ⊗_R B → K[s][1/x]` is the identity. -/
theorem toLoc_comp_fromLoc : (toLoc c e).comp (fromLoc c e) = AlgHom.id K _ := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (chartXK c))
  have : ((toLoc c e).comp (toTensorPoly c e)) =
      IsScalarTower.toAlgHom K K[X] (chartLocK c) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, toTensorPoly, aeval_X, sK, toLoc_includeRight,
      AlgEquiv.symm_apply_apply]
    simp [toLocB, toLocPoly]
  exact RingHom.ext fun p => by simpa [fromLoc_algebraMap] using congrArg (fun f => f p) this

/-- `K ⊗_R B → K[s][1/x] → K ⊗_R B` fixes the elements of `B`. -/
theorem fromLoc_toLoc_includeRight_mk (q : (R[X])[X]) :
    fromLoc c e (toLoc c e (Algebra.TensorProduct.includeRight (e (Ideal.Quotient.mk _ q)))) =
      Algebra.TensorProduct.includeRight (e (Ideal.Quotient.mk _ q)) := by
  have hinv : fromLoc c e (IsLocalization.Away.invSelf (chartXK c)) *
      toTensorPoly c e (chartXK c) = 1 := by
    rw [← fromLoc_algebraMap, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  let f : (R[X])[X] →ₐ[R] K ⊗[R] B :=
    (((fromLoc c e).comp (toLoc c e)).restrictScalars R).comp
      (((Algebra.TensorProduct.includeRight).comp e.toAlgHom).comp (Ideal.Quotient.mkₐ R _))
  have hfg : f = ((Algebra.TensorProduct.includeRight).comp e.toAlgHom).comp
      (Ideal.Quotient.mkₐ R _) := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      simp only [f, AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk,
        CAlgHom_apply, AlgEquiv.coe_toAlgHom, toLoc_includeRight, AlgEquiv.symm_apply_apply]
      change fromLoc c e (toLocPoly c (C X)) = sK c e
      simp only [toLocPoly, AlgHom.coe_mk, coe_eval₂RingHom, eval₂_C, RingHom.coe_comp,
        Function.comp_apply, coe_mapRingHom, Polynomial.map_X, fromLoc_algebraMap]
      exact aeval_X _
    · simp only [f, AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk,
        AlgEquiv.coe_toAlgHom, toLoc_includeRight, AlgEquiv.symm_apply_apply]
      change fromLoc c e (toLocPoly c X) = TK c e
      simp only [toLocPoly, AlgHom.coe_mk, coe_eval₂RingHom, eval₂_X, map_mul]
      rw [fromLoc_algebraMap, ← toTensorPoly_chartXK_mul_TK, mul_comm,
        ← mul_assoc, hinv, one_mul]
  exact congrArg (fun φ => φ q) hfg

/-- `K ⊗_R B → K[s][1/x] → K ⊗_R B` is the identity. -/
theorem fromLoc_comp_toLoc : (fromLoc c e).comp (toLoc c e) = AlgHom.id K _ := by
  apply Algebra.TensorProduct.ext_ring
  ext b
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (e.symm b)
  have hb : b = e (Ideal.Quotient.mk _ q) := by rw [hq, AlgEquiv.apply_symm_apply]
  subst hb
  exact fromLoc_toLoc_includeRight_mk c e q

/-- **The chart of the generic fibre**: `K ⊗_R B ≃ K[s][1/x]`. -/
def tensorChartEquiv : K ⊗[R] B ≃ₐ[K] chartLocK c :=
  AlgEquiv.ofAlgHom (toLoc c e) (fromLoc c e) (toLoc_comp_fromLoc c e) (fromLoc_comp_toLoc c e)

end Maps

/-- `K[s][1/x]` is a domain, as a localization of `K[s]` away from a nonzero element. -/
instance isDomain_chartLocK (c : Fin 3) : IsDomain (chartLocK c) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (chartXK_ne_zero c))

/-- **The generic fibre of a chart is smooth**: `K ⊗_R B` is smooth over `K`, being isomorphic
to the localization `K[s][1/x]` of `K[s]`. -/
theorem smooth_tensor_chartRing (c : Fin 3) : Algebra.Smooth K (K ⊗[R] chartRing c) := by
  have : Algebra.Smooth (Polynomial K) (chartLocK c) :=
    Algebra.Smooth.of_isLocalization_Away (A := chartLocK c) (chartXK c)
  have : Algebra.Smooth K (Polynomial K) := {}
  have : Algebra.Smooth K (chartLocK c) := Algebra.Smooth.comp K K[X] (chartLocK c)
  exact Algebra.Smooth.of_equiv (tensorChartEquiv c AlgEquiv.refl).symm

/-- **The generic fibre of a chart is a domain.** -/
theorem isDomain_tensor_chartRing (c : Fin 3) : IsDomain (K ⊗[R] chartRing c) :=
  (tensorChartEquiv c AlgEquiv.refl).toRingEquiv.toMulEquiv.isDomain_iff.mpr inferInstance

/-- `K[s][1/x]` is not a field: the prime `(s)` of `K[s]` survives, as `x(0) ≠ 0`. -/
theorem not_isField_chartLocK (c : Fin 3) : ¬ IsField (chartLocK c) := by
  intro hF
  have hP : (Ideal.span {(X : K[X])}).IsPrime :=
    (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  have hd : Disjoint (Submonoid.powers (chartXK c) : Set K[X]) (Ideal.span {(X : K[X])}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    have := hP.mem_of_pow_mem n hn
    rw [Ideal.mem_span_singleton, X_dvd_iff] at this
    exact chartXK_coeff_zero_ne_zero c this
  have hQ := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (chartXK c))
    (chartLocK c) _ hP hd
  have hX : algebraMap K[X] (chartLocK c) X ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsLocalization.injective (chartLocK c)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (chartXK_ne_zero c)))]
    exact X_ne_zero
  obtain ⟨u, hu⟩ := hF.mul_inv_cancel hX
  apply hQ.ne_top
  rw [Ideal.eq_top_iff_one, ← hu]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))

/-- `K[s][1/x]` has Krull dimension one: it is a Dedekind domain which is not a field. -/
theorem ringKrullDim_chartLocK (c : Fin 3) : ringKrullDim (chartLocK c) = 1 := by
  have : IsDedekindDomain (chartLocK c) :=
    IsLocalization.isDedekindDomain K[X]
      (powers_le_nonZeroDivisors_of_noZeroDivisors (chartXK_ne_zero c)) _
  apply eq_of_le_of_not_lt ?_ fun h' ↦ not_isField_chartLocK c ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · have h'' : ringKrullDim (chartLocK c) ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

/-- **The generic fibre of a chart has Krull dimension one.** -/
theorem ringKrullDim_tensor_chartRing (c : Fin 3) : ringKrullDim (K ⊗[R] chartRing c) = 1 := by
  rw [ringKrullDim_eq_of_ringEquiv (tensorChartEquiv c AlgEquiv.refl).toRingEquiv,
    ringKrullDim_chartLocK]

end Stacks.Models.InseparableModel

module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.NormalizationUniformizer

/-!
# The order of vanishing of a one-dimensional local domain, read on its normalization

Let `A` be a Noetherian local domain of dimension one with fraction field `F` and normalization
`A'`. With `v_𝔪` the valuation of `A'_𝔪` and `t_𝔪` the uniformizer of
`Stacks.Chow.normalizationUniformizer`, the order of vanishing of `A` is

`ord_A(x) = ∑_𝔪 ord_A(t_𝔪) · v_𝔪(x)` (`Stacks.Chow.ordInt_eq_sum_normalizationOrd`).

Indeed `y = x · ∏_𝔪 t_𝔪 ^ (-v_𝔪(x))` has valuation zero at every maximal ideal of `A'`, so it is a
unit of `A'` (an integral domain is the intersection of its localizations at maximal ideals),
hence `y` and `y⁻¹` are integral over `A` and `ord_A(y) = 0`.

## Main results

* `Stacks.Chow.isIntegral_of_forall_normalizationOrd_eq_zero` — valuation zero everywhere means
  integral over `A`.
* `Stacks.Chow.ordInt_eq_sum_normalizationOrd` — the formula.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing Stacks.Normalization

universe u

namespace Stacks.Chow

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]

/-- `ord_A` as a homomorphism `F^* → ℤ`, written multiplicatively. -/
def ordIntHom [Ring.KrullDimLE 1 A] : Fˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ordInt A (x : F) x.ne_zero)
  map_one' := by
    have h := ordInt_mul A (1 : F) 1 one_ne_zero one_ne_zero
    simp only [mul_one] at h
    have h0 : ordInt A (1 : F) one_ne_zero = 0 := by linarith
    simp [h0]
  map_mul' x y := by
    rw [← ofAdd_add, ← ordInt_mul A (x : F) y x.ne_zero y.ne_zero]
    rfl

/-- The additive value of `ordIntHom A F x` is `ord_A(x)`. -/
theorem ordIntHom_apply [Ring.KrullDimLE 1 A] (x : Fˣ) :
    Multiplicative.toAdd (ordIntHom A F x) = ordInt A (x : F) x.ne_zero := rfl

variable [Ring.DimensionLEOne A] (hA : maximalIdeal A ≠ ⊥)

/-- The valuation `v_𝔪` as a homomorphism `F^* → ℤ`, written multiplicatively. -/
def normalizationOrdHom (m : MaximalSpectrum ↥(integralClosure A F)) :
    Fˣ →* Multiplicative ℤ :=
  letI := localizationAlgebra A F m.asIdeal
  haveI := isFractionRing_localization A F m.asIdeal
  haveI := isDiscreteValuationRing_localization A F hA m.asIdeal
  { toFun := fun x ↦ Multiplicative.ofAdd (normalizationOrd A F hA m x)
    map_one' := by
      change Multiplicative.ofAdd (dvrFracOrd _ (1 : Fˣ)) = 1
      rw [dvrFracOrd_one]; rfl
    map_mul' := fun x y ↦ by
      change Multiplicative.ofAdd (dvrFracOrd _ (x * y)) =
        Multiplicative.ofAdd (dvrFracOrd _ x) * Multiplicative.ofAdd (dvrFracOrd _ y)
      rw [dvrFracOrd_mul]; rfl }

/-- The additive value of `normalizationOrdHom A F hA m x` is `v_𝔪(x)`. -/
theorem normalizationOrdHom_apply (m : MaximalSpectrum ↥(integralClosure A F)) (x : Fˣ) :
    Multiplicative.toAdd (normalizationOrdHom A F hA m x) = normalizationOrd A F hA m x := rfl

/-- **An element of `F` with valuation zero at every maximal ideal of `A'` lies in `A'`**, so it is
integral over `A`. -/
theorem isIntegral_of_forall_normalizationOrd_eq_zero {y : Fˣ}
    (hy : ∀ m, normalizationOrd A F hA m y = 0) : IsIntegral A (y : F) := by
  have := Stacks.Normalization.isFractionRing_integralClosure A F
  have hmem : (y : F) ∈ (⊥ : Subalgebra ↥(integralClosure A F) F) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot ↥(integralClosure A F) F, Algebra.mem_iInf]
    intro m
    let := localizationAlgebra A F m.asIdeal
    have := isFractionRing_localization A F m.asIdeal
    have := isDiscreteValuationRing_localization A F hA m.asIdeal
    obtain ⟨u, hu, -⟩ := exists_val_eq_algebraMap_of_dvrFracOrd_eq_zero
      (exists_irreducible (Localization.AtPrime m.asIdeal)).choose_spec (hy m)
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective m.asIdeal.primeCompl
      (u : Localization.AtPrime m.asIdeal)
    have := isScalarTower_localization A F m.asIdeal
    refine ⟨a, s, s.2, ?_⟩
    have hs0 : algebraMap ↥(integralClosure A F) F (s : ↥(integralClosure A F)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ F)).mpr
        (fun h ↦ s.2 (h ▸ m.asIdeal.zero_mem))
    have h := congrArg (algebraMap (Localization.AtPrime m.asIdeal) F)
      (IsLocalization.mk'_spec (Localization.AtPrime m.asIdeal) a s)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    rw [hu, ← hs, eq_mul_inv_iff_mul_eq₀ hs0]
    exact h
  obtain ⟨b, hb⟩ := Algebra.mem_bot.mp hmem
  rw [← hb]
  exact b.2

/-- **`ord_A` as a combination of the valuations of the normalization**:
`ord_A(x) = ∑_𝔪 ord_A(t_𝔪) · v_𝔪(x)`. -/
theorem ordInt_eq_sum_normalizationOrd (x : Fˣ) :
    haveI := finite_maximalSpectrum_integralClosure A F
    letI := Fintype.ofFinite (MaximalSpectrum ↥(integralClosure A F))
    ordInt A (x : F) x.ne_zero =
      ∑ m, ordInt A (normalizationUniformizer A F hA m : F)
          (normalizationUniformizer_ne_zero A F hA m) * normalizationOrd A F hA m x := by
  classical
  have := finite_maximalSpectrum_integralClosure A F
  let := Fintype.ofFinite (MaximalSpectrum ↥(integralClosure A F))
  set t := normalizationUniformizerUnit A F hA
  set y : Fˣ := x * ∏ m, (t m) ^ (-normalizationOrd A F hA m x)
  have hy : ∀ m', normalizationOrd A F hA m' y = 0 := by
    intro m'
    rw [← normalizationOrdHom_apply, map_mul, map_prod, toAdd_mul, toAdd_prod,
      normalizationOrdHom_apply]
    simp_rw [map_zpow, toAdd_zpow, normalizationOrdHom_apply, t,
      normalizationOrd_normalizationUniformizerUnit, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ m', if_pos (Finset.mem_univ m')]
    ring
  have hyinv : ∀ m', normalizationOrd A F hA m' y⁻¹ = 0 := by
    intro m'
    rw [← normalizationOrdHom_apply, map_inv, toAdd_inv, normalizationOrdHom_apply, hy, neg_zero]
  have h0 : ordInt A (y : F) y.ne_zero = 0 :=
    ordInt_eq_zero_of_isIntegral A F y.ne_zero
      (isIntegral_of_forall_normalizationOrd_eq_zero A F hA hy)
      (by simpa using isIntegral_of_forall_normalizationOrd_eq_zero A F hA hyinv)
  have hx : x = y * ∏ m, (t m) ^ (normalizationOrd A F hA m x) := by
    simp only [y, mul_assoc, ← Finset.prod_mul_distrib, ← zpow_add, neg_add_cancel, zpow_zero,
      Finset.prod_const_one, mul_one]
  have key := congrArg (fun z ↦ Multiplicative.toAdd (ordIntHom A F z)) hx
  simp only [map_mul, map_prod, map_zpow, toAdd_mul, toAdd_prod, toAdd_zpow, ordIntHom_apply,
    h0, zero_add, smul_eq_mul] at key
  rw [key]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [mul_comm]
  rfl

end Stacks.Chow

end

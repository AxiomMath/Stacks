module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.DegreeOne

/-!
# Generators of the normalization of a one-dimensional local domain

Let `A` be a Noetherian local domain of dimension one with fraction field `F` and normalization
`A'`, a semi-local Dedekind domain, and let `t_𝔪 ∈ A'` be the element of
`Stacks.Chow.normalizationUniformizer`: a uniformizer of `A'_𝔪` and a unit at every other maximal
ideal. This file proves:

* `t_𝔪` generates `𝔪` (`Stacks.Chow.span_normalizationUniformizer`), so `A'/t_𝔪 A'` is the
  residue field `κ(𝔪)` (`Stacks.Chow.normalizationQuotientEquiv`);
* `t_𝔪` and `t_𝔫` are coprime for `𝔪 ≠ 𝔫`;
* every nonzero element of `A'` is a unit times a product of powers of the `t_𝔪`
  (`Stacks.Chow.mem_closure_normalizationGenerators`).

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing Stacks.Normalization

universe u

namespace Stacks.Chow

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F] [Ring.DimensionLEOne A]
  (hA : maximalIdeal A ≠ ⊥)

/-- `t_𝔪` lies in `𝔪`: its image in `A'_𝔪` is not a unit. -/
theorem normalizationUniformizer_mem (m : MaximalSpectrum ↥(integralClosure A F)) :
    normalizationUniformizer A F hA m ∈ m.asIdeal := by
  by_contra h
  exact (exists_normalizationUniformizer A F hA m).choose_spec.1.not_isUnit
    (IsLocalization.map_units (Localization.AtPrime m.asIdeal)
      (⟨_, h⟩ : m.asIdeal.primeCompl))

/-- **`t_𝔪` generates the maximal ideal `𝔪` of the normalization.** -/
theorem span_normalizationUniformizer (m : MaximalSpectrum ↥(integralClosure A F)) :
    Ideal.span {normalizationUniformizer A F hA m} = m.asIdeal := by
  have := isDedekindDomain_integralClosure A F
  have := isDiscreteValuationRing_localization A F hA m.asIdeal
  set t := normalizationUniformizer A F hA m with ht
  have hirr : Irreducible (algebraMap ↥(integralClosure A F) (Localization.AtPrime m.asIdeal) t) :=
    (exists_normalizationUniformizer A F hA m).choose_spec.1
  have hle : Ideal.span {t} ≤ m.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (normalizationUniformizer_mem A F hA m)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  suffices hJ1 : J = ⊤ by rw [hJ, hJ1, Ideal.mul_top]
  by_contra hJt
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJt
  have htJ : t ∈ m.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self t
  by_cases hPm : P = m.asIdeal
  · subst hPm
    have ht2 : t ∈ m.asIdeal ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mono_right hJP htJ
    have hmem : algebraMap _ (Localization.AtPrime m.asIdeal) t ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) ^ 2 := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m.asIdeal (Localization.AtPrime m.asIdeal),
        ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ht2
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    set τ := algebraMap ↥(integralClosure A F) (Localization.AtPrime m.asIdeal) t with hτ
    have h1 : τ * (τ * c) = τ * 1 := by
      calc τ * (τ * c) = c * τ ^ 2 := by ring
        _ = τ := hc
        _ = τ * 1 := (mul_one τ).symm
    exact hirr.not_isUnit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hirr.ne_zero h1))
  · have htP : t ∈ P := hJP (Ideal.mul_le_left (I := J) (J := m.asIdeal) (by rwa [mul_comm] at htJ))
    have hne : (⟨P, hP⟩ : MaximalSpectrum ↥(integralClosure A F)) ≠ m :=
      fun h ↦ hPm (congrArg MaximalSpectrum.asIdeal h)
    exact (exists_normalizationUniformizer A F hA m).choose_spec.2 ⟨P, hP⟩ hne htP

/-- `t_𝔪` and `t_𝔫` are coprime for distinct maximal ideals `𝔪 ≠ 𝔫`. -/
theorem isCoprime_normalizationUniformizer {m n : MaximalSpectrum ↥(integralClosure A F)}
    (h : m ≠ n) :
    IsCoprime (normalizationUniformizer A F hA m) (normalizationUniformizer A F hA n) := by
  rw [← Ideal.isCoprime_span_singleton_iff, span_normalizationUniformizer,
    span_normalizationUniformizer, Ideal.isCoprime_iff_sup_eq]
  exact m.isMaximal.coprime_of_ne n.isMaximal fun e ↦ h (MaximalSpectrum.ext e)

/-- **`A'/t_𝔪 A'` is the residue field `κ(𝔪)` of `A'_𝔪`.** -/
def normalizationQuotientEquiv (m : MaximalSpectrum ↥(integralClosure A F)) :
    (↥(integralClosure A F) ⧸ Ideal.span {normalizationUniformizer A F hA m}) ≃+*
      ResidueField (Localization.AtPrime m.asIdeal) :=
  (Ideal.quotEquivOfEq (span_normalizationUniformizer A F hA m)).trans
    (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField m.asIdeal))

/-- `normalizationQuotientEquiv` sends the class of `x` to the residue of the image of `x` in
`A'_𝔪`. -/
theorem normalizationQuotientEquiv_mk (m : MaximalSpectrum ↥(integralClosure A F))
    (x : ↥(integralClosure A F)) :
    normalizationQuotientEquiv A F hA m (Ideal.Quotient.mk _ x) =
      residue _ (algebraMap _ (Localization.AtPrime m.asIdeal) x) := by
  show algebraMap (↥(integralClosure A F) ⧸ m.asIdeal) m.asIdeal.ResidueField
    (Ideal.Quotient.mk _ x) = _
  rw [Ideal.algebraMap_quotient_residueField_mk,
    IsScalarTower.algebraMap_apply ↥(integralClosure A F) (Localization.AtPrime m.asIdeal)
      m.asIdeal.ResidueField x, IsLocalRing.ResidueField.algebraMap_eq]

/-- The identification `A'/t_𝔪 A' ≃ κ(𝔪)` is `A`-linear. -/
def normalizationQuotientLinearEquiv (m : MaximalSpectrum ↥(integralClosure A F)) :
    (↥(integralClosure A F) ⧸ Ideal.span {normalizationUniformizer A F hA m}) ≃ₗ[A]
      ResidueField (Localization.AtPrime m.asIdeal) :=
  { normalizationQuotientEquiv A F hA m with
    map_smul' := fun a x ↦ by
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        change normalizationQuotientEquiv A F hA m (Ideal.Quotient.mk _ (a • x)) =
          a • normalizationQuotientEquiv A F hA m (Ideal.Quotient.mk _ x)
        rw [normalizationQuotientEquiv_mk, normalizationQuotientEquiv_mk, Algebra.smul_def,
          map_mul, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
          IsScalarTower.algebraMap_apply A (Localization.AtPrime m.asIdeal)
            (ResidueField (Localization.AtPrime m.asIdeal)),
          IsLocalRing.ResidueField.algebraMap_eq] }

/-- `normalizationQuotientLinearEquiv` sends the class of `x` to the residue of the image of `x`
in `A'_𝔪`. -/
theorem normalizationQuotientLinearEquiv_mk (m : MaximalSpectrum ↥(integralClosure A F))
    (x : ↥(integralClosure A F)) :
    normalizationQuotientLinearEquiv A F hA m (Ideal.Quotient.mk _ x) =
      residue _ (algebraMap _ (Localization.AtPrime m.asIdeal) x) :=
  normalizationQuotientEquiv_mk A F hA m x

/-- The valuation of a nonzero element of `A'` at a maximal ideal is nonnegative. -/
theorem normalizationOrd_nonneg (m : MaximalSpectrum ↥(integralClosure A F))
    (s : ↥(integralClosure A F)) (hs : (s : F) ≠ 0) :
    0 ≤ normalizationOrd A F hA m (Units.mk0 _ hs) := by
  let := localizationAlgebra A F m.asIdeal
  have := isFractionRing_localization A F m.asIdeal
  have := isDiscreteValuationRing_localization A F hA m.asIdeal
  have := isScalarTower_localization A F m.asIdeal
  have hval : algebraMap (Localization.AtPrime m.asIdeal) F
      (algebraMap ↥(integralClosure A F) (Localization.AtPrime m.asIdeal) s) = (s : F) := by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hne : algebraMap ↥(integralClosure A F) (Localization.AtPrime m.asIdeal) s ≠ 0 :=
    fun h ↦ hs (by rw [← hval, h, map_zero])
  have hF : algebraMap (Localization.AtPrime m.asIdeal) F
      (algebraMap ↥(integralClosure A F) (Localization.AtPrime m.asIdeal) s) ≠ 0 := hval ▸ hs
  have := dvrFracOrd_algebraMap_eq_ord F
    (exists_irreducible (Localization.AtPrime m.asIdeal)).choose_spec hne hF
  have hu : Units.mk0 _ hF = Units.mk0 (s : F) hs := Units.ext hval
  unfold normalizationOrd
  rw [← hu, this]
  exact Int.natCast_nonneg _

/-- **Every nonzero element of the normalization is a unit times a product of powers of the
`t_𝔪`.** -/
theorem mem_closure_normalizationGenerators (s : ↥(integralClosure A F)) (hs : s ≠ 0) :
    s ∈ Submonoid.closure
      ({x : ↥(integralClosure A F) | IsUnit x} ∪ Set.range (normalizationUniformizer A F hA)) := by
  classical
  have := finite_maximalSpectrum_integralClosure A F
  let := Fintype.ofFinite (MaximalSpectrum ↥(integralClosure A F))
  have hsF : (s : F) ≠ 0 := fun h ↦ hs (Subtype.ext h)
  set x : Fˣ := Units.mk0 _ hsF
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
  have h1 := isIntegral_of_forall_normalizationOrd_eq_zero A F hA hy
  have h2 := isIntegral_of_forall_normalizationOrd_eq_zero A F hA hyinv
  let w : ↥(integralClosure A F) := ⟨y, h1⟩
  let w' : ↥(integralClosure A F) := ⟨(y⁻¹ : Fˣ), h2⟩
  have hww : w * w' = 1 := Subtype.ext (by simp [w, w'])
  have hw : IsUnit w := IsUnit.of_mul_eq_one _ hww
  have hn : ∀ m, ((normalizationOrd A F hA m x).toNat : ℤ) = normalizationOrd A F hA m x :=
    fun m ↦ Int.toNat_of_nonneg (normalizationOrd_nonneg A F hA m s hsF)
  have hsw :
      s = w * ∏ m, normalizationUniformizer A F hA m ^ (normalizationOrd A F hA m x).toNat := by
    apply Subtype.ext
    have hprod : ((∏ m, normalizationUniformizer A F hA m ^
        (normalizationOrd A F hA m x).toNat : ↥(integralClosure A F)) : F) =
        ((∏ m, (t m) ^ (normalizationOrd A F hA m x) : Fˣ) : F) := by
      rw [SubmonoidClass.coe_finset_prod, Units.coe_prod]
      refine Finset.prod_congr rfl fun m _ ↦ ?_
      rw [SubmonoidClass.coe_pow, ← hn m, zpow_natCast, Units.val_pow_eq_pow_val]
      rfl
    rw [Subalgebra.coe_mul, hprod]
    show (x : F) = ((x * ∏ m, (t m) ^ (-normalizationOrd A F hA m x) : Fˣ) : F) * _
    rw [← Units.val_mul, mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, mul_one]
  rw [hsw]
  exact mul_mem (Submonoid.subset_closure (Set.mem_union_left _ hw))
    (prod_mem fun m _ ↦ pow_mem (Submonoid.subset_closure (Set.mem_union_right _
      (Set.mem_range_self (f := normalizationUniformizer A F hA) m))) _)

end Stacks.Chow

end

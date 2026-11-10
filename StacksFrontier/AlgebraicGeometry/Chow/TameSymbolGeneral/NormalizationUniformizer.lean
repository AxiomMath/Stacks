module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocity
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.Invariance
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.Local
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm

/-!
# Uniformizers of the normalization of a one-dimensional local domain

Let `A` be a Noetherian local domain of dimension one with fraction field `F` and normalization
`A'`, a semi-local Dedekind domain. For a maximal ideal `𝔪` of `A'` this file produces an element
`t_𝔪 ∈ A'` which is a uniformizer of the discrete valuation ring `A'_𝔪` and a unit at every other
maximal ideal of `A'` (`Stacks.Chow.exists_normalizationUniformizer`, by the Chinese remainder
theorem), and computes its valuations: `v_𝔪'(t_𝔪) = δ_{𝔪 𝔪'}`
(`Stacks.Chow.normalizationOrd_normalizationUniformizerUnit`). It also records that the order of
vanishing `ord_A` kills an element of `F` which, together with its inverse, is integral over `A`
(`Stacks.Chow.ordInt_eq_zero_of_isIntegral`, from Stacks 02MJ on the finite algebra
`A[y, y⁻¹]`).

## Main definitions

* `Stacks.Chow.normalizationOrd` — the valuation `v_𝔪 : F^* → ℤ` of `A'_𝔪`.
* `Stacks.Chow.normalizationUniformizer` — the element `t_𝔪`.

## Main results

* `Stacks.Chow.finite_maximalSpectrum_of_finite` — a finite algebra over a local ring is
  semi-local.
* `Stacks.Chow.ordInt_eq_zero_of_isUnit_of_finite`, `Stacks.Chow.ordInt_eq_zero_of_isIntegral`.
* `Stacks.Chow.exists_normalizationUniformizer`,
  `Stacks.Chow.normalizationOrd_normalizationUniformizerUnit`.

## References

* [Stacks Project, Tag 02MJ](https://stacks.math.columbia.edu/tag/02MJ)
* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing Stacks.Normalization

universe u

namespace Stacks.Chow

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]

/-! ### The order of vanishing along a finite subalgebra of `F` -/

omit [IsDomain A] [IsNoetherianRing A] in
/-- A finite algebra over a local ring has only finitely many maximal ideals: they all lie over
the maximal ideal, and the fibre is finite. -/
theorem finite_maximalSpectrum_of_finite (B : Type*) [CommRing B] [Algebra A B]
    [Module.Finite A B] : Finite (MaximalSpectrum B) := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := A) (S := B) (maximalIdeal A)
  have := hfin.to_subtype
  exact Finite.of_injective (fun v : MaximalSpectrum B ↦ (⟨v.asIdeal, v.isMaximal.isPrime,
    ⟨(eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A)
      v.asIdeal)).symm⟩⟩ : (maximalIdeal A).primesOver B))
    fun v w h ↦ MaximalSpectrum.ext (congrArg Subtype.val h)

/-- An element of a subalgebra `B` of `K`, viewed in `K`, is the image of its localization at a
prime of `B`. -/
private theorem coe_eq_algebraMap_localization {R K : Type*} [CommRing R] [CommRing K]
    [Algebra R K] (B : Subalgebra R K) (p : Ideal B) [p.IsPrime]
    [Algebra (Localization.AtPrime p) K] [IsScalarTower B (Localization.AtPrime p) K] (x : B) :
    (x : K) = algebraMap (Localization.AtPrime p) K (algebraMap B (Localization.AtPrime p) x) := by
  rw [← IsScalarTower.algebraMap_apply]
  rfl

/-- **Stacks 02MJ for a finite `A`-subalgebra `B` of `F`, at an element which is a unit of `B`**:
its order of vanishing over `A` is zero, being the sum of its orders at the local rings of `B`. -/
theorem ordInt_eq_zero_of_isUnit_of_finite [Ring.KrullDimLE 1 A] (B : Subalgebra A F)
    [Module.Finite A B] (y : B) (hy : IsUnit y) (hy0 : (y : F) ≠ 0) :
    ordInt A (y : F) hy0 = 0 := by
  classical
  have hinjAB : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply IsFractionRing.injective A F
    simpa using congrArg (fun z : B ↦ (z : F)) hab
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Ring.DimensionLEOne A := ⟨fun {p} hp _ => Ideal.isMaximal_of_isPrime_of_ne_bot p hp⟩
  have : Ring.DimensionLEOne B := Ring.DimensionLEOne.of_isIntegral (R := A) B
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinjAB
  have : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_finite A B
  have hfB : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let algL : ∀ v : MaximalSpectrum B, Algebra (Localization.AtPrime v.asIdeal) F := fun v =>
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ v.asIdeal.primeCompl (nonZeroDivisors B)
      v.asIdeal.primeCompl_le_nonZeroDivisors
  have towL : ∀ v : MaximalSpectrum B, IsScalarTower B (Localization.AtPrime v.asIdeal) F :=
    fun v => IsLocalization.localization_isScalarTower_of_submonoid_le _ _
      v.asIdeal.primeCompl (nonZeroDivisors B) v.asIdeal.primeCompl_le_nonZeroDivisors
  have fracL : ∀ v : MaximalSpectrum B, IsFractionRing (Localization.AtPrime v.asIdeal) F :=
    fun v => IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl _ _
  have kdL : ∀ v : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal) := by
    intro v
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height v.asIdeal]
    exact le_trans Ideal.height_le_ringKrullDim_of_isPrime
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 B))
  have hnorm : (y : F) = Algebra.norm F (y : F) := by
    rw [Algebra.norm_self]
    rfl
  rw [ord_norm_eq_sum_inertiaDeg_mul_ord A B F F hinjAB (y : F) hy0 (y : F) hnorm hy0]
  refine Finset.sum_eq_zero fun v _ ↦ ?_
  have hyv : IsUnit (algebraMap B (Localization.AtPrime v.asIdeal) y) := hy.map _
  have he := coe_eq_algebraMap_localization B v.asIdeal y
  have hne : algebraMap (Localization.AtPrime v.asIdeal) F
      (algebraMap B (Localization.AtPrime v.asIdeal) y) ≠ 0 := he ▸ hy0
  rw [ordInt_val_congr (Localization.AtPrime v.asIdeal) he hy0 hne,
    ordInt_eq_zero_of_isUnit _ hyv, mul_zero]

/-- **The order of vanishing kills an element integral over `A` together with its inverse.** -/
theorem ordInt_eq_zero_of_isIntegral [Ring.KrullDimLE 1 A] {y : F} (hy0 : y ≠ 0)
    (h1 : IsIntegral A y) (h2 : IsIntegral A y⁻¹) : ordInt A y hy0 = 0 := by
  let B : Subalgebra A F := Algebra.adjoin A {y, y⁻¹}
  have : Module.Finite A B := by
    refine Module.Finite.iff_fg.mpr (fg_adjoin_of_finite (Set.toFinite _) ?_)
    rintro z (rfl | rfl) <;> assumption
  let y' : B := ⟨y, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let y'' : B := ⟨y⁻¹, Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)⟩
  exact ordInt_eq_zero_of_isUnit_of_finite A F B y'
    (isUnit_iff_exists_inv.mpr ⟨y'', Subtype.ext (mul_inv_cancel₀ hy0)⟩) hy0

/-! ### The valuations of the normalization -/

section Normalization

variable [Ring.DimensionLEOne A]

/-- **The valuation `v_𝔪 : F^* → ℤ` of the local ring `A'_𝔪` of the normalization `A'` of `A` at a
maximal ideal `𝔪`**, computed with the uniformizer the tame symbol of `A'_𝔪` uses. -/
def normalizationOrd (hA : maximalIdeal A ≠ ⊥) (m : MaximalSpectrum ↥(integralClosure A F))
    (x : Fˣ) : ℤ :=
  letI := localizationAlgebra A F m.asIdeal
  haveI := isFractionRing_localization A F m.asIdeal
  haveI := isDiscreteValuationRing_localization A F hA m.asIdeal
  dvrFracOrd (A := Localization.AtPrime m.asIdeal) (F := F)
    (exists_irreducible (Localization.AtPrime m.asIdeal)).choose_spec x

/-- **A uniformizer of `A'_𝔪` inside `A'` which is a unit at the other maximal ideals of `A'`.**
Clear the denominator of a uniformizer of `A'_𝔪` and correct it, by the Chinese remainder theorem
in the Dedekind domain `A'`, modulo `𝔪 ^ 2` and modulo the other maximal ideals. -/
theorem exists_normalizationUniformizer (hA : maximalIdeal A ≠ ⊥)
    (m : MaximalSpectrum ↥(integralClosure A F)) :
    ∃ t : ↥(integralClosure A F),
      Irreducible (algebraMap ↥(integralClosure A F) (Localization.AtPrime m.asIdeal) t) ∧
        ∀ m' : MaximalSpectrum ↥(integralClosure A F), m' ≠ m → t ∉ m'.asIdeal := by
  classical
  have := isDedekindDomain_integralClosure A F
  have := isDiscreteValuationRing_localization A F hA m.asIdeal
  have := finite_maximalSpectrum_integralClosure A F
  have : Fintype (MaximalSpectrum ↥(integralClosure A F)) := Fintype.ofFinite _
  set R := Localization.AtPrime m.asIdeal
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective m.asIdeal.primeCompl ϖ
  have has : algebraMap _ R a = ϖ * algebraMap _ R (s : ↥(integralClosure A F)) := by
    rw [← IsLocalization.mk'_spec R a s]
    exact congrArg (· * _) hs
  have hsu : IsUnit (algebraMap _ R (s : ↥(integralClosure A F))) :=
    IsLocalization.map_units R s
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun m' : MaximalSpectrum ↥(integralClosure A F) ↦ m'.asIdeal)
    (fun m' ↦ if m' = m then 2 else 1)
    (fun m' _ ↦ Ideal.prime_of_isPrime (ne_bot_of_isMaximal A F hA m'.asIdeal) inferInstance)
    (fun m₁ _ m₂ _ h ↦ fun h' ↦ h (MaximalSpectrum.ext h'))
    (fun m' ↦ if (m' : MaximalSpectrum ↥(integralClosure A F)) = m then a else 1)
  refine ⟨t, ?_, fun m' hm' ↦ ?_⟩
  · have htm := ht m (Finset.mem_univ m)
    simp only [ite_true] at htm
    have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
    have hmem : algebraMap _ R (t - a) ∈ (IsLocalRing.maximalIdeal R) ^ 2 := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m.asIdeal R, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ htm
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hteq : algebraMap _ R t =
        ϖ * (algebraMap _ R (s : ↥(integralClosure A F)) + ϖ * c) := by
      have : algebraMap _ R t = algebraMap _ R a + algebraMap _ R (t - a) := by
        rw [map_sub]
        ring
      rw [this, has, ← hc]
      ring
    have hunit : IsUnit (algebraMap _ R (s : ↥(integralClosure A F)) + ϖ * c) := by
      by_contra hnu
      have h1 : algebraMap _ R (s : ↥(integralClosure A F)) + ϖ * c ∈
          IsLocalRing.maximalIdeal R :=
        (mem_maximalIdeal _).mpr hnu
      have h2 : ϖ * c ∈ IsLocalRing.maximalIdeal R := by
        rw [hmax]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      have h3 := Ideal.sub_mem _ h1 h2
      rw [add_sub_cancel_right] at h3
      exact (mem_maximalIdeal _).mp h3 hsu
    rwa [hteq, irreducible_mul_isUnit hunit]
  · have htm := ht m' (Finset.mem_univ m')
    simp only [ite_eq_right hm', pow_one] at htm
    intro hmem
    have h1 : (1 : ↥(integralClosure A F)) ∈ m'.asIdeal := by
      have := Ideal.sub_mem _ hmem htm
      rwa [sub_sub_cancel] at this
    exact m'.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The element `t_𝔪` of `Stacks.Chow.exists_normalizationUniformizer`. -/
def normalizationUniformizer (hA : maximalIdeal A ≠ ⊥)
    (m : MaximalSpectrum ↥(integralClosure A F)) :
    ↥(integralClosure A F) :=
  (exists_normalizationUniformizer A F hA m).choose

/-- The element `t_𝔪` is nonzero in `F`. -/
theorem normalizationUniformizer_ne_zero (hA : maximalIdeal A ≠ ⊥)
    (m : MaximalSpectrum ↥(integralClosure A F)) :
    (normalizationUniformizer A F hA m : F) ≠ 0 := by
  intro h
  have h0 : normalizationUniformizer A F hA m = 0 := Subtype.ext h
  have h1 : Irreducible (algebraMap ↥(integralClosure A F) (Localization.AtPrime m.asIdeal)
      (normalizationUniformizer A F hA m)) :=
    (exists_normalizationUniformizer A F hA m).choose_spec.1
  rw [h0, map_zero] at h1
  exact not_irreducible_zero h1

/-- `t_𝔪` as a unit of `F`. -/
def normalizationUniformizerUnit (hA : maximalIdeal A ≠ ⊥)
    (m : MaximalSpectrum ↥(integralClosure A F)) : Fˣ :=
  Units.mk0 _ (normalizationUniformizer_ne_zero A F hA m)

/-- **`v_𝔪'(t_𝔪)` is `1` for `𝔪' = 𝔪` and `0` otherwise.** -/
theorem normalizationOrd_normalizationUniformizerUnit (hA : maximalIdeal A ≠ ⊥)
    (m m' : MaximalSpectrum ↥(integralClosure A F)) :
    open Classical in
    normalizationOrd A F hA m' (normalizationUniformizerUnit A F hA m) =
      if m' = m then 1 else 0 := by
  let := localizationAlgebra A F m'.asIdeal
  have := isFractionRing_localization A F m'.asIdeal
  have := isDiscreteValuationRing_localization A F hA m'.asIdeal
  have := isScalarTower_localization A F m'.asIdeal
  set R := Localization.AtPrime m'.asIdeal
  set t := normalizationUniformizer A F hA m
  have hval : (normalizationUniformizerUnit A F hA m : F) =
      algebraMap R F (algebraMap ↥(integralClosure A F) R t) :=
    coe_eq_algebraMap_localization _ m'.asIdeal t
  split_ifs with h
  · subst h
    have hirr : Irreducible (algebraMap ↥(integralClosure A F) R t) :=
      (exists_normalizationUniformizer A F hA m').choose_spec.1
    obtain ⟨w, hw⟩ := exists_unit_eq_mul_of_irreducible
      (exists_irreducible R).choose_spec hirr
    refine dvrFracOrd_eq_of_eq (u := w) (n := 1) _ ?_
    rw [hval, hw, map_mul, zpow_one]
  · have hnot : t ∉ m'.asIdeal := (exists_normalizationUniformizer A F hA m).choose_spec.2 m' h
    have hunit : IsUnit (algebraMap ↥(integralClosure A F) R t) :=
      IsLocalization.map_units R (⟨t, hnot⟩ : m'.asIdeal.primeCompl)
    exact dvrFracOrd_eq_zero_of_eq_algebraMap_unit (u := hunit.unit) _
      (by rw [IsUnit.unit_spec, ← hval])

end Normalization

end Stacks.Chow

end

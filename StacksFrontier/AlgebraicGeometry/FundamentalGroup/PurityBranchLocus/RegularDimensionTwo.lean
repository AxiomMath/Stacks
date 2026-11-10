module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.UnramifiedCodimensionOne
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecStalkHeight
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import StacksFrontier.RingTheory.Serre.Criterion
public import StacksFrontier.Topology.Sober.Generization

/-!
# Purity of the branch locus over a regular local ring of dimension two

Let `A` be a regular local ring of Krull dimension two and let `B` be a finite normal
`A`-algebra, torsion-free over `A`, whose spectrum is étale over the punctured spectrum of `A`.
Then `A → B` is étale. This is the second clause of [Stacks, Tag 0BMA] in the case `d = 2`.

Normality of `B` is `IsNormalRing B`: every localization of `B` at a prime is an integrally
closed domain, item (1) of [Stacks, Tag 030C]. Torsion-freeness of `B` over `A` is not assumed
in the source, and is necessary: the residue field `A ⧸ 𝔪_A` is a finite normal `A`-algebra
whose spectrum misses the punctured spectrum, so it is étale there, and `A → A ⧸ 𝔪_A` is not
flat.

## Main results

* `Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_ringKrullDim_eq_two`: a finite normal
  torsion-free algebra over a two-dimensional regular local ring `A` which is étale over the
  punctured spectrum of `A` is étale over `A`.

## References

* [Stacks Project, Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 0BJH](https://stacks.math.columbia.edu/tag/0BJH)
* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [Stacks Project, Tag 00HT](https://stacks.math.columbia.edu/tag/00HT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.PurityDimensionTwo

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-! ### Minimal primes of a normal ring -/

/-- The quotient of a normal Noetherian ring by a minimal prime is an integrally closed
domain. -/
@[ega "IV 5.13.5" "special case"]
private lemma isIntegrallyClosed_quotient_minimalPrime
    [IsNoetherianRing B] (hB : IsNormalRing B) {r : Ideal B} (hr : r ∈ minimalPrimes B) :
    IsIntegrallyClosed (B ⧸ r) := by
  have : IsReduced B := hB.isReduced
  have htfae := isIntegrallyClosed_tfae_of_finite_minimalPrimes (R := B)
    (minimalPrimes.finite_of_isNoetherianRing B)
  have h4 := (htfae.out 1 4).mp (isNormalRing_iff.mp hB)
  exact h4.1 r hr

/-- The maximal ideal of the localization of a normal ring at a minimal prime is zero. -/
private lemma maximalIdeal_eq_bot_of_minimalPrime (hB : IsNormalRing B)
    {r : Ideal B} (hr : r ∈ minimalPrimes B) :
    let : r.IsPrime := hr.1.1
    IsLocalRing.maximalIdeal (Localization.AtPrime r) = ⊥ := by
  let : r.IsPrime := hr.1.1
  let : IsDomain (Localization.AtPrime r) := (hB r).1
  have hdim : ringKrullDim (Localization.AtPrime r) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height r (Localization.AtPrime r),
      Ideal.height_eq_zero_iff.2 hr]
    rfl
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime r)).height = 0 := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      (R := Localization.AtPrime r)
    rw [hdim] at h
    exact_mod_cast h
  exact Ideal.height_eq_zero_iff_eq_bot.1 hmax

/-- If `B` is normal and torsion-free over a domain `A`, then `A → B ⧸ 𝔯` is injective for every
minimal prime `𝔯` of `B`. -/
private lemma injective_algebraMap_quotient_minimalPrime [IsDomain A]
    [Module.IsTorsionFree A B] (hB : IsNormalRing B)
    {r : Ideal B} (hr : r ∈ minimalPrimes B) :
    let : r.IsPrime := hr.1.1
    Function.Injective (algebraMap A (B ⧸ r)) := by
  let : r.IsPrime := hr.1.1
  apply (injective_iff_map_eq_zero (algebraMap A (B ⧸ r))).2
  intro a ha
  have har : algebraMap A B a ∈ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq r,
      ← IsScalarTower.algebraMap_apply A B (B ⧸ r)]
    exact ha
  have hzero : algebraMap B (Localization.AtPrime r) (algebraMap A B a) = 0 := by
    have hmem : algebraMap B (Localization.AtPrime r) (algebraMap A B a) ∈
        r.map (algebraMap B (Localization.AtPrime r)) := Ideal.mem_map_of_mem _ har
    rw [Localization.AtPrime.map_eq_maximalIdeal,
      maximalIdeal_eq_bot_of_minimalPrime B hB hr] at hmem
    exact (Submodule.mem_bot _).mp hmem
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff r.primeCompl
    (Localization.AtPrime r) (algebraMap A B a)).mp hzero
  have hsmul : a • (s : B) = 0 := by
    simpa [Algebra.smul_def, mul_comm] using hs
  rcases Module.isTorsionFree_iff_smul_eq_zero.mp ‹Module.IsTorsionFree A B› a s hsmul with
    ha0 | hs0
  · exact ha0
  · exact absurd (hs0 ▸ r.zero_mem) s.2

/-- `A → B` is injective when `B` is normal and torsion-free over the domain `A`. -/
private lemma faithfulSMul_of_isNormalRing [IsDomain A] [IsNoetherianRing B]
    [Module.IsTorsionFree A B] (hB : IsNormalRing B) (Q : Ideal B) [Q.IsPrime] :
    FaithfulSMul A B := by
  obtain ⟨r, hr, -⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal B) ≤ Q from bot_le)
  let : r.IsPrime := hr.1.1
  refine (faithfulSMul_iff_algebraMap_injective A B).2 fun a b hab => ?_
  refine injective_algebraMap_quotient_minimalPrime A B hB hr ?_
  rw [IsScalarTower.algebraMap_apply A B (B ⧸ r), IsScalarTower.algebraMap_apply A B (B ⧸ r),
    hab]

/-! ### Going down -/

/-- Going down holds for a finite normal torsion-free algebra over a regular local ring. -/
private lemma hasGoingDown_of_isNormalRing [IsRegularLocalRing A] [IsNoetherianRing B]
    [Module.Finite A B] [Module.IsTorsionFree A B] (hB : IsNormalRing B) :
    Algebra.HasGoingDown A B := by
  let : IsDomain A := IsRegularLocalRing.isDomain A
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  refine ⟨?_⟩
  intro p hp Q hQ hlt
  obtain ⟨r, hrmin, hrQ⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal B) ≤ Q from bot_le)
  let : r.IsPrime := hrmin.1.1
  let : IsIntegrallyClosed (B ⧸ r) := isIntegrallyClosed_quotient_minimalPrime B hB hrmin
  let : FaithfulSMul A (B ⧸ r) := (faithfulSMul_iff_algebraMap_injective A (B ⧸ r)).2
    (injective_algebraMap_quotient_minimalPrime A B hB hrmin)
  let : Module.Finite A (B ⧸ r) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A r).toLinearMap
      Ideal.Quotient.mk_surjective
  let : Algebra.IsIntegral A (B ⧸ r) := Algebra.IsIntegral.of_finite A (B ⧸ r)
  set π : B →+* B ⧸ r := Ideal.Quotient.mk r with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = r := Ideal.mk_ker
  have hkerQ : RingHom.ker π ≤ Q := hker.trans_le hrQ
  set Q' : Ideal (B ⧸ r) := Q.map π with hQ'
  let : Q'.IsPrime := Ideal.map_isPrime_of_surjective hsurj hkerQ
  have hQ'comap : Q'.comap π = Q := by
    rw [hQ', Ideal.comap_map_of_surjective π hsurj, ← RingHom.ker_eq_comap_bot, hker,
      sup_eq_left.mpr hrQ]
  have hcomp : algebraMap A (B ⧸ r) = π.comp (algebraMap A B) := by
    rw [IsScalarTower.algebraMap_eq A B (B ⧸ r), hπ, Ideal.Quotient.algebraMap_eq]
  have hunder : Ideal.under A Q' = Ideal.under A Q := by
    change Q'.comap (algebraMap A (B ⧸ r)) = Q.comap (algebraMap A B)
    rw [hcomp, ← Ideal.comap_comap, hQ'comap]
  obtain ⟨P', hP'Q', hP'prime, hP'lies⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (R := A) (S := B ⧸ r) Q'
      (by rwa [hunder])
  refine ⟨P'.comap π, (Ideal.comap_mono hP'Q').trans_eq hQ'comap, hP'prime.comap π, ?_⟩
  refine ⟨?_⟩
  change p = (P'.comap π).comap (algebraMap A B)
  rw [Ideal.comap_comap, ← hcomp]
  exact hP'lies.over

/-! ### The dimension of a local ring of `B` at a closed point -/

/-- For a finite normal torsion-free algebra `B` over a regular local ring `A`, a prime of `B`
over the maximal ideal of `A` has height `dim A`. -/
@[ega "IV 5.6.11" "special case"]
private lemma height_eq_ringKrullDim_of_liesOver_maximalIdeal
    [IsRegularLocalRing A] [IsNoetherianRing B]
    [Module.Finite A B] [Module.IsTorsionFree A B] (hB : IsNormalRing B)
    (Q : Ideal B) [Q.IsPrime] (hunder : Ideal.under A Q = IsLocalRing.maximalIdeal A) :
    (Q.height : WithBot ℕ∞) = ringKrullDim A := by
  let : IsDomain A := IsRegularLocalRing.isDomain A
  let : FaithfulSMul A B := faithfulSMul_of_isNormalRing A B hB Q
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : Algebra.HasGoingDown A B := hasGoingDown_of_isNormalRing A B hB
  let : (IsLocalRing.maximalIdeal A).IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  let : Q.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hunder.symm⟩
  have hdimB : ringKrullDim B = ringKrullDim A :=
    (Algebra.IsIntegral.ringKrullDim_eq A B).symm
  refine le_antisymm ?_ ?_
  · calc (Q.height : WithBot ℕ∞) ≤ ringKrullDim B := by
          exact_mod_cast Ideal.height_le_ringKrullDim_of_isPrime (I := Q)
      _ = ringKrullDim A := hdimB
  · have hle : (IsLocalRing.maximalIdeal A).height ≤ Q.height := by
      rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (IsLocalRing.maximalIdeal A) Q]
      exact le_add_right le_rfl
    calc ringKrullDim A = ((IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) :=
          (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).symm
      _ ≤ (Q.height : WithBot ℕ∞) := by exact_mod_cast hle

/-! ### Cohen–Macaulayness in dimension at most two -/

/-- The localization of a normal Noetherian ring at a prime, if of dimension at most two, is
Cohen–Macaulay. -/
@[sga "2 XI 3.11" "(ii), special case"]
private lemma isMaximalCohenMacaulay_of_isNormalRing_of_ringKrullDim_le_two
    [IsNoetherianRing B] (hB : IsNormalRing B) (Q : Ideal B) [Q.IsPrime]
    (hdim : ringKrullDim (Localization.AtPrime Q) ≤ 2) :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q) := by
  have hS2 := (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
    (R := B)).mp (isNormalRing_iff.mp hB) |>.2 Q
  have hdepth : ringKrullDim (Localization.AtPrime Q) ≤
      (Module.depth (Localization.AtPrime Q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) :
          WithBot ℕ∞) := by
    simpa only [min_eq_right hdim] using hS2
  have hle : (Module.depth (Localization.AtPrime Q)
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) :
        WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime Q) := by
    calc _ ≤ Module.supportDim (Localization.AtPrime Q) (Localization.AtPrime Q) :=
          Module.depth_le_supportDim (Localization.AtPrime Q) _ (Localization.AtPrime Q)
            (by simpa using (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime Q)).ne_top)
      _ = ringKrullDim (Localization.AtPrime Q) :=
          Module.supportDim_self_eq_ringKrullDim (Localization.AtPrime Q)
  exact le_antisymm hle hdepth

/-! ### The fibre ring is zero-dimensional -/

attribute [local instance] Ideal.algebraLocalizationAtPrimeUnder
  Ideal.isScalarTower_localizationAtPrimeUnder
  Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder

/-- The radical of `𝔭B_𝔮`, for `𝔭 = A ∩ 𝔮`, is the maximal ideal of `B_𝔮` when `𝔭` is maximal
and `A → B` is integral. -/
private lemma radical_map_under_eq_maximalIdeal [Algebra.IsIntegral A B]
    (Q : Ideal B) [Q.IsPrime] (hmax : (Ideal.under A Q).IsMaximal) :
    ((Ideal.under A Q).map (algebraMap A (Localization.AtPrime Q))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  have hmapD : (Ideal.under A Q).map (algebraMap A (Localization.AtPrime Q)) =
      ((Ideal.under A Q).map (algebraMap A B)).map (algebraMap B (Localization.AtPrime Q)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hle : (Ideal.under A Q).map (algebraMap A (Localization.AtPrime Q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [hmapD, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono Ideal.map_comap_le
  refine le_antisymm ?_ ?_
  · exact (IsLocalRing.maximalIdeal.isMaximal
      (Localization.AtPrime Q)).isPrime.isRadical.radical_le_iff.mpr hle
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro J ⟨hJle, hJprime⟩
    let : J.IsPrime := hJprime
    let : (J.comap (algebraMap B (Localization.AtPrime Q))).IsPrime := hJprime.comap _
    have hJmax : J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
      IsLocalRing.le_maximalIdeal_of_isPrime J
    have hQ'Q : J.comap (algebraMap B (Localization.AtPrime Q)) ≤ Q := by
      have h := Ideal.comap_mono (f := algebraMap B (Localization.AtPrime Q)) hJmax
      rwa [show (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
        (algebraMap B (Localization.AtPrime Q)) = Q from
          Localization.AtPrime.under_maximalIdeal] at h
    have hpQ' : Ideal.under A Q ≤
        Ideal.under A (J.comap (algebraMap B (Localization.AtPrime Q))) := by
      intro a ha
      have hmem : algebraMap A (Localization.AtPrime Q) a ∈ J :=
        hJle (Ideal.mem_map_of_mem _ ha)
      rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q)] at hmem
      exact hmem
    have hunder' : Ideal.under A (J.comap (algebraMap B (Localization.AtPrime Q))) =
        Ideal.under A Q :=
      (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hpQ').symm
    have hQ'eq : J.comap (algebraMap B (Localization.AtPrime Q)) = Q := by
      refine le_antisymm hQ'Q ?_
      by_contra hne
      exact absurd hunder' (ne_of_lt (Ideal.IsIntegral.under_lt_under (R := A)
        (lt_of_le_of_ne hQ'Q (fun h => hne (le_of_eq h.symm)))))
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    calc Ideal.map (algebraMap B (Localization.AtPrime Q)) Q
        = Ideal.map (algebraMap B (Localization.AtPrime Q))
            (J.comap (algebraMap B (Localization.AtPrime Q))) := by rw [hQ'eq]
      _ ≤ J := Ideal.map_comap_le

/-- The fibre ring of `A → B_𝔮` is zero-dimensional when `A ∩ 𝔮` is maximal and `A → B` is
integral. -/
private lemma ringKrullDim_fiberRing_eq_zero [Algebra.IsIntegral A B]
    (Q : Ideal B) [Q.IsPrime] (hmax : (Ideal.under A Q).IsMaximal) :
    ringKrullDim (Localization.AtPrime Q ⧸
      (Ideal.under A Q).map (algebraMap A (Localization.AtPrime Q))) = 0 := by
  have hrad := radical_map_under_eq_maximalIdeal A B Q hmax
  have hle : (Ideal.under A Q).map (algebraMap A (Localization.AtPrime Q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [← hrad]
    exact Ideal.le_radical
  have hproper : (Ideal.under A Q).map (algebraMap A (Localization.AtPrime Q)) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime Q)).ne_top hle
  have : Nontrivial (Localization.AtPrime Q ⧸
      (Ideal.under A Q).map (algebraMap A (Localization.AtPrime Q))) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  refine ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
    (Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr fun J hJ => ?_)
  have hmaxle : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ J := by
    rw [← hrad]
    exact hJ.1.1.radical_le_iff.mpr hJ.1.2
  have hJeq : IsLocalRing.maximalIdeal (Localization.AtPrime Q) = J :=
    (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime Q)).eq_of_le hJ.1.1.ne_top hmaxle
  rw [← hJeq]
  exact IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime Q)

/-! ### Flatness -/

/-- A finite normal torsion-free algebra over a two-dimensional regular local ring is flat. -/
private lemma flat_of_isNormalRing_of_ringKrullDim_eq_two
    [IsRegularLocalRing A] [IsNoetherianRing B]
    [Module.Finite A B] [Module.IsTorsionFree A B] (hB : IsNormalRing B)
    (hdimA : ringKrullDim A = 2) : Module.Flat A B := by
  let : IsDomain A := IsRegularLocalRing.isDomain A
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hAreg : IsRegularRing A :=
    ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp (inferInstance : IsRegularLocalRing A)
  refine Module.flat_of_isLocalized_maximal B B (fun P => Localization.AtPrime P)
    (fun P => Algebra.linearMap B (Localization.AtPrime P)) ?_
  intro P hP
  let : P.IsPrime := hP.isPrime
  have hPunder : Ideal.under A P = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) P)
  have hPmax : (Ideal.under A P).IsMaximal := hPunder ▸ IsLocalRing.maximalIdeal.isMaximal A
  have hPheight : (P.height : WithBot ℕ∞) = ringKrullDim A :=
    height_eq_ringKrullDim_of_liesOver_maximalIdeal A B hB P hPunder
  let : IsRegularLocalRing (Localization.AtPrime (Ideal.under A P)) :=
    isRegularRing_iff.mp hAreg (Ideal.under A P)
  have hdimD : ringKrullDim (Localization.AtPrime P) = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hPheight, hdimA]
  have hdimL : ringKrullDim (Localization.AtPrime (Ideal.under A P)) = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (Ideal.under A P)
      (Localization.AtPrime (Ideal.under A P)), hPunder,
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A), hdimA]
  have hcm :=
    isMaximalCohenMacaulay_of_isNormalRing_of_ringKrullDim_le_two B hB P (le_of_eq hdimD)
  have hflat : Module.Flat (Localization.AtPrime (Ideal.under A P)) (Localization.AtPrime P) := by
    refine Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add hcm ?_
    rw [Ideal.map_maximalIdeal_eq_map_under (R := A) P,
      ringKrullDim_fiberRing_eq_zero A B P hPmax, add_zero, hdimD, hdimL]
  have : Module.Flat A (Localization.AtPrime (Ideal.under A P)) :=
    IsLocalization.flat (Localization.AtPrime (Ideal.under A P)) (Ideal.under A P).primeCompl
  exact Module.Flat.trans A (Localization.AtPrime (Ideal.under A P)) (Localization.AtPrime P)

/-! ### Étaleness -/

/-- A finite normal torsion-free algebra `B` over a two-dimensional regular local ring `A` which
is étale over the punctured spectrum of `A` gives an étale morphism `Spec B ⟶ Spec A`. -/
@[ega "IV 21.12.14" "special case"]
private lemma etale_specMap_of_isNormalRing_of_ringKrullDim_eq_two
    [IsRegularLocalRing A] [Module.Finite A B] [Module.IsTorsionFree A B]
    (hB : IsNormalRing B) (hdimA : ringKrullDim A = 2)
    (hetale : Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
      Stacks.puncturedSpectrum A)) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  let : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsNoetherianRing B := isNoetherian_of_tower A (inferInstance : IsNoetherian A B)
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  set f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B)) with hf
  have : IsFinite f := (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap A B))).2
    (RingHom.finite_algebraMap.mpr ‹Module.Finite A B›)
  have : Flat f := Flat.SpecMap_iff.2
    (RingHom.flat_algebraMap_iff.2 (flat_of_isNormalRing_of_ringKrullDim_eq_two A B hB hdimA))
  set U : (Spec (.of A)).Opens := Stacks.puncturedSpectrum A with hU
  set W : (Spec (.of B)).Opens := f ⁻¹ᵁ U with hW
  have hEtComp : Etale (W.ι ≫ f) := by
    rw [hW, ← morphismRestrict_ι f U]
    let := hetale
    infer_instance
  have hunrU : ∀ y : Spec (.of B), f.base y ∈ (U : Set (Spec (.of A))) → UnramifiedAt f y := by
    intro y hy
    have hyW : y ∈ (W : Set (Spec (.of B))) := hy
    have hEtAt : EtaleAt (W.ι ≫ f) (⟨y, hyW⟩ : W.toScheme) :=
      (etale_iff_forall_etaleAt (W.ι ≫ f)).mp hEtComp _
    have := ((etaleAt_iff_smoothAt_and_unramifiedAt (W.ι ≫ f) _).mp hEtAt).2
    exact (unramifiedAt_comp_ι_iff f W ⟨y, hyW⟩).mp this
  have hheight : ∀ y : Spec (.of B), f.base y = IsLocalRing.closedPoint A →
      (y.asIdeal.height : WithBot ℕ∞) = 2 := by
    intro y hy
    let : y.asIdeal.IsPrime := y.isPrime
    have hunder : Ideal.under A y.asIdeal = IsLocalRing.maximalIdeal A := by
      change (f.base y).asIdeal = IsLocalRing.maximalIdeal A
      rw [hy]; rfl
    exact (height_eq_ringKrullDim_of_liesOver_maximalIdeal A B hB y.asIdeal hunder).trans hdimA
  have hunr : ∀ y : Spec (.of B), UnramifiedAt f y := by
    intro y
    by_cases hy : f.base y ∈ (U : Set (Spec (.of A)))
    · exact hunrU y hy
    have hyc : f.base y = IsLocalRing.closedPoint A := by
      have : f.base y ∈ ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) := not_not.mp hy
      exact Set.mem_singleton_iff.mp this
    have hqf : quasiFiniteAt f y :=
      (forall_quasiFiniteAt_iff f).mpr ⟨inferInstance, inferInstance⟩ y
    have hgen : y ∉ genericPoints (Spec (.of B)) := by
      intro hmem
      let : y.asIdeal.IsPrime := y.isPrime
      obtain ⟨r, hrmin, hrQ⟩ :=
        Ideal.exists_minimalPrimes_le (show (⊥ : Ideal B) ≤ y.asIdeal from bot_le)
      let : r.IsPrime := hrmin.1.1
      have hspec : (⟨r, hrmin.1.1⟩ : PrimeSpectrum B) ⤳ y :=
        (PrimeSpectrum.le_iff_specializes _ _).mp hrQ
      have hreq : r = y.asIdeal := congrArg PrimeSpectrum.asIdeal
        (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hmem _ hspec)
      have hzero : y.asIdeal.height = 0 := by
        rw [← hreq]; exact Ideal.height_eq_zero_iff.2 hrmin
      simpa [hzero] using hheight y hyc
    have hcodim : ∀ y' : Spec (.of B), y' ⤳ y →
        ringKrullDim ((Spec (.of B)).presheaf.stalk y') = 1 → UnramifiedAt f y' := by
      intro y' _ hdim'
      refine hunrU y' ?_
      change f.base y' ∉ ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))
      intro hmem'
      have hy'c : f.base y' = IsLocalRing.closedPoint A := Set.mem_singleton_iff.mp hmem'
      rw [ringKrullDim_stalk_spec (CommRingCat.of B) y', hheight y' hy'c] at hdim'
      simp at hdim'
    exact ((etaleAt_iff_smoothAt_and_unramifiedAt f y).mp
      (etaleAt_of_flat_of_unramifiedAt_codimensionOne f y hqf hgen hcodim)).2
  exact (etale_iff_forall_etaleAt f).mpr fun y => (etaleAt_iff_isFlatAt_and_gUnramifiedAt f y).mpr
    ⟨(Flat.iff_flat_stalkMap f).mp inferInstance y, gUnramifiedAt_of_unramifiedAt f y (hunr y)⟩

/-- Let `A` be a regular local ring of Krull dimension `2`, and let `B` be a finite `A`-algebra
which is a normal ring and torsion-free over `A`, such that the induced morphism on punctured
spectra is étale. Then `A → B` is étale. -/
@[stacks 0BMA "clause (2) of the tag, and only in the case `d = 2`: `A` regular local with \
`ringKrullDim A = 2`, `B` a finite `A`-algebra which is a normal ring in the sense of \
`IsNormalRing` (item (1) of tag 030C) and is torsion-free over `A`, and `Spec B ⟶ Spec A` \
étale over the punctured spectrum; the conclusion is `Algebra.Etale A B`. This is the base case \
of the source's induction on `d`; the inductive step is tag 0BLM, and clause (2) for every \
`d ≥ 2` is `etale_of_isNormalRing_of_two_le_ringKrullDim` in \
`PurityBranchLocus.PurityRegularLocal`. Clause (1) at `d = 2` — \
essential surjectivity of `FÉt_X ⟶ FÉt_U`, i.e. purity for `A` — follows from this result \
through tag 0BM9 and is `Stacks.PurityDimensionTwo.hasPurity_of_ringKrullDim_eq_two`. \
Torsion-freeness over `A` is an \
extra hypothesis, not present in the source and necessary for the statement to be true: the \
residue field `A ⧸ 𝔪` is a finite normal `A`-algebra whose spectrum misses the punctured \
spectrum, hence is étale there, and is not étale over `A`. See the module docstring.",
  sga "1 X 3.2" "special case"]
public theorem etale_of_isNormalRing_of_ringKrullDim_eq_two
    [IsRegularLocalRing A] [Module.Finite A B] [Module.IsTorsionFree A B]
    (hB : IsNormalRing B) (hdimA : ringKrullDim A = 2)
    (hetale : Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
      Stacks.puncturedSpectrum A)) :
    Algebra.Etale A B := by
  have hEt := etale_specMap_of_isNormalRing_of_ringKrullDim_eq_two A B hB hdimA hetale
  have hTop := (HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 hEt
  exact RingHom.etale_algebraMap.mp ((RingHom.Etale.respectsIso.arrow_mk_iso_iff
    (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom (algebraMap A B)))).mpr hTop)

end Stacks.PurityDimensionTwo

end

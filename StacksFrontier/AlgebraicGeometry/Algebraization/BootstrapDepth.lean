module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.FlatLocalHom

/-!
# Depth outside the adic locus in the bootstrap situation

In the bootstrap situation, a prime `p` outside the adic locus `V(I)` which specializes to a
prime of the distinguished locus `T` without passing through any prime of `V(I) \ T` has
`depth(M_p) > s`, strictly better than the bound the situation assumes for a general chain.

The argument replaces `q` by the minimal prime `q₀` of `p + I` below it, which lies in `T` and
below which no further prime of `T` sits, and then transports the assumption on the completed
localization `A_{q₀}^∧` back down: a minimal prime `p'` of `p A_{q₀}^∧` meets the adic locus
only in the closed point, so the assumed strict bound applies to it, and the local fibre of
`A_p → (A_{q₀}^∧)_{p'}` is Artinian, hence of depth zero.

## Main results

* `Stacks.Algebraization.depth_localized_gt_of_no_intermediate_prime` — the strict depth bound
  at the smaller prime.

## Implementation notes

The inclusions between primes are non-strict, as in the source, and the depth of the localized
module is compared with the integer bound in the extended integers.

## References

* [Stacks Project, Tag 0EID](https://stacks.math.columbia.edu/tag/0EID)
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence
open scoped TensorProduct

universe u v w

namespace Stacks.Algebraization

/-- In a Noetherian local ring, an Artinian quotient by an ideal contained in the maximal ideal
has depth zero: its support dimension is zero and the maximal ideal does not annihilate it. -/
private lemma depth_quotient_eq_zero_of_isArtinianRing {L : Type*} [CommRing L]
    [IsNoetherianRing L] [IsLocalRing L] (J : Ideal L) (hJ : J ≤ maximalIdeal L)
    (hart : IsArtinianRing (L ⧸ J)) :
    Module.depth L (maximalIdeal L) (L ⧸ J) = 0 := by
  have hnontriv : Nontrivial (L ⧸ J) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal L).ne_top hJ
  have hdim : ringKrullDim (L ⧸ J) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp (isArtinianRing_iff_krullDimLE_zero.mp hart)
  have hnot : maximalIdeal L • (⊤ : Submodule L (L ⧸ J)) ≠ ⊤ := by
    intro heq
    have hm : ((maximalIdeal L).map (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hJ)
    refine hm.ne_top ?_
    have hmaptop : Submodule.restrictScalars L
        ((maximalIdeal L).map (Ideal.Quotient.mk J)) = ⊤ := by
      simpa [Ideal.smul_top_eq_map] using heq
    simpa using hmaptop
  have hle := Module.depth_le_supportDim L (maximalIdeal L) (L ⧸ J) hnot
  rw [Module.supportDim_quotient_eq_ringKrullDim, hdim] at hle
  exact le_antisymm (by exact_mod_cast hle) zero_le

/-- Scalar towers `R → S → T` on a module compatible with both steps compose. -/
private theorem isScalarTower_of_tower_of_tower {R S T M : Type*} [CommSemiring R]
    [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [AddCommMonoid M] [Module R M] [Module S M] [Module T M]
    [IsScalarTower R S M] [IsScalarTower S T M] : IsScalarTower R T M :=
  IsScalarTower.of_algebraMap_smul fun a x => by
    rw [IsScalarTower.algebraMap_apply R S T, algebraMap_smul, algebraMap_smul]

/-- Extending an ideal along `R → S → T` in two steps is extending it along the composite. -/
private theorem map_map_algebraMap {R S T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (I : Ideal R) :
    (I.map (algebraMap R S)).map (algebraMap S T) = I.map (algebraMap R T) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **Stacks Project, Tag 0EID.** In the bootstrap situation the depth at `p` exceeds `s` when
no prime of `V(I) \ T` lies between `p` and a prime `q` of `T`. -/
@[stacks 0EID]
public theorem depth_localized_gt_of_no_intermediate_prime
    (S : BootstrapSituation.{u, v, w})
    (p q : PrimeSpectrum S.A)
    (hpq : p.asIdeal ≤ q.asIdeal)
    (hp : p ∉ PrimeSpectrum.zeroLocus (S.I : Set S.A))
    (hq : q ∈ S.T)
    (h : ¬ ∃ r : PrimeSpectrum S.A,
      p.asIdeal ≤ r.asIdeal ∧ r.asIdeal ≤ q.asIdeal ∧
      r ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) ∧ r ∉ S.T) :
    enatToEInt
      (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl S.M)) > (S.s : EInt) := by
  classical
  let := S.isNoetherianRing
  have hqI : S.I ≤ q.asIdeal := S.subset_adicLocus hq
  have hpI_le_q : p.asIdeal ⊔ S.I ≤ q.asIdeal := sup_le hpq hqI
  obtain ⟨qIdeal, hqIdeal_min, hqIdeal_le⟩ :=
    Ideal.exists_minimalPrimes_le (J := q.asIdeal) hpI_le_q
  have hqIdeal_prime : qIdeal.IsPrime := hqIdeal_min.isPrime
  let q0 : PrimeSpectrum S.A := ⟨qIdeal, hqIdeal_prime⟩
  have hq0_le_q : q0.asIdeal ≤ q.asIdeal := hqIdeal_le
  have hp_le_q0 : p.asIdeal ≤ q0.asIdeal := le_trans le_sup_left hqIdeal_min.le
  have hI_le_q0 : S.I ≤ q0.asIdeal := le_trans le_sup_right hqIdeal_min.le
  have hq0T : q0 ∈ S.T := by
    by_contra hq0_not_T
    exact h ⟨q0, hp_le_q0, hq0_le_q, (fun x hx => hI_le_q0 hx), hq0_not_T⟩
  have hminimal : ∀ r : PrimeSpectrum S.A, p.asIdeal ≤ r.asIdeal →
      r.asIdeal ≤ q0.asIdeal → r ∈ S.T → r = q0 := by
    intro r hpr hrq hrT
    have hrI : S.I ≤ r.asIdeal := S.subset_adicLocus hrT
    have hsup : p.asIdeal ⊔ S.I ≤ r.asIdeal := sup_le hpr hrI
    have hq0r : q0.asIdeal ≤ r.asIdeal := hqIdeal_min.2 ⟨inferInstance, hsup⟩ hrq
    exact PrimeSpectrum.ext (le_antisymm hrq hq0r)
  let Aq := Localization.AtPrime q0.asIdeal
  let Iq := S.I.map (algebraMap S.A Aq)
  let Mq := LocalizedModule q0.asIdeal.primeCompl S.M
  let A' := AdicCompletion Iq Aq
  let I' := Iq.map (algebraMap Aq A')
  have hIq_le_max : Iq ≤ maximalIdeal Aq := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q0.asIdeal Aq]
    exact Ideal.map_mono hI_le_q0
  have : Module.FaithfullyFlat Aq A' :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson Iq (by
      rwa [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have : Module.Flat Aq A' := AdicCompletion.flat_of_isNoetherian Iq
  have : Algebra.HasGoingDown Aq A' := Algebra.HasGoingDown.of_flat
  let m' := (maximalIdeal Aq).map (algebraMap Aq A')
  have hm'max : m'.IsMaximal :=
    AdicCompletion.isMaximal_map_of_le Iq (maximalIdeal Aq) hIq_le_max
      (Ideal.fg_of_isNoetherianRing Iq)
  have hm'under : m'.under Aq = maximalIdeal Aq := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal_of_isPrime (m'.under Aq)
    · exact (Ideal.map_le_iff_le_comap).mp le_rfl
  let pAq := p.asIdeal.map (algebraMap S.A Aq)
  have hpAq_prime : pAq.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime q0.asIdeal hp_le_q0
  have hm'over : m'.LiesOver (maximalIdeal Aq) := ⟨hm'under.symm⟩
  obtain ⟨P, hPle_m', hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := pAq) (q := maximalIdeal Aq)
      (Q := m') (IsLocalRing.le_maximalIdeal_of_isPrime pAq)
  have hpAqA'leP : pAq.map (algebraMap Aq A') ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hPover.over
  obtain ⟨p2, hp2min, hp2leP⟩ := Ideal.exists_minimalPrimes_le hpAqA'leP
  have hp2prime : p2.IsPrime := hp2min.isPrime
  have hpAqA'lep2 : pAq.map (algebraMap Aq A') ≤ p2 := hp2min.le
  have hp2over : p2.comap (algebraMap Aq A') = pAq := by
    apply le_antisymm
    · calc
        p2.comap (algebraMap Aq A') ≤ P.comap (algebraMap Aq A') := Ideal.comap_mono hp2leP
        _ = pAq := hPover.over.symm
    · exact (Ideal.map_le_iff_le_comap).mp hpAqA'lep2
  let M' := AdicCompletion Iq Mq
  have hdepth' := S.completedLocalDepth q0 hq0T
  have hdepthAtP2 :
      enatToEInt
        (Module.depth (Localization.AtPrime p2) (maximalIdeal (Localization.AtPrime p2))
          (LocalizedModule p2.primeCompl M')) > (S.s : EInt) := by
    have hcondition : {r' : Ideal A' | r'.IsPrime ∧ p2 ≤ r' ∧ I' ≤ r'} = {m'} := by
      apply Set.ext
      intro r'
      constructor
      · rintro ⟨hr'prime, hp2r', hIr'⟩
        have hpAq_r : pAq ≤ r'.comap (algebraMap Aq A') := by
          apply (Ideal.map_le_iff_le_comap).mp
          exact hpAqA'lep2.trans hp2r'
        have hIq_r : Iq ≤ r'.comap (algebraMap Aq A') := by
          rw [Ideal.map_le_iff_le_comap] at hIr'
          exact hIr'
        let rAq := r'.comap (algebraMap Aq A')
        have hrAq_prime : rAq.IsPrime := Ideal.comap_isPrime _ _
        have hrAq_le_max : rAq ≤ maximalIdeal Aq :=
          IsLocalRing.le_maximalIdeal_of_isPrime rAq
        have hp_le_rA : p.asIdeal ≤ rAq.under S.A := by
          rw [Ideal.map_le_iff_le_comap] at hpAq_r
          simpa [rAq, pAq, Ideal.under_map_of_isLocalizationAtPrime q0.asIdeal hp_le_q0]
            using hpAq_r
        have hrA_le_q0 : rAq.under S.A ≤ q0.asIdeal := by
          calc
            rAq.under S.A ≤ (maximalIdeal Aq).under S.A := Ideal.comap_mono hrAq_le_max
            _ = q0.asIdeal := IsLocalization.AtPrime.under_maximalIdeal Aq q0.asIdeal
        let rA : PrimeSpectrum S.A := ⟨rAq.under S.A, Ideal.IsPrime.under S.A rAq⟩
        change rA.asIdeal ≤ q0.asIdeal at hrA_le_q0
        have hrA_le_q : rA.asIdeal ≤ q.asIdeal := hrA_le_q0.trans hq0_le_q
        have hrI : S.I ≤ rA.asIdeal := by
          have hIq_under : Iq ≤ rAq := by simpa [rAq] using hIq_r
          have hIunder : S.I ≤ rAq.under S.A := by
            apply (Ideal.map_le_iff_le_comap).mp
            simpa [Iq] using hIq_under
          simpa [rA] using hIunder
        have hrAT : rA ∈ S.T := by
          by_contra hrAnotT
          exact h ⟨rA, hp_le_rA, hrA_le_q, hrI, hrAnotT⟩
        have hrAeq : rA = q0 := hminimal rA hp_le_rA hrA_le_q0 hrAT
        have hunder : rAq.under S.A = q0.asIdeal := by
          simpa [rA, Ideal.under_under] using congrArg PrimeSpectrum.asIdeal hrAeq
        have hmax_le_rAq : maximalIdeal Aq ≤ rAq := by
          rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q0.asIdeal Aq,
            Ideal.map_le_iff_le_comap]
          exact hunder.ge
        have hm'le_r' : m' ≤ r' := by
          show (maximalIdeal Aq).map (algebraMap Aq A') ≤ r'
          rw [Ideal.map_le_iff_le_comap]
          exact hmax_le_rAq
        exact Set.mem_singleton_iff.mpr (hm'max.eq_of_le hr'prime.ne_top hm'le_r').symm
      · intro hr'
        subst r'
        refine ⟨hm'max.isPrime, ?_, ?_⟩
        · exact le_trans hp2leP hPle_m'
        · exact Ideal.map_mono hIq_le_max
    have hnotI : ¬ I' ≤ p2 := by
      intro hI'
      have hIq : Iq ≤ pAq := by
        rw [Ideal.map_le_iff_le_comap, hp2over] at hI'
        exact hI'
      have hI : S.I ≤ p.asIdeal := by
        rw [Ideal.map_le_iff_le_comap] at hIq
        simpa [pAq, Ideal.under_map_of_isLocalizationAtPrime q0.asIdeal hp_le_q0] using hIq
      exact hp hI
    exact hdepth' ⟨p2, hp2prime⟩ hnotI hcondition
  let L := Localization.AtPrime p2
  let J := pAq.map (algebraMap Aq L)
  have hp2underA : p2.under S.A = p.asIdeal := by
    show (p2.comap (algebraMap Aq A')).comap (algebraMap S.A Aq) = p.asIdeal
    rw [hp2over]
    simpa [pAq] using (Ideal.under_map_of_isLocalizationAtPrime q0.asIdeal hp_le_q0)
  have : Ideal.LiesOver p2 p.asIdeal := ⟨hp2underA.symm⟩
  let R := Localization.AtPrime p.asIdeal
  let N := LocalizedModule p.asIdeal.primeCompl S.M
  have : Ideal.LiesOver p2 pAq := ⟨hp2over.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal p2
  have : IsScalarTower S.A Aq L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply S.A A' L,
      IsScalarTower.algebraMap_apply Aq A' L,
      IsScalarTower.algebraMap_apply S.A Aq A']
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing p.asIdeal.primeCompl R ‹_›
  have : IsNoetherianRing A' := inferInstance
  have : IsNoetherianRing L := IsLocalization.isNoetherianRing p2.primeCompl L ‹_›
  have : Module.Flat S.A Aq := inferInstance
  have : Module.Flat S.A A' := Module.Flat.trans S.A Aq A'
  have : Module.Flat A' L := inferInstance
  have : Module.Flat S.A L := Module.Flat.trans S.A A' L
  have : Module.Flat R L :=
    (Module.flat_iff_of_isLocalization R p.asIdeal.primeCompl L).mpr inferInstance
  let fAq := LocalizedModule.mkLinearMap q0.asIdeal.primeCompl S.M
  have hAq : IsBaseChange Aq fAq :=
    IsLocalizedModule.isBaseChange q0.asIdeal.primeCompl Aq fAq
  let fcomp := AdicCompletion.of Iq Mq
  have hcompletion : IsBaseChange A' fcomp := by
    let : Small.{u} Mq := Module.Finite.small Aq Mq
    let M₀ := Shrink.{u} Mq
    let eM : M₀ ≃ₗ[Aq] Mq := Shrink.linearEquiv Aq Mq
    have hsmall : IsBaseChange A' (AdicCompletion.of Iq M₀) :=
      IsBaseChange.of_equiv (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian Iq M₀)
        (by intro x
            show (AdicCompletion.ofTensorProduct Iq M₀) (1 ⊗ₜ[Aq] x) = _
            rw [AdicCompletion.ofTensorProduct_tmul, one_smul])
    exact (IsBaseChange.iff_of_equiv_comm eM (AdicCompletion.congr Iq eM)
      (by
        apply LinearMap.ext
        intro x
        show (AdicCompletion.of Iq Mq) (eM x) =
          (AdicCompletion.congr Iq eM) ((AdicCompletion.of Iq M₀) x)
        exact (AdicCompletion.map_of Iq eM.toLinearMap x).symm)).mp hsmall
  let : IsScalarTower Aq A' M' := IsScalarTower.of_algebraMap_smul (fun a x => rfl)
  let floc := LocalizedModule.mkLinearMap p2.primeCompl M'
  let : IsScalarTower Aq A' (LocalizedModule p2.primeCompl M') := inferInstance
  let : Module S.A (LocalizedModule p2.primeCompl M') :=
    Module.compHom _ (algebraMap S.A Aq)
  let : IsScalarTower S.A Aq (LocalizedModule p2.primeCompl M') :=
    IsScalarTower.of_algebraMap_smul (R := S.A) (A := Aq)
      (M := LocalizedModule p2.primeCompl M') (fun a x => by
        show (algebraMap S.A Aq a) • x = a • x
        rfl)
  let : IsScalarTower Aq L (LocalizedModule p2.primeCompl M') :=
    isScalarTower_of_tower_of_tower (S := A')
  let : IsScalarTower S.A L (LocalizedModule p2.primeCompl M') :=
    isScalarTower_of_tower_of_tower (S := Aq)
  have hloc : IsBaseChange L floc := IsLocalizedModule.isBaseChange p2.primeCompl L floc
  have hA : IsBaseChange L
      (((floc.restrictScalars Aq).comp fcomp).restrictScalars S.A |>.comp fAq) :=
    hAq.comp (hcompletion.comp hloc)
  have hR : IsBaseChange R (LocalizedModule.mkLinearMap p.asIdeal.primeCompl S.M) :=
    IsLocalizedModule.isBaseChange p.asIdeal.primeCompl R _
  let e : L ⊗[R] N ≃ₗ[L] LocalizedModule p2.primeCompl M' :=
    (hR.equiv.symm.baseChange R L) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange S.A R L L S.M ≪≫ₗ hA.equiv
  have hFormula := Module.depth_tensorProduct_of_flat (R := R) (S := L) (M := N) (N := L)
  have hDepth :
      Module.depth L (maximalIdeal L) (LocalizedModule p2.primeCompl M') =
        Module.depth R (maximalIdeal R) N + Module.depth L (maximalIdeal L) (L ⧸ J) := by
    have h' : Module.depth L (maximalIdeal L) (LocalizedModule p2.primeCompl M') =
        Module.depth R (maximalIdeal R) N +
          Module.depth L (maximalIdeal L)
            (L ⧸ ((maximalIdeal R).map (algebraMap R L) • (⊤ : Submodule L L))) := by
      rw [← Module.depth_eq_depth_of_linearEquiv (maximalIdeal L) e]
      exact hFormula
    have hmap : (maximalIdeal R).map (algebraMap R L) = J := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal R]
      exact (map_map_algebraMap (S := R) p.asIdeal).trans
        (map_map_algebraMap (S := Aq) p.asIdeal).symm
    have hquot : J • (⊤ : Submodule L L) = (J : Submodule L L) :=
      (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
    rw [hmap, hquot] at h'
    exact h'
  have hJmap : J = (pAq.map (algebraMap Aq A')).map (algebraMap A' L) :=
    (map_map_algebraMap (S := A') pAq).symm
  have hFiberArt : IsArtinianRing (L ⧸ J) := by
    have hmaxmin : maximalIdeal L ∈ J.minimalPrimes := by
      rw [hJmap, IsLocalization.minimalPrimes_map p2.primeCompl L]
      simpa [IsLocalization.AtPrime.under_maximalIdeal L p2] using hp2min
    exact IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J hmaxmin
  have hJle : J ≤ maximalIdeal L := by
    rw [hJmap]
    calc
      (pAq.map (algebraMap Aq A')).map (algebraMap A' L) ≤ p2.map (algebraMap A' L) :=
        Ideal.map_mono hpAqA'lep2
      _ = maximalIdeal L := IsLocalization.AtPrime.map_eq_maximalIdeal p2 L
  have hFiberZero : Module.depth L (maximalIdeal L) (L ⧸ J) = 0 :=
    depth_quotient_eq_zero_of_isArtinianRing J hJle hFiberArt
  rw [hDepth, hFiberZero, add_zero] at hdepthAtP2
  exact hdepthAtP2

end Stacks.Algebraization

end

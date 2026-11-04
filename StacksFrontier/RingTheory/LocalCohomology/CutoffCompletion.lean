module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Small
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCutoff
public import StacksFrontier.RingTheory.Depth.AlgebraMap
import StacksFrontier.RingTheory.Catenary.FormalFibresAssociatedDimension
import StacksFrontier.RingTheory.Sequence.RegularLocus

/-!
# Pairwise cutoff values and completion

For a finite module over a universally catenary Noetherian local ring, this
file compares the terms defining the local-cohomology cutoff before and after
completion. The correction terms are the dimension and depth of the relevant
local formal fibres.

## Main results

* `Stacks.LocalCohomology.pairwiseCutoffValue_eq_under_completion` computes a cutoff
  term over the completion from the corresponding term over the original
  local ring.

## Implementation notes

The prime ideals downstairs are taken to be the canonical contractions of the
two primes in the completion. The local formal fibre at a prime `P` of the
completion is represented as `Ahat_P / p Ahat_P`, where `p` is the contraction
of `P`. Its dimension is expressed as the height of the maximal ideal, so all
terms of the identity naturally take values in `ℕ∞`.

## References

* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
-/

public section

namespace Stacks.LocalCohomology

open scoped TensorProduct

/-- A linear equivalence of modules localizes to a linear equivalence of localizations. -/
public noncomputable def localizedEquiv {R N N' : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (S : Submonoid R) (e : N ≃ₗ[R] N') :
    LocalizedModule S N ≃ₗ[Localization S] LocalizedModule S N' :=
  LinearEquiv.ofBijective (LocalizedModule.map S e.toLinearMap)
    ⟨LocalizedModule.map_injective S e.toLinearMap e.injective,
      LocalizedModule.map_surjective S e.toLinearMap e.surjective⟩

private noncomputable def lTensorLinearEquiv
    {R A M N Q : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    (e : N ≃ₗ[R] Q) : M ⊗[R] N ≃ₗ[A] M ⊗[R] Q :=
  LinearEquiv.ofLinearMap
    (TensorProduct.AlgebraTensorModule.lTensor A M e)
    (TensorProduct.AlgebraTensorModule.lTensor A M e.symm)
    (by ext; simp [LinearMap.comp_apply]) (by ext; simp [LinearMap.comp_apply])

private noncomputable def localizedBaseChangeEquiv
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] (P : Ideal B) [P.IsPrime] :
    let p := P.comap (algebraMap A B)
    let Ap := Localization.AtPrime p
    let BP := Localization.AtPrime P
    letI : Algebra Ap BP := Localization.AtPrime.algebraOfLiesOver p P
    BP ⊗[Ap] LocalizedModule p.primeCompl M ≃ₗ[BP]
      LocalizedModule P.primeCompl (B ⊗[A] M) := by
  dsimp only
  letI : P.LiesOver (P.comap (algebraMap A B)) := ⟨rfl⟩
  letI : Algebra (Localization.AtPrime (P.comap (algebraMap A B)))
      (Localization.AtPrime P) := Localization.AtPrime.algebraOfLiesOver _ _
  let hbase := IsLocalizedModule.isBaseChange (P.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime (P.comap (algebraMap A B)))
    (LocalizedModule.mkLinearMap (P.comap (algebraMap A B)).primeCompl M :
      M →ₗ[A] LocalizedModule (P.comap (algebraMap A B)).primeCompl M)
  exact lTensorLinearEquiv (hbase.equiv.symm) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange A
      (Localization.AtPrime (P.comap (algebraMap A B))) (Localization.AtPrime P)
      (Localization.AtPrime P) M ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (Localization.AtPrime P)
      (Localization.AtPrime P) M).symm ≪≫ₗ
    (LocalizedModule.equivTensorProduct P.primeCompl (B ⊗[A] M)).symm

private theorem catenarySaturated_of_ringCatenary
    {R : Type*} [CommRing R] (hcat : Ring.IsCatenary R) :
    IsCatenaryRingSaturated R := by
  intro p q hpq
  obtain ⟨⟨N, hN⟩, ⟨n, hn⟩⟩ := hcat p q hpq
  refine ⟨⟨N, hN⟩, ?_⟩
  intro s t hsp hsq htp htq
  have hsat (u : CovChain R) :
      ∀ i : Fin (covToLT u).length,
        (covToLT u) i.castSucc ⋖ (covToLT u) i.succ := fun i => u.step i
  have hs := hn (covToLT s) hsp hsq (hsat s)
  have ht := hn (covToLT t) htp htq (hsat t)
  exact hs.trans ht.symm

private alias add_right_cancel_of_ne_bot_of_ne_top :=
  Stacks.RegularSequence.FibrewiseLocus.add_right_cancel_of_ne_bot_of_ne_top

private lemma enat_add_add_sub_eq_of_add_eq (a b c d x y : ℕ∞) (ha : a ≠ ⊤)
    (h : a + b = c + d) : x + y + b = (x + c + d + y) - a := by
  have hsums : x + c + d + y = a + (x + y + b) := by
    calc
      x + c + d + y = (c + d) + (x + y) := by ac_rfl
      _ = (a + b) + (x + y) := by rw [← h]
      _ = a + (x + y + b) := by ac_rfl
  calc
    x + y + b = a + (x + y + b) - a :=
      ((ENat.addLECancellable_of_ne_top ha).add_tsub_cancel_left).symm
    _ = (x + c + d + y) - a := by rw [hsums]

private theorem ringKrullDim_eq_height_add_quotient_of_univCat_equidim
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (huc : Ring.IsUniversallyCatenary R)
    (hequi : TopologicalSpace.Equidimensional (PrimeSpectrum R))
    (P : Ideal R) [P.IsPrime] :
    ringKrullDim R = (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) := by
  classical
  obtain ⟨r, hr, hrP⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := P) bot_le
  let rSpec : PrimeSpectrum R := ⟨r, hr.1.1⟩
  have hcat : Ring.IsCatenary R := huc R
  have hsat := catenarySaturated_of_ringCatenary hcat
  have hcov := coheight_covby_of_catenary hsat
  have hequi' : SpecEquidimensional R :=
    (specEquidimensional_iff_equidimensional).mpr hequi
  have hsumP := FlatLocalCatenary.height_add_coheight_eq hcov hequi' ⟨P, inferInstance⟩ rSpec hr
  have hsumMax := FlatLocalCatenary.height_add_coheight_eq hcov hequi' ⊤ rSpec hr
  have hmaxHeight : (IsLocalRing.maximalIdeal R).height = Order.coheight rSpec := by
    have h : (((⊤ : PrimeSpectrum R).asIdeal).height) = Order.coheight rSpec := by
      simpa only [Order.coheight_top, add_zero, PrimeSpectrum.height_eq_orderHeight] using hsumMax
    simpa using h
  have hdimMax : ringKrullDim R = (Order.coheight rSpec : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hmaxHeight
  have hsumP' : P.height + Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum R)
      = Order.coheight rSpec := by
    simpa only [← PrimeSpectrum.height_eq_orderHeight] using hsumP
  calc
    ringKrullDim R = (Order.coheight rSpec : WithBot ℕ∞) := hdimMax
    _ = ((P.height : ℕ∞) + Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
      exact_mod_cast hsumP'.symm
    _ = (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) := by
      rw [coheight_eq_ringKrullDim_quotient]

/-- The maximal ideal of a localization at a prime `p` extends, in the localization at a prime
`P` over `p`, to the extension of `p`. -/
private theorem map_maximalIdeal_localization_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime P)] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) =
      p.map (algebraMap A (Localization.AtPrime P)) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p), Ideal.map_map]
  exact congrArg (fun f : A →+* Localization.AtPrime P => p.map f)
    (IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime P)).symm

/-- For a prime `P'` of the completion of a universally catenary Noetherian local ring `A`, the
dimension of the quotient of `A` by the contraction of `P'` is the height of the maximal ideal of
the local formal fibre at `P'` plus the dimension of the quotient by `P'`. -/
private theorem ringKrullDim_quotient_comap_eq_fibre_height_add
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Ring.IsUniversallyCatenary A)
    (P' : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) [P'.IsPrime] :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let p := P'.comap (algebraMap A Ahat)
    let mp := (IsLocalRing.maximalIdeal (Localization.AtPrime P')).map
      (Ideal.Quotient.mk (p.map (algebraMap A (Localization.AtPrime P'))))
    ringKrullDim (A ⧸ p) = (mp.height : WithBot ℕ∞) + ringKrullDim (Ahat ⧸ P') := by
  intro Ahat p mp
  have hpPrime : p.IsPrime := Ideal.IsPrime.comap _
  let : p.IsPrime := hpPrime
  let Ap := Localization.AtPrime p
  let Ap' := Localization.AtPrime P'
  let : P'.LiesOver p := ⟨rfl⟩
  let : Algebra Ap Ap' := Localization.AtPrime.algebraOfLiesOver p P'
  have hpmap := map_maximalIdeal_localization_eq (A := A) (B := Ahat) p P'
  have hheight : P'.height = p.height + mp.height := by
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (IsLocalRing.maximalIdeal Ap) (IsLocalRing.maximalIdeal Ap')
    rw [← IsLocalization.height_under p.primeCompl (IsLocalRing.maximalIdeal Ap),
      ← IsLocalization.height_under P'.primeCompl (IsLocalRing.maximalIdeal Ap'),
      IsLocalization.AtPrime.under_maximalIdeal Ap p,
      IsLocalization.AtPrime.under_maximalIdeal Ap' P'] at h
    rwa [hpmap] at h
  have hAhat : Ring.IsUniversallyCatenary Ahat :=
    isUniversallyCatenary_of_isPrecomplete_maximalIdeal Ahat
  have hUCp : Ring.IsUniversallyCatenary (A ⧸ p) :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hA
  let : IsLocalRing (A ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hDomainP : IsDomain (A ⧸ p) := (Ideal.Quotient.isDomain_iff_prime (I := p)).mpr hpPrime
  have hFormalP : IsFormallyCatenary (A ⧸ p) :=
    (isUniversallyCatenary_iff_isFormallyCatenary (A ⧸ p)).mp hUCp
  have hbotP : (⊥ : Ideal (A ⧸ p)) ∈ minimalPrimes (A ⧸ p) :=
    ⟨⟨inferInstance, le_rfl⟩, fun _ _ _ => bot_le⟩
  let Cp := AdicCompletion (IsLocalRing.maximalIdeal (A ⧸ p)) (A ⧸ p)
  have hFormalBotP := hFormalP (⊥ : Ideal (A ⧸ p)) hbotP
  have hFormalBotP' : TopologicalSpace.Equidimensional
      (PrimeSpectrum (Cp ⧸ (⊥ : Ideal Cp))) := by
    change TopologicalSpace.Equidimensional
      (PrimeSpectrum (Cp ⧸ ((⊥ : Ideal (A ⧸ p)).map
        (algebraMap (A ⧸ p) Cp)))) at hFormalBotP
    rwa [Ideal.map_bot] at hFormalBotP
  have hcompEquiP : TopologicalSpace.Equidimensional (PrimeSpectrum Cp) :=
    TopologicalSpace.Equidimensional.of_homeomorph
      (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.quotientBot Cp).symm) hFormalBotP'
  obtain ⟨ep⟩ := nonempty_ringEquiv_quotient_adicCompletion A p
  let Bp := Ahat ⧸ p.map (algebraMap A Ahat)
  have hBpEqui : TopologicalSpace.Equidimensional (PrimeSpectrum Bp) :=
    TopologicalSpace.Equidimensional.of_homeomorph
      (PrimeSpectrum.homeomorphOfRingEquiv ep) hcompEquiP
  have hJp : p.map (algebraMap A Ahat) ≤ P' := by
    rw [Ideal.map_le_iff_le_comap]
  have hJpTop : p.map (algebraMap A Ahat) ≠ ⊤ :=
    ne_top_of_le_ne_top (inferInstance : P'.IsPrime).ne_top hJp
  let : Nontrivial Bp := Ideal.Quotient.nontrivial_iff.mpr hJpTop
  let : IsLocalRing Bp :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (p.map (algebraMap A Ahat)))
      Ideal.Quotient.mk_surjective
  let Pbar : Ideal Bp := P'.map (Ideal.Quotient.mk (p.map (algebraMap A Ahat)))
  have hPbarPrime : Pbar.IsPrime := by
    change (P'.map (Ideal.Quotient.mk (p.map (algebraMap A Ahat)))).IsPrime
    exact Ideal.isPrime_map_quotientMk_of_isPrime hJp
  have hUC_Bp : Ring.IsUniversallyCatenary Bp :=
    Ring.IsUniversallyCatenary.of_surjective (f := Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective hAhat
  have hdimBp := ringKrullDim_eq_height_add_quotient_of_univCat_equidim hUC_Bp hBpEqui Pbar
  have hPbarHeight : Pbar.height = mp.height := by
    let : Algebra.HasGoingDown A Ahat := Algebra.HasGoingDown.of_flat
    have h00ON : P'.height = p.height + Pbar.height := by
      simpa [Pbar] using
        (Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := A) p P')
    exact WithTop.add_left_cancel (Ideal.height_ne_top_of_isPrime (I := p))
      (h00ON.symm.trans hheight)
  have hquotBp : ringKrullDim (Bp ⧸ Pbar) = ringKrullDim (Ahat ⧸ P') :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)
  calc
    ringKrullDim (A ⧸ p) = ringKrullDim Cp := _root_.ringKrullDim_adicCompletion_maximalIdeal
    _ = ringKrullDim Bp := (ringKrullDim_eq_of_ringEquiv ep).symm
    _ = _ := by rwa [hPbarHeight, hquotBp] at hdimBp

/-- The cutoff summand belonging to a pair of primes is compatible with
completion, up to the dimensions and depth of the two local formal fibres. -/
public theorem pairwiseCutoffValue_eq_under_completion
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Ring.IsUniversallyCatenary A)
    (I : Ideal A) (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p' q' : PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (_hp' : ¬ I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ≤
      p'.asIdeal)
    (_hq' : I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ≤
      q'.asIdeal)
    (hpq' : p'.asIdeal ≤ q'.asIdeal) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let p := PrimeSpectrum.comap (algebraMap A Ahat) p'
    let q := PrimeSpectrum.comap (algebraMap A Ahat) q'
    let Ap' := Localization.AtPrime p'.asIdeal
    let Aq' := Localization.AtPrime q'.asIdeal
    let Fp := Ap' ⧸ p.asIdeal.map (algebraMap A Ap')
    let mp := (IsLocalRing.maximalIdeal Ap').map
      (Ideal.Quotient.mk (p.asIdeal.map (algebraMap A Ap')))
    let mq := (IsLocalRing.maximalIdeal Aq').map
      (Ideal.Quotient.mk (q.asIdeal.map (algebraMap A Aq')))
    Module.depth (Localization.AtPrime p'.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p'.asIdeal))
          (LocalizedModule p'.asIdeal.primeCompl (Ahat ⊗[A] M)) +
        (q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)).height =
      Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height +
        mq.height + Module.depth Fp mp Fp - mp.height := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let p : Ideal A := p'.asIdeal.comap (algebraMap A Ahat)
  let q : Ideal A := q'.asIdeal.comap (algebraMap A Ahat)
  let Ap := Localization.AtPrime p
  let Ap' := Localization.AtPrime p'.asIdeal
  let Fp := Ap' ⧸ p.map (algebraMap A Ap')
  let mp := (IsLocalRing.maximalIdeal Ap').map
    (Ideal.Quotient.mk (p.map (algebraMap A Ap')))
  let mq := (IsLocalRing.maximalIdeal (Localization.AtPrime q'.asIdeal)).map
    (Ideal.Quotient.mk (q.map (algebraMap A (Localization.AtPrime q'.asIdeal))))
  let : p'.asIdeal.LiesOver p := ⟨rfl⟩
  let : Algebra Ap Ap' := Localization.AtPrime.algebraOfLiesOver p p'.asIdeal
  have hpmap := map_maximalIdeal_localization_eq (A := A) (B := Ahat) p p'.asIdeal
  have hdepth : Module.depth Ap' (IsLocalRing.maximalIdeal Ap')
        (LocalizedModule p'.asIdeal.primeCompl (Ahat ⊗[A] M)) =
      Module.depth Ap (IsLocalRing.maximalIdeal Ap)
        (LocalizedModule p.primeCompl M) + Module.depth Fp mp Fp := by
    rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal Ap')
      (localizedBaseChangeEquiv (A := A) (B := Ahat) (M := M) p'.asIdeal).symm,
      Module.depth_tensorProduct_of_flat]
    rw [Stacks.Depth.FlatLocalFibreRing.depth_quotient_smul_top]
    rw [hpmap]
    rw [Module.depth_eq_depth_map_algebraMap (A := Ap') (B := Fp)
      Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal Ap') Fp]
    rfl
  have hAhat : Ring.IsUniversallyCatenary Ahat :=
    isUniversallyCatenary_of_isPrecomplete_maximalIdeal Ahat
  have hUCp : Ring.IsUniversallyCatenary (A ⧸ p) :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hA
  have hpPrime : p.IsPrime := Ideal.IsPrime.comap _
  have hqPrime : q.IsPrime := Ideal.IsPrime.comap _
  have hpq : p ≤ q := Ideal.comap_mono hpq'
  let : p.IsPrime := hpPrime
  let : q.IsPrime := hqPrime
  let : IsLocalRing (A ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hDomainP' : IsDomain (Ahat ⧸ p'.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime (I := p'.asIdeal)).mpr inferInstance
  have hUCp' : Ring.IsUniversallyCatenary (Ahat ⧸ p'.asIdeal) :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hAhat
  let : IsLocalRing (Ahat ⧸ p'.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p'.asIdeal) Ideal.Quotient.mk_surjective
  let : IsLocalRing (Ahat ⧸ q'.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q'.asIdeal) Ideal.Quotient.mk_surjective
  let : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq
  let : (q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq'
  have hdimDownP := ringKrullDim_eq_height_add_quotient_of_univCat_equidim hUCp
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace (PrimeSpectrum (A ⧸ p)))
    (q.map (Ideal.Quotient.mk p))
  have hdimUpP := ringKrullDim_eq_height_add_quotient_of_univCat_equidim hUCp'
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace (PrimeSpectrum (Ahat ⧸ p'.asIdeal)))
    (q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)] at hdimDownP
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq')] at hdimUpP
  have hFiberP := ringKrullDim_quotient_comap_eq_fibre_height_add hA p'.asIdeal
  have hFiberQ := ringKrullDim_quotient_comap_eq_fibre_height_add hA q'.asIdeal
  have hsum :
      (mp.height : WithBot ℕ∞) +
          ((q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)).height : WithBot ℕ∞) +
          ringKrullDim (Ahat ⧸ q'.asIdeal) =
        ((q.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) +
          (mq.height : WithBot ℕ∞) + ringKrullDim (Ahat ⧸ q'.asIdeal) := by
    rw [add_assoc, ← hdimUpP, ← hFiberP, hdimDownP, hFiberQ, add_assoc]
  have hcancelTop : mp.height +
      (q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)).height =
    (q.map (Ideal.Quotient.mk p)).height + mq.height :=
    WithBot.coe_inj.mp (add_right_cancel_of_ne_bot_of_ne_top ringKrullDim_ne_bot
      (ringKrullDim_lt_top.ne) hsum)
  have hcancelArithmetic :=
    enat_add_add_sub_eq_of_add_eq mp.height
      (q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)).height
      (q.map (Ideal.Quotient.mk p)).height mq.height
      (Module.depth Ap (IsLocalRing.maximalIdeal Ap) (LocalizedModule p.primeCompl M))
      (Module.depth Fp mp Fp) (Ideal.height_ne_top_of_isPrime (I := mp)) hcancelTop
  rwa [hdepth]

end Stacks.LocalCohomology

end

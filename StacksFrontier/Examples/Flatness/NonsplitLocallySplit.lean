module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.Tactic.FieldSimp
public import StacksCore.Algebra.Category.ModuleCat.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# A nonsplit short exact sequence of modules that splits Zariski locally

There is a short exact sequence of `ℤ`-modules which does not split, although over a principal
open neighbourhood of every point of `Spec ℤ` it does.

The sequence is `0 → K → ⨁_p ℤ_(p) → ℚ → 0`, the sum running over all prime numbers, the map to
`ℚ` being the sum of the inclusions of the localizations, and `K` its kernel. It cannot split:
a section `ℚ → ⨁_p ℤ_(p)` has image in a finite partial sum, and a rational number whose
denominator involves a prime outside that finite set cannot be hit. After inverting one prime
`q`, however, the summand `ℤ_(q)` becomes all of `ℚ` — localizing at `q` and then inverting `q`
gives the fraction field — so the `q`-th component of the surjection is an isomorphism and
provides a section. Every point of `Spec ℤ` misses `2` or misses `3`, so each has a principal
open neighbourhood over which the sequence splits.

## Main results

* `Stacks.Examples.exists_nonsplit_shortExact_locally_split`: a short exact sequence of
  `ℤ`-modules that is not split but splits on a principal open neighbourhood of every point.

## References

* [Stacks Project, Tag 0H7G](https://stacks.math.columbia.edu/tag/0H7G)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Examples

open scoped DirectSum

private noncomputable instance : DecidableEq Nat.Primes := Classical.decEq _

private abbrev primeIdeal (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p : ℤ)}

private theorem primeIdeal_isPrime (p : Nat.Primes) : (primeIdeal p).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.property.ne_zero)).2 <|
    Int.prime_iff_natAbs_prime.mpr (by simpa using p.property)

private instance (p : Nat.Primes) : (primeIdeal p).IsPrime := primeIdeal_isPrime p

private abbrev primeLocalization (p : Nat.Primes) := Localization.AtPrime (primeIdeal p)

private theorem int_factor_by_prime (P : Nat.Primes) {x : ℤ} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ y : ℤ, y ∉ primeIdeal P ∧ x = (P : ℤ) ^ n * y := by
  obtain ⟨n, hn⟩ : ∃ n, x.natAbs = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hdiv : (P : ℤ) ∣ x
    · obtain ⟨y, rfl⟩ := hdiv
      have hy : y ≠ 0 := right_ne_zero_of_mul hx
      have hlt : y.natAbs < n := by
        rw [← hn, Int.natAbs_mul, Int.natAbs_natCast]
        exact lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hy) P.property.one_lt
      obtain ⟨k, z, hz, rfl⟩ := ih _ hlt hy rfl
      exact ⟨k + 1, z, hz, by ring⟩
    · exact ⟨0, x, fun hmem ↦ hdiv (Ideal.mem_span_singleton.mp hmem), by simp⟩

private noncomputable def locToQ (p : Nat.Primes) : primeLocalization p →+* FractionRing ℤ :=
  IsLocalization.map (R := ℤ) (M := (primeIdeal p).primeCompl) (S := primeLocalization p)
    (T := nonZeroDivisors ℤ) (FractionRing ℤ) (RingHom.id ℤ)
    (Ideal.primeCompl_le_nonZeroDivisors (primeIdeal p))

private theorem locToQ_injective (p : Nat.Primes) : Function.Injective (locToQ p) :=
  IsLocalization.map_injective_of_injective' ((primeIdeal p).primeCompl) ℤ
    (f := RingHom.id ℤ) (Rₘ := primeLocalization p) (FractionRing ℤ) (N := nonZeroDivisors ℤ)
    (Ideal.primeCompl_le_nonZeroDivisors (primeIdeal p))
    (zero_notMem_nonZeroDivisors (M₀ := ℤ)) (fun _ _ h ↦ h)

private theorem locToQ_mk' (P : Nat.Primes) (a : ℤ) (d : (primeIdeal P).primeCompl) :
    locToQ P (IsLocalization.mk' (primeLocalization P) a d) =
      algebraMap ℤ (FractionRing ℤ) a / algebraMap ℤ (FractionRing ℤ) d := by
  rw [locToQ, IsLocalization.map_mk' (Ideal.primeCompl_le_nonZeroDivisors _),
    IsFractionRing.mk'_eq_div]
  rfl

private theorem algebraMap_prime_ne_zero (P : Nat.Primes) :
    algebraMap ℤ (FractionRing ℤ) (P : ℤ) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective ℤ _)).2 (Int.natCast_ne_zero.2 P.property.ne_zero)

private noncomputable def locLin (p : Nat.Primes) : primeLocalization p →ₗ[ℤ] FractionRing ℤ :=
  (locToQ p).toAddMonoidHom.toIntLinearMap

private theorem fractionRing_powers_map_units (P : Nat.Primes)
    (s : Submonoid.powers (P : ℤ)) :
    IsUnit (algebraMap ℤ (Module.End ℤ (FractionRing ℤ)) s) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have hs : ((s : ℤ) : FractionRing ℤ) ≠ 0 := by
    rw [← hn, ← eq_intCast (algebraMap ℤ (FractionRing ℤ))]
    simpa using pow_ne_zero n (algebraMap_prime_ne_zero P)
  rw [Module.End.isUnit_iff]
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨((s : ℤ) : FractionRing ℤ)⁻¹ * y, ?_⟩⟩
  · simp only [Module.algebraMap_end_apply, zsmul_eq_mul] at hxy
    exact mul_left_cancel₀ hs hxy
  · simp [hs]

private theorem locLin_isLocalized (P : Nat.Primes) :
    IsLocalizedModule (Submonoid.powers (P : ℤ)) (locLin P) := by
  refine ⟨fractionRing_powers_map_units P, fun z ↦ ?_,
    fun hxy ↦ ⟨1, by simpa using locToQ_injective P hxy⟩⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective ℤ z
  obtain ⟨n, c, hc, hbc⟩ := int_factor_by_prime P (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  let d : (primeIdeal P).primeCompl := ⟨c, hc⟩
  refine ⟨⟨IsLocalization.mk' (primeLocalization P) a d,
    ⟨(P : ℤ) ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩⟩, ?_⟩
  change ((P : ℤ) ^ n : ℤ) •
      (algebraMap ℤ (FractionRing ℤ) a / algebraMap ℤ (FractionRing ℤ) b) =
    locToQ P (IsLocalization.mk' (primeLocalization P) a d)
  rw [zsmul_eq_mul, ← eq_intCast (algebraMap ℤ (FractionRing ℤ)), locToQ_mk', hbc]
  simp only [map_mul, map_pow]
  rw [← mul_div_assoc, mul_div_mul_left _ _ (pow_ne_zero n (algebraMap_prime_ne_zero P))]

private theorem fractionRing_id_isLocalized (P : Nat.Primes) :
    IsLocalizedModule (Submonoid.powers (P : ℤ))
      (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) :=
  ⟨fractionRing_powers_map_units P, fun z ↦ ⟨(z, 1), by simp⟩, fun h ↦ ⟨1, by simpa using h⟩⟩

private theorem ulift_isLocalized.{u} {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (S : Submonoid ℤ) (f : M →ₗ[ℤ] N)
    [IsLocalizedModule S f] :
    IsLocalizedModule S
      (((ModuleCat.uliftFunctor.{u} ℤ).map (ModuleCat.ofHom f)).hom) := by
  let : Module ℤ (ULift.{u} M) := ULift.module'
  let : Module ℤ (ULift.{u} N) := ULift.module'
  let eN : N ≃ₗ[ℤ] ULift.{u} N := ULift.moduleEquiv.{0, 0, u}.symm
  let eM : ULift.{u} M ≃ₗ[ℤ] M := ULift.moduleEquiv.{0, 0, u}
  have : IsLocalizedModule S (eN.toLinearMap.comp f) := IsLocalizedModule.of_linearEquiv S f eN
  change IsLocalizedModule S (eN.toLinearMap.comp (f.comp eM.toLinearMap))
  exact IsLocalizedModule.of_linearEquiv_right S (eN.toLinearMap.comp f) eM

private theorem liftedFractionRingMk_bijective.{u} (P : Nat.Primes) :
    Function.Bijective
      (ModuleCat.localizedModuleMkLinearMap
        ((ModuleCat.uliftFunctor.{u, 0, 0} ℤ).obj (ModuleCat.of ℤ (FractionRing ℤ)))
        (Submonoid.powers (P : ℤ))) := by
  let S := Submonoid.powers (P : ℤ)
  let U : ModuleCat.{0} ℤ ⥤ ModuleCat.{u} ℤ := ModuleCat.uliftFunctor.{u, 0, 0} ℤ
  let Q := U.obj (ModuleCat.of ℤ (FractionRing ℤ))
  let : Module ℤ (Q.localizedModule S) :=
    ModuleCat.instModuleCarrierLocalizationLocalizedModule Q S
  have : IsLocalizedModule S (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ) :=
    fractionRing_id_isLocalized P
  let f := (U.map
    (ModuleCat.ofHom (LinearMap.id : FractionRing ℤ →ₗ[ℤ] FractionRing ℤ))).hom
  let g := ModuleCat.localizedModuleMkLinearMap Q S
  have : IsLocalizedModule S f := ulift_isLocalized S _
  have : IsLocalizedModule S g := ModuleCat.localizedModule_isLocalizedModule Q S
  let e := IsLocalizedModule.linearEquiv S f g
  have he : e.toLinearMap = g := by
    ext x
    simpa [e, f, g] using IsLocalizedModule.linearEquiv_apply S f g x
  change Function.Bijective g
  rw [← he]
  exact e.bijective

private theorem localizedSelectedSummand_isIso.{u} (P : Nat.Primes) :
    IsIso ((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers (P : ℤ))).map
      ((ModuleCat.uliftFunctor.{u} ℤ).map (ModuleCat.ofHom (locLin P)))) := by
  let S := Submonoid.powers (P : ℤ)
  let U : ModuleCat.{0} ℤ ⥤ ModuleCat.{u} ℤ := ModuleCat.uliftFunctor.{u, 0, 0} ℤ
  let L : ModuleCat.{u} ℤ := U.obj (ModuleCat.of ℤ (primeLocalization P))
  let Q : ModuleCat.{u} ℤ := U.obj (ModuleCat.of ℤ (FractionRing ℤ))
  let : Module ℤ (L.localizedModule S) :=
    ModuleCat.instModuleCarrierLocalizationLocalizedModule L S
  let : Module ℤ (Q.localizedModule S) :=
    ModuleCat.instModuleCarrierLocalizationLocalizedModule Q S
  let f := ModuleCat.localizedModuleMkLinearMap L S
  let g := ModuleCat.localizedModuleMkLinearMap Q S
  have : IsLocalizedModule S (locLin P) := locLin_isLocalized P
  let liftLocLin := U.map (ModuleCat.ofHom (locLin P))
  let hcat := ModuleCat.localizedModuleMap.{u, 0} S liftLocLin
  have : IsLocalizedModule S f := ModuleCat.localizedModule_isLocalizedModule L S
  have : IsLocalizedModule S g := ModuleCat.localizedModule_isLocalizedModule Q S
  let eL := ModuleCat.restrictScalarsAlgebraMapEquiv (R := ℤ) (L.localizedModule S)
  let eQ := ModuleCat.restrictScalarsAlgebraMapEquiv (R := ℤ) (Q.localizedModule S)
  let f' := eL.symm.toLinearMap.comp f
  let h := ((ModuleCat.restrictScalars (algebraMap ℤ (Localization S))).map hcat).hom
  let g' := eQ.symm.toLinearMap.comp g
  have hcomp : h.comp f' = g'.comp liftLocLin.hom := by
    ext x
    change hcat.hom (eL (eL.symm (f x))) = eQ.symm (g (liftLocLin.hom x))
    rw [LinearEquiv.apply_symm_apply]
    change IsLocalizedModule.mapExtendScalars S f g (Localization S) liftLocLin.hom (f x) = _
    rw [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
    rfl
  have : IsLocalizedModule S liftLocLin.hom := ulift_isLocalized S (locLin P)
  have : IsLocalizedModule S (g.comp liftLocLin.hom) :=
    (IsLocalizedModule.comp_iff_of_bijective_left S (f := liftLocLin.hom) g
      (liftedFractionRingMk_bijective.{u} P)).2 this
  have : IsLocalizedModule S (h.comp f') := by
    rw [hcomp]
    exact IsLocalizedModule.of_linearEquiv S (f := g.comp liftLocLin.hom) eQ.symm
  have hb : Function.Bijective h := by
    rw [← IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S f' h]
    exact (IsLocalizedModule.linearEquiv S f' (h.comp f')).bijective
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hb

private abbrev directSumLoc := DirectSum Nat.Primes primeLocalization

private noncomputable def epi : directSumLoc →ₗ[ℤ] FractionRing ℤ :=
  DirectSum.toModule ℤ Nat.Primes (FractionRing ℤ) locLin

private theorem epi_surjective : Function.Surjective epi := by
  classical
  intro z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective ℤ z
  obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (b.natAbs + 1)
  let P : Nat.Primes := ⟨p, hp⟩
  have : (primeIdeal P).IsPrime := primeIdeal_isPrime P
  have hpb : (b : ℤ) ∉ primeIdeal P := fun hdiv ↦ by
    have : p ≤ b.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hb))
        (Int.natCast_dvd.mp (Ideal.mem_span_singleton.mp hdiv))
    omega
  let d : (primeIdeal P).primeCompl := ⟨b, hpb⟩
  refine ⟨DirectSum.lof ℤ Nat.Primes primeLocalization P
    (IsLocalization.mk' (primeLocalization P) a d), ?_⟩
  simp only [epi, DirectSum.toModule_lof, locLin, AddMonoidHom.coe_toIntLinearMap]
  change locToQ P (IsLocalization.mk' (primeLocalization P) a d) = _
  rw [locToQ_mk']

private theorem homQToLoc_zero (P : Nat.Primes)
    (f : FractionRing ℤ →ₗ[ℤ] primeLocalization P) : f = 0 := by
  classical
  let q : ℕ := P
  let I : Ideal (primeLocalization P) := IsLocalRing.maximalIdeal (primeLocalization P)
  have hpI : algebraMap ℤ (primeLocalization P) (q : ℤ) ∈ I := by
    change (q : ℤ) ∈ Ideal.under ℤ I
    rw [Localization.AtPrime.under_maximalIdeal]
    exact Ideal.mem_span_singleton_self _
  have : IsNoetherianRing (primeLocalization P) :=
    IsLocalization.isNoetherianRing (primeIdeal P).primeCompl (primeLocalization P) inferInstance
  ext x
  have hx : f x ∈ ⨅ n : ℕ, I ^ n := by
    refine Ideal.mem_iInf.mpr fun n ↦ ?_
    let d : FractionRing ℤ := (algebraMap ℤ (FractionRing ℤ) (q : ℤ)) ^ n
    have hd : d ≠ 0 := pow_ne_zero _ (algebraMap_prime_ne_zero P)
    have heq : ((q : ℤ) ^ n) • (x / d) = x := by
      rw [zsmul_eq_mul]
      simpa [d, map_pow] using mul_div_cancel₀ x hd
    rw [← heq, map_smul, zsmul_eq_mul, Int.cast_pow]
    change (((q : ℤ) : primeLocalization P) ^ n) * f (x / d) ∈ I ^ n
    rw [← map_intCast (algebraMap ℤ (primeLocalization P)) (q : ℤ), ← map_pow]
    simpa [mul_comm] using
      (Ideal.mul_mem_left (I ^ n) (f (x / d)) (Ideal.pow_mem_pow hpI n))
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing I (IsLocalRing.maximalIdeal.isMaximal _).ne_top] at hx

private noncomputable def kernel := LinearMap.ker epi

private noncomputable abbrev baseSequence : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk (ModuleCat.ofHom (kernel.subtype)) (ModuleCat.ofHom epi) (by
    ext x
    exact x.property)

private theorem baseSequence_exact : baseSequence.Exact :=
  baseSequence.moduleCat_exact_iff.mpr fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩

private theorem baseSequence_shortExact : baseSequence.ShortExact :=
  .mk' baseSequence_exact ((ModuleCat.mono_iff_injective _).2 (Submodule.subtype_injective _))
    ((ModuleCat.epi_iff_surjective _).2 epi_surjective)

private theorem baseSequence_not_splitting :
    ¬ Nonempty baseSequence.Splitting := by
  rintro ⟨s⟩
  let t : FractionRing ℤ →ₗ[ℤ] directSumLoc := s.s.hom
  have ht : t = 0 := by
    ext x p
    have hz := homQToLoc_zero p ((DirectSum.component ℤ Nat.Primes primeLocalization p).comp t)
    change (t x) p = 0
    exact LinearMap.congr_fun hz x
  have hs : 𝟙 baseSequence.X₃ = 0 := by
    rw [← s.s_g, ModuleCat.hom_ext (f := s.s) (g := 0) ht]
    simp
  simpa using LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hs) (1 : FractionRing ℤ)

private theorem baseSequence_localSplit.{u} (P : Nat.Primes) :
    Nonempty ((((baseSequence.map (ModuleCat.uliftFunctor.{u, 0, 0} ℤ)).map
      (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers (P : ℤ))))).Splitting) := by
  let S := Submonoid.powers (P : ℤ)
  let F : ModuleCat.{u} ℤ ⥤ ModuleCat.{u} (Localization S) :=
    ModuleCat.localizedModuleFunctor.{u, 0} S
  let U : ModuleCat.{0} ℤ ⥤ ModuleCat.{u} ℤ := ModuleCat.uliftFunctor.{u, 0, 0} ℤ
  let S0 := baseSequence.map U
  let i : U.obj (ModuleCat.of ℤ (primeLocalization P)) ⟶ S0.X₂ :=
    U.map (ModuleCat.ofHom (DirectSum.lof ℤ Nat.Primes primeLocalization P))
  let h := F.map (U.map (ModuleCat.ofHom (locLin P)))
  let i' := F.map i
  have hi0 : ModuleCat.ofHom (DirectSum.lof ℤ Nat.Primes primeLocalization P) ≫
      baseSequence.g = ModuleCat.ofHom (locLin P) := by
    apply ModuleCat.hom_ext
    ext x
    simp [baseSequence, epi, DirectSum.toModule_lof]
  have hi : i ≫ S0.g = U.map (ModuleCat.ofHom (locLin P)) := by
    dsimp [i, S0]
    rw [← U.map_comp, hi0]
  have hcomp : i' ≫ (S0.map F).g = h := by
    change F.map i ≫ F.map S0.g = _
    rw [← F.map_comp, hi]
  have : IsIso h := localizedSelectedSummand_isIso.{u} P
  let s : (S0.map F).X₃ ⟶ (S0.map F).X₂ := inv h ≫ i'
  have hs : s ≫ (S0.map F).g = 𝟙 _ := by
    change inv h ≫ i' ≫ (S0.map F).g = 𝟙 _
    rw [hcomp]
    simp
  have hShort : (S0.map F).ShortExact :=
    (baseSequence_shortExact.map_of_exact (ModuleCat.uliftFunctor.{u} ℤ)).map_of_exact F
  exact ⟨.ofExactOfSection (S0.map F) hShort.exact s hs hShort.mono_f⟩

/-- A short exact sequence of integer modules that is nonsplit but splits Zariski locally. -/
@[stacks 0H7G]
theorem exists_nonsplit_shortExact_locally_split.{u} :
    ∃ S : ShortComplex (ModuleCat.{u} ℤ),
      S.ShortExact ∧
        (¬ Nonempty S.Splitting) ∧
        ∀ p : PrimeSpectrum ℤ,
          ∃ f : ℤ, f ∉ p.asIdeal ∧
            Nonempty
              ((S.map (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers f))).Splitting) :=
  by
    refine ⟨(baseSequence.map (ModuleCat.uliftFunctor.{u} ℤ)), ?_, ?_, ?_⟩
    · exact baseSequence_shortExact.map_of_exact (ModuleCat.uliftFunctor.{u} ℤ)
    · intro hs
      let F := ModuleCat.uliftFunctor.{u} ℤ
      let eF := ModuleCat.fullyFaithfulUliftFunctor ℤ
      let r := eF.preimage hs.some.r
      let s := eF.preimage hs.some.s
      have hr : baseSequence.f ≫ r = 𝟙 _ := by
        apply eF.map_injective
        rw [F.map_comp, eF.map_preimage, F.map_id]
        exact hs.some.f_r
      have hsg : s ≫ baseSequence.g = 𝟙 _ := by
        apply eF.map_injective
        rw [F.map_comp, eF.map_preimage, F.map_id]
        exact hs.some.s_g
      have hid : r ≫ baseSequence.f + baseSequence.g ≫ s = 𝟙 _ := by
        apply eF.map_injective
        rw [F.map_add, F.map_comp, F.map_comp, eF.map_preimage, eF.map_preimage, F.map_id]
        exact hs.some.id
      exact baseSequence_not_splitting ⟨⟨r, s, hr, hsg, hid⟩⟩
    · intro p
      by_cases h₂ : (2 : ℤ) ∈ p.asIdeal
      · refine ⟨3, fun h ↦ p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_),
          baseSequence_localSplit.{u} ⟨3, by decide⟩⟩
        simpa using p.asIdeal.sub_mem h h₂
      · exact ⟨2, h₂, baseSequence_localSplit.{u} ⟨2, by decide⟩⟩

end Stacks.Examples

end

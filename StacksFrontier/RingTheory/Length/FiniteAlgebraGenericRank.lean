module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.RingTheory.Length.FibreLengthSum
public import StacksFrontier.RingTheory.Length.LocalizationModelIndependence
public import Mathlib.RingTheory.Ideal.Height
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Length of `M / aM` for a module of constant generic length over a one-dimensional local ring

Let `A` be a reduced Noetherian local ring of dimension at most one, and let `M` be a finite
`A`-module on which every nonzerodivisor of `A` acts injectively and whose localization at every
minimal prime `𝔭` of `A` has length `d` times that of `A_𝔭`. Then for every nonzerodivisor `a`
of `A`

`length_A(M / aM) = d · length_A(A / aA)`.

This is the reduced case of Stacks 02QG applied to `M` and to `A` and compared term by term: the
minimal primes of the support of `M` are the minimal primes of `A`.
-/

@[expose] public section

open scoped nonZeroDivisors Pointwise

universe u

namespace Stacks.Length

variable {A : Type*} [CommRing A]

/-- In a reduced Noetherian ring every associated prime is a minimal prime. -/
theorem mem_minimalPrimes_of_mem_associatedPrimes_of_isReduced [IsNoetherianRing A] [IsReduced A]
    {q : Ideal A}
    (hq : q ∈ associatedPrimes A A) : q ∈ minimalPrimes A := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hq
  obtain ⟨hp, x, hx⟩ := hq
  have hmem : ∀ r : A, r ∈ q ↔ r * x = 0 := by
    intro r
    rw [hx, Submodule.mem_colon_singleton]
    simp [Submodule.mem_bot, smul_eq_mul]
  have hxq : x ∉ q := by
    intro h
    have hx0 : x = 0 := IsReduced.eq_zero x ⟨2, by rw [pow_two]; exact (hmem x).1 h⟩
    exact hp.ne_top ((Ideal.eq_top_iff_one _).2 ((hmem 1).2 (by simp [hx0])))
  refine ⟨⟨hp, bot_le⟩, fun p hp' hpq => ?_⟩
  intro r hr
  have h0 : r * x ∈ p := by rw [(hmem r).1 hr]; exact p.zero_mem
  exact (hp'.1.mem_or_mem h0).resolve_right (fun h => hxq (hpq h))

variable [IsNoetherianRing A]

/-- **A minimal prime of the support of a torsion-free module is a minimal prime of the ring.**
If every nonzerodivisor of a reduced Noetherian ring `A` acts injectively on a finite module `M`,
every minimal element of the support of `M` is a minimal prime of `A`. -/
theorem mem_minimalPrimes_of_minimal_mem_support [IsReduced A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] (hreg : ∀ a ∈ A⁰, IsSMulRegular M a)
    {q : PrimeSpectrum A} (hq : Minimal (· ∈ Module.support A M) q) :
    q.asIdeal ∈ minimalPrimes A := by
  have hass := Module.mem_associatedPrimes_of_minimal_mem_support hq
  have hsub : (q.asIdeal : Set A) ⊆ ⋃ p ∈ associatedPrimes A A, ((id p : Ideal A) : Set A) := by
    intro r hr
    have hr' : r ∈ ⋃ p ∈ associatedPrimes A M, (p : Set A) := Set.mem_biUnion hass hr
    rw [biUnion_associatedPrimes_eq_compl_regular A M] at hr'
    have hA : r ∈ {r : A | IsSMulRegular A r}ᶜ := fun h => by
      refine hr' (hreg r ?_)
      rw [mem_nonZeroDivisors_iff]
      exact ⟨fun x hx => h (show r • x = r • (0 : A) by
          rw [smul_eq_mul, smul_eq_mul, mul_zero]; exact hx),
        fun x hx => h (show r • x = r • (0 : A) by
          rw [smul_eq_mul, smul_eq_mul, mul_zero, mul_comm]; exact hx)⟩
    rw [← biUnion_associatedPrimes_eq_compl_regular A A] at hA
    simpa using hA
  obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite A A)
    (f := id) ⊥ ⊥ (fun i hi _ _ => (IsAssociatedPrime.isPrime hi : i.IsPrime))).mp hsub
  have hPmin := mem_minimalPrimes_of_mem_associatedPrimes_of_isReduced hP
  have hPq : P ≤ q.asIdeal := hPmin.2 ⟨q.isPrime, bot_le⟩ hle
  rwa [le_antisymm hle hPq]

omit [IsNoetherianRing A] in
/-- A minimal prime of `A` at which `M` does not vanish is a minimal element of the support of
`M`. -/
theorem minimal_mem_support_of_mem_minimalPrimes {M : Type*} [AddCommGroup M] [Module A M]
    {q : PrimeSpectrum A} (hq : q.asIdeal ∈ minimalPrimes A)
    (hM : Nontrivial (LocalizedModule q.asIdeal.primeCompl M)) :
    Minimal (· ∈ Module.support A M) q :=
  ⟨Module.mem_support_iff.mpr hM, fun q' _ hle => hq.2 ⟨q'.isPrime, bot_le⟩ hle⟩

/-- The sum of Stacks 02QG over the minimal primes of the support of a torsion-free module is
the same sum over all minimal primes of `A`: the extra summands vanish. -/
theorem finsum_minimal_support_eq_finsum_minimalPrimes [IsReduced A] {M : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] (hreg : ∀ a ∈ A⁰, IsSMulRegular M a)
    (g : PrimeSpectrum A → ℕ∞) :
    (∑ᶠ q ∈ {q : PrimeSpectrum A | Minimal (· ∈ Module.support A M) q},
        g q * Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)) =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | q.asIdeal ∈ minimalPrimes A},
        g q * Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M) := by
  rw [← finsum_mem_inter_support, ← finsum_mem_inter_support (s := {q : PrimeSpectrum A |
    q.asIdeal ∈ minimalPrimes A})]
  refine finsum_mem_congr ?_ (fun _ _ => rfl)
  ext q
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
  refine ⟨fun h => ⟨mem_minimalPrimes_of_minimal_mem_support hreg h.1, h.2⟩, fun h => ⟨?_, h.2⟩⟩
  refine minimal_mem_support_of_mem_minimalPrimes h.1 ?_
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  exact h.2 (by rw [Module.length_eq_zero_iff.mpr hn, mul_zero])

omit [IsNoetherianRing A] in
/-- A nonzerodivisor of `A` acts injectively on `A`. -/
theorem isSMulRegular_self_of_mem_nonZeroDivisors' {a : A} (ha : a ∈ A⁰) : IsSMulRegular A a :=
  fun x y hxy => by
    have h : (x - y) * a = 0 := by
      have : a * x = a * y := hxy
      rw [sub_mul, mul_comm x, mul_comm y, this, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp ha).2 _ h)

/-- If `e + 1 ≤ 1` in `ℕ∞` then `e = 0`. -/
private theorem eq_zero_of_add_one_le_one {e : ℕ∞} (h : e + 1 ≤ 1) : e = 0 := by
  by_contra hc
  have : 1 ≤ e := Order.one_le_iff_ne_zero.mpr hc
  exact absurd ((add_le_add_left this 1).trans h) (by decide)

/-- Over a Noetherian local ring of dimension at most one, a nontrivial finite module on which an
element of the maximal ideal acts injectively has support of dimension one. -/
theorem supportDim_eq_one_of_isSMulRegular [IsLocalRing A] [Ring.KrullDimLE 1 A] {M : Type*}
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] {a : A}
    (ha : IsSMulRegular M a) (ham : a ∈ IsLocalRing.maximalIdeal A) :
    Module.supportDim A M = 1 := by
  have h := Module.supportDim_quotSMulTop_succ_eq_supportDim ha ham
  have hnt : Nontrivial (QuotSMulTop a M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M ham
  have hne : Module.supportDim A (QuotSMulTop a M) ≠ ⊥ :=
    (Module.supportDim_ne_bot_iff_nontrivial A _).mpr hnt
  have hle : Module.supportDim A M ≤ 1 :=
    (Module.supportDim_le_ringKrullDim A M).trans (by exact_mod_cast Ring.krullDimLE_iff.mp ‹_›)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← he] at h
  rw [← h] at hle ⊢
  have : (e : WithBot ℕ∞) + 1 = ((e + 1 : ℕ∞) : WithBot ℕ∞) := rfl
  rw [this] at hle ⊢
  have h1 : e + 1 ≤ 1 := by exact_mod_cast hle
  simp [eq_zero_of_add_one_le_one h1]

omit [IsNoetherianRing A] in
/-- A unit kills `M / aM`. -/
theorem subsingleton_quotSMulTop_of_isUnit {M : Type*} [AddCommGroup M] [Module A M] {a : A}
    (ha : IsUnit a) : Subsingleton (QuotSMulTop a M) := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | H x => ?_
  induction y using Submodule.Quotient.induction_on with | H y => ?_
  rw [Submodule.Quotient.eq]
  obtain ⟨u, rfl⟩ := ha
  have : x - y = (u : A) • ((↑u⁻¹ : A) • (x - y)) := by
    rw [smul_smul, Units.mul_inv, one_smul]
  rw [this]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- **Stacks 02QG for a torsion-free module, over the minimal primes of the ring.** For a
nonzerodivisor `a` in the maximal ideal of a reduced Noetherian local ring `A` of dimension at
most one and a finite `A`-module `N` on which every nonzerodivisor of `A` acts injectively,
`length(N / aN) = ∑_𝔭 length(A / (a, 𝔭)) · length(N_𝔭)` over the minimal primes `𝔭` of `A`. -/
@[ega "IV 3.4.1.2" "special case"]
theorem length_quotSMulTop_eq_finsum_minimalPrimes [IsLocalRing A] [IsReduced A]
    [Ring.KrullDimLE 1 A] {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hreg : ∀ a ∈ A⁰, IsSMulRegular N a) {a : A} (ha : a ∈ A⁰)
    (ham : a ∈ IsLocalRing.maximalIdeal A) :
    Module.length A (QuotSMulTop a N) =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | q.asIdeal ∈ minimalPrimes A},
        Module.length A (A ⧸ (Ideal.span {a} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl N) := by
  rcases subsingleton_or_nontrivial N with hN | hN
  · rw [Module.length_eq_zero_iff.mpr inferInstance]
    symm
    refine finsum_mem_eq_zero_of_forall_eq_zero fun q _ => ?_
    rw [Module.length_eq_zero_iff.mpr
      (inferInstance : Subsingleton (LocalizedModule q.asIdeal.primeCompl N)), mul_zero]
  · rw [Stacks.Chow.length_quotSMulTop_eq_sum_of_regular_of_supportDim_eq_one a (hreg a ha)
      ham (supportDim_eq_one_of_isSMulRegular (hreg a ha) ham),
      finsum_minimal_support_eq_finsum_minimalPrimes hreg]

/-- **Stacks 02QG, compared on two modules.** Let `A` be a reduced Noetherian local ring of
dimension at most one and `M`, `M₀` finite `A`-modules on which every nonzerodivisor of `A` acts
injectively, with `length_{A_𝔭}(M_𝔭) = d · length_{A_𝔭}((M₀)_𝔭)` at every minimal prime `𝔭` of
`A`. Then for every nonzerodivisor `a` of `A`,

`length_A(M / aM) = d · length_A(M₀ / aM₀)`. -/
theorem length_quotSMulTop_eq_mul_length_quotSMulTop [IsLocalRing A] [IsReduced A]
    [Ring.KrullDimLE 1 A] {M M₀ : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀]
    (d : ℕ) (hreg : ∀ a ∈ A⁰, IsSMulRegular M a) (hreg₀ : ∀ a ∈ A⁰, IsSMulRegular M₀ a)
    (hrank : ∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
      Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) =
        d * Module.length (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M₀))
    {a : A} (ha : a ∈ A⁰) :
    Module.length A (QuotSMulTop a M) = d * Module.length A (QuotSMulTop a M₀) := by
  by_cases ham : a ∈ IsLocalRing.maximalIdeal A
  · rw [length_quotSMulTop_eq_finsum_minimalPrimes hreg ha ham,
      length_quotSMulTop_eq_finsum_minimalPrimes hreg₀ ha ham, mul_finsum_mem]
    refine finsum_mem_congr rfl fun q hq => ?_
    rw [hrank q hq]
    ring
  · have hu : IsUnit a := by simpa using ham
    have := subsingleton_quotSMulTop_of_isUnit (M := M) hu
    have := subsingleton_quotSMulTop_of_isUnit (M := M₀) hu
    rw [Module.length_eq_zero_iff.mpr ‹Subsingleton (QuotSMulTop a M)›,
      Module.length_eq_zero_iff.mpr ‹Subsingleton (QuotSMulTop a M₀)›, mul_zero]

/-! ### Localization commutes with `M / xM` -/

section Localization

variable {R : Type*} [CommRing R] (S : Submonoid R) (T : Type*) [CommRing T] [Algebra R T]
  [IsLocalization S T] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module T N] [IsScalarTower R T N] (f : M →ₗ[R] N) [IsLocalizedModule S f]

/-- The localization of `x • M` is `x • N`. -/
theorem localized'_smul_top (x : R) :
    Submodule.localized' T S f (x • (⊤ : Submodule R M)) =
      (algebraMap R T x) • (⊤ : Submodule T N) := by
  ext y
  rw [Submodule.mem_localized']
  constructor
  · rintro ⟨m, hm, s, rfl⟩
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
    rw [IsLocalizedModule.mk'_smul, ← algebraMap_smul T x]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · intro hy
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f z
    refine ⟨x • m, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top, s, ?_⟩
    simp only [Function.uncurry_apply_pair]
    rw [IsLocalizedModule.mk'_smul, algebraMap_smul]

/-- The length of a localization of any module `Q` isomorphic to `M / xM` is the length of
`N / xN`, for `N` a localization of `M`. -/
private theorem length_localizedModule_of_linearEquiv_quotSMulTop (f' : M →ₗ[R] N)
    [IsLocalizedModule S f'] (x : R) {Q : Type*} [AddCommGroup Q]
    [Module R Q] (e : Q ≃ₗ[R] QuotSMulTop x M) :
    Module.length (Localization S) (LocalizedModule S Q) =
      Module.length T (QuotSMulTop (algebraMap R T x) N) := by
  have : IsLocalizedModule S
      (((x • (⊤ : Submodule R M)).toLocalizedQuotient' T S f') ∘ₗ e.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right _ _ _
  rw [Module.length_eq_of_isLocalization_of_isLocalizedModule S T
    (((x • (⊤ : Submodule R M)).toLocalizedQuotient' T S f') ∘ₗ e.toLinearMap)]
  exact (Submodule.quotEquivOfEq _ _ (localized'_smul_top S T f' x)).length_eq

include f in
/-- **The length of a localization of `M / xM` is the length of `N / xN`** for `N` any
localization of `M`. -/
theorem length_localizedModule_quotSMulTop (x : R) :
    Module.length (Localization S) (LocalizedModule S (QuotSMulTop x M)) =
      Module.length T (QuotSMulTop (algebraMap R T x) N) :=
  length_localizedModule_of_linearEquiv_quotSMulTop S T f x (LinearEquiv.refl R _)

end Localization

/-! ### Nonzerodivisors along a map whose minimal primes lie over minimal primes -/

section MinimalPrimes

variable {R : Type*} [CommRing R]

/-- In a reduced ring an element lying in no minimal prime is a nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_forall_notMem_minimalPrimes [IsReduced R] {x : R}
    (h : ∀ P ∈ minimalPrimes R, x ∉ P) : x ∈ R⁰ := by
  have key : ∀ y : R, y * x = 0 → y = 0 := by
    intro y hy
    have hrad : y ∈ (⊥ : Ideal R).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      refine Submodule.mem_sInf.mpr fun P hP => ?_
      have hP' : Ideal.IsPrime P := hP.1.1
      have h0 : y * x ∈ P := by rw [hy]; exact P.zero_mem
      exact (hP'.mem_or_mem h0).resolve_right (h P hP)
    obtain ⟨n, hn⟩ := hrad
    exact IsReduced.eq_zero y ⟨n, by simpa using hn⟩
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun y hy => key y (by rw [mul_comm]; exact hy), fun y hy => key y hy⟩

/-- The image in a localization of a minimal prime disjoint from the submonoid is a minimal
prime of the localization. -/
theorem map_mem_minimalPrimes_of_isLocalization (M : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] {P : Ideal R} (hP : P ∈ minimalPrimes R)
    (hdisj : Disjoint (M : Set R) P) : P.map (algebraMap R S) ∈ minimalPrimes S := by
  have hPp : P.IsPrime := hP.1.1
  refine ⟨⟨IsLocalization.isPrime_of_isPrime_disjoint M S P hPp hdisj, bot_le⟩,
    fun J hJ hle => ?_⟩
  have hJp : J.IsPrime := hJ.1
  have hc : J.comap (algebraMap R S) ≤ P := by
    have := Ideal.comap_mono (f := algebraMap R S) hle
    exact this.trans (le_of_eq (IsLocalization.under_map_of_isPrime_disjoint M S hPp hdisj))
  have heq : J.comap (algebraMap R S) = P :=
    le_antisymm hc (hP.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hc)
  rw [← heq, IsLocalization.map_under M S J]

/-- The contraction of a minimal prime of a localization is a minimal prime. -/
theorem comap_mem_minimalPrimes_of_isLocalization (T : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S] {Q' : Ideal S}
    (hQ' : Q' ∈ minimalPrimes S) : Q'.comap (algebraMap R S) ∈ minimalPrimes R := by
  have hQ'p : Q'.IsPrime := hQ'.1.1
  have hdisjQ : Disjoint (T : Set R) (Q'.comap (algebraMap R S)) := by
    rw [Set.disjoint_left]
    intro b hb hbQ
    exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hbQ (IsLocalization.map_units S ⟨b, hb⟩))
  refine ⟨⟨Ideal.comap_isPrime _ _, bot_le⟩, fun J hJ hJle => ?_⟩
  have hJp : J.IsPrime := hJ.1
  have hdisj : Disjoint (T : Set R) J := hdisjQ.mono_right hJle
  have hmapP := IsLocalization.isPrime_of_isPrime_disjoint T S J hJp hdisj
  have hmap_le : J.map (algebraMap R S) ≤ Q' := Ideal.map_le_iff_le_comap.mpr hJle
  have := hQ'.2 ⟨hmapP, bot_le⟩ hmap_le
  have h2 := Ideal.comap_mono (f := algebraMap R S) this
  exact h2.trans (le_of_eq (IsLocalization.under_map_of_isPrime_disjoint T S hJp hdisj))

end MinimalPrimes

/-- If `a / s` is a nonzerodivisor of a localization, so is the image of `a`. -/
private theorem algebraMap_mem_nonZeroDivisors_of_mk'_mem {R : Type*} [CommRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] {a : R} {s : M}
    (hy : IsLocalization.mk' S a s ∈ S⁰) : algebraMap R S a ∈ S⁰ := by
  rw [← IsLocalization.mk'_spec S a s]
  exact Submonoid.mul_mem _ hy (IsLocalization.map_units S s).mem_nonZeroDivisors

/-- **Nonzerodivisors go to nonzerodivisors along a map whose minimal primes lie over minimal
primes.** Let `φ : A → B` be a ring homomorphism with `B` reduced such that every minimal prime
of `B` contracts to a minimal prime of `A`, and let `ψ : A_M → B_T` be a homomorphism of
localizations compatible with `φ`. Then `ψ` carries nonzerodivisors to nonzerodivisors. -/
theorem map_mem_nonZeroDivisors_of_minimalPrimes {A B : Type*} [CommRing A] [CommRing B]
    [IsReduced B] (φ : A →+* B) (hmin : ∀ Q ∈ minimalPrimes B, Q.comap φ ∈ minimalPrimes A)
    (M : Submonoid A) (Aₘ : Type*) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ]
    (T : Submonoid B) (Bₜ : Type*) [CommRing Bₜ] [Algebra B Bₜ] [IsLocalization T Bₜ]
    (ψ : Aₘ →+* Bₜ) (hψ : ψ.comp (algebraMap A Aₘ) = (algebraMap B Bₜ).comp φ)
    {y : Aₘ} (hy : y ∈ Aₘ⁰) : ψ y ∈ Bₜ⁰ := by
  have : IsReduced Bₜ := by
    refine ⟨fun x ⟨n, hn⟩ => ?_⟩
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective T x
    simp only at hn ⊢
    rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_zero_iff] at hn
    obtain ⟨c, hc⟩ := hn
    have hcb : (c : B) * b = 0 := by
      refine IsReduced.eq_zero _ ⟨n + 1, ?_⟩
      calc ((c : B) * b) ^ (n + 1) = ((c : B) ^ n * b) * ((c : B) * b ^ n) := by ring
        _ = 0 := by rw [hc, mul_zero]
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨c, hcb⟩
  refine mem_nonZeroDivisors_of_forall_notMem_minimalPrimes fun Q' hQ' hmem => ?_
  have hQ'p : Q'.IsPrime := hQ'.1.1
  set Q₀ := Q'.comap (algebraMap B Bₜ) with hQ₀
  have hQ₀min : Q₀ ∈ minimalPrimes B := comap_mem_minimalPrimes_of_isLocalization T Bₜ hQ'
  have hP₀min := hmin Q₀ hQ₀min
  have hψa : ∀ a : A, ψ (algebraMap A Aₘ a) = algebraMap B Bₜ (φ a) := fun a =>
    RingHom.congr_fun hψ a
  have hdisj : Disjoint (M : Set A) (Q₀.comap φ) := by
    rw [Set.disjoint_left]
    intro b hb hbP
    have hu : IsUnit (ψ (algebraMap A Aₘ b)) := (IsLocalization.map_units Aₘ ⟨b, hb⟩).map ψ
    rw [hψa] at hu
    exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hbP hu)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  simp only at hmem hy
  have hspec := IsLocalization.mk'_spec Aₘ a s
  have ha : φ a ∈ Q₀ := by
    rw [hQ₀, Ideal.mem_comap, ← hψa, ← hspec, map_mul]
    exact Q'.mul_mem_right _ hmem
  have hJ := map_mem_minimalPrimes_of_isLocalization M Aₘ hP₀min hdisj
  have hamem : algebraMap A Aₘ a ∈ (Q₀.comap φ).map (algebraMap A Aₘ) :=
    Ideal.mem_map_of_mem _ (show a ∈ Q₀.comap φ from ha)
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hJ) hamem
    (algebraMap_mem_nonZeroDivisors_of_mk'_mem M Aₘ hy)

/-- The local form of `Stacks.Length.map_mem_nonZeroDivisors_of_minimalPrimes`: for a prime `Q`
of `B` over `P`, the local homomorphism `A_P → B_Q` carries nonzerodivisors to nonzerodivisors. -/
theorem localRingHom_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] [IsReduced B]
    (φ : A →+* B) (hmin : ∀ Q ∈ minimalPrimes B, Q.comap φ ∈ minimalPrimes A)
    (Q : Ideal B) [Q.IsPrime] (P : Ideal A) [P.IsPrime] (hPQ : P = Q.comap φ)
    {y : Localization.AtPrime P} (hy : y ∈ (Localization.AtPrime P)⁰) :
    Localization.localRingHom P Q φ hPQ y ∈ (Localization.AtPrime Q)⁰ :=
  map_mem_nonZeroDivisors_of_minimalPrimes φ hmin P.primeCompl (Localization.AtPrime P)
    Q.primeCompl (Localization.AtPrime Q) _ (IsLocalization.map_comp _) hy

/-! ### The fibre formula over a finite algebra -/

section Fibre

/-- **Torsion-freeness of a localized algebra.** Let `X` be an `A`-algebra and `X_p` a
localization of `X` at the image of `A ∖ 𝔭`, carrying an `A_𝔭`-algebra structure. If
`A_𝔭 → X_𝔭` carries nonzerodivisors to nonzerodivisors, then every nonzerodivisor of `A_𝔭` acts
injectively on the formal localization `X_𝔭` of the `A`-module `X`. -/
theorem isSMulRegular_localizedModule_of_map_mem_nonZeroDivisors {A : Type*} [CommRing A]
    (p : Ideal A) [p.IsPrime] {X Xp : Type*} [CommRing X] [Algebra A X] [CommRing Xp]
    [Algebra A Xp] [Algebra (Localization.AtPrime p) Xp]
    [IsScalarTower A (Localization.AtPrime p) Xp] (f : X →ₗ[A] Xp)
    [IsLocalizedModule p.primeCompl f]
    (hψ : ∀ y ∈ (Localization.AtPrime p)⁰, algebraMap (Localization.AtPrime p) Xp y ∈ Xp⁰)
    {y : Localization.AtPrime p} (hy : y ∈ (Localization.AtPrime p)⁰) :
    IsSMulRegular (LocalizedModule p.primeCompl X) y := by
  have key : ∀ z : LocalizedModule p.primeCompl X, y • z = 0 → z = 0 := by
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
    simp only at hz hy
    have hspec := IsLocalization.mk'_spec (Localization.AtPrime p) a s
    have haz : a • z = 0 := by
      rw [← algebraMap_smul (Localization.AtPrime p) a z, ← hspec, mul_comm, mul_smul, hz,
        smul_zero]
    have hX : algebraMap A Xp a ∈ Xp⁰ := by
      rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime p) Xp]
      exact hψ _ (algebraMap_mem_nonZeroDivisors_of_mk'_mem p.primeCompl _ hy)
    let e := IsLocalizedModule.iso p.primeCompl f
    have he : e (a • z) = 0 := by rw [haz, map_zero]
    rw [map_smul, Algebra.smul_def] at he
    exact e.injective ((mem_nonZeroDivisors_iff.mp hX).1 _ he |>.trans (map_zero e).symm)
  intro z₁ z₂ h
  have h' : y • (z₁ - z₂) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp (key _ h')

/-- In a local ring of dimension at most one a prime other than the maximal ideal is minimal. -/
theorem mem_minimalPrimes_of_ne_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] {J : Ideal R} [J.IsPrime] (hJ : J ≠ IsLocalRing.maximalIdeal R) :
    J ∈ minimalPrimes R := by
  rw [← Ideal.height_eq_zero_iff]
  have hlt : J < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hJ
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) ≤ 1 :=
    Ideal.height_le_ringKrullDim_of_isPrime.trans (Ring.krullDimLE_iff.mp ‹_›)
  have h3 : (IsLocalRing.maximalIdeal R).height ≤ 1 := by exact_mod_cast h2
  exact eq_zero_of_add_one_le_one (h1.trans h3)

/-- `x • R` is the principal ideal of `x`. -/
theorem smul_top_eq_span_singleton {R : Type*} [CommRing R] (x : R) :
    (x • (⊤ : Submodule R R)) = Ideal.span {x} := by
  ext z
  rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨w, -, rfl⟩
    exact ⟨w, by rw [smul_eq_mul, mul_comm]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, Submodule.mem_top, by rw [smul_eq_mul, mul_comm]⟩

/-- The order of vanishing is the length of `R / xR`, read as `QuotSMulTop`. -/
theorem ord_eq_length_quotSMulTop {R : Type*} [CommRing R] (x : R) :
    Ring.ord R x = Module.length R (QuotSMulTop x R) :=
  ((Submodule.quotEquivOfEq _ _ (smul_top_eq_span_singleton x)).length_eq).symm

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]

/-- For `a ∈ A`, the `B`-module `B / aB` is, as an `A`-module, the `A`-module `B / aB`. -/
noncomputable def quotSMulTopAlgebraMapEquiv (a : A) :
    QuotSMulTop (algebraMap A B a) B ≃ₗ[A] QuotSMulTop a B :=
  (Submodule.Quotient.restrictScalarsEquiv A ((algebraMap A B a) • (⊤ : Submodule B B))).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by
      ext z
      simp only [Submodule.restrictScalars_mem, Submodule.mem_smul_pointwise_iff_exists,
        Submodule.mem_top, true_and]
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨w, by rw [algebraMap_smul]⟩
      · rintro ⟨w, rfl⟩
        exact ⟨w, by rw [algebraMap_smul]⟩)

/-- **The fibre formula for orders of vanishing over a finite algebra.** Let `A` be Noetherian,
`B` a finite `A`-algebra which is reduced with every minimal prime lying over a minimal prime of
`A`, and `𝔭` a prime of `A` with `A_𝔭` reduced of dimension at most one. Suppose that at every
minimal prime `P ⊆ 𝔭` of `A` the length of `B_P` over `A_P` is `d` times that of `A_P`. Then
for every `a ∈ A` which is a nonzerodivisor in `A_𝔭`,

`∑_{𝔮 ∩ A = 𝔭} [κ(𝔮) : κ(𝔭)] · ord_{B_𝔮}(a) = d · ord_{A_𝔭}(a)`. -/
theorem finsum_primeResidueDegree_mul_ord_eq_mul_ord [IsReduced B]
    (hmin : ∀ Q ∈ minimalPrimes B, Q.comap (algebraMap A B) ∈ minimalPrimes A)
    [IsReduced (Localization.AtPrime p)] [Ring.KrullDimLE 1 (Localization.AtPrime p)] (d : ℕ)
    (hrank : ∀ P : PrimeSpectrum A, P.asIdeal ∈ minimalPrimes A → P.asIdeal ≤ p →
      Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl B) =
        d * Module.length (Localization.AtPrime P.asIdeal)
          (LocalizedModule P.asIdeal.primeCompl A))
    {a : A} (ha : algebraMap A (Localization.AtPrime p) a ∈ (Localization.AtPrime p)⁰) :
    ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = p},
        (primeResidueDegree (algebraMap A B) p Q.asIdeal : ℕ∞) *
          Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ (algebraMap A B a)) =
      d * Ring.ord (Localization.AtPrime p) (algebraMap A _ a) := by
  classical
  set b := algebraMap A B a with hb
  let Bp := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  have hterm : ∀ Q : PrimeSpectrum B,
      Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ b) =
        Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl (QuotSMulTop b B)) := fun Q => by
    rw [ord_eq_length_quotSMulTop, length_localizedModule_quotSMulTop Q.asIdeal.primeCompl
      (Localization.AtPrime Q.asIdeal) (Algebra.linearMap B (Localization.AtPrime Q.asIdeal)) b]
  have hsupp : ∀ Q : PrimeSpectrum B, Q ∈ Module.support B (QuotSMulTop b B) →
      Q.asIdeal.comap (algebraMap A B) ≤ p → Q.asIdeal.comap (algebraMap A B) = p := by
    intro Q hQ hle
    by_contra hne
    have hbQ : b ∈ Q.asIdeal := by
      refine (Module.mem_support_iff_of_finite.mp hQ) ?_
      rw [Module.mem_annihilator]
      intro z
      induction z using Submodule.Quotient.induction_on with | H z => ?_
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    set P := Q.asIdeal.comap (algebraMap A B) with hP
    have hPp : P.IsPrime := Ideal.comap_isPrime _ _
    have haP : a ∈ P := hbQ
    have hdisj : Disjoint (p.primeCompl : Set A) P := by
      rw [Set.disjoint_left]
      intro x hx hxP
      exact hx (hle hxP)
    have hJp := IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl
      (Localization.AtPrime p) P hPp hdisj
    have hJne : P.map (algebraMap A (Localization.AtPrime p)) ≠
        IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      intro h
      have h1 := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl
        (Localization.AtPrime p) hPp hdisj
      rw [h, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p] at h1
      exact hne h1.symm
    have hJmin := mem_minimalPrimes_of_ne_maximalIdeal hJne
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hJmin)
      (Ideal.mem_map_of_mem _ haP) ha
  have hfib := length_localizedModule_eq_finsum_fibre p (QuotSMulTop b B) hsupp
  have hsum : (∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = p},
        (primeResidueDegree (algebraMap A B) p Q.asIdeal : ℕ∞) *
          Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ b)) =
      Module.length (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (QuotSMulTop b B)) := by
    rw [hfib]
    exact finsum_mem_congr rfl fun Q _ => by rw [hterm]
  rw [hsum]
  have h3 : Module.length (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (QuotSMulTop b B)) =
      Module.length (Localization.AtPrime p)
        (QuotSMulTop (algebraMap A (Localization.AtPrime p) a)
          (LocalizedModule p.primeCompl B)) := by
    exact length_localizedModule_of_linearEquiv_quotSMulTop p.primeCompl (Localization.AtPrime p)
      (LocalizedModule.mkLinearMap p.primeCompl B) a (quotSMulTopAlgebraMapEquiv a)
  have hψ : (algebraMap (Localization.AtPrime p) Bp).comp (algebraMap A (Localization.AtPrime p)) =
      (algebraMap B Bp).comp (algebraMap A B) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hregB : ∀ y ∈ (Localization.AtPrime p)⁰,
      IsSMulRegular (LocalizedModule p.primeCompl B) y := fun y hy =>
    isSMulRegular_localizedModule_of_map_mem_nonZeroDivisors p (X := B) (Xp := Bp)
      (IsScalarTower.toAlgHom A B Bp).toLinearMap
      (fun z hz => map_mem_nonZeroDivisors_of_minimalPrimes (algebraMap A B) hmin p.primeCompl
        (Localization.AtPrime p) (Algebra.algebraMapSubmonoid B p.primeCompl) Bp _ hψ hz) hy
  have hregA : ∀ y ∈ (Localization.AtPrime p)⁰,
      IsSMulRegular (LocalizedModule p.primeCompl A) y := fun y hy =>
    isSMulRegular_localizedModule_of_map_mem_nonZeroDivisors p (X := A)
      (Xp := Localization.AtPrime p) (Algebra.linearMap A (Localization.AtPrime p))
      (fun z hz => by simpa using hz) hy
  have hrank' : ∀ P' : PrimeSpectrum (Localization.AtPrime p), P'.asIdeal ∈ minimalPrimes _ →
      Module.length (Localization.AtPrime P'.asIdeal)
          (LocalizedModule P'.asIdeal.primeCompl (LocalizedModule p.primeCompl B)) =
        d * Module.length (Localization.AtPrime P'.asIdeal)
          (LocalizedModule P'.asIdeal.primeCompl (LocalizedModule p.primeCompl A)) := by
    intro P' hP'
    rw [length_localizedModule_localizedModule p.primeCompl B P'.asIdeal,
      length_localizedModule_localizedModule p.primeCompl A P'.asIdeal]
    have hmin' := comap_mem_minimalPrimes_of_isLocalization p.primeCompl
      (Localization.AtPrime p) hP'
    have hle : P'.asIdeal.comap (algebraMap A (Localization.AtPrime p)) ≤ p := by
      intro x hx
      by_contra hxp
      exact P'.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (IsLocalization.map_units _ (⟨x, hxp⟩ : p.primeCompl)))
    exact hrank ⟨_, Ideal.comap_isPrime _ _⟩ hmin' hle
  rw [h3, length_quotSMulTop_eq_mul_length_quotSMulTop d hregB hregA hrank' ha,
    ord_eq_length_quotSMulTop, ← length_localizedModule_quotSMulTop p.primeCompl
      (Localization.AtPrime p) (LocalizedModule.mkLinearMap p.primeCompl A) a,
    length_localizedModule_quotSMulTop p.primeCompl (Localization.AtPrime p)
      (Algebra.linearMap A (Localization.AtPrime p)) a]

end Fibre

end Stacks.Length

end

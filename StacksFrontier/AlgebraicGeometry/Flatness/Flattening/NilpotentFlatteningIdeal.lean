module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Order.Zorn
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ZeroLocusOnLocalSpectrum
public import StacksFrontier.RingTheory.Flat.FlatteningSectionsKernel

/-!
# The nilpotent flattening ideal in the proof of Stacks 05U9

The proof of Stacks 05U9 runs an induction over a generic flatness stratification
`Spec A ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` of the base. Writing `Spec (A/J_i)` for the scheme theoretic
closure of the stratum `S_i ∖ S_{i+1}`, *Claim 1* of that proof is that `N/J_iN` is flat over
`A/J_i`, and the paragraph after it concludes that there is a **finitely generated nilpotent**
ideal `I₀ ⊆ A` with `N/I₀N` flat over `A/I₀`.

This file contains two things.

* The two **ring-theoretic steps** of that argument which are independent of the stratification
  and of the henselization, stated over an arbitrary local ring: the vanishing of the smallest
  flattening ideal when the module is flat on a scheme theoretically dense quasi-compact open
  (`Stacks.eq_bot_of_le_sectionsKernel`, `Stacks.flat_of_least_flattening_of_flat_away`), and the
  passage from a flattening ideal inside every prime to nilpotence of the smallest flattening
  ideal (`Stacks.isNilpotent_of_least_flattening`).
* A **refutation**, `Stacks.not_forall_exists_fg_isNilpotent_flat_quotient`, of the statement that
  the conclusion of that paragraph holds for `N` alone, without the standing hypotheses of the
  source (a flat `A`-module `M` and an `A`-linear `u : N → M` which is injective modulo `𝔪_A`):
  it fails for `A = B = ℤ₂` and `N = ℤ₂/(2)`.

## Main results

* `Stacks.exists_annihilator_of_locally_sq`: Nakayama on a principal open, elementwise. If
  `gⁿx ∈ I²` for every `x ∈ I` and some `n`, and `I` is finitely generated, then there are
  `z ∈ A` and `k` with `z - g^k ∈ I` and `z` annihilating `I` after inverting `g`.
* `Stacks.exists_maximal_isPrime_not_le`: a prime not containing a finitely generated ideal `J`
  is contained in one maximal among the primes not containing `J`; by
  `Stacks.isClosed_singleton_of_maximal` such a prime is a closed point of `Spec A ∖ V(J)`.
* `Stacks.le_of_not_le_of_le_pow`: strengthening of Stacks 0ATB from the closed points of
  `U = Spec A ∖ V(J)` to all of `U`, for an ideal which is locally on `U` its own square.
* `Stacks.eq_bot_of_le_sectionsKernel`: **the vanishing step of Claim 1.** A finitely generated
  ideal `I` contained in every positive power of `J = (g₁, …, g_r) ≠ (1)`, equal to the ideal
  `Ker (I → Γ(U, I/I²))` of Stacks 0ATC, is zero as soon as `U` is scheme theoretically dense.
* `Stacks.flat_of_least_flattening_of_flat_away`: the same statement phrased for the smallest
  flattening ideal of a module, so that its conclusion is flatness of `N` over `A`.
* `Stacks.isNilpotent_of_least_flattening` and
  `Stacks.exists_fg_isNilpotent_flat_quotient_of_least`: **the second paragraph.** A finitely
  generated smallest flattening ideal is nilpotent once every prime of `A` contains some
  flattening ideal, and then it is the ideal `I₀` the paragraph produces.
* `Stacks.not_forall_exists_fg_isNilpotent_flat_quotient`: the counterexample.

## Implementation notes

The open `U = Spec A ∖ V(J)` of the source is presented by a finite family `g : ι → A` with
`J = (g i)`. Three conditions on `U` are then elementary statements about that family: `U` is
quasi-compact because the family is finite; flatness of `N` over `U` is flatness of `N_{g i}`
over `A_{g i}` for each `i`; and *scheme theoretic density* of `U` is injectivity of
`A → ∏ᵢ A_{g i}`, written elementwise as `(∀ i, ∃ n, g i ^ n * x = 0) → x = 0`.

## References

* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 0ATA](https://stacks.math.columbia.edu/tag/0ATA)
* [Stacks Project, Tag 0ATB](https://stacks.math.columbia.edu/tag/0ATB)
* [Stacks Project, Tag 0ATC](https://stacks.math.columbia.edu/tag/0ATC)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks

variable {A : Type u} [CommRing A]

/-- Local idempotency, read on the principal open: if `gⁿx ∈ I²` for every `x ∈ I` and some
`n`, then the extension of `I` to `A_g` is contained in its own square. -/
theorem map_le_sq_of_locally_sq {I : Ideal A} (g : A)
    (hsq : ∀ x ∈ I, ∃ n : ℕ, g ^ n * x ∈ I ^ 2) :
    I.map (algebraMap A (Localization.Away g)) ≤
      I.map (algebraMap A (Localization.Away g)) ^ 2 := by
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  obtain ⟨n, hn⟩ := hsq x hx
  have hu : IsUnit (algebraMap A (Localization.Away g) (g ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow n
  refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ hn

/-- An element killed in the localization at `g` is killed by a power of `g`. -/
private theorem exists_pow_mul_eq_zero_of_map_eq_zero (g x : A)
    (h : algebraMap A (Localization.Away g) x = 0) : ∃ n : ℕ, g ^ n * x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hcx⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp h
  exact ⟨n, hcx⟩

/-- Nakayama on a principal open, elementwise. -/
theorem exists_annihilator_of_locally_sq {I : Ideal A} (hIfg : I.FG) (g : A)
    (hsq : ∀ x ∈ I, ∃ n : ℕ, g ^ n * x ∈ I ^ 2) :
    ∃ (z : A) (k : ℕ), z - g ^ k ∈ I ∧ ∀ x ∈ I, ∃ n : ℕ, g ^ n * (z * x) = 0 := by
  classical
  let L := Localization.Away g
  let K : Ideal L := I.map (algebraMap A L)
  have hKfg : K.FG := hIfg.map _
  have hKle : K ≤ K • K := by
    rw [smul_eq_mul, ← pow_two]
    exact map_le_sq_of_locally_sq g hsq
  obtain ⟨r, hr1, hr2⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul K (K : Submodule L L) hKfg hKle
  obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g) (S := L) r
  obtain ⟨k, hk⟩ := s.2
  have hs' : r * algebraMap A L (g ^ k) = algebraMap A L y := by
    rw [show g ^ k = (s : A) from hk]
    exact hs
  have h1 : algebraMap A L (y - g ^ k) ∈ K := by
    rw [map_sub, ← hs', ← sub_one_mul]
    exact Ideal.mul_mem_right _ _ hr1
  obtain ⟨m, hm, hmI⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g) L I _).mp h1
  obtain ⟨m₀, rfl⟩ := hm
  refine ⟨g ^ m₀ * y, m₀ + k, ?_, ?_⟩
  · rw [show g ^ m₀ * y - g ^ (m₀ + k) = g ^ m₀ * (y - g ^ k) by ring]
    exact hmI
  · intro x hx
    have hrx : r * algebraMap A L x = 0 := hr2 _ (Ideal.mem_map_of_mem _ hx)
    have hyx : algebraMap A L (y * x) = 0 := by
      rw [map_mul, ← hs', mul_right_comm, hrx, zero_mul]
    obtain ⟨n, hcx⟩ := exists_pow_mul_eq_zero_of_map_eq_zero g _ hyx
    exact ⟨n, by rw [show g ^ n * (g ^ m₀ * y * x) = g ^ m₀ * (g ^ n * (y * x)) by ring, hcx,
      mul_zero]⟩


/-- A finite family of elements of a directed union lies in a single member. -/
theorem exists_mem_of_finset_subset_sSup {A : Type u} [CommRing A] {c : Set (Ideal A)}
    (hne : c.Nonempty) (hdir : DirectedOn (· ≤ ·) c) (T : Finset A)
    (hT : ∀ t ∈ T, t ∈ sSup c) : ∃ q ∈ c, ∀ t ∈ T, t ∈ q := by
  classical
  induction T using Finset.induction with
  | empty => obtain ⟨q, hq⟩ := hne; exact ⟨q, hq, by simp⟩
  | @insert a T _ ih =>
      obtain ⟨q, hq, hqT⟩ := ih fun t ht => hT t (Finset.mem_insert_of_mem ht)
      obtain ⟨q', hq', haq'⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp
        (hT a (Finset.mem_insert_self a T))
      obtain ⟨q'', hq''c, hle1, hle2⟩ := hdir q hq q' hq'
      refine ⟨q'', hq''c, fun t ht => ?_⟩
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact hle2 haq'
      · exact hle1 (hqT t ht')

/-- A prime not containing a finitely generated ideal `J` is contained in a prime which is
maximal among the primes not containing `J`. -/
theorem exists_maximal_isPrime_not_le {A : Type u} [CommRing A] {J : Ideal A} (hJfg : J.FG)
    (p : Ideal A) (hp : p.IsPrime) (hpJ : ¬ J ≤ p) :
    ∃ q : Ideal A, q.IsPrime ∧ p ≤ q ∧ ¬ J ≤ q ∧
      ∀ q' : Ideal A, q'.IsPrime → q ≤ q' → ¬ J ≤ q' → q' ≤ q := by
  classical
  obtain ⟨T, hT⟩ := hJfg
  have hub : ∀ c ⊆ {q : Ideal A | q.IsPrime ∧ ¬ J ≤ q}, IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ {q : Ideal A | q.IsPrime ∧ ¬ J ≤ q}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hchain.directedOn
    have hJsup : ¬ J ≤ sSup c := by
      intro hJle
      obtain ⟨q, hqc, hqT⟩ := exists_mem_of_finset_subset_sSup hne hdir T
        fun t ht => hJle (hT ▸ Ideal.subset_span ht)
      exact (hc hqc).2 (hT ▸ (Ideal.span_le.mpr fun t ht => hqT t ht))
    refine ⟨sSup c, ⟨⟨?_, ?_⟩, hJsup⟩, fun z hz => le_sSup hz⟩
    · intro htop
      exact hJsup (htop ▸ le_top)
    · intro a b hab
      obtain ⟨q, hqc, habq⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hab
      rcases (hc hqc).1.mem_or_mem habq with h | h
      · exact Or.inl (le_sSup hqc h)
      · exact Or.inr (le_sSup hqc h)
  obtain ⟨q, hpq, hmax⟩ := zorn_le_nonempty₀ {q : Ideal A | q.IsPrime ∧ ¬ J ≤ q} hub p ⟨hp, hpJ⟩
  exact ⟨q, hmax.1.1, hpq, hmax.1.2, fun q' hq' hle hnle => hmax.2 ⟨hq', hnle⟩ hle⟩

/-- A prime maximal among the primes not containing `J` is a closed point of the open
`Spec A ∖ V(J)`. -/
theorem isClosed_singleton_of_maximal {A : Type u} [CommRing A] {J : Ideal A} {q : Ideal A}
    (_ : q.IsPrime) (_ : ¬ J ≤ q)
    (hmax : ∀ q' : Ideal A, q'.IsPrime → q ≤ q' → ¬ J ≤ q' → q' ≤ q)
    (x : ((PrimeSpectrum.zeroLocus (J : Set A))ᶜ : Set (PrimeSpectrum A)))
    (hx : x.val.asIdeal = q) : IsClosed ({x} : Set _) := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
  rw [closure_subtype] at hy
  simp only [Set.image_singleton] at hy
  have hle : x.val ≤ y.val := (PrimeSpectrum.le_iff_mem_closure x.val y.val).mpr hy
  have hyJ : ¬ J ≤ y.val.asIdeal := fun h => y.property ((PrimeSpectrum.mem_zeroLocus _ _).mpr h)
  have h1 : q ≤ y.val.asIdeal := hx ▸ hle
  have h2 : y.val.asIdeal ≤ q := hmax _ y.val.isPrime h1 hyJ
  have : y.val.asIdeal = x.val.asIdeal := by rw [hx]; exact le_antisymm h2 h1
  exact Set.mem_singleton_iff.mpr (Subtype.ext (PrimeSpectrum.ext this))

/-- Every prime of the open `Spec A ∖ V(J)` contains `I`. -/
theorem le_of_not_le_of_le_pow {A : Type u} [CommRing A] [IsLocalRing A] {ι : Type v} [Finite ι]
    (g : ι → A) {I : Ideal A} (hIfg : I.FG)
    (hJtop : Ideal.span (Set.range g) ≠ ⊤)
    (hIpow : ∀ n : ℕ, 0 < n → I ≤ Ideal.span (Set.range g) ^ n)
    (hsq : ∀ x ∈ I, ∀ i, ∃ n : ℕ, g i ^ n * x ∈ I ^ 2)
    (p : Ideal A) (hp : p.IsPrime) (hpJ : ¬ Ideal.span (Set.range g) ≤ p) : I ≤ p := by
  classical
  set J : Ideal A := Ideal.span (Set.range g) with hJ
  have hJfg : J.FG := Submodule.fg_span (Set.finite_range g)
  obtain ⟨q, hq, hpq, hqJ, hmax⟩ := exists_maximal_isPrime_not_le hJfg p hp hpJ
  have hqU : (⟨q, hq⟩ : PrimeSpectrum A) ∈
      ((PrimeSpectrum.zeroLocus (J : Set A))ᶜ : Set (PrimeSpectrum A)) := by
    simpa [PrimeSpectrum.mem_zeroLocus] using hqJ
  have hIq : I ≤ q := by
    have hmem := PrimeSpectrum.closedPoints_compl_zeroLocus_subset_zeroLocus I J hJtop hJfg hIpow
      (Set.mem_image_of_mem Subtype.val
        (show (⟨⟨q, hq⟩, hqU⟩ : ((PrimeSpectrum.zeroLocus (J : Set A))ᶜ :
            Set (PrimeSpectrum A))) ∈ closedPoints _ from
          isClosed_singleton_of_maximal hq hqJ hmax ⟨⟨q, hq⟩, hqU⟩ rfl))
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hmem
  obtain ⟨i, hgi⟩ : ∃ i, g i ∉ q := by
    by_contra hcon
    push Not at hcon
    exact hqJ (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i))
  obtain ⟨z, k, hz, hzx⟩ := exists_annihilator_of_locally_sq hIfg (g i) fun x hx => hsq x hx i
  have hzq : z ∉ q := by
    intro hzmem
    refine hgi (hq.mem_of_pow_mem k ?_)
    rw [show g i ^ k = z - (z - g i ^ k) by ring]
    exact Ideal.sub_mem _ hzmem (hIq hz)
  intro x hx
  obtain ⟨n, hn⟩ := hzx x hx
  have h0 : g i ^ n * (z * x) ∈ p := hn ▸ p.zero_mem
  exact (hp.mem_or_mem ((hp.mem_or_mem h0).resolve_left fun h =>
    hgi (hpq (hp.mem_of_pow_mem n h)))).resolve_left fun h => hzq (hpq h)

/-- **The smallest flattening ideal of the proof of Stacks 05U9 vanishes.** -/
theorem eq_bot_of_le_sectionsKernel {A : Type u} [CommRing A] [IsLocalRing A] {ι : Type v}
    [Finite ι] (g : ι → A) (I : Ideal A) (hIfg : I.FG)
    (hJtop : Ideal.span (Set.range g) ≠ ⊤)
    (hIpow : ∀ n : ℕ, 0 < n → I ≤ Ideal.span (Set.range g) ^ n)
    (hsec : I ≤ Stacks.sectionsKernel I g)
    (hdense : ∀ x : A, (∀ i, ∃ n : ℕ, g i ^ n * x = 0) → x = 0) :
    I = ⊥ := by
  classical
  have hsq : ∀ x ∈ I, ∀ i, ∃ n : ℕ, g i ^ n * x ∈ I ^ 2 := fun x hx =>
    ((Stacks.mem_sectionsKernel_iff I g x).mp (hsec hx)).2
  have hkey := le_of_not_le_of_le_pow g hIfg hJtop hIpow hsq
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [Submodule.mem_bot]
  refine hdense x fun i => ?_
  set L := Localization.Away (g i) with hL
  set K : Ideal L := I.map (algebraMap A L) with hK
  have hKfg : K.FG := hIfg.map _
  have hKsq : K ≤ K ^ 2 := map_le_sq_of_locally_sq (g i) fun y hy => hsq y hy i
  have hKnil : K ≤ (⊥ : Ideal L).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨-, hP⟩
    have hcomap : (P.comap (algebraMap A L)).IsPrime := hP.comap _
    have hgP : g i ∉ P.comap (algebraMap A L) := fun h => hP.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit (S := L) (g i)))
    exact Ideal.map_le_iff_le_comap.mpr
      (hkey _ hcomap fun h => hgP (h (Ideal.subset_span ⟨i, rfl⟩)))
  have hKbot : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot K K hKfg
    (by rwa [smul_eq_mul, ← pow_two]) (hKnil.trans Ideal.radical_le_jacobson)
  have hx0 : algebraMap A L x = 0 := by
    have : algebraMap A L x ∈ K := Ideal.mem_map_of_mem _ hx
    rwa [hKbot, Submodule.mem_bot] at this
  exact exists_pow_mul_eq_zero_of_map_eq_zero (g i) x hx0

/-- Flatness over `A` read off flatness over `A ⧸ ⊥`. -/
theorem flat_of_flat_quotient_bot {A : Type u} [CommRing A] {N : Type w} [AddCommGroup N]
    [Module A N]
    (h : Module.Flat (A ⧸ (⊥ : Ideal A)) (N ⧸ ((⊥ : Ideal A) • (⊤ : Submodule A N)))) :
    Module.Flat A N := by
  have hquot : Module.Flat A (A ⧸ (⊥ : Ideal A)) :=
    Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule A A) rfl)
  have htr : Module.Flat A (N ⧸ ((⊥ : Ideal A) • (⊤ : Submodule A N))) :=
    Module.Flat.trans A (A ⧸ (⊥ : Ideal A)) (N ⧸ ((⊥ : Ideal A) • (⊤ : Submodule A N)))
  exact Module.Flat.of_linearEquiv
    (Submodule.quotEquivOfEqBot ((⊥ : Ideal A) • (⊤ : Submodule A N))
      (Submodule.bot_smul _)).symm

/-- **The inner step of Claim 1 of the proof of Stacks 05U9.** -/
theorem flat_of_least_flattening_of_flat_away {A : Type u} [CommRing A] [IsLocalRing A]
    {N : Type w} [AddCommGroup N] [Module A N] {ι : Type v} [Finite ι] (g : ι → A)
    (hJtop : Ideal.span (Set.range g) ≠ ⊤)
    (I : Ideal A) (hIfg : I.FG)
    (hI : ∀ K : Ideal A, Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N))) ↔ I ≤ K)
    (hU : ∀ i, Module.Flat (Localization.Away (g i))
      (Localization.Away (g i) ⊗[A] N))
    (hpow : ∀ n : ℕ, 0 < n → Module.Flat (A ⧸ Ideal.span (Set.range g) ^ n)
      (N ⧸ ((Ideal.span (Set.range g) ^ n) • (⊤ : Submodule A N))))
    (hdense : ∀ x : A, (∀ i, ∃ n : ℕ, g i ^ n * x = 0) → x = 0) :
    Module.Flat A N := by
  have hIflat : Module.Flat (A ⧸ I) (N ⧸ (I • (⊤ : Submodule A N))) := (hI I).mpr le_rfl
  have hIpow : ∀ n : ℕ, 0 < n → I ≤ Ideal.span (Set.range g) ^ n := fun n hn =>
    (hI _).mp (hpow n hn)
  have hsec : I ≤ sectionsKernel I g := (hI _).mp (flat_quotient_sectionsKernel I g hIflat hU)
  have hIbot : I = ⊥ := eq_bot_of_le_sectionsKernel g I hIfg hJtop hIpow hsec hdense
  rw [hIbot] at hIflat
  exact flat_of_flat_quotient_bot hIflat

/-- **Paragraph two of the proof of Stacks 05U9.** -/
theorem isNilpotent_of_least_flattening {A : Type u} [CommRing A] {N : Type w} [AddCommGroup N]
    [Module A N] (I : Ideal A) (hIfg : I.FG)
    (hI : ∀ K : Ideal A, Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N))) → I ≤ K)
    (hcover : ∀ p : Ideal A, p.IsPrime → ∃ K : Ideal A, K ≤ p ∧
      Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N)))) :
    IsNilpotent I := by
  rw [hIfg.isNilpotent_iff_le_nilradical, nilradical_eq_sInf]
  refine le_sInf fun p hp => ?_
  obtain ⟨K, hKp, hK⟩ := hcover p hp
  exact (hI K hK).trans hKp

/-- **The conclusion of the second paragraph of the proof of Stacks 05U9.** -/
theorem exists_fg_isNilpotent_flat_quotient_of_least {A : Type u} [CommRing A] {N : Type w}
    [AddCommGroup N] [Module A N] (I : Ideal A) (hIfg : I.FG)
    (hI : ∀ K : Ideal A, Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N))) ↔ I ≤ K)
    (hcover : ∀ p : Ideal A, p.IsPrime → ∃ K : Ideal A, K ≤ p ∧
      Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N)))) :
    ∃ J : Ideal A, J.FG ∧ IsNilpotent J ∧
      Module.Flat (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N))) :=
  ⟨I, hIfg, isNilpotent_of_least_flattening I hIfg (fun K hK => (hI K).mp hK) hcover,
    (hI I).mpr le_rfl⟩

/-- **The conclusion of the second paragraph of the proof of Stacks 05U9 fails for `N` alone.**
There are a local ring `A`, a localization `B` of a finitely presented `A`-algebra with `A → B`
local, and a finitely presented `B`-module `N` such that no finitely generated nilpotent ideal
`I ⊆ A` makes `N ⧸ IN` flat over `A ⧸ I`. -/
theorem not_forall_exists_fg_isNilpotent_flat_quotient :
    ¬ ∀ (A : Type) [CommRing A] [IsLocalRing A]
        (B₀ : Type) [CommRing B₀] [Algebra A B₀] [Algebra.FinitePresentation A B₀]
        (B : Type) [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra B₀ B]
        [IsScalarTower A B₀ B] [IsLocalHom (algebraMap A B)]
        (W : Submonoid B₀) [IsLocalization W B]
        (N : Type) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
        [Module.FinitePresentation B N],
      ∃ I : Ideal A, I.FG ∧ IsNilpotent I ∧
        Module.Flat (A ⧸ I) (N ⧸ (I • (⊤ : Submodule A N))) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := ℤ_[2]
  let P : Ideal A := Ideal.span {((2 : ℕ) : A)}
  let N := A ⧸ P
  have : Module.FinitePresentation A N := Module.finitePresentation_of_finite _ _
  have : IsLocalization (IsUnit.submonoid A) A := IsLocalization.self le_rfl
  obtain ⟨I, hfg, hnil, hflat⟩ := h A A A (IsUnit.submonoid A) N
  have hPtop : P ≠ ⊤ := by
    have hP : P = IsLocalRing.maximalIdeal A := PadicInt.maximalIdeal_eq_span_p.symm
    rw [hP]
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hIbot : I = ⊥ := by
    obtain ⟨n, hn⟩ := hnil
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxn : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hxn
    have hx0 : x ^ n = 0 := by simpa using hxn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hx0
    · exact (pow_eq_zero_iff hpos.ne').mp hx0
  subst hIbot
  have h2 : ((2 : ℕ) : A) ≠ 0 := by simp
  have h2' : (Ideal.Quotient.mk (⊥ : Ideal A) (((2 : ℕ) : A))) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  have hreg :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (M := N ⧸ ((⊥ : Ideal A) • (⊤ : Submodule A N)))
      (mem_nonZeroDivisors_of_ne_zero h2')
  set x : N ⧸ ((⊥ : Ideal A) • (⊤ : Submodule A N)) :=
    Submodule.Quotient.mk (p := ((⊥ : Ideal A) • (⊤ : Submodule A N)))
      (Ideal.Quotient.mk P 1) with hxdef
  have h21 : ((2 : ℕ) : A) • (Ideal.Quotient.mk P 1 : N) = 0 := by
    show Ideal.Quotient.mk P (((2 : ℕ) : A) * 1) = 0
    rw [mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hsmul : (Ideal.Quotient.mk (⊥ : Ideal A) (((2 : ℕ) : A))) • x = 0 := by
    rw [hxdef, Module.Quotient.mk_smul_mk, h21]
    exact Submodule.Quotient.mk_zero _
  have hx0 : x = 0 := hreg (by simpa using hsmul)
  rw [hxdef, Submodule.Quotient.mk_eq_zero, Submodule.bot_smul, Submodule.mem_bot] at hx0
  exact hPtop (Ideal.eq_top_of_isUnit_mem P (Ideal.Quotient.eq_zero_iff_mem.mp hx0) isUnit_one)

end Stacks

end

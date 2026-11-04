module

public import Mathlib.Data.Set.Card
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.ApproximationProperty.Approx
public import StacksFrontier.RingTheory.ApproximationProperty.Basic
public import StacksFrontier.RingTheory.ApproximationProperty.CertificateSolution
public import StacksFrontier.RingTheory.Derivation.Regularity

/-!
# The core of Rotthaus' theorem

Let `B` be a Noetherian local domain with the approximation property and `B^∧` its completion.
This file proves that for every prime `P` of `B^∧` with `P ∩ B = 0` the local ring `B^∧_P` is
regular (Rotthaus, Claim (3.2)), given a presentation `ρ : R ↠ B^∧` by a complete regular local
ring `R` which is a filtered colimit of smooth algebras over a ring `R₀` mapping compatibly to `B`
and containing elements whose images generate an ideal primary to the maximal ideal of `R` (such
a presentation exists by the Cohen structure theorem and Popescu's theorem).

The proof is Rotthaus' (Sections 2 and 3). Suppose the claim fails. The singular locus of the
complete local ring `B^∧` is closed (complete local rings are J-2), so it is the zero locus of an
ideal, with finitely many minimal primes. Choose a singular prime `𝔭` with `𝔭 ∩ B = 0` of maximal
coheight `k_v`, and `c ∈ B ∖ 0` lying in every minimal singular prime of larger coheight (these
meet `B`). Encode `𝔭` by a solution in `R` of the certificate system over `R₀`, approximate this
solution by solutions whose values lie in `B` modulo `ker ρ` (the approximation property, through
the ind-smoothness of `R` over `R₀`), and read off from each approximation a minimal singular
prime of coheight `k_v` meeting `B`. Infinitely many approximations give the same prime `𝔓'`,
and Krull's intersection theorem gives `𝔭 ⊆ 𝔓'`, hence `𝔭 = 𝔓'`, a contradiction.

## Implementation notes

The argument departs from Rotthaus' text in the following points, none of which changes the
statement.

* Instead of her equations (2.1), which force the approximated generators of `𝔮 = ker ρ` to
  generate `𝔮`, the approximations are taken congruent to the true solution modulo
  `𝔮 ∩ 𝔪_R ^ n` (a lift along the henselian pair `(R, 𝔮 ∩ 𝔪_R ^ n)`); Artin–Rees and Nakayama then
  show that they generate `𝔮`.
* The prime is an associated prime of the ideal of the `V`'s containing the annihilator of `S`,
  instead of a primary component, and unmixedness in the Cohen–Macaulay ring `R` gives its
  coheight.
* The singularity relations are indexed by the sets of `ht 𝔮` generators of `𝔮` rather than by
  permutations, and a prime of maximal coheight replaces one of minimal height.
* Her Theorem 2 (a power series ring over an excellent discrete valuation ring is a filtered
  colimit of smooth algebras) is replaced by Popescu's theorem applied to `ℤ[X] → Λ[[X]]`.

## Main results

* `Stacks.ApproximationProperty.isRegularLocalRing_localization_of_presentation`: the claim, given
  the presentation.

## References

* [C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466][Rotthaus]
* [Stacks Project, Tag 07PJ](https://stacks.math.columbia.edu/tag/07PJ)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.ApproximationProperty

open Certificate

/-- The local ring of a commutative ring at the prime `⊥` (when it is prime) is regular: it is a
field. -/
theorem isRegularLocalRing_localization_of_eq_bot {A : Type u} [CommRing A] (P : Ideal A)
    [P.IsPrime] (hP : P = ⊥) : IsRegularLocalRing (Localization.AtPrime P) := by
  have hmax : maximalIdeal (Localization.AtPrime P) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact (congrArg (Ideal.map _) hP).trans Ideal.map_bot
  have hfield : IsField (Localization.AtPrime P) := (isField_iff_maximalIdeal_eq).2 hmax
  let := hfield.toField
  infer_instance

/-- The dimension of a Noetherian local ring is a natural number. -/
theorem exists_natCast_eq_ringKrullDim (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : ∃ n : ℕ, ringKrullDim R = n := by
  have hne : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have hlt : ringKrullDim R < ⊤ := ringKrullDim_lt_top
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← hm] at hlt
  have hm' : m ≠ ⊤ := by
    rintro rfl
    exact lt_irrefl _ hlt
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hm'
  exact ⟨n, hm.symm⟩

/-- The coheight `dim R/P` of a prime `P` of a Noetherian local ring is a natural number. -/
theorem exists_natCast_eq_ringKrullDim_quotient {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] : ∃ n : ℕ, ringKrullDim (R ⧸ P) = n := by
  have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have : IsLocalRing (R ⧸ P) := .of_surjective' _ Ideal.Quotient.mk_surjective
  exact exists_natCast_eq_ringKrullDim (R ⧸ P)

/-- Coheights decrease along inclusions of primes in a Noetherian local ring. -/
theorem ringKrullDim_quotient_le_of_le {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {P P' : Ideal R} [P.IsPrime] [P'.IsPrime] (h : P ≤ P') :
    ringKrullDim (R ⧸ P') ≤ ringKrullDim (R ⧸ P) := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (ringKrullDim_quotient_lt_of_lt h).le

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B]

/-- The completion of `B`. -/
local notation "Bh" => AdicCompletion (maximalIdeal B) B

/-- The completion map of `B`. -/
local notation "ι" => algebraMap B (AdicCompletion (maximalIdeal B) B)

/-- **The core of Rotthaus' theorem, given a presentation** (Rotthaus, Claim (3.2)). Let `B` be a
Noetherian local domain with the approximation property, let `ρ : R ↠ B^∧` be a surjection from a
complete regular local ring which is a filtered colimit of smooth `R₀`-algebras, compatible with a
ring map `R₀ → B`, and let `y_1, …, y_e ∈ R₀` have images in `𝔪_R` generating an ideal primary to
`𝔪_R`. Then for every prime `P` of `B^∧` with `P ∩ B = 0`, the local ring `B^∧_P` is regular. -/
theorem isRegularLocalRing_localization_of_presentation
    (hB : IsLocalRing.HasApproximationProperty B)
    {R₀ R : Type u} [CommRing R₀] [CommRing R] [IsRegularLocalRing R] [Algebra R₀ R]
    [Algebra R₀ B] [IsAdicComplete (maximalIdeal R) R] (hind : Stacks.Smoothing.IndSmooth R₀ R)
    (ρ : R →+* AdicCompletion (maximalIdeal B) B) (hρ : Function.Surjective ρ)
    (hcompat : ρ.comp (algebraMap R₀ R) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp (algebraMap R₀ B))
    {e : ℕ} (y : Fin e → R₀) (hy𝔪 : ∀ i, algebraMap R₀ R (y i) ∈ maximalIdeal R)
    (hy : ∃ N : ℕ, maximalIdeal R ^ N ≤ Ideal.span (Set.range (algebraMap R₀ R ∘ y)))
    (P₀ : Ideal (AdicCompletion (maximalIdeal B) B)) [P₀.IsPrime]
    (hP₀ : P₀.comap (algebraMap B (AdicCompletion (maximalIdeal B) B)) = ⊥) :
    IsRegularLocalRing (Localization.AtPrime P₀) := by
  classical
  by_contra hsing₀
  -- If `B` is a field, so is `B^∧`, and every local ring of it is regular.
  by_cases hfield : maximalIdeal B = ⊥
  · have hmaxBh : maximalIdeal Bh = ⊥ := by
      rw [AdicCompletion.maximalIdeal_eq_map, hfield, Ideal.map_bot]
    exact hsing₀ (isRegularLocalRing_localization_of_eq_bot P₀
      (le_bot_iff.1 (hmaxBh ▸ le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))))
  -- `B^∧` is a domain, so `𝔮 = ker ρ` is prime.
  have : IsDomain Bh := hB.isDomain_adicCompletion
  have hqprime : (RingHom.ker ρ).IsPrime := RingHom.ker_isPrime ρ
  have hker𝔪 : RingHom.ker ρ ≤ maximalIdeal R := le_maximalIdeal (RingHom.ker_ne_top ρ)
  obtain ⟨a, q, hq⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (RingHom.ker ρ))
  have hq' : Ideal.span (Set.range q) = (RingHom.ker ρ) := hq
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℕ∞) = (RingHom.ker ρ).height :=
    ⟨(RingHom.ker ρ).height.toNat, ENat.natCast_toNat (Ideal.height_ne_top (RingHom.ker_ne_top ρ))⟩
  -- The dimension of `R`.
  obtain ⟨d, hdR⟩ := exists_natCast_eq_ringKrullDim R
  -- The singular locus of `B^∧` is closed (complete local rings are J-2).
  have hJ2 : IsJ2 Bh := (isJ2_of_standard_classes_and_finiteType.{u, u}).2.1 Bh
  have hJ1 : IsJ1 Bh := hJ2 Bh
  obtain ⟨Jh, hJh⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hJ1.isClosed_compl
  have hsingJh : ∀ (Q : Ideal Bh) [Q.IsPrime],
      ¬ IsRegularLocalRing (Localization.AtPrime Q) ↔ Jh ≤ Q := by
    intro Q _
    simpa [PrimeSpectrum.mem_zeroLocus] using
      congrArg (fun s : Set (PrimeSpectrum Bh) => (⟨Q, inferInstance⟩ : PrimeSpectrum Bh) ∈ s) hJh
  set J' := Jh.comap ρ
  have hkerJ' : RingHom.ker ρ ≤ J' := Ideal.ker_le_comap ρ
  have hsing : ∀ (P : Ideal R) [P.IsPrime] (hP : RingHom.ker ρ ≤ P),
      IsSingularPoint ρ hρ P hP ↔ J' ≤ P := by
    intro P _ hP
    let := Ideal.map_isPrime_of_surjective hρ hP
    change ¬ IsRegularLocalRing (Localization.AtPrime (P.map ρ)) ↔ _
    rw [hsingJh]
    constructor
    · intro h
      calc J' ≤ (P.map ρ).comap ρ := Ideal.comap_mono h
        _ = P := by rw [Ideal.comap_map_of_surjective' ρ hρ, sup_eq_left.2 hP]
    · intro h
      calc Jh = J'.map ρ := (Ideal.map_comap_of_surjective ρ hρ Jh).symm
        _ ≤ P.map ρ := Ideal.map_mono h
  -- The bad primes: singular, with trivial intersection with `B`.
  let Bad : Ideal R → Prop := fun P =>
    ∃ (_ : P.IsPrime), RingHom.ker ρ ≤ P ∧ J' ≤ P ∧ (P.map ρ).comap ι = ⊥
  have hbad₀ : Bad (P₀.comap ρ) := by
    refine ⟨inferInstance, Ideal.ker_le_comap ρ, Ideal.comap_mono ((hsingJh P₀).1 hsing₀), ?_⟩
    rwa [Ideal.map_comap_of_surjective ρ hρ]
  -- A bad prime of maximal coheight.
  let coh : Set ℕ := {n | ∃ P, Bad P ∧ ringKrullDim (R ⧸ P) = n}
  have hcoh_ne : coh.Nonempty := by
    obtain ⟨n, hn⟩ := exists_natCast_eq_ringKrullDim_quotient (P₀.comap ρ)
    exact ⟨n, P₀.comap ρ, hbad₀, hn⟩
  have hcoh_bdd : BddAbove coh := by
    refine ⟨d, fun n ⟨P, _, hn⟩ => ?_⟩
    have := ringKrullDim_quotient_le P
    rw [hn, hdR] at this
    exact_mod_cast this
  obtain ⟨𝔭, ⟨h𝔭prime, hker𝔭, hJ𝔭, h𝔭B⟩, hcoh𝔭⟩ := Nat.sSup_mem hcoh_ne hcoh_bdd
  set kv := sSup coh
  have hmaxcoh : ∀ P, Bad P → ∀ n : ℕ, ringKrullDim (R ⧸ P) = n → n ≤ kv :=
    fun P hP n hn => le_csSup hcoh_bdd ⟨P, hP, hn⟩
  -- The height of `𝔭`.
  obtain ⟨l, hl⟩ : ∃ l : ℕ, 𝔭.height = l :=
    ⟨𝔭.height.toNat, (ENat.natCast_toNat (Ideal.height_ne_top (Ideal.IsPrime.ne_top h𝔭prime))).symm⟩
  have hdim𝔭 : ringKrullDim R = (l + kv : ℕ) := by
    rw [ringKrullDim_eq_height_add_ringKrullDim_quotient_of_isRegularLocalRing 𝔭, hl, hcoh𝔭]
    push_cast
    rfl
  -- `𝔭` is not the maximal ideal, since `B` is not a field.
  have hkv : 0 < kv := by
    refine Nat.pos_of_ne_zero fun h0' => ?_
    have hmax : 𝔭 = maximalIdeal R := by
      have : 𝔭 ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top h𝔭prime)
      refine eq_of_le_of_ringKrullDim_quotient_eq this ?_
      rw [hcoh𝔭, h0']
      have : IsField (R ⧸ maximalIdeal R) := Ideal.Quotient.maximal_ideal_iff_isField_quotient _
        |>.1 inferInstance
      let := this.toField
      simp
    apply hfield
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ (𝔭.map ρ).comap ι := by
      rw [Ideal.mem_comap, hmax, IsLocalRing.map_maximalIdeal_of_surjective ρ hρ,
        AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ hx
    rwa [h𝔭B] at hx'
  obtain ⟨kz, hkz⟩ : ∃ kz, kv = kz + 1 := ⟨kv - 1, by omega⟩
  -- The minimal singular primes of larger coheight meet `B`; `c` lies in all of them.
  have hfin : (J'.minimalPrimes).Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing R J'
  have hbig : ∀ 𝔯 ∈ J'.minimalPrimes, ∀ n : ℕ, ringKrullDim (R ⧸ 𝔯) = n → kv < n →
      ∃ b : B, b ≠ 0 ∧ ι b ∈ 𝔯.map ρ := by
    intro 𝔯 h𝔯 n hn hlt
    have h𝔯prime : 𝔯.IsPrime := h𝔯.1.1
    by_contra hcon
    push Not at hcon
    have hbot : (𝔯.map ρ).comap ι = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      by_contra hb0
      exact hcon b hb0 hb
    have := hmaxcoh 𝔯 ⟨h𝔯prime, hkerJ'.trans h𝔯.1.2, h𝔯.1.2, hbot⟩ n hn
    omega
  have hbig' : ∀ 𝔯 : Ideal R, ∃ b : B, b ≠ 0 ∧ (𝔯 ∈ J'.minimalPrimes →
      (∃ n : ℕ, ringKrullDim (R ⧸ 𝔯) = n ∧ kv < n) → ι b ∈ 𝔯.map ρ) := by
    intro 𝔯
    by_cases h : 𝔯 ∈ J'.minimalPrimes ∧ ∃ n : ℕ, ringKrullDim (R ⧸ 𝔯) = n ∧ kv < n
    · obtain ⟨h𝔯, n, hn, hlt⟩ := h
      obtain ⟨b, hb0, hb⟩ := hbig 𝔯 h𝔯 n hn hlt
      exact ⟨b, hb0, fun _ _ => hb⟩
    · exact ⟨1, one_ne_zero, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose bsel hbsel0 hbsel using hbig'
  let c : B := ∏ 𝔯 ∈ hfin.toFinset, bsel 𝔯
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun 𝔯 _ => hbsel0 𝔯
  obtain ⟨c₀, hc₀⟩ := hρ (ι c)
  have hc₀big : ∀ 𝔯 ∈ J'.minimalPrimes, ∀ n : ℕ, ringKrullDim (R ⧸ 𝔯) = n → kv < n →
      c₀ ∈ 𝔯 := by
    intro 𝔯 h𝔯 n hn hlt
    have h𝔯prime : 𝔯.IsPrime := h𝔯.1.1
    have hmem : ι c ∈ 𝔯.map ρ := by
      obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem bsel (hfin.mem_toFinset.2 h𝔯)
      change ι (∏ 𝔯 ∈ hfin.toFinset, bsel 𝔯) ∈ _
      rw [ht, map_mul]
      exact Ideal.mul_mem_right _ _ (hbsel 𝔯 h𝔯 ⟨n, hn, hlt⟩)
    have : c₀ ∈ (𝔯.map ρ).comap ρ := by rwa [Ideal.mem_comap, hc₀]
    rwa [Ideal.comap_map_of_surjective' ρ hρ, sup_eq_left.2 (hkerJ'.trans h𝔯.1.2)] at this
  have hc₀𝔭 : c₀ ∉ 𝔭 := by
    intro h
    apply hc0
    have : c ∈ (𝔭.map ρ).comap ι := by
      rw [Ideal.mem_comap, ← hc₀]
      exact Ideal.mem_map_of_mem _ h
    rwa [h𝔭B] at this
  -- The true solution of the certificate system.
  have hsing𝔭 : IsSingularPoint ρ hρ 𝔭 hker𝔭 := (hsing 𝔭 hker𝔭).2 hJ𝔭
  have hdim' : ringKrullDim R = (l + (kz + 1) : ℕ) := by rw [hdim𝔭, hkz]
  obtain ⟨cc, N, pick, p₀, hp₀, hpick, hp₀q, hp₀span, hp₀S, hp₀C, hp₀Lv, hp₀Lz⟩ :=
    exists_solution ρ hρ q hq' hr y hy𝔪 𝔭 hker𝔭 hsing𝔭 hl hdim' c₀ hc₀𝔭
  let sh : Shape := ⟨a, l, cc, kz + 1, kz, e, r, N, pick⟩
  -- The approximations of the true solution.
  let τ : Alg sh y →ₐ[R₀] R := lift sh y p₀ hp₀
  have hτ : ∀ v, τ (Ideal.Quotient.mk _ (MvPolynomial.X v)) = p₀ v := lift_mk_X sh y p₀ hp₀
  let eE : Fin (a + 1) → Alg sh y :=
    Fin.snoc (fun i => Ideal.Quotient.mk _ (MvPolynomial.X (Var.Q (.inl i))))
      (Ideal.Quotient.mk _ (MvPolynomial.X Var.C))
  let bE : Fin (a + 1) → B := Fin.snoc (fun _ => 0) c
  have hqker : ∀ i, q i ∈ (RingHom.ker ρ) := fun i => hq' ▸ Ideal.subset_span ⟨i, rfl⟩
  have hbE : ∀ i, ρ (τ (eE i)) = ι (bE i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [eE, bE, Fin.snoc_last, hτ]
      rw [hp₀C, hc₀]
    · simp only [eE, bE, Fin.snoc_castSucc, hτ, map_zero]
      rw [hp₀q]
      exact (RingHom.mem_ker).1 (hqker j)
  choose φ hφclose hφB hφe using fun n : ℕ => exists_algHom_approx
    (fun E _ _ _ f _ x N => hB.exists_algHom_sub_mem f x N) hind ρ hρ hcompat τ eE bE hbE n
  let pn : ℕ → Var sh → R := fun n => eval sh y (φ n)
  have hpn_rel : ∀ n k, rel sh y (pn n) k = 0 := fun n k => rel_eval sh y (φ n) k
  have hpn_close : ∀ n v, pn n v - p₀ v ∈ maximalIdeal R ^ n := by
    intro n v
    have h := hφclose n (Ideal.Quotient.mk _ (MvPolynomial.X v))
    rwa [hτ] at h
  have hpn_q : ∀ n i, pn n (.Q (.inl i)) ∈ (RingHom.ker ρ) := by
    intro n i
    have h := hφe n (Fin.castSucc i)
    simp only [eE, bE, Fin.snoc_castSucc, map_zero] at h
    exact (RingHom.mem_ker).2 h
  have hpn_C : ∀ n, ρ (pn n .C) = ι c := by
    intro n
    have h := hφe n (Fin.last a)
    simp only [eE, bE, Fin.snoc_last] at h
    exact h
  have hpn_B : ∀ n v, ∃ b : B, ρ (pn n v) = ι b := fun n v => hφB n _
  have hp₀𝔭 : ∀ σ, p₀ (.Q σ) ∈ 𝔭 := fun σ => hp₀span ▸ Ideal.subset_span ⟨σ, rfl⟩
  -- Membership in `𝔭 + 𝔪ⁿ` of the approximated generators.
  have hpn𝔭 : ∀ n σ, pn n (.Q σ) ∈ 𝔭 ⊔ maximalIdeal R ^ n := by
    intro n σ
    have := Submodule.add_mem_sup (hp₀𝔭 σ) (hpn_close n (.Q σ))
    rwa [add_sub_cancel] at this
  -- Threshold 1 (Artin–Rees and Nakayama): the approximated generators of `𝔮` generate `𝔮`.
  obtain ⟨k₀, hk₀⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := R) (maximalIdeal R) (RingHom.ker ρ)
  have hgen : ∀ n, k₀ + 1 ≤ n →
      Ideal.span (Set.range fun i => pn n (.Q (qIdx sh i))) = (RingHom.ker ρ) := by
    intro n hn
    have hAR : maximalIdeal R ^ n ⊓ RingHom.ker ρ ≤ maximalIdeal R • (RingHom.ker ρ) := by
      have h := hk₀ n (by omega)
      simp only [smul_eq_mul, Ideal.mul_top] at h
      change maximalIdeal R ^ n ⊓ RingHom.ker ρ ≤ maximalIdeal R * (RingHom.ker ρ)
      rw [h]
      exact Ideal.mul_mono (Ideal.pow_le_self (by omega)) inf_le_right
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hpn_q n i
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian (RingHom.ker ρ))
        (IsLocalRing.maximalIdeal_le_jacobson _) (hq'.symm.le.trans (Ideal.span_le.2 ?_))
      rintro _ ⟨i, rfl⟩
      have hd : q i - pn n (.Q (.inl i)) ∈ maximalIdeal R ^ n ⊓ (RingHom.ker ρ) := by
        refine ⟨?_, (RingHom.ker ρ).sub_mem (hqker i) (hpn_q n i)⟩
        rw [← neg_sub, ← hp₀q i]
        exact (maximalIdeal R ^ n).neg_mem (hpn_close n _)
      have := Submodule.add_mem_sup (Ideal.subset_span ⟨i, rfl⟩ :
        pn n (.Q (qIdx sh i)) ∈ Ideal.span (Set.range fun i => pn n (.Q (qIdx sh i))))
        (hAR hd)
      rwa [add_sub_cancel] at this
  -- Threshold 2: `S` stays outside the ideal of the approximated `V`'s.
  have hSthr : ∃ N₁, ∀ n ≥ N₁,
      pn n .S ∉ Ideal.span (Set.range fun i => pn n (.Q (vIdx sh i))) := by
    by_contra hcon
    push Not at hcon
    apply hp₀S
    refine mem_of_frequently_mem_sup_pow 𝔭 fun M => ?_
    obtain ⟨n, hn, hmem⟩ := hcon M
    refine ⟨n, hn, ?_⟩
    have hle : Ideal.span (Set.range fun i => pn n (.Q (vIdx sh i))) ≤
        𝔭 ⊔ maximalIdeal R ^ n := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hpn𝔭 n _
    have := Submodule.sub_mem_sup (hle hmem) (hpn_close n .S)
    rwa [sub_sub_cancel, sup_assoc, sup_idem] at this
  obtain ⟨N₁, hN₁⟩ := hSthr
  -- Threshold 3: a generator of `𝔭` outside `𝔮` stays outside `𝔮`.
  have hσ₀ : ∃ σ₀, p₀ (.Q σ₀) ∉ (RingHom.ker ρ) := by
    by_contra hcon
    push Not at hcon
    have hle : 𝔭 ≤ (RingHom.ker ρ) := by
      rw [← hp₀span, Ideal.span_le]
      rintro _ ⟨σ, rfl⟩
      exact hcon σ
    have heq : 𝔭 = (RingHom.ker ρ) := le_antisymm hle hker𝔭
    apply hsing𝔭
    have hbot : 𝔭.map ρ = ⊥ := by
      rw [heq]
      exact (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl
    let := Ideal.map_isPrime_of_surjective hρ hker𝔭
    exact isRegularLocalRing_localization_of_eq_bot _ hbot
  obtain ⟨σ₀, hσ₀⟩ := hσ₀
  have hσthr : ∃ N₂, ∀ n ≥ N₂, pn n (.Q σ₀) ∉ (RingHom.ker ρ) := by
    by_contra hcon
    push Not at hcon
    apply hσ₀
    refine mem_of_frequently_mem_sup_pow (RingHom.ker ρ) fun M => ?_
    obtain ⟨n, hn, hmem⟩ := hcon M
    refine ⟨n, hn, ?_⟩
    have := Submodule.sub_mem_sup hmem (hpn_close n (.Q σ₀))
    rwa [sub_sub_cancel] at this
  obtain ⟨N₂, hN₂⟩ := hσthr
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, N₀ = k₀ + 1 + N₁ + N₂ + 1 := ⟨_, rfl⟩
  -- For `n ≥ N₀` the approximation gives a minimal singular prime of coheight `k_v` meeting `B`
  -- and containing the approximated generators of `𝔭`.
  have hmain : ∀ n, N₀ ≤ n → ∃ 𝔓 : Ideal R, 𝔓 ∈ J'.minimalPrimes ∧
      (∀ σ, pn n (.Q σ) ∈ 𝔓) ∧ ringKrullDim (R ⧸ 𝔓) = kv ∧ (𝔓.map ρ).comap ι ≠ ⊥ := by
    intro n hn
    have hm𝔪 : ∀ v, p₀ v ∈ maximalIdeal R → pn n v ∈ maximalIdeal R := by
      intro v hv
      have h1 : pn n v - p₀ v ∈ maximalIdeal R :=
        Ideal.pow_le_self (by omega) (hpn_close n v)
      have := (maximalIdeal R).add_mem h1 hv
      rwa [sub_add_cancel] at this
    obtain ⟨𝔓, h𝔓prime, hker𝔓, h𝔓Q, h𝔓coh, hT𝔓, hC𝔓, hsing𝔓⟩ :=
      exists_prime_of_rel sh y ρ hρ (pn n) (hpn_rel n) (hgen n (by omega))
        hr hpick (by rw [hdim']) rfl hy
        (hN₁ n (by omega))
        (fun j => hm𝔪 _ (hp₀Lv j)) (fun j => hm𝔪 _ (hp₀Lz j))
    have hcoh𝔓 : ringKrullDim (R ⧸ 𝔓) = kv := by rw [h𝔓coh, hkz]
    refine ⟨𝔓, ?_, h𝔓Q, hcoh𝔓, ?_⟩
    · -- `𝔓` is a minimal prime of `J'`.
      have hJ𝔓 : J' ≤ 𝔓 := (hsing 𝔓 hker𝔓).1 hsing𝔓
      obtain ⟨𝔯, h𝔯, h𝔯le⟩ := Ideal.exists_minimalPrimes_le hJ𝔓
      have h𝔯prime : 𝔯.IsPrime := h𝔯.1.1
      obtain ⟨m, hm⟩ := exists_natCast_eq_ringKrullDim_quotient 𝔯
      have hge : kv ≤ m := by
        have := ringKrullDim_quotient_le_of_le h𝔯le
        rw [hcoh𝔓, hm] at this
        exact_mod_cast this
      rcases eq_or_lt_of_le hge with heq | hlt
      · rwa [← eq_of_le_of_ringKrullDim_quotient_eq h𝔯le (by rw [hm, ← heq, hcoh𝔓])]
      · exfalso
        have hc₀𝔓 : c₀ ∈ 𝔓 := h𝔯le (hc₀big 𝔯 h𝔯 m hm hlt)
        have hdiff : pn n .C - c₀ ∈ RingHom.ker ρ := by
          rw [RingHom.mem_ker, map_sub, hpn_C, hc₀, sub_self]
        have := 𝔓.add_mem (hker𝔓 hdiff) hc₀𝔓
        rw [sub_add_cancel] at this
        exact hC𝔓 this
    · -- `𝔓` meets `B`.
      obtain ⟨b, hb⟩ := hpn_B n (.Q σ₀)
      have hσn := hN₂ n (by omega)
      intro hbot
      have hbmem : b ∈ (𝔓.map ρ).comap ι := by
        rw [Ideal.mem_comap, ← hb]
        exact Ideal.mem_map_of_mem _ (h𝔓Q σ₀)
      rw [hbot, Ideal.mem_bot] at hbmem
      apply hσn
      rw [RingHom.mem_ker, hb, hbmem, map_zero]
  choose 𝔓 h𝔓min h𝔓Q h𝔓coh h𝔓B using hmain
  -- Pigeonhole: infinitely many approximations give the same prime.
  have : Finite J'.minimalPrimes := hfin.to_subtype
  have : Infinite {n : ℕ // N₀ ≤ n} := Set.infinite_coe_iff.2 (Set.Ici_infinite N₀)
  let f : {n : ℕ // N₀ ≤ n} → J'.minimalPrimes := fun n => ⟨𝔓 n.1 n.2, h𝔓min n.1 n.2⟩
  obtain ⟨𝔓', hinf⟩ := Finite.exists_infinite_fiber f
  have hinf' : (Subtype.val '' (f ⁻¹' {𝔓'})).Infinite :=
    (Set.infinite_coe_iff.1 hinf).image Subtype.val_injective.injOn
  have h𝔓'prime : (𝔓' : Ideal R).IsPrime := 𝔓'.2.1.1
  -- Every generator of `𝔭` lies in `𝔓' + 𝔪ⁿ` for infinitely many `n`, hence in `𝔓'`.
  have hle : 𝔭 ≤ 𝔓' := by
    rw [← hp₀span, Ideal.span_le]
    rintro _ ⟨σ, rfl⟩
    refine mem_of_frequently_mem_sup_pow (𝔓' : Ideal R) fun M => ?_
    obtain ⟨n, ⟨⟨n', hn'⟩, hfib, rfl⟩, hlt⟩ := hinf'.exists_gt M
    refine ⟨n', hlt.le, ?_⟩
    have hf : 𝔓 n' hn' = 𝔓' := congrArg Subtype.val hfib
    have := Submodule.sub_mem_sup (hf ▸ h𝔓Q n' hn' σ) (hpn_close n' (.Q σ))
    rwa [sub_sub_cancel] at this
  -- Hence `𝔭 = 𝔓'`, which meets `B`: a contradiction.
  obtain ⟨⟨n', hn'⟩, hfib⟩ := (Set.infinite_coe_iff.1 hinf).nonempty
  have hf : 𝔓 n' hn' = 𝔓' := congrArg Subtype.val hfib
  have heq : 𝔭 = 𝔓' := eq_of_le_of_ringKrullDim_quotient_eq hle
    (by rw [hcoh𝔭, ← hf, h𝔓coh n' hn'])
  exact h𝔓B n' hn' (by rwa [hf, ← heq])

end Stacks.ApproximationProperty

end

module

public import StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.Counterexample
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.Dimension
public import StacksFrontier.RingTheory.MvPolynomial.MaximalIdeal
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# The local rings of the non-catenary counterexample to Stacks 0EJA

Let `A'' = A/𝔟` be the local ring of the counterexample to Stacks 0EJA
(`StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.Situation`), with
`g = x₁ ∈ A''`, and write `𝔭'' = (𝔭B ∩ A)/𝔟` for a prime `𝔭 ⊇ Q₀ ∩ W` of `R = K[x₁, …, x₆]`.
This file computes the two local facts about `A''` that the counterexample needs.

* At `P''`, the extension `𝔨` of `Q₀''` to `A''_{P''}` is a prime avoiding `g`, killed by `g`,
  with `𝔪 = √(𝔨 + (g))`: every prime of `A''_{P''}` containing `Q₀''` and `g` comes from a prime of
  `B` containing `Q₀B + x₁B = PB`.
* At a prime `q ⊇ W''` of `A''` of coheight one other than the closed point, either `g = 0` in
  `A''_q` (when `Q₀'' ⊄ q`: then some element of `Q₀''`, killed by `g`, is a unit), or
  `A''_q/Q₀''A''_q` is a regular local ring of dimension three. In the second case `q` comes from
  a prime `Q ⊇ PB` of `B` lying only under `𝔪₁B`, and `A''_q/Q₀'' ≅ B_Q/Q₀B_Q` is a localization of
  `B/Q₀B`, itself a localization of `R/Q₀ ≅ K[y₁, …, y₄]`; so it is regular, and its dimension
  is the height of `Q/Q₀B` in `B/Q₀B`, which is covered by the height four maximal ideal `𝔪₁/Q₀`.

## Main results

* `Stacks.NonCatenaryExample.exists_annihilatedPrime_primePpp` — the annihilated prime at `P''`.
* `Stacks.NonCatenaryExample.localization_eq_zero_or_regular` — the dichotomy at the primes of
  coheight one.
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.Pinch MvPolynomial

universe u

namespace Stacks.NonCatenaryExample

/-- Taking preimages along a surjective ring map does not change coheights of primes. -/
theorem coheight_comap_of_surjective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Surjective f) (q : PrimeSpectrum S) :
    Order.coheight (⟨q.asIdeal.comap f, inferInstance⟩ : PrimeSpectrum R) =
      Order.coheight q := by
  let g : PrimeSpectrum S → PrimeSpectrum R := fun x => ⟨x.asIdeal.comap f, inferInstance⟩
  have hg : StrictMono g := by
    intro a b h
    have hab : a.asIdeal < b.asIdeal := h
    change a.asIdeal.comap f < b.asIdeal.comap f
    refine lt_of_le_of_ne (Ideal.comap_mono hab.le) fun he => hab.ne ?_
    calc a.asIdeal = (a.asIdeal.comap f).map f := (Ideal.map_comap_of_surjective f hf _).symm
      _ = (b.asIdeal.comap f).map f := by rw [he]
      _ = b.asIdeal := Ideal.map_comap_of_surjective f hf _
  refine (Order.coheight_eq_of_strictMono g hg (fun a b h => ?_) q).symm
  have h' : a.asIdeal.comap f < b.asIdeal := h
  have hker : Ideal.comap f ⊥ ≤ b.asIdeal := (Ideal.comap_mono bot_le).trans h'.le
  have hcm : (b.asIdeal.map f).comap f = b.asIdeal := by
    rw [Ideal.comap_map_of_surjective f hf, sup_eq_left.mpr hker]
  refine ⟨⟨b.asIdeal.map f, Ideal.map_isPrime_of_surjective hf
    (by rwa [RingHom.ker_eq_comap_bot])⟩, ?_, PrimeSpectrum.ext hcm⟩
  change a.asIdeal < b.asIdeal.map f
  refine lt_of_le_of_ne ?_ fun he => h'.ne ?_
  · rw [← Ideal.map_comap_of_surjective f hf a.asIdeal]
    exact Ideal.map_mono h'.le
  · rw [he, hcm]

/-- Above an element of coheight one there is no chain of length two. -/
private theorem not_lt_of_lt_of_coheight_eq_one {α : Type*} [Preorder α] {a x b : α}
    (ha : Order.coheight a = 1) (h1 : a < x) : ¬ x < b := by
  intro h2
  have c1 := Order.coheight_add_one_le h2
  have c2 := Order.coheight_add_one_le h1
  rw [ha] at c2
  have c3 : (2 : ℕ∞) ≤ 1 := calc
    (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight b + 1 + 1 := by
      gcongr
      exact zero_le
    _ ≤ _ := by gcongr
    _ ≤ 1 := c2
  norm_num at c3

/-- The image of a maximal ideal containing `I` in `R ⧸ I` is maximal. -/
theorem isMaximal_map_mk {R : Type*} [CommRing R] {I J : Ideal R} [J.IsMaximal] (h : I ≤ J) :
    (J.map (Ideal.Quotient.mk I)).IsMaximal := by
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    inferInstance).resolve_left fun htop => (Ideal.IsMaximal.ne_top ‹J.IsMaximal›) ?_
  have := congrArg (Ideal.comap (Ideal.Quotient.mk I)) htop
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr h, Ideal.comap_top] at this

/-- The image in `R ⧸ I` of the complement of a prime `P ⊇ I` is the complement of `P ⧸ I`. -/
theorem algebraMapSubmonoid_primeCompl_quotient {R : Type*} [CommRing R] (I P : Ideal R)
    [P.IsPrime] [(P.map (Ideal.Quotient.mk I)).IsPrime] (h : I ≤ P) :
    Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl =
      (P.map (Ideal.Quotient.mk I)).primeCompl := by
  have hc : (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr h]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ hy
    exact hx (hc.le hy)
  · intro hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, fun hx => hy (Ideal.mem_map_of_mem _ hx), rfl⟩

variable (K : Type u) [Field K] (e : K ≃+* FractionRing (MvPolynomial (Fin 3) K))

/-! ### The ring `R/Q₀ ≅ K[y₁, …, y₄]` and the ring `B/Q₀B` -/

/-- The map `R → K[y₁, …, y₄]` with kernel `Q₀` is surjective. -/
theorem mapQ0_surjective : Function.Surjective (mapQ0 K) := by
  intro q
  refine ⟨aeval ![X 0, X 1, X 2, X 5] q, ?_⟩
  change ((mapQ0 K).comp (aeval ![X 0, X 1, X 2, X 5])) q = q
  have : (mapQ0 K).comp (aeval (R := K) ![(X 0 : R6 K), X 1, X 2, X 5]) = AlgHom.id K _ := by
    refine MvPolynomial.algHom_ext fun j => ?_
    fin_cases j <;> simp [mapQ0]
  rw [this]
  rfl

/-- `R/Q₀ ≅ K[y₁, …, y₄]`. -/
def quotientQ0Equiv : R6 K ⧸ idealQ0 K ≃+* MvPolynomial (Fin 4) K :=
  (Ideal.quotEquivOfEq (ker_mapQ0 K).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (mapQ0_surjective K)).toRingEquiv

/-- `R/Q₀` is a regular ring. -/
instance : IsRegularRing (R6 K ⧸ idealQ0 K) := IsRegularRing.of_ringEquiv (quotientQ0Equiv K).symm

/-- Every maximal ideal of `R/Q₀` has height four. -/
theorem height_eq_four_of_isMaximal (I : Ideal (R6 K ⧸ idealQ0 K)) [I.IsMaximal] :
    I.height = 4 := by
  rw [← RingEquiv.height_comap (quotientQ0Equiv K).symm I]
  exact height_maximal_ideal_eq 4 _
    (Ideal.comap_isMaximal_of_surjective _ (quotientQ0Equiv K).symm.surjective)

/-- The ring `B/Q₀B`, a localization of `R/Q₀`. -/
abbrev RingBQ0 : Type u := RingB K ⧸ ext K (idealQ0 K)

/-- `B/Q₀B` is a regular ring. -/
instance : IsRegularRing (RingBQ0 K) :=
  isRegularRing_of_isLocalization (Algebra.algebraMapSubmonoid (R6 K ⧸ idealQ0 K) (submonoidS K))

/-- The maximal ideal `𝔪₁B/Q₀B` of `B/Q₀B`. -/
abbrev idealMQ0 : Ideal (RingBQ0 K) := (ext K (idealM K)).map (Ideal.Quotient.mk _)

/-- `𝔪₁B/Q₀B` is a maximal ideal of `B/Q₀B`. -/
instance : (idealMQ0 K).IsMaximal := isMaximal_map_mk (Ideal.map_mono (idealQ0_le_idealM K))

/-- `𝔪₁B/Q₀B` has height four. -/
theorem height_idealMQ0 : (idealMQ0 K).height = 4 := by
  rw [← IsLocalization.height_under
    (Algebra.algebraMapSubmonoid (R6 K ⧸ idealQ0 K) (submonoidS K)) (idealMQ0 K)]
  have h1 : (idealM K).map (Ideal.Quotient.mk (idealQ0 K)) ≤
      (idealMQ0 K).under (R6 K ⧸ idealQ0 K) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change algebraMap (R6 K ⧸ idealQ0 K) (RingBQ0 K) (Ideal.Quotient.mk _ r) ∈ idealMQ0 K
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr)
  have hmax : ((idealM K).map (Ideal.Quotient.mk (idealQ0 K))).IsMaximal :=
    isMaximal_map_mk (idealQ0_le_idealM K)
  rw [← hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) h1]
  exact height_eq_four_of_isMaximal K _

/-- **`B_Q/Q₀B_Q` is regular local of dimension three** when `Q ⊇ Q₀B` is a prime of `B` covered
by `𝔪₁B`: it is the localization of the regular ring `B/Q₀B` at `Q/Q₀B`, whose height is one less
than that of `𝔪₁B/Q₀B`. -/
theorem isRegularLocalRing_and_ringKrullDim_eq_three (Q : Ideal (RingB K)) [Q.IsPrime]
    (hQ0 : ext K (idealQ0 K) ≤ Q) (hlt : Q < ext K (idealM K))
    (hcov : ∀ X : Ideal (RingB K), X.IsPrime → Q < X → ¬ X < ext K (idealM K)) :
    IsRegularLocalRing (Localization.AtPrime Q ⧸
        (ext K (idealQ0 K)).map (algebraMap (RingB K) (Localization.AtPrime Q))) ∧
      ringKrullDim (Localization.AtPrime Q ⧸
        (ext K (idealQ0 K)).map (algebraMap (RingB K) (Localization.AtPrime Q))) = 3 := by
  set mk := Ideal.Quotient.mk (ext K (idealQ0 K))
  have hker : RingHom.ker mk ≤ Q := by rwa [Ideal.mk_ker]
  set Q' : Ideal (RingBQ0 K) := Q.map mk with hQ'
  have hQ'p : Q'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcQ : Q'.comap mk = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  have hcM : (idealMQ0 K).comap mk = ext K (idealM K) := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr (hker.trans hlt.le)]
  have hlt' : Q' < idealMQ0 K := by
    refine lt_of_le_of_ne (Ideal.map_mono hlt.le) fun h => hlt.ne ?_
    rw [← hcQ, h, hcM]
  have hcov' : (⟨Q', hQ'p⟩ : PrimeSpectrum (RingBQ0 K)) ⋖ ⟨idealMQ0 K, inferInstance⟩ := by
    refine ⟨hlt', fun x h1 h2 => ?_⟩
    have h1' : Q' < x.asIdeal := h1
    have h2' : x.asIdeal < idealMQ0 K := h2
    refine hcov (x.asIdeal.comap mk) inferInstance ?_ ?_
    · refine lt_of_le_of_ne (hcQ ▸ Ideal.comap_mono h1'.le) fun h => h1'.ne ?_
      rw [← Ideal.map_comap_of_surjective mk Ideal.Quotient.mk_surjective x.asIdeal, ← h]
    · refine lt_of_le_of_ne (hcM ▸ Ideal.comap_mono h2'.le) fun h => h2'.ne ?_
      rw [← Ideal.map_comap_of_surjective mk Ideal.Quotient.mk_surjective x.asIdeal, h]
  let s := (RelSeries.singleton {(p, q) : PrimeSpectrum (RingBQ0 K) × PrimeSpectrum (RingBQ0 K) |
    p ⋖ q} (⟨Q', hQ'p⟩ : PrimeSpectrum (RingBQ0 K))).snoc ⟨idealMQ0 K, inferInstance⟩ hcov'
  have hht := IsRegularRing.height_last_eq_length_add_height_head s
  have hl : s.last = ⟨idealMQ0 K, inferInstance⟩ := RelSeries.last_snoc _ _ _
  have hh : s.head = ⟨Q', hQ'p⟩ := RelSeries.head_snoc _ _ _
  have hlen : s.length = 1 := rfl
  rw [hl, hh, hlen, height_idealMQ0] at hht
  have h3 : Q'.height = 3 := by
    change (4 : ℕ∞) = ((1 : ℕ) : ℕ∞) + Q'.height at hht
    generalize Q'.height = h at hht ⊢
    induction h using ENat.recTopCoe with
    | top => simp at hht
    | coe n =>
      have : (4 : ℕ) = 1 + n := by exact_mod_cast hht
      exact_mod_cast (by omega : n = 3)
  have hsub : Algebra.algebraMapSubmonoid (RingBQ0 K) Q.primeCompl = Q'.primeCompl :=
    algebraMapSubmonoid_primeCompl_quotient _ _ hQ0
  have : IsLocalization.AtPrime (Localization.AtPrime Q ⧸
      (ext K (idealQ0 K)).map (algebraMap (RingB K) (Localization.AtPrime Q))) Q' := by
    change IsLocalization Q'.primeCompl _
    rw [← hsub]
    infer_instance
  refine ⟨IsRegularRing.isRegularLocalRing_of_isLocalization Q' _, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q', h3]
  rfl

/-! ### From `A''` to `B` -/

/-- A prime of `B` containing `Q₀B` and `x₁` contains `PB = Q₀B + x₁B`. -/
theorem extP_le (Q : Ideal (RingB K)) (hQ0 : ext K (idealQ0 K) ≤ Q)
    (hx : algebraMap (R6 K) (RingB K) (X 0) ∈ Q) : ext K (idealP K) ≤ Q := by
  refine Ideal.map_le_iff_le_comap.mpr ?_
  rw [idealP, Ideal.span_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact hx
  · exact hQ0 (Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp)))
  · exact hQ0 (Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp)))

/-- A prime of `A` containing `Q₀B ∩ A` and `x₁` contains `PB ∩ A`. -/
theorem primeA_P_le (p : Ideal (RingA K e)) [p.IsPrime] (hQ0 : primeA K e (idealQ0 K) ≤ p)
    (hf : elemF K e ∈ p) : primeA K e (idealP K) ≤ p := by
  by_cases hm : p = maximalIdeal (RingA K e)
  · rw [hm]
    exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨Q, hQp, hQm, rfl⟩ :=
    exists_comap_eq (residueEquiv K e) (extM_ne_extN K) (maximal_eq_or_eq K) p hm
  exact Ideal.comap_mono (extP_le K Q ((comap_le_comap_iff _ Q hQm).mp hQ0) hf)

/-- At a non-maximal prime `Q` of `B`, `(Q₀B ∩ A) B_Q = Q₀B_Q`. -/
theorem map_primeA_Q0_eq (Q : Ideal (RingB K)) [Q.IsPrime] (hQ : ¬ Q.IsMaximal) :
    (primeA K e (idealQ0 K)).map (algebraMap (RingA K e) (Localization.AtPrime Q)) =
      (ext K (idealQ0 K)).map (algebraMap (RingB K) (Localization.AtPrime Q)) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
    (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_)
  · rw [Ideal.mem_comap,
      IsScalarTower.algebraMap_apply (RingA K e) (RingB K) (Localization.AtPrime Q)]
    exact Ideal.mem_map_of_mem _ ha
  · obtain ⟨s, hs, hsQ⟩ := exists_mem_inf_notMem (ext K (idealM K)) (ext K (idealN K)) Q hQ
    let t : RingA K e := ⟨s * b, mem_pinch_of_mem_inf _ _ _ (Ideal.mul_mem_right b _ hs)⟩
    have ht : t ∈ primeA K e (idealQ0 K) := Ideal.mul_mem_left _ s hb
    have hu : IsUnit (algebraMap (RingB K) (Localization.AtPrime Q) s) :=
      IsLocalization.map_units _ (⟨s, hsQ⟩ : Q.primeCompl)
    have heq : algebraMap (RingA K e) (Localization.AtPrime Q) t =
        algebraMap (RingB K) (Localization.AtPrime Q) s *
          algebraMap (RingB K) (Localization.AtPrime Q) b := by
      rw [IsScalarTower.algebraMap_apply (RingA K e) (RingB K) (Localization.AtPrime Q), ← map_mul]
      rfl
    rw [Ideal.mem_comap]
    have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : Localization.AtPrime Q)
      (Ideal.mem_map_of_mem (algebraMap (RingA K e) (Localization.AtPrime Q)) ht)
    rwa [heq, ← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

/-- **`A''_q/Q₀''A''_q ≅ B_Q/Q₀B_Q`** for a prime `q ⊇ Q₀''` of `A''` lying under a non-maximal
prime `Q` of `B`: both are localizations of `A/(Q₀B ∩ A)` at the image of the complement of
`Q ∩ A`. -/
def quotientLocalizationEquiv (q : Ideal (RingA2 K e)) [q.IsPrime] (Q : Ideal (RingB K))
    [Q.IsPrime] (hQ : ¬ Q.IsMaximal)
    (hqQ : q.comap (Ideal.Quotient.mk (idealB K e)) = Q.comap (pinchA K e).subtype) :
    Localization.AtPrime q ⧸ ((primeA K e (idealQ0 K)).map (Ideal.Quotient.mk (idealB K e))).map
        (algebraMap (RingA2 K e) (Localization.AtPrime q)) ≃+*
      Localization.AtPrime Q ⧸
        (ext K (idealQ0 K)).map (algebraMap (RingB K) (Localization.AtPrime Q)) :=
  haveI := isLocalization_atPrime (residueEquiv K e) Q hQ
  have H : (Algebra.algebraMapSubmonoid
        (RingA2 K e ⧸ (primeA K e (idealQ0 K)).map (Ideal.Quotient.mk (idealB K e)))
        q.primeCompl).map
        (DoubleQuot.quotQuotEquivQuotOfLE (idealB_le_primeA_Q0 K e)).toMonoidHom =
      Algebra.algebraMapSubmonoid (RingA K e ⧸ primeA K e (idealQ0 K))
        (Q.comap (pinchA K e).subtype).primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Algebra.algebraMapSubmonoid]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨a, fun ha => hx (Ideal.mem_comap.mp (hqQ.ge ha)), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨Ideal.Quotient.mk (idealB K e) a,
        fun h => ha (hqQ.le (Ideal.mem_comap.mpr h)), rfl⟩, rfl⟩
  (IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime q ⧸ ((primeA K e (idealQ0 K)).map (Ideal.Quotient.mk (idealB K e))).map
        (algebraMap (RingA2 K e) (Localization.AtPrime q)))
    (Localization.AtPrime Q ⧸
      (primeA K e (idealQ0 K)).map (algebraMap (RingA K e) (Localization.AtPrime Q)))
    (DoubleQuot.quotQuotEquivQuotOfLE (idealB_le_primeA_Q0 K e)) H).trans
    (Ideal.quotEquivOfEq (map_primeA_Q0_eq K e Q hQ))

/-! ### The two local computations -/

/-- **The annihilated prime at `P''`.** In `A''_{P''}`, the extension `𝔨` of `Q₀''` is a prime
avoiding `g = x₁`, killed by `g`, and `√(𝔨 + (g))` is the maximal ideal: a prime containing `𝔨`
and `g` contracts to a prime of `A` containing `Q₀B ∩ A` and `x₁`, hence `PB ∩ A`. -/
theorem exists_annihilatedPrime_primePpp :
    ∃ 𝔨 : Ideal (Localization.AtPrime (primePpp K e).asIdeal), 𝔨.IsPrime ∧
      algebraMap (RingA2 K e) _ (elemG K e) ∉ 𝔨 ∧
      (∀ k ∈ 𝔨, algebraMap (RingA2 K e) _ (elemG K e) * k = 0) ∧
      maximalIdeal _ ≤ (𝔨 ⊔ Ideal.span {algebraMap (RingA2 K e) _ (elemG K e)}).radical := by
  set π := Ideal.Quotient.mk (idealB K e)
  set Q0'' := (primeA K e (idealQ0 K)).map π
  have hQ0'' : Q0''.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact idealB_le_primeA_Q0 K e)
  have hcQ0 : Q0''.comap π = primeA K e (idealQ0 K) := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr (idealB_le_primeA_Q0 K e)]
  have hle : Q0'' ≤ (primePpp K e).asIdeal :=
    Ideal.map_mono (Ideal.comap_mono (Ideal.map_mono (idealQ0_le_idealP K)))
  have hdisj : Disjoint ((primePpp K e).asIdeal.primeCompl : Set (RingA2 K e)) Q0'' :=
    Set.disjoint_left.mpr fun x hx hx' => hx (hle hx')
  refine ⟨Q0''.map (algebraMap (RingA2 K e) (Localization.AtPrime (primePpp K e).asIdeal)),
    IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hQ0'' hdisj, fun h => ?_,
    elemF_mul_eq_zero_of_mem K e _, ?_⟩
  · have hc := IsLocalization.under_map_of_isPrime_disjoint _
      (Localization.AtPrime (primePpp K e).asIdeal) hQ0'' hdisj
    apply elemF_notMem_primeA_Q0 K e
    rw [← hcQ0, ← hc]
    exact h
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf fun 𝔮 ⟨hJ, h𝔮⟩ => ?_
    set ψ := (algebraMap (RingA2 K e) (Localization.AtPrime (primePpp K e).asIdeal)).comp π
    have hq0 : primeA K e (idealQ0 K) ≤ 𝔮.comap ψ := fun a ha =>
      hJ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)))
    have hf : elemF K e ∈ 𝔮.comap ψ := hJ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine (Ideal.map_mono ?_).trans Ideal.map_comap_le
    change (primeA K e (idealP K)).map π ≤ _
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    exact primeA_P_le K e _ hq0 hf

/-- **The dichotomy at the primes of coheight one.** Let `q ⊇ W''` be a prime of `A''` of coheight
one other than the closed point. Either `g = x₁` vanishes in `A''_q` (when `Q₀'' ⊄ q`, as `g` kills
`Q₀''`), or the extension `𝔨` of `Q₀''`, killed by `g`, has `A''_q/𝔨` regular local of
dimension (at least) three. -/
theorem localization_eq_zero_or_regular (q : PrimeSpectrum (RingA2 K e))
    (hW : (primeA K e (idealW K)).map (Ideal.Quotient.mk (idealB K e)) ≤ q.asIdeal)
    (hq : q.asIdeal ≠ maximalIdeal (RingA2 K e)) (hc : Order.coheight q = 1) :
    algebraMap (RingA2 K e) (Localization.AtPrime q.asIdeal) (elemG K e) = 0 ∨
      ∃ 𝔨 : Ideal (Localization.AtPrime q.asIdeal),
        (∀ k ∈ 𝔨, algebraMap (RingA2 K e) _ (elemG K e) * k = 0) ∧
        IsRegularLocalRing (_ ⧸ 𝔨) ∧ (3 : WithBot ℕ∞) ≤ ringKrullDim (_ ⧸ 𝔨) := by
  set π := Ideal.Quotient.mk (idealB K e)
  set Q0'' := (primeA K e (idealQ0 K)).map π
  by_cases h0 : Q0'' ≤ q.asIdeal
  swap
  · left
    obtain ⟨a, ha, haq⟩ := Set.not_subset.mp h0
    have hu : IsUnit (algebraMap (RingA2 K e) (Localization.AtPrime q.asIdeal) a) :=
      IsLocalization.map_units _ (⟨a, haq⟩ : q.asIdeal.primeCompl)
    exact hu.mul_left_eq_zero.mp
      (elemF_mul_eq_zero_of_mem K e q.asIdeal _ (Ideal.mem_map_of_mem _ ha))
  right
  refine ⟨Q0''.map (algebraMap (RingA2 K e) (Localization.AtPrime q.asIdeal)),
    elemF_mul_eq_zero_of_mem K e q.asIdeal, ?_⟩
  set p := q.asIdeal.comap π
  have hpm : p ≠ maximalIdeal (RingA K e) := fun h => hq <| by
    have h2 : (maximalIdeal (RingA2 K e)).comap π = maximalIdeal (RingA K e) :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective q.asIdeal,
      ← Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective (maximalIdeal _)]
    exact congrArg (Ideal.map π) (h.trans h2.symm)
  obtain ⟨Q, hQp, hQm, hQeq⟩ :=
    exists_comap_eq (residueEquiv K e) (extM_ne_extN K) (maximal_eq_or_eq K) p hpm
  have hQ0 : ext K (idealQ0 K) ≤ Q := by
    refine (comap_le_comap_iff (φ := residueEquiv K e) _ Q hQm).mp ?_
    rw [hQeq]
    exact fun a ha => h0 (Ideal.mem_map_of_mem π ha)
  have hx : elemF K e ∈ Q.comap (pinchA K e).subtype := by
    rw [hQeq]
    exact hW (Ideal.mem_map_of_mem π (elemF_mem_primeA_W K e))
  have hQM : Q ≤ ext K (idealM K) := (le_extM_or_le_extN K Q).resolve_right fun hN =>
    X3_notMem_idealN K ((algebraMap_mem_ext_iff K (Or.inr le_rfl) _).mp
      (hN (extP_le K Q hQ0 hx (Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))))))
  have hcoh : Order.coheight (⟨Q, hQp⟩ : PrimeSpectrum (RingB K)) = 1 := by
    have e1 := coheight_comap (residueEquiv K e) (extM_ne_extN K) (maximal_eq_or_eq K) Q
    have e2 := coheight_comap_of_surjective (f := π) Ideal.Quotient.mk_surjective q
    have e3 : (⟨Q.comap (pinchA K e).subtype, inferInstance⟩ : PrimeSpectrum (RingA K e)) =
        ⟨q.asIdeal.comap π, inferInstance⟩ := PrimeSpectrum.ext hQeq
    rw [← e1, e3, e2, hc]
  have hcov : ∀ X : Ideal (RingB K), X.IsPrime → Q < X → ¬ X < ext K (idealM K) :=
    fun X hX h1 => not_lt_of_lt_of_coheight_eq_one (x := (⟨X, hX⟩ : PrimeSpectrum (RingB K)))
      (b := ⟨ext K (idealM K), inferInstance⟩) hcoh h1
  have hlt : Q < ext K (idealM K) := lt_of_le_of_ne hQM fun h => hQm (h ▸ isMaximal_extM K)
  obtain ⟨hreg, hdim⟩ := isRegularLocalRing_and_ringKrullDim_eq_three K Q hQ0 hlt hcov
  let φ := quotientLocalizationEquiv K e q.asIdeal Q hQm hQeq.symm
  exact ⟨IsRegularLocalRing.of_ringEquiv φ.symm, by rw [ringKrullDim_eq_of_ringEquiv φ, hdim]⟩

end Stacks.NonCatenaryExample

end

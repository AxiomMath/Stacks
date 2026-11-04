module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.SymbolicPower.AssociatedPrimes
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Weakly associated primes

Let `R` be a ring and `M` an `R`-module. A prime `𝔭` of `R` is *weakly associated* to `M` if
there exists `m ∈ M` such that `𝔭` is minimal among the prime ideals containing the annihilator
`Ann(m)`. The set of all such primes is denoted `WeakAss_R(M)`.

## Main definitions

* `IsWeaklyAssociatedPrime`, `weaklyAssociatedPrimes`: weakly associated primes and their set.
* `annihilatorOfElem_semiring`: the annihilator `Ann_R(n)` of an element `n`.
* `WeaklyAssociated`: a prime is weakly associated to a module over a commutative semiring.
* `IsWeaklyAssociatedPrimeIdeal`, `weaklyAssociatedPrimes05C3`: the same notion with the
  annihilator written `(⊥ : Submodule R M).colon {m}`.
* `zeroDivisorsOn05C3`: the zerodivisors on a module.
* `weakAss`: the weakly associated primes as a subset of `PrimeSpectrum R`.
* `localizationComap`: the map `Spec(S⁻¹R) → Spec(R)` induced by a localization.

## Main results

* `weaklyAssociated_iff_localization_and_exists_radical_eq`: `p` is weakly associated to `M` iff
  `p R_p` is weakly associated to `M_p`, iff some `t ∈ M_p` has `√(Ann_{R_p}(t)) = p R_p`.
* `iUnion_weaklyAssociatedPrimes_eq_zeroDivisorsOn`: the union of the weakly associated primes of
  `M` is the set of zerodivisors on `M`.
* `weaklyAssociatedPrimes_comap_quotient`, `mem_weaklyAssociatedPrimes_quotient_iff`: the weakly
  associated primes of an `R ⧸ I`-module over `R ⧸ I` and over `R` correspond.
* `weakAss_localizedModule_eq_image`, `weakAss_inter_image_eq_weakAss_localizedModule`: the weakly
  associated primes of a localization `S⁻¹M`.
* `weakAss_eq_minimalPrimes0EMA`: the weakly associated primes of a reduced ring are its minimal
  primes.
-/

@[expose] public section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- A prime ideal `I` of `R` is *weakly associated* to the `R`-module `M` if `I` is minimal among
the prime ideals containing the annihilator `(R ∙ m).annihilator` of some element `m ∈ M`. -/
@[stacks 0547 "predicate"]
def IsWeaklyAssociatedPrime (I : Ideal R) : Prop :=
  ∃ m : M, I ∈ Ideal.minimalPrimes (R ∙ m).annihilator

/-- The set of weakly associated primes of `M` (over `R`). -/
@[stacks 0547 "set"]
def weaklyAssociatedPrimes : Set (Ideal R) :=
  {I | IsWeaklyAssociatedPrime R M I}

/-- `I` is a weakly associated prime of `M` if and only if `I` is minimal among the primes
containing the annihilator of some `m : M`. -/
theorem mem_weaklyAssociatedPrimes_iff {I : Ideal R} :
    I ∈ weaklyAssociatedPrimes R M ↔
      ∃ m : M, I ∈ Ideal.minimalPrimes (R ∙ m).annihilator :=
  Iff.rfl

/-- A weakly associated prime is a prime ideal. -/
theorem IsWeaklyAssociatedPrime.isPrime {I : Ideal R} (h : IsWeaklyAssociatedPrime R M I) :
    I.IsPrime :=
  h.choose_spec.left.left

/-! ### Weakly associated primes and localization at a prime

For a prime `p` of `R`, with `R_p = Localization.AtPrime p` and
`M_p = LocalizedModule.AtPrime p M`, the following are equivalent: `p` is weakly associated to
`M`; `p R_p` is weakly associated to the `R_p`-module `M_p`; there is `t ∈ M_p` with
`√(Ann_{R_p}(t)) = p R_p`.
-/

@[expose] public section

/-- The annihilator of an element `n` of an `R`-module `N`, i.e. the ideal
`Ann_R(n) = {f ∈ R | f • n = 0}`. This is the annihilator of the cyclic submodule `R • n`. -/
def annihilatorOfElem_semiring {R : Type*} [CommSemiring R] {N : Type*} [AddCommMonoid N]
    [Module R N] (n : N) : Ideal R := (Submodule.span R {n}).annihilator

/-- `f ∈ Ann_R(n)` if and only if `f • n = 0`. -/
@[ega "0 1.7.4" "one generator"]
theorem mem_annihilatorOfElem_semiring_iff {R : Type*} [CommSemiring R] {N : Type*}
    [AddCommMonoid N] [Module R N] (n : N) (f : R) :
    f ∈ annihilatorOfElem_semiring n ↔ f • n = 0 := by
  rw [annihilatorOfElem_semiring, Submodule.mem_annihilator_span_singleton]

/-- A prime ideal `p ⊆ R` is *weakly associated* to the `R`-module `N` if there exists an element
`n ∈ N` such that `p` is minimal among the prime ideals containing `Ann_R(n)`. -/
def WeaklyAssociated {R : Type*} [CommSemiring R] (p : Ideal R)
    (N : Type*) [AddCommMonoid N] [Module R N] : Prop :=
  ∃ n : N, p ∈ (annihilatorOfElem_semiring (R := R) n).minimalPrimes

/-- In a local ring `S` with maximal ideal `m`, `m` is weakly associated to an `S`-module `N` iff
there is an element `t ∈ N` whose annihilator has radical equal to `m`. -/
theorem weaklyAssociated_maximalIdeal_iff_exists_radical_eq
    {S : Type*} [CommRing S] [IsLocalRing S]
    {N : Type*} [AddCommGroup N] [Module S N] :
    WeaklyAssociated (IsLocalRing.maximalIdeal S) N ↔
      ∃ t : N, (annihilatorOfElem_semiring (R := S) t).radical = IsLocalRing.maximalIdeal S := by
  have hmp : (IsLocalRing.maximalIdeal S).IsPrime := (IsLocalRing.maximalIdeal.isMaximal S).isPrime
  constructor
  · rintro ⟨t, ⟨-, hIm⟩, hmin⟩
    refine ⟨t, le_antisymm ((Ideal.radical_mono hIm).trans_eq hmp.radical) ?_⟩
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun J ⟨hIJ, hJ⟩ => hmin ⟨hJ, hIJ⟩ (IsLocalRing.le_maximalIdeal hJ.ne_top)
  · rintro ⟨t, ht⟩
    exact ⟨t, ⟨hmp, ht ▸ Ideal.le_radical⟩, fun q ⟨hq, hIq⟩ _ =>
      (ht.symm.trans_le (Ideal.radical_mono hIq)).trans_eq hq.radical⟩

/-- For the localization `S` of `R` at a submonoid `T`, a localized module `M'` (via
`g : M →ₗ[R] M'`), an element `x ∈ M`, and a prime `q` of `S`, the annihilator of `g x` is
contained in `q` iff the annihilator of `x` is contained in the contraction of `q`. -/
theorem annOfElem_localized_le_iff
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module R M]
    {M' : Type*} [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
    (T : Submonoid R) [IsLocalization T S]
    (g : M →ₗ[R] M') [IsLocalizedModule T g]
    (x : M) (q : Ideal S) (hq : q.IsPrime) :
    annihilatorOfElem_semiring (R := S) (g x) ≤ q ↔
      annihilatorOfElem_semiring (R := R) x ≤ Ideal.comap (algebraMap R S) q := by
  refine ⟨fun h a ha => Ideal.mem_comap.mpr (h ?_), fun h b hb => ?_⟩
  · rw [mem_annihilatorOfElem_semiring_iff] at ha ⊢
    rw [algebraMap_smul, ← map_smul, ha, map_zero]
  · rw [mem_annihilatorOfElem_semiring_iff] at hb
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (S := S) T b
    simp only at hs
    obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_zero_iff T g).mp (show g (a • x) = 0 by
      rw [map_smul, ← algebraMap_smul S, ← hs, mul_comm, mul_smul, hb, smul_zero])
    have hmem : algebraMap R S (u * a) ∈ q :=
      h (by rwa [mem_annihilatorOfElem_semiring_iff, mul_smul])
    rw [map_mul] at hmem
    have ha := (hq.mem_or_mem hmem).resolve_left fun h1 =>
      hq.ne_top (Ideal.eq_top_of_isUnit_mem q h1 (IsLocalization.map_units S u))
    exact (Ideal.mul_unit_mem_iff_mem q (IsLocalization.map_units S s)).mp (hs ▸ ha)

/-- For a prime `q'` of `R` contained in `p`, there is a prime `q` of `R_p` whose contraction to
`R` is `q'`. -/
@[ega "0 1.2.6" "partial", ega "0 16.1.3" "partial", ega "0 7.6.10" "partial"]
theorem exists_prime_comap_eq {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (q' : Ideal R) (hq' : q'.IsPrime) (hle : q' ≤ p) :
    ∃ q : Ideal (Localization.AtPrime p), q.IsPrime ∧
      Ideal.comap (algebraMap R (Localization.AtPrime p)) q = q' :=
  let e := IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime p) p
  ⟨(e.symm ⟨q', hq', hle⟩).val, (e.symm ⟨q', hq', hle⟩).property,
    congrArg Subtype.val (e.apply_symm_apply ⟨q', hq', hle⟩)⟩

/-- Contraction along the localization map is injective on primes of `R_p`. -/
@[ega "0 1.2.6" "partial", ega "0 7.6.10" "partial"]
theorem comap_localization_injective {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (q1 q2 : Ideal (Localization.AtPrime p)) (h1 : q1.IsPrime) (h2 : q2.IsPrime)
    (h : Ideal.comap (algebraMap R (Localization.AtPrime p)) q1
       = Ideal.comap (algebraMap R (Localization.AtPrime p)) q2) : q1 = q2 :=
  congrArg PrimeSpectrum.asIdeal
    (PrimeSpectrum.localization_comap_injective (Localization.AtPrime p) p.primeCompl
      (a₁ := ⟨q1, h1⟩) (a₂ := ⟨q2, h2⟩) (PrimeSpectrum.ext h))

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- `p` is weakly associated to `M` iff `p R_p` is weakly associated to `M_p`. -/
theorem weaklyAssociated_iff_localization (p : Ideal R) [p.IsPrime] :
    WeaklyAssociated p M ↔
      WeaklyAssociated (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p M) := by
  set S := Localization.AtPrime p
  set f := algebraMap R S
  set g := LocalizedModule.mkLinearMap p.primeCompl M
  set m : Ideal S := IsLocalRing.maximalIdeal S
  have hmp : m.IsPrime := (IsLocalRing.maximalIdeal.isMaximal S).isPrime
  have hcomap_m : Ideal.comap f m = p := Localization.AtPrime.under_maximalIdeal
  constructor
  · rintro ⟨x, ⟨-, hxp⟩, hmin⟩
    refine ⟨g x, ⟨hmp, ?_⟩, fun q ⟨hq, hAq⟩ hqm => ?_⟩
    · exact (annOfElem_localized_le_iff p.primeCompl g x m hmp).mpr (hxp.trans hcomap_m.ge)
    · have hq'p : Ideal.comap f q ≤ p := (Ideal.comap_mono hqm).trans hcomap_m.le
      refine (comap_localization_injective p q m hq hmp ?_).ge
      exact (hq'p.antisymm (hmin ⟨Ideal.comap_isPrime f q,
        (annOfElem_localized_le_iff p.primeCompl g x q hq).mp hAq⟩ hq'p)).trans hcomap_m.symm
  · rintro ⟨t, ht⟩
    obtain ⟨⟨x, s⟩, hsx⟩ := IsLocalizedModule.surj p.primeCompl g t
    obtain ⟨v, hv⟩ := IsLocalization.map_units S s
    have hann : annihilatorOfElem_semiring (R := S) (g x) = annihilatorOfElem_semiring t := by
      have h1 : g x = (v : S) • t := by
        rw [hv, algebraMap_smul]
        exact hsx.symm
      rw [annihilatorOfElem_semiring, annihilatorOfElem_semiring, h1,
        Submodule.span_singleton_smul_eq v.isUnit]
    obtain ⟨⟨-, hAm⟩, hmin⟩ := hann ▸ ht
    refine ⟨x, ⟨inferInstance, ?_⟩, fun q' ⟨hq', hAq'⟩ hq'p => ?_⟩
    · exact ((annOfElem_localized_le_iff p.primeCompl g x m hmp).mp hAm).trans hcomap_m.le
    · obtain ⟨q, hq, rfl⟩ := exists_prime_comap_eq p q' hq' hq'p
      exact hcomap_m.ge.trans (Ideal.comap_mono (hmin
        ⟨hq, (annOfElem_localized_le_iff p.primeCompl g x q hq).mpr hAq'⟩
        (IsLocalRing.le_maximalIdeal hq.ne_top)))

/-- `p` is weakly associated to `M` iff there is an element `t ∈ M_p` with
`√(Ann_{R_p}(t)) = p R_p`. -/
theorem weaklyAssociated_iff_exists_radical_eq (p : Ideal R) [p.IsPrime] :
    WeaklyAssociated p M ↔
      ∃ t : LocalizedModule.AtPrime p M,
        (annihilatorOfElem_semiring (R := Localization.AtPrime p) t).radical
          = IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
  (weaklyAssociated_iff_localization p).trans weaklyAssociated_maximalIdeal_iff_exists_radical_eq

/-- For a prime `p` of `R`, the following are equivalent:

1. `p` is weakly associated to `M`;
2. `p R_p` is weakly associated to `M_p`;
3. there exists `t ∈ M_p` with `√(Ann_{R_p}(t)) = p R_p`. -/
@[stacks 0566]
theorem weaklyAssociated_iff_localization_and_exists_radical_eq
    (p : Ideal R) [p.IsPrime] :
    (WeaklyAssociated p M ↔
      WeaklyAssociated (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p M))
    ∧ (WeaklyAssociated (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule.AtPrime p M) ↔
      ∃ t : LocalizedModule.AtPrime p M,
        (annihilatorOfElem_semiring (R := Localization.AtPrime p) t).radical
          = IsLocalRing.maximalIdeal (Localization.AtPrime p)) :=
  ⟨weaklyAssociated_iff_localization p, weaklyAssociated_maximalIdeal_iff_exists_radical_eq⟩


set_option linter.style.show false


open Submodule Ideal

/-- A prime ideal `q` of a commutative ring `R` is a *weakly associated prime* of an `R`-module `M`
if there exists `m : M` such that `q` is a minimal prime over the annihilator
`(⊥ : Submodule R M).colon {m}`. -/
def IsWeaklyAssociatedPrimeIdeal {R : Type*} [CommRing R] (q : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∃ m : M, q ∈ ((⊥ : Submodule R M).colon {m}).minimalPrimes

/-- The set of weakly associated primes of an `R`-module `M`. -/
def weaklyAssociatedPrimes05C3 (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : Set (Ideal R) :=
  {q | IsWeaklyAssociatedPrimeIdeal q M}

/-- The set of zerodivisors on an `R`-module `M`: elements `r : R` for which there exists a nonzero
`m : M` with `r • m = 0`. -/
@[ega "0 15.1.1"]
def zeroDivisorsOn05C3 (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : Set R :=
  {r | ∃ m : M, m ≠ 0 ∧ r • m = 0}

/-- The annihilator of a nonzero element of `M` is a proper ideal. -/
private lemma colon_bot_singleton_ne_top {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {m : M} (hm : m ≠ 0) :
    ((⊥ : Submodule R M).colon {m}) ≠ ⊤ :=
  fun h => hm (by simpa using (Submodule.colon_eq_top_iff_subset _).mp h (Set.mem_singleton m))

/-- Let `R` be a commutative ring and `M` an `R`-module. The union of the weakly associated primes
of `M` is the set of zerodivisors on `M`. -/
@[stacks 05C3]
theorem iUnion_weaklyAssociatedPrimes_eq_zeroDivisorsOn
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    (⋃ q ∈ weaklyAssociatedPrimes05C3 R M, (q : Set R)) = zeroDivisorsOn05C3 R M := by
  ext r
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨q, ⟨m, hqm⟩, hrq⟩
    obtain ⟨s, hs, hrs⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hqm hrq
    exact ⟨s • m, fun h => hs (Submodule.mem_colon_singleton.mpr (by simpa using h)),
      by simpa [smul_smul] using Submodule.mem_colon_singleton.mp hrs⟩
  · rintro ⟨m, hm, hrm⟩
    obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes (colon_bot_singleton_ne_top (R := R) hm)
    exact ⟨q, ⟨m, hq⟩, hq.1.2 (Submodule.mem_colon_singleton.mpr (by simpa using hrm))⟩

/-! ### Weakly associated primes of a module over a quotient ring

For an ideal `I ⊆ R` and an `R ⧸ I`-module `M` viewed as an `R`-module by restriction of scalars,
`Ideal.comap (Ideal.Quotient.mk I)` carries the weakly associated primes of `M` over `R ⧸ I` onto
those over `R`.
-/

@[expose] public section

variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M]
  [Module (R ⧸ I) M] [Module R M] [IsScalarTower R (R ⧸ I) M]

/-- The annihilator over `R` of an element `x` of an `A`-module `N` (via restriction of scalars) is
the contraction along `R → A` of its annihilator over `A`. -/
private theorem annihilator_span_eq_comap_algebraMap {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] (x : N) :
    (Submodule.span R {x}).annihilator
      = Ideal.comap (algebraMap R A) (Submodule.span A {x}).annihilator := by
  ext r
  rw [Ideal.mem_comap, Submodule.mem_annihilator_span_singleton,
    Submodule.mem_annihilator_span_singleton, algebraMap_smul]

/-- The minimal primes of the `R`-annihilator of `m` are exactly the comaps along `π` of the
minimal primes of the `R/I`-annihilator of `m`. -/
private theorem ann_minimalPrimes_eq (m : M) :
    (Submodule.span R {m}).annihilator.minimalPrimes
      = Ideal.comap (Ideal.Quotient.mk I) ''
          (Submodule.span (R ⧸ I) {m}).annihilator.minimalPrimes :=
  (congrArg Ideal.minimalPrimes (annihilator_span_eq_comap_algebraMap (A := R ⧸ I) m)).trans
    (Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective _)

/-- For a commutative ring `R`, an ideal `I`, and an `R/I`-module `M` (viewed as an `R`-module by
restriction of scalars), the canonical injection `π* = Ideal.comap (R → R/I)` carries the weakly
associated primes computed over `R/I` onto those computed over `R`. -/
@[stacks 05C8, ega "IV 3.1.10.1" "Quotient maps A → A/I"]
theorem weaklyAssociatedPrimes_comap_quotient :
    Ideal.comap (Ideal.Quotient.mk I) '' weaklyAssociatedPrimes (R ⧸ I) M
      = weaklyAssociatedPrimes R M := by
  ext p
  simp only [mem_weaklyAssociatedPrimes_iff, Set.mem_image, ann_minimalPrimes_eq I M]
  aesop

/-- A prime ideal `𝔭` of `R` is weakly associated to `M` (as an `R`-module) iff it contains `I` and
its image `𝔭/I = 𝔭.map π` in `R/I` is weakly associated to `M` (as an `R/I`-module). -/
theorem mem_weaklyAssociatedPrimes_quotient_iff {p : Ideal R} :
    p ∈ weaklyAssociatedPrimes R M
      ↔ (I ≤ p ∧ (p.map (Ideal.Quotient.mk I)) ∈ weaklyAssociatedPrimes (R ⧸ I) M) := by
  rw [← weaklyAssociatedPrimes_comap_quotient I M]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    · rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  · rintro ⟨hIp, hp⟩
    refine ⟨_, hp, ?_⟩
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left]

/-! ### Weakly associated primes and localization at a multiplicative subset

For a submonoid `S ⊆ R` with `ι : Spec(S⁻¹R) → Spec(R)` the induced map, the weakly associated
primes of the `R`-module `S⁻¹M` are the image under `ι` of those of the `S⁻¹R`-module `S⁻¹M`, and
they are the weakly associated primes of `M` lying in the image of `ι`.
-/

@[expose] public section

/-- The set of weakly associated primes of an `R`-module `M`: a prime `p` is weakly associated to
`M` if and only if there is `m : M` with `p` minimal among the primes containing `Ann_R(m)`. -/
def weakAss (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Set (PrimeSpectrum R) :=
  {p | ∃ m : M, p.asIdeal ∈ (Submodule.span R {m}).annihilator.minimalPrimes}

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

/-- The canonical map `ι : Spec(S⁻¹R) → Spec(R)` induced by the localization ring map `R → S⁻¹R`.
Here `S⁻¹R = Localization S` and `S⁻¹M = LocalizedModule S M`, the latter carrying both an
`R`-module structure (via `R → S⁻¹R`) and an `S⁻¹R`-module structure. -/
noncomputable abbrev localizationComap : PrimeSpectrum (Localization S) → PrimeSpectrum R :=
  PrimeSpectrum.comap (algebraMap R (Localization S))

/-- The `R`-annihilator of an element `x` of `S⁻¹M` is the contraction (under `R → S⁻¹R`) of its
`S⁻¹R`-annihilator. -/
theorem annElem_eq_comap_annElem_localization (x : LocalizedModule S M) :
    (Submodule.span R {x}).annihilator =
      ((Submodule.span (Localization S) {x}).annihilator).comap
        (algebraMap R (Localization S)) :=
  annihilator_span_eq_comap_algebraMap x

/-- The minimal primes of the `R`-annihilator of `x : S⁻¹M` are exactly the contractions of the
minimal primes of its `S⁻¹R`-annihilator. -/
theorem minimalPrimes_annihilator_localizedModule (x : LocalizedModule S M) :
    (Submodule.span R {x}).annihilator.minimalPrimes =
      Ideal.comap (algebraMap R (Localization S)) ''
        (Submodule.span (Localization S) {x}).annihilator.minimalPrimes := by
  rw [annElem_eq_comap_annElem_localization]
  exact IsLocalization.minimalPrimes_comap S _ _

/-- `f` annihilates `mk m s` iff some multiple of `f` by an element of `S` annihilates `m`. -/
theorem mem_annihilator_span_mk (m : M) (s : S) (f : R) :
    f ∈ (Submodule.span R {LocalizedModule.mk m s}).annihilator ↔
      ∃ u : S, ((u : R) * f) • m = 0 := by
  rw [Submodule.mem_annihilator_span_singleton, LocalizedModule.smul'_mk,
    ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u * s, ?_⟩
    simpa [Submonoid.smul_def, smul_smul, mul_assoc] using hu
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, smul_smul]
    rw [show ((↑u : R) * (↑s * f)) = ↑s * (↑u * f) by ring, mul_smul, hu, smul_zero]

/-- For a prime `p` disjoint from `S`, containing `Ann_R(mk m s)` is equivalent to containing
`Ann_R(m)`. -/
theorem annElem_mk_le_iff (m : M) (s : S) (p : Ideal R) [hp' : p.IsPrime]
    (hp : Disjoint (S : Set R) (p : Set R)) :
    (Submodule.span R {LocalizedModule.mk m s}).annihilator ≤ p ↔
      (Submodule.span R {m}).annihilator ≤ p := by
  refine ⟨fun h f hf ↦ h ((mem_annihilator_span_mk S m s f).mpr
    ⟨1, by simpa using (Submodule.mem_annihilator_span_singleton m f).mp hf⟩), fun h f hf ↦ ?_⟩
  obtain ⟨u, hu⟩ := (mem_annihilator_span_mk S m s f).mp hf
  exact (hp'.mem_or_mem (h ((Submodule.mem_annihilator_span_singleton m _).mpr hu))).resolve_left
    (Set.disjoint_left.mp hp u.property)

/-- `WeakAss_R(S⁻¹M) = ι(WeakAss_{S⁻¹R}(S⁻¹M))`: the `R`-module weakly associated primes of `S⁻¹M`
are the image under `ι` of the `S⁻¹R`-module weakly associated primes of `S⁻¹M`. -/
@[stacks 05C9 "(1)"]
theorem weakAss_localizedModule_eq_image :
    weakAss R (LocalizedModule S M) =
      localizationComap S '' (weakAss (Localization S) (LocalizedModule S M)) := by
  ext p
  simp only [weakAss, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx⟩
    have hx : p.asIdeal ∈ (Submodule.span R {x}).annihilator.minimalPrimes := hx
    rw [minimalPrimes_annihilator_localizedModule] at hx
    obtain ⟨q, hq, hqp⟩ := hx
    exact ⟨⟨q, hq.left.left⟩, ⟨x, hq⟩, PrimeSpectrum.ext hqp⟩
  · rintro ⟨q, ⟨x, hx⟩, rfl⟩
    refine ⟨x, ?_⟩
    show (localizationComap S q).asIdeal ∈
      (Submodule.span R {x}).annihilator.minimalPrimes
    rw [minimalPrimes_annihilator_localizedModule]
    exact ⟨q.asIdeal, hx, rfl⟩

/-- The `R`-annihilator of `m` is contained in the `R`-annihilator of `mk m s`. -/
theorem annihilator_span_le_annihilator_span_mk (m : M) (s : S) :
    (Submodule.span R {m}).annihilator ≤
      (Submodule.span R {LocalizedModule.mk m s}).annihilator := by
  intro f hf
  rw [Submodule.mem_annihilator_span_singleton] at hf ⊢
  rw [LocalizedModule.smul'_mk, hf, LocalizedModule.zero_mk]

/-- `{ p ∈ WeakAss_R(M) | p ∈ ι(Spec(S⁻¹R)) } = WeakAss_R(S⁻¹M)`: the primes weakly associated to
`M` and lying in the image of `ι` (i.e. disjoint from `S`) are exactly the primes weakly associated
to `S⁻¹M`. -/
@[stacks 05C9 "(2)"]
theorem weakAss_inter_image_eq_weakAss_localizedModule :
    {p ∈ weakAss R M | p ∈ Set.range (localizationComap S)} =
      weakAss R (LocalizedModule S M) := by
  rw [PrimeSpectrum.localization_comap_range (Localization S) S]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨m, hm⟩, hdisj : Disjoint (S : Set R) p.asIdeal⟩
    refine ⟨LocalizedModule.mk m 1,
      ⟨p.isPrime, (annElem_mk_le_iff S m 1 p.asIdeal hdisj).mpr hm.left.right⟩,
      fun q hq hqp ↦ hm.right
        ⟨hq.left, (annihilator_span_le_annihilator_span_mk S m 1).trans hq.right⟩ hqp⟩
  · intro hp
    have hdisj : Disjoint (S : Set R) p.asIdeal := by
      simpa [PrimeSpectrum.localization_comap_range (Localization S) S] using
        Set.image_subset_range _ _ ((weakAss_localizedModule_eq_image S).subset hp)
    refine ⟨?_, hdisj⟩
    obtain ⟨x, hx⟩ := hp
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      refine ⟨m, ⟨p.isPrime, (annElem_mk_le_iff S m s p.asIdeal hdisj).mp hx.left.right⟩,
        fun q hq hqp ↦ hx.right ⟨hq.left, ?_⟩ hqp⟩
      have := hq.left
      exact (annElem_mk_le_iff S m s q
        (Set.disjoint_left.mpr fun a ha haq ↦ Set.disjoint_left.mp hdisj ha (hqp haq))).mpr hq.right

/-! ### Weakly associated primes of a reduced ring

For a reduced ring `R`, the weakly associated primes of `R` as a module over itself are its
minimal primes.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

/-- For a reduced commutative ring `R`, the weakly associated primes of `R` are exactly the minimal
primes of `R`. -/
@[stacks 0EMA]
theorem weakAss_eq_minimalPrimes0EMA [IsReduced R] :
    weaklyAssociatedPrimes R R = minimalPrimes R := by
  ext p
  refine ⟨fun ⟨m, hp⟩ => ?_, fun hp => ⟨1, ⟨hp.1.1, fun f hf => ?_⟩,
    fun q hq hqp => hp.2 ⟨hq.1, bot_le⟩ hqp⟩⟩
  · have hmp : m ∉ p := fun hm => by
      obtain ⟨y, hy, hmy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hp hm
      rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hy hmy
      refine hy (IsReduced.eq_zero _ ⟨2, ?_⟩)
      linear_combination y * hmy
    refine ⟨⟨hp.1.1, bot_le⟩, fun q ⟨hq, _⟩ hqp => ?_⟩
    obtain ⟨q0, hq0min, hq0q⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := q) bot_le
    have hq0 : q0.IsPrime := hq0min.1.1
    refine le_trans (hp.2 ⟨hq0, fun f hf => ?_⟩ (hq0q.trans hqp)) hq0q
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hf
    exact (hq0.mem_or_mem (hf ▸ q0.zero_mem)).resolve_right fun hh => hmp (hqp (hq0q hh))
  · rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_one] at hf
    simp [hf]

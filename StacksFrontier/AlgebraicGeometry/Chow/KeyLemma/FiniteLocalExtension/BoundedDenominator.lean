module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.RingTheory.KrullDimension.FinitePrimeSpectrum
public import StacksCore.Tactic.StacksAttribute

/-!
# Bounded denominators in the ambient product

Auxiliary steps for `exists_finite_local_extension_with_prescribed_localizations`: the
subalgebra of `A[1/t] × ∏ᵢ Bᵢ` of elements with denominator bounded by a power of `t`, its
coordinate maps, and the separation of the finitely many primes above `t`.
-/

@[expose] public section

open scoped Pointwise

universe u v w

/-- Tuples whose denominator is bounded by a power of `t` form a submodule. -/
def boundedDenominator (R C : Type*) [CommRing R] [CommRing C] [Algebra R C]
    (t : R) (n : ℕ) : Submodule R C where
  carrier := {x | ∃ a : R, algebraMap R C a = algebraMap R C (t ^ n) * x}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb, mul_add]
  smul_mem' := by
    intro r x hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨r * a, ?_⟩
    rw [map_mul, ha, Algebra.smul_def]
    ring

/-- Products of elements with bounded denominators have bounded denominator. -/
private lemma boundedDenominator_mul (R C : Type*) [CommRing R] [CommRing C]
    [Algebra R C] (t : R) (n m : ℕ) {x y : C}
    (hx : x ∈ boundedDenominator R C t n) (hy : y ∈ boundedDenominator R C t m) :
    x * y ∈ boundedDenominator R C t (n + m) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a * b, ?_⟩
  rw [map_mul, ha, hb, pow_add, map_mul]
  ring

/-- Every element of the base ring lands in the bounded-denominator submodule, since `tⁿ`
times it is again in the base. -/
lemma boundedDenominator_algebraMap (R C : Type*) [CommRing R] [CommRing C]
    [Algebra R C] (t a : R) (n : ℕ) :
    algebraMap R C a ∈ boundedDenominator R C t n := by
  refine ⟨t ^ n * a, ?_⟩
  rw [map_mul]

/-- Allowing a larger power of `t` as denominator gives a larger submodule. -/
private lemma boundedDenominator_mono (R C : Type*) [CommRing R] [CommRing C]
    [Algebra R C] (t : R) {n m : ℕ} (hnm : n ≤ m) :
    boundedDenominator R C t n ≤ boundedDenominator R C t m := by
  intro x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  obtain ⟨a, ha⟩ := hx
  refine ⟨t ^ k * a, ?_⟩
  rw [map_mul, ha, pow_add, map_mul]
  ring

/-- Elements with some bounded denominator form an algebra; this includes `t`-power torsion in
the ambient ring. -/
def boundedDenominatorAlgebra (R C : Type*) [CommRing R] [CommRing C]
    [Algebra R C] (t : R) : Subalgebra R C where
  carrier := {x | ∃ n : ℕ, x ∈ boundedDenominator R C t n}
  zero_mem' := ⟨0, (boundedDenominator R C t 0).zero_mem⟩
  one_mem' := ⟨0, by simpa using boundedDenominator_algebraMap R C t 1 0⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨max n m, (boundedDenominator R C t (max n m)).add_mem ?_ ?_⟩
    · exact boundedDenominator_mono R C t (le_max_left n m) hn
    · exact boundedDenominator_mono R C t (le_max_right n m) hm
  mul_mem' := by
    intro x y hx hy
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨n + m, boundedDenominator_mul R C t n m hn hm⟩
  algebraMap_mem' a := ⟨0, boundedDenominator_algebraMap R C t a 0⟩

/-- Multiplication by `tⁿ` clears the chosen denominator in `A[1/t]`. -/
private lemma away_mul_inv_pow {A : Type*} [CommRing A] (t a : A) (n : ℕ) :
    algebraMap A (Localization.Away t) (t ^ n) *
      (algebraMap A (Localization.Away t) a * (IsLocalization.Away.invSelf t) ^ n) =
        algebraMap A (Localization.Away t) a := by
  rw [map_pow]
  calc
    algebraMap A (Localization.Away t) t ^ n *
        (algebraMap A (Localization.Away t) a * IsLocalization.Away.invSelf t ^ n) =
      (algebraMap A (Localization.Away t) t * IsLocalization.Away.invSelf t) ^ n *
        algebraMap A (Localization.Away t) a := by ring
    _ = algebraMap A (Localization.Away t) a := by
      rw [IsLocalization.Away.mul_invSelf, one_pow, one_mul]

/-- An injective module map with power-torsion cokernel becomes bijective after inverting
the element. -/
private lemma localizedModule_map_bijective_of_power_mem_range
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : R) (f : M →ₗ[R] N) (hf : Function.Injective f)
    (h : ∀ y : N, ∃ n : ℕ, ∃ x : M, f x = t ^ n • y) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers t) f) := by
  constructor
  · exact LocalizedModule.map_injective _ f hf
  · intro z
    induction z using LocalizedModule.induction_on with
    | _ y s =>
      obtain ⟨n, x, hx⟩ := h y
      let tn : Submonoid.powers t := ⟨t ^ n, ⟨n, rfl⟩⟩
      refine ⟨LocalizedModule.mk x (s * tn), ?_⟩
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [one_smul]
      rw [hx]
      simp only [Submonoid.smul_def, mul_smul]
      rfl

/-- If a power of `s` is divisible by the torsion bound `tⁿ`, the modification disappears after
inverting `s`. -/
private lemma localized_algebraMap_bijective_of_divisible_power
    (R C : Type*) [CommRing R] [CommRing C] [Algebra R C]
    (t s : R) (hinj : Function.Injective (algebraMap R C))
    (htorsion : ∃ n : ℕ, ∀ c : C, ∃ a : R,
      algebraMap R C a = algebraMap R C (t ^ n) * c)
    (hdiv : ∀ n : ℕ, ∃ k : ℕ, ∃ a : R, s ^ k = t ^ n * a) :
    Function.Bijective
      (LocalizedModule.map (Submonoid.powers s) (Algebra.linearMap R C)) := by
  obtain ⟨n, hn⟩ := htorsion
  obtain ⟨k, a, ha⟩ := hdiv n
  apply localizedModule_map_bijective_of_power_mem_range s
    (Algebra.linearMap R C) (fun x y hxy => hinj (by
      simpa only [Algebra.linearMap_apply] using hxy))
  intro c
  obtain ⟨b, hb⟩ := hn c
  refine ⟨k, a * b, ?_⟩
  simp only [Algebra.linearMap_apply, map_mul, hb, map_pow]
  rw [ha, Algebra.smul_def, map_mul, map_pow]
  ring

/-- Every element of a finite algebra over a prime localization has an integral multiple by a
denominator outside the prime. -/
lemma exists_integral_multiple_atPrime
    (R C : Type*) [CommRing R] [CommRing C]
    (q : Ideal R) [q.IsPrime]
    [Algebra (Localization.AtPrime q) C] [Algebra R C]
    [IsScalarTower R (Localization.AtPrime q) C]
    [Module.Finite (Localization.AtPrime q) C] (c : C) :
    ∃ s : q.primeCompl, IsIntegral R ((s : R) • c) :=
  IsIntegral.exists_multiple_integral_of_isLocalization
    (M := q.primeCompl) (Rₘ := Localization.AtPrime q) c
    (IsIntegral.of_finite _ c)

/-- A local numerator for `tⁿ b` can be cleared by an element outside the prime to give a
numerator in the original ring. -/
private lemma exists_global_numerator_atPrime
    (R C : Type*) [CommRing R] [CommRing C]
    (q : Ideal R) [q.IsPrime]
    [Algebra (Localization.AtPrime q) C] [Algebra R C]
    [IsScalarTower R (Localization.AtPrime q) C]
    (t : R) (n : ℕ) (c : C)
    (hc : ∃ a : Localization.AtPrime q,
      algebraMap (Localization.AtPrime q) C a = algebraMap R C (t ^ n) * c) :
    ∃ u : q.primeCompl, ∃ a : R,
      algebraMap R C a = algebraMap R C (t ^ n) * (algebraMap R C u * c) := by
  obtain ⟨a₀, ha₀⟩ := hc
  obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj q.primeCompl a₀
  refine ⟨u, a, ?_⟩
  have hmap := congrArg (algebraMap (Localization.AtPrime q) C) hu
  simp only [map_mul, ← IsScalarTower.algebraMap_apply R (Localization.AtPrime q) C] at hmap
  rw [ha₀] at hmap
  rw [← hmap]
  ring

/-- Elements of an algebra which acquire a numerator in a subalgebra after multiplying by an
element outside a prime form a module over the corresponding prime localization. -/
def denominatorSubmodule
    (R C : Type*) [CommRing R] [CommRing C]
    (q : Ideal R) [q.IsPrime]
    [Algebra (Localization.AtPrime q) C] [Algebra R C]
    [IsScalarTower R (Localization.AtPrime q) C]
    (T : Subalgebra R C) : Submodule (Localization.AtPrime q) C where
  carrier := {c | ∃ s : q.primeCompl, algebraMap R C s * c ∈ T}
  zero_mem' := ⟨1, by simp⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s * t, ?_⟩
    have hsum : algebraMap R C ((s * t : q.primeCompl) : R) * (x + y) =
        algebraMap R C t * (algebraMap R C s * x) +
          algebraMap R C s * (algebraMap R C t * y) := by
      simp only [Submonoid.coe_mul, map_mul]
      ring
    rw [hsum]
    exact T.add_mem (T.mul_mem (T.algebraMap_mem _) hs)
      (T.mul_mem (T.algebraMap_mem _) ht)
  smul_mem' := by
    intro r x hx
    obtain ⟨s, hs⟩ := hx
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj q.primeCompl r
    refine ⟨d * s, ?_⟩
    have hdC : (algebraMap (Localization.AtPrime q) C) r *
        algebraMap R C d = algebraMap R C a := by
      have h := congrArg (algebraMap (Localization.AtPrime q) C) hd
      simpa only [map_mul, ← IsScalarTower.algebraMap_apply R (Localization.AtPrime q) C]
        using h
    have hmul : algebraMap R C (((d * s : q.primeCompl) : R)) * (r • x) =
        algebraMap R C a * (algebraMap R C s * x) := by
      simp only [Submonoid.coe_mul, map_mul]
      rw [Algebra.smul_def, ← hdC]
      ring
    rw [hmul]
    exact T.mul_mem (T.algebraMap_mem _) hs

/-- Membership in the denominator submodule, unfolded. -/
lemma mem_denominatorSubmodule_iff
    (R C : Type*) [CommRing R] [CommRing C]
    (q : Ideal R) [q.IsPrime]
    [Algebra (Localization.AtPrime q) C] [Algebra R C]
    [IsScalarTower R (Localization.AtPrime q) C]
    (T : Subalgebra R C) (c : C) :
    c ∈ denominatorSubmodule R C q T ↔
      ∃ s : q.primeCompl, algebraMap R C s * c ∈ T := Iff.rfl

/-- The `A[1/t]` coordinate makes the diagonal map into the ambient product injective. -/
lemma ambient_algebraMap_injective
    {A : Type*} [CommRing A] (t : A) (ht : IsSMulRegular A t)
    {ι : Type*} (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)] [∀ i, Algebra A (Bᵢ i)] :
    Function.Injective
      (algebraMap A (Localization.Away t × (∀ i, Bᵢ i))) := by
  have haway : Function.Injective (algebraMap A (Localization.Away t)) := by
    apply (IsLocalization.injective_iff_isRegular (Submonoid.powers t)).mpr
    rintro ⟨s, n, rfl⟩
    have hn := IsSMulRegular.pow n ht
    exact isLeftRegular_iff_isRegular.mp (isLeftRegular_iff.mpr hn)
  exact fun _ _ hab => haway (congrArg Prod.fst hab)

/-- Projection from the ambient product to the prescribed algebra at index `i`. -/
def ambientProjection
    (A : Type*) [CommRing A] (t : A)
    {ι : Type*} (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)] [∀ i, Algebra A (Bᵢ i)]
    (i : ι) :
    (Localization.Away t × (∀ j, Bᵢ j)) →ₐ[A] Bᵢ i :=
  (Pi.evalAlgHom A Bᵢ i).comp
    (AlgHom.snd A (Localization.Away t) (∀ j, Bᵢ j))

/-- The ambient projection is the evaluation of the second component. -/
lemma ambientProjection_apply
    (A : Type*) [CommRing A] (t : A)
    {ι : Type*} (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)] [∀ i, Algebra A (Bᵢ i)]
    (i : ι) (x : Localization.Away t × (∀ j, Bᵢ j)) :
    ambientProjection A t Bᵢ i x = x.2 i := rfl

/-- The second component of the structure map into the ambient product is the structure map
into the corresponding factor. -/
private lemma ambient_algebraMap_snd_apply
    (A : Type*) [CommRing A] (t : A)
    {ι : Type*} (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)] [∀ i, Algebra A (Bᵢ i)]
    (j : ι) (a : A) :
    (algebraMap A (Localization.Away t × (∀ k, Bᵢ k)) a).2 j =
      algebraMap A (Bᵢ j) a := rfl

/-- The coordinate map from the bounded-denominator algebra to the prescribed local algebra. -/
def boundedDenominatorProjection
    (A : Type*) [CommRing A] (t : A)
    {ι : Type*} (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)] [∀ i, Algebra A (Bᵢ i)]
    (i : ι) :
    (boundedDenominatorAlgebra A (Localization.Away t × (∀ j, Bᵢ j)) t) →ₐ[A] Bᵢ i :=
  (ambientProjection A t Bᵢ i).comp
    (boundedDenominatorAlgebra A (Localization.Away t × (∀ j, Bᵢ j)) t).val

/-- The coordinate map on the bounded-denominator algebra is the evaluation of the second
component of the underlying ambient element. -/
lemma boundedDenominatorProjection_apply
    (A : Type*) [CommRing A] (t : A)
    {ι : Type*} (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)] [∀ i, Algebra A (Bᵢ i)]
    (i : ι)
    (x : boundedDenominatorAlgebra A (Localization.Away t × (∀ j, Bᵢ j)) t) :
    boundedDenominatorProjection A t Bᵢ i x = x.1.2 i := rfl

/-- If only finitely many primes contain an element, the quotient by that element has finite
prime spectrum. -/
private lemma finite_quotient_primeSpectrum_of_finite_primes_over
    {A : Type*} [CommRing A] [IsLocalRing A] (t : A)
    {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i)) :
    Finite (PrimeSpectrum (A ⧸ Ideal.span {t})) := by
  classical
  let f : A →+* A ⧸ Ideal.span {t} := Ideal.Quotient.mk _
  have hinj : Function.Injective (PrimeSpectrum.comap f) :=
    PrimeSpectrum.comap_injective_of_surjective f Ideal.Quotient.mk_surjective
  have hclass (P : PrimeSpectrum (A ⧸ Ideal.span {t})) :
      (PrimeSpectrum.comap f P).asIdeal = IsLocalRing.maximalIdeal A ∨
        ∃ i, (PrimeSpectrum.comap f P).asIdeal = q i := by
    apply (hV _ (PrimeSpectrum.comap f P).isPrime).mp
    have ht : t ∈ Ideal.span ({t} : Set A) := Ideal.subset_span (Set.mem_singleton t)
    have hzero : f t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ht
    show f t ∈ P.asIdeal
    rw [hzero]
    exact (P.asIdeal).zero_mem
  let ix (P : PrimeSpectrum (A ⧸ Ideal.span {t}))
      (h : (PrimeSpectrum.comap f P).asIdeal ≠ IsLocalRing.maximalIdeal A) : ι :=
    Classical.choose (Or.resolve_left (hclass P) h)
  have hix (P : PrimeSpectrum (A ⧸ Ideal.span {t}))
      (h : (PrimeSpectrum.comap f P).asIdeal ≠ IsLocalRing.maximalIdeal A) :
      (PrimeSpectrum.comap f P).asIdeal = q (ix P h) :=
    Classical.choose_spec (Or.resolve_left (hclass P) h)
  let g : PrimeSpectrum (A ⧸ Ideal.span {t}) → Option ι := fun P =>
    if h : (PrimeSpectrum.comap f P).asIdeal = IsLocalRing.maximalIdeal A then none
    else some (ix P h)
  apply Finite.of_injective g
  intro P Q hpq
  apply hinj
  by_cases hp : (PrimeSpectrum.comap f P).asIdeal = IsLocalRing.maximalIdeal A
  · have hq : (PrimeSpectrum.comap f Q).asIdeal = IsLocalRing.maximalIdeal A := by
      by_contra hq
      change Ideal.comap f P.asIdeal = IsLocalRing.maximalIdeal A at hp
      change Ideal.comap f Q.asIdeal ≠ IsLocalRing.maximalIdeal A at hq
      dsimp [g] at hpq
      simp [hp, hq] at hpq
    exact PrimeSpectrum.ext (hp.trans hq.symm)
  · have hq : (PrimeSpectrum.comap f Q).asIdeal ≠ IsLocalRing.maximalIdeal A := by
      intro hq
      change Ideal.comap f P.asIdeal ≠ IsLocalRing.maximalIdeal A at hp
      change Ideal.comap f Q.asIdeal = IsLocalRing.maximalIdeal A at hq
      dsimp [g] at hpq
      simp [hp, hq] at hpq
    have hPQ : ix P hp = ix Q hq := by
      change Ideal.comap f P.asIdeal ≠ IsLocalRing.maximalIdeal A at hp
      change Ideal.comap f Q.asIdeal ≠ IsLocalRing.maximalIdeal A at hq
      dsimp [g] at hpq
      simpa [hp, hq] using hpq
    exact PrimeSpectrum.ext ((hix P hp).trans (hPQ ▸ (hix Q hq).symm))

/-- Nonmaximal primes containing an element are incomparable when its quotient has finite prime
spectrum. -/
private lemma eq_of_le_nonmaximal_primes_over
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) [Finite (PrimeSpectrum (A ⧸ Ideal.span {t}))]
    {P Q : Ideal A} (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPt : t ∈ P) (hQt : t ∈ Q)
    (hPne : P ≠ IsLocalRing.maximalIdeal A)
    (hQne : Q ≠ IsLocalRing.maximalIdeal A)
    (hPQ : P ≤ Q) : P = Q := by
  let I : Ideal A := Ideal.span {t}
  let f : A →+* A ⧸ I := Ideal.Quotient.mk I
  have key (P : Ideal A) (hP : P.IsPrime) (hPt : t ∈ P) (hPne : P ≠ IsLocalRing.maximalIdeal A) :
      (Ideal.map f P).IsPrime ∧ ¬(Ideal.map f P).IsMaximal ∧ Ideal.comap f (Ideal.map f P) = P := by
    have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hPt
    have hcomap : Ideal.comap f (Ideal.map f P) = P := by
      ext a
      exact Ideal.mem_quotient_iff_mem hIP
    refine ⟨Ideal.isPrime_map_quotientMk_of_isPrime hIP, fun hm => hPne ?_, hcomap⟩
    refine IsLocalRing.eq_maximalIdeal ?_
    rw [← hcomap]
    exact Ideal.comap_isMaximal_of_surjective f Ideal.Quotient.mk_surjective
  obtain ⟨hP', hPnotmax, hcomapP⟩ := key P hP hPt hPne
  obtain ⟨hQ', hQnotmax, hcomapQ⟩ := key Q hQ hQt hQne
  have hdim : Ring.KrullDimLE 1 (A ⧸ I) :=
    Ring.krullDimLE_one_of_finite_primeSpectrum _
  have hminQ : Ideal.map f Q ∈ minimalPrimes (A ⧸ I) :=
    (Ring.krullDimLE_one_iff.mp hdim _ hQ').resolve_right hQnotmax
  have heq : Ideal.map f P = Ideal.map f Q :=
    (minimalPrimes_eq_minimals (R := A ⧸ I) ▸ hminQ).eq_of_le hP' (Ideal.map_mono hPQ)
  calc
    P = Ideal.comap f (Ideal.map f P) := hcomapP.symm
    _ = Ideal.comap f (Ideal.map f Q) := congrArg _ heq
    _ = Q := hcomapQ

/-- A finite family of primes incomparable with `qᵢ` has a common element outside `qᵢ`. -/
private lemma exists_element_in_other_primes
    {A : Type*} [CommRing A] {ι : Type*} [Finite ι]
    (q : ι → Ideal A) (hq : ∀ i, (q i).IsPrime)
    (hincomp : ∀ i j, i ≠ j → ¬q j ≤ q i) (i : ι) :
    ∃ s : A, s ∉ q i ∧ ∀ j, j ≠ i → s ∈ q j := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let F : Finset ι := Finset.univ.erase i
  have hnot : ¬F.inf q ≤ q i := by
    rw [(hq i).inf_le']
    rintro ⟨j, hj, hji⟩
    exact hincomp i j (by simpa [F, ne_comm] using hj) hji
  by_contra h
  push Not at h
  apply hnot
  intro s hs
  by_contra hsi
  obtain ⟨j, hj, hjnot⟩ := h s hsi
  exact hjnot ((Finset.inf_le (by simp [F, hj]) : F.inf q ≤ q j) hs)

/-- Listed nonmaximal primes over `t` are incomparable. -/
private lemma listed_prime_eq_of_le
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    {j k : ι} (hle : q j ≤ q k) : q j = q k := by
  let : Finite (PrimeSpectrum (A ⧸ Ideal.span {t})) :=
    finite_quotient_primeSpectrum_of_finite_primes_over t q hV
  have ht (k : ι) : t ∈ q k :=
    (hV (q k) (hq k)).mpr (Or.inr ⟨k, rfl⟩)
  exact eq_of_le_nonmaximal_primes_over t (hq j) (hq k) (ht j) (ht k) (hq_ne j) (hq_ne k) hle

/-- Distinct nonmaximal primes over `t` admit a separating element. -/
private lemma exists_prime_separator
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hq_inj : Function.Injective q)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    {i j : ι} (hij : i ≠ j) : ∃ s : A, s ∈ q j ∧ s ∉ q i := by
  have hnot : ¬q j ≤ q i := fun hle =>
    hij (hq_inj (listed_prime_eq_of_le t q hq hq_ne hV hle)).symm
  by_contra h
  push Not at h
  exact hnot (fun x hx => h x hx)

/-- One element avoids `qᵢ` and lies in every other listed prime. -/
private lemma exists_common_prime_separator
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hq_inj : Function.Injective q)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (i : ι) : ∃ s : A, s ∉ q i ∧ ∀ j, j ≠ i → s ∈ q j := by
  apply exists_element_in_other_primes q hq
  intro k j hkj hle
  exact hkj (hq_inj (listed_prime_eq_of_le t q hq hq_ne hV hle)).symm

/-- A listed nonmaximal prime is minimal over the principal ideal generated by `t`. -/
private lemma listed_prime_mem_minimalPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (i : ι) : q i ∈ (Ideal.span {t}).minimalPrimes := by
  have hIq : Ideal.span {t} ≤ q i :=
    (Ideal.span_singleton_le_iff_mem _).mpr ((hV _ (hq i)).mpr (Or.inr ⟨i, rfl⟩))
  let : (q i).IsPrime := hq i
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hIq
  have hpprime : p.IsPrime := hp.1.1
  have hpt : t ∈ p := hp.1.2 (Ideal.subset_span (Set.mem_singleton t))
  rcases (hV p hpprime).mp hpt with hpm | ⟨k, hpk⟩
  · have hqm : q i ≤ IsLocalRing.maximalIdeal A := by
      let : (q i).IsPrime := hq i
      exact IsLocalRing.le_maximalIdeal_of_isPrime _
    exact False.elim (hq_ne i (le_antisymm hqm (hpm ▸ hpq)))
  · exact (listed_prime_eq_of_le t q hq hq_ne hV (hpk ▸ hpq) ▸ hpk.symm ▸ hp)

/-- At a listed minimal prime, a power of every element of that prime lies in the extension
of the principal ideal `(t)`. -/
private lemma exists_pow_mem_map_span_singleton_atPrime
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (i : ι) (s : A) (hs : s ∈ q i) :
    ∃ n : ℕ, (algebraMap A (Localization.AtPrime (q i)) s) ^ n ∈
      Ideal.map (algebraMap A (Localization.AtPrime (q i))) (Ideal.span {t}) := by
  let : (q i).IsPrime := hq i
  have hmin := listed_prime_mem_minimalPrimes t q hq hq_ne hV i
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (Localization.AtPrime (q i)) (q i) (Ideal.span {t}) hmin
  have hmem : algebraMap A (Localization.AtPrime (q i)) s ∈
      Ideal.map (algebraMap A (Localization.AtPrime (q i))) (q i) :=
    Ideal.mem_map_of_mem _ hs
  rw [← hrad] at hmem
  exact Ideal.mem_radical_iff.mp hmem

/-- A separating element in `qᵢ` acquires a power divisible by `t` in `A_{qᵢ}`. -/
private lemma exists_pow_divisible_atPrime
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (i : ι) (s : A) (hs : s ∈ q i) :
    ∃ n : ℕ, ∃ a : Localization.AtPrime (q i),
      algebraMap A (Localization.AtPrime (q i)) s ^ n =
        algebraMap A (Localization.AtPrime (q i)) t * a := by
  obtain ⟨n, hn⟩ := exists_pow_mem_map_span_singleton_atPrime t q hq hq_ne hV i s hs
  have hspan : algebraMap A (Localization.AtPrime (q i)) s ^ n ∈
      Ideal.span {algebraMap A (Localization.AtPrime (q i)) t} := by
    simpa only [Ideal.map_span, Set.image_singleton] using hn
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hspan
  exact ⟨n, a, by rw [← ha, mul_comm]⟩

/-- The same divisibility holds by any prescribed power of `t`. -/
private lemma exists_pow_divisible_by_pow_atPrime
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (i : ι) (s : A) (hs : s ∈ q i) (N : ℕ) :
    ∃ n : ℕ, ∃ a : Localization.AtPrime (q i),
      algebraMap A (Localization.AtPrime (q i)) s ^ n =
        algebraMap A (Localization.AtPrime (q i)) (t ^ N) * a := by
  obtain ⟨k, a, ha⟩ := exists_pow_divisible_atPrime t q hq hq_ne hV i s hs
  refine ⟨k * N, a ^ N, ?_⟩
  rw [pow_mul, ha, mul_pow, map_pow]

/-- One separator power is divisible by `tᴺ` at every other listed prime. -/
private lemma exists_common_separator_power
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hq_inj : Function.Injective q)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (i : ι) (N : ℕ) :
    ∃ s : A, s ∉ q i ∧ ∃ K : ℕ, ∀ j, j ≠ i →
      ∃ a : Localization.AtPrime (q j),
        algebraMap A (Localization.AtPrime (q j)) s ^ K =
          algebraMap A (Localization.AtPrime (q j)) (t ^ N) * a := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨s, hsi, hsj⟩ := exists_common_prime_separator t q hq hq_ne hq_inj hV i
  have hex (j : ι) : ∃ k : ℕ, ∃ a : Localization.AtPrime (q j),
      j ≠ i → algebraMap A (Localization.AtPrime (q j)) s ^ k =
        algebraMap A (Localization.AtPrime (q j)) (t ^ N) * a := by
    by_cases hji : j = i
    · exact ⟨0, 0, fun h => (h hji).elim⟩
    · obtain ⟨k, a, ha⟩ := exists_pow_divisible_by_pow_atPrime
        t q hq hq_ne hV j s (hsj j hji) N
      exact ⟨k, a, fun _ => ha⟩
  choose k a ha using hex
  let K := Finset.univ.sup k
  refine ⟨s, hsi, K, fun j hji => ?_⟩
  have hle : k j ≤ K := Finset.le_sup (f := k) (Finset.mem_univ j)
  refine ⟨a j * algebraMap A (Localization.AtPrime (q j)) s ^ (K - k j), ?_⟩
  calc
    algebraMap A (Localization.AtPrime (q j)) s ^ K =
        algebraMap A (Localization.AtPrime (q j)) s ^ (k j + (K - k j)) := by
          congr 1
          omega
    _ = algebraMap A (Localization.AtPrime (q j)) s ^ (k j) *
        algebraMap A (Localization.AtPrime (q j)) s ^ (K - k j) := pow_add _ _ _
    _ = algebraMap A (Localization.AtPrime (q j)) (t ^ N) *
        (a j * algebraMap A (Localization.AtPrime (q j)) s ^ (K - k j)) := by
          rw [ha j hji]
          ring

/-- At a different listed prime, one can invert a separator so that the prescribed finite
modification agrees with its base ring. -/
private lemma exists_separator_localized_algebraMap_bijective
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hq_inj : Function.Injective q)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)]
    [∀ i, Algebra (Localization.AtPrime (q i)) (Bᵢ i)]
    [∀ i, Algebra A (Bᵢ i)]
    [∀ i, IsScalarTower A (Localization.AtPrime (q i)) (Bᵢ i)]
    (hinj : ∀ i, Function.Injective
      (algebraMap (Localization.AtPrime (q i)) (Bᵢ i)))
    (htorsion : ∀ i, ∃ n : ℕ, ∀ b : Bᵢ i, ∃ a : Localization.AtPrime (q i),
      algebraMap (Localization.AtPrime (q i)) (Bᵢ i) a =
        algebraMap A (Bᵢ i) (t ^ n) * b)
    {i j : ι} (hij : i ≠ j) :
    ∃ s : A, s ∈ q j ∧ s ∉ q i ∧
      Function.Bijective
        (LocalizedModule.map
          (Submonoid.powers (algebraMap A (Localization.AtPrime (q j)) s))
          (Algebra.linearMap (Localization.AtPrime (q j)) (Bᵢ j))) := by
  obtain ⟨s, hsj, hsi⟩ := exists_prime_separator t q hq hq_ne hq_inj hV hij
  refine ⟨s, hsj, hsi, ?_⟩
  apply localized_algebraMap_bijective_of_divisible_power
    (Localization.AtPrime (q j)) (Bᵢ j)
    (algebraMap A (Localization.AtPrime (q j)) t)
    (algebraMap A (Localization.AtPrime (q j)) s) (hinj j)
  · obtain ⟨n, hn⟩ := htorsion j
    refine ⟨n, fun b => ?_⟩
    obtain ⟨a, ha⟩ := hn b
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime (q j)) (Bᵢ j) (t ^ n),
      map_pow] at ha
    exact ha
  · intro N
    obtain ⟨k, a, ha⟩ := exists_pow_divisible_by_pow_atPrime
      t q hq hq_ne hV j s hsj N
    exact ⟨k, a, by simpa only [map_pow] using ha⟩

/-- Transport a divisibility `s ^ K = t ^ N * d` from a localization `L` to an algebra over it. -/
private lemma algebraMap_pow_eq_mul_of_atPrime {A : Type*} (L B : Type*) [CommRing A] [CommRing L]
    [CommRing B] [Algebra A L] [Algebra L B] [Algebra A B] [IsScalarTower A L B]
    {s t : A} {K N : ℕ} {d : L} (h : algebraMap A L s ^ K = algebraMap A L (t ^ N) * d) :
    algebraMap A B s ^ K = algebraMap A B (t ^ N) * algebraMap L B d := by
  simpa only [map_mul, map_pow, IsScalarTower.algebraMap_apply A L B] using
    congrArg (algebraMap L B) h

/-- After multiplying by an element outside `qᵢ`, a prescribed local element is the `i`th
coordinate of a bounded-denominator tuple in the ambient product. -/
lemma exists_boundedDenominator_lift
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hq_inj : Function.Injective q)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)]
    [∀ i, Algebra (Localization.AtPrime (q i)) (Bᵢ i)]
    [∀ i, Algebra A (Bᵢ i)]
    [∀ i, IsScalarTower A (Localization.AtPrime (q i)) (Bᵢ i)]
    (htorsion : ∀ i, ∃ n : ℕ, ∀ b : Bᵢ i, ∃ a : Localization.AtPrime (q i),
      algebraMap (Localization.AtPrime (q i)) (Bᵢ i) a =
        algebraMap A (Bᵢ i) (t ^ n) * b)
    (i : ι) (b : Bᵢ i) :
    ∃ n : ℕ, ∃ x : Localization.Away t × (∀ j, Bᵢ j), ∃ v : (q i).primeCompl,
      x ∈ boundedDenominator A (Localization.Away t × (∀ j, Bᵢ j)) t n ∧
        ambientProjection A t Bᵢ i x = algebraMap A (Bᵢ i) v * b := by
  classical
  obtain ⟨n, hn⟩ := htorsion i
  obtain ⟨a₀, ha₀⟩ := hn b
  obtain ⟨u, a, ha⟩ := exists_global_numerator_atPrime
    A (Bᵢ i) (q i) t n b ⟨a₀, ha₀⟩
  obtain ⟨s, hsi, K, hd⟩ := exists_common_separator_power
    t q hq hq_ne hq_inj hV i n
  let v : (q i).primeCompl := ⟨u * s ^ K, by
    have hsK : s ^ K ∉ q i := fun h => hsi ((hq i).mem_of_pow_mem K h)
    exact (hq i).mul_notMem u.property hsK⟩
  let d (j : ι) (hji : j ≠ i) : Localization.AtPrime (q j) :=
    Classical.choose (hd j hji)
  let y : ∀ j, Bᵢ j := fun j =>
    if hji : j = i then hji.symm ▸ (algebraMap A (Bᵢ i) v * b)
    else algebraMap (Localization.AtPrime (q j)) (Bᵢ j)
      (algebraMap A (Localization.AtPrime (q j)) a * d j hji)
  let x : Localization.Away t × (∀ j, Bᵢ j) :=
    (algebraMap A (Localization.Away t) (a * s ^ K) *
      (IsLocalization.Away.invSelf t) ^ n, y)
  refine ⟨n, x, v, ?_, ?_⟩
  · refine ⟨a * s ^ K, ?_⟩
    apply Prod.ext
    · exact (away_mul_inv_pow t (a * s ^ K) n).symm
    · funext j
      by_cases hji : j = i
      · subst j
        show (algebraMap A (Localization.Away t × (∀ j, Bᵢ j)) (a * s ^ K)).2 i =
          (algebraMap A (Localization.Away t × (∀ j, Bᵢ j)) (t ^ n)).2 i * y i
        rw [ambient_algebraMap_snd_apply A t Bᵢ i,
          ambient_algebraMap_snd_apply A t Bᵢ i]
        simp only [y, dite_eq_left rfl, v, map_mul, map_pow]
        rw [ha, map_pow]
        ring
      · show (algebraMap A (Localization.Away t × (∀ j, Bᵢ j)) (a * s ^ K)).2 j =
          (algebraMap A (Localization.Away t × (∀ j, Bᵢ j)) (t ^ n)).2 j * y j
        rw [ambient_algebraMap_snd_apply A t Bᵢ j,
          ambient_algebraMap_snd_apply A t Bᵢ j]
        simp only [y, dite_eq_right hji, map_mul, map_pow]
        rw [algebraMap_pow_eq_mul_of_atPrime (Localization.AtPrime (q j)) (Bᵢ j)
          (Classical.choose_spec (hd j hji)), map_pow,
          IsScalarTower.algebraMap_apply A (Localization.AtPrime (q j)) (Bᵢ j) a]
        ring
  · simp [ambientProjection_apply, x, y]

/-- In `A[1/t]`, an element killed by `v` after clearing the denominator `t ^ N` is killed
by `v`. -/
private lemma away_algebraMap_mul_eq_zero {A : Type*} [CommRing A] (t : A) (N : ℕ)
    {a v : A} {y : Localization.Away t}
    (ha : algebraMap A (Localization.Away t) a =
      algebraMap A (Localization.Away t) (t ^ N) * y)
    (hv : v * a = 0) : algebraMap A (Localization.Away t) v * y = 0 := by
  have hunit : IsUnit (algebraMap A (Localization.Away t) (t ^ N)) :=
    IsLocalization.map_units (M := Submonoid.powers t) (Localization.Away t)
      ⟨t ^ N, ⟨N, rfl⟩⟩
  refine hunit.mul_left_cancel ?_
  calc algebraMap A (Localization.Away t) (t ^ N) * (algebraMap A (Localization.Away t) v * y)
      = algebraMap A (Localization.Away t) v *
          (algebraMap A (Localization.Away t) (t ^ N) * y) := by ring
    _ = algebraMap A (Localization.Away t) (v * a) := by rw [← ha, map_mul]
    _ = algebraMap A (Localization.Away t) (t ^ N) * 0 := by rw [hv, map_zero, mul_zero]

/-- If `t ^ N` divides `s ^ K` in `B` and `u` kills `a = t ^ N * y`, then `u * s ^ K`
kills `y`. -/
private lemma algebraMap_mul_pow_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {a u s t : A} {K N : ℕ} {y d : B}
    (ha : algebraMap A B a = algebraMap A B (t ^ N) * y) (hu : u * a = 0)
    (hs : algebraMap A B s ^ K = algebraMap A B (t ^ N) * d) :
    algebraMap A B (u * s ^ K) * y = 0 := by
  calc algebraMap A B (u * s ^ K) * y
      = d * (algebraMap A B u * (algebraMap A B (t ^ N) * y)) := by
        rw [map_mul, map_pow _ s, hs]
        ring
    _ = 0 := by rw [← ha, ← map_mul, hu, map_zero, mul_zero]

/-- The kernel of a coordinate projection on bounded-denominator tuples is killed by some
element outside the corresponding prime. -/
lemma boundedDenominator_projection_kernel_torsion
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (t : A) {ι : Type*} [Finite ι] (q : ι → Ideal A)
    (hq : ∀ i, (q i).IsPrime)
    (hq_ne : ∀ i, q i ≠ IsLocalRing.maximalIdeal A)
    (hq_inj : Function.Injective q)
    (hV : ∀ p : Ideal A, p.IsPrime →
      (t ∈ p ↔ p = IsLocalRing.maximalIdeal A ∨ ∃ i, p = q i))
    (Bᵢ : ι → Type*) [∀ i, CommRing (Bᵢ i)]
    [∀ i, Algebra (Localization.AtPrime (q i)) (Bᵢ i)]
    [∀ i, Algebra A (Bᵢ i)]
    [∀ i, IsScalarTower A (Localization.AtPrime (q i)) (Bᵢ i)]
    (hinj : ∀ i, Function.Injective
      (algebraMap (Localization.AtPrime (q i)) (Bᵢ i)))
    (i : ι) (N : ℕ)
    (x : Localization.Away t × (∀ j, Bᵢ j))
    (hx : x ∈ boundedDenominator A (Localization.Away t × (∀ j, Bᵢ j)) t N)
    (hxi : ambientProjection A t Bᵢ i x = 0) :
    ∃ v : (q i).primeCompl,
      algebraMap A (Localization.Away t × (∀ j, Bᵢ j)) v * x = 0 := by
  classical
  obtain ⟨a, ha⟩ := hx
  have hx0 : x.2 i = 0 := by simpa [ambientProjection_apply] using hxi
  have ha_i : algebraMap A (Bᵢ i) a = 0 := by
    have h := congrArg (fun z : Localization.Away t × (∀ j, Bᵢ j) => z.2 i) ha
    change algebraMap A (Bᵢ i) a = algebraMap A (Bᵢ i) (t ^ N) * x.2 i at h
    simpa [hx0] using h
  have ha_loc : algebraMap A (Localization.AtPrime (q i)) a = 0 := by
    apply hinj i
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime (q i)) (Bᵢ i)]
    simpa using ha_i
  obtain ⟨u, hu⟩ :=
    (IsLocalization.map_eq_zero_iff (q i).primeCompl (Localization.AtPrime (q i)) a).mp ha_loc
  obtain ⟨s, hsi, K, hd⟩ := exists_common_separator_power
    t q hq hq_ne hq_inj hV i N
  let v : (q i).primeCompl := ⟨u * s ^ K, by
    have hsK : s ^ K ∉ q i := fun h => hsi ((hq i).mem_of_pow_mem K h)
    exact (hq i).mul_notMem u.property hsK⟩
  refine ⟨v, Prod.ext ?_ (funext fun j => ?_)⟩
  · show algebraMap A (Localization.Away t) (u * s ^ K) * x.1 = 0
    exact away_algebraMap_mul_eq_zero t N (a := a)
      (by simpa using congrArg Prod.fst ha) (by rw [mul_right_comm, hu, zero_mul])
  · by_cases hji : j = i
    · subst j
      simp [hx0]
    · obtain ⟨d, hsd⟩ := hd j hji
      show algebraMap A (Bᵢ j) (u * s ^ K) * x.2 j = 0
      exact algebraMap_mul_pow_eq_zero (a := a)
        (by simpa using congrArg (fun z : Localization.Away t × (∀ k, Bᵢ k) => z.2 j) ha)
        hu (algebraMap_pow_eq_mul_of_atPrime (Localization.AtPrime (q j)) (Bᵢ j) hsd)

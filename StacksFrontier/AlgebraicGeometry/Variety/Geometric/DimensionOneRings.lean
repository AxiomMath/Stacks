module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.IntegralClosure
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.MinimalPrimesPower
public import StacksFrontier.RingTheory.Artinian.Basic
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Valuation.Restriction

/-!
# A parameter in the image of an integral subring

Let `A` be a one-dimensional Noetherian local ring, and let `L` be the product of its
localizations at the minimal primes. If a ring map from `K` to `L` is integral, then the
image of `K` meets the image of `A` in an element of the maximal ideal whose principal
ideal has radical equal to the maximal ideal.

## Main results

* `IsLocalRing.exists_mem_maximalIdeal_radical_span_eq_of_isIntegral` gives the common
  element and its preimages in `A` and `K`.

## Implementation notes

The product is indexed by minimal points of the prime spectrum. The equality of images is
stated using the canonical algebra map from `A` and the given ring homomorphism from `K`.

The parameter is produced one minimal prime at a time. Over each minimal prime the quotient is
a one-dimensional Noetherian local domain, so its integral closure in its fraction field is a
semilocal Dedekind domain; an element of the integral subring whose valuation is small at every
height-one prime of that closure has a positive power in the maximal ideal of the quotient.
Combining the resulting elements and clearing the discrepancy, which is nilpotent, gives the
element of `A`.

## References

* [Stacks Project, Tag 0AB4](https://stacks.math.columbia.edu/tag/0AB4)
-/

@[expose] public section

namespace IsLocalRing

open scoped NNReal

universe u v

/-- A Noetherian ring has finitely many minimal primes. -/
private lemma finite_minimalPrimePoints (A : Type*) [CommRing A] [IsNoetherianRing A] :
    Finite {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} := by
  have := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  exact Finite.of_injective
    (fun p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} =>
      (⟨p.1.asIdeal, p.2⟩ : minimalPrimes A))
    (fun p q h => Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val h)))

/-- A nontrivial valuation on an algebraic field extension restricts to a nontrivial
valuation on the base field. -/
private lemma valuation_comap_isNontrivial_of_algebraic {K L : Type*} [Field K] [Field L]
    [Algebra K L] (halg : Algebra.IsAlgebraic K L)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
    (hv : v.IsNontrivial) : (v.comap (algebraMap K L)).IsNontrivial := by
  have : Algebra.IsAlgebraic K L := halg
  let B := v.valuationSubring
  have hB : B ≠ ⊤ := fun h => v.valuationSubring_eq_top_iff.mp h hv
  have hEq : (v.comap (algebraMap K L)).valuationSubring =
      intersectionSubring B := by
    ext x
    show v (algebraMap K L x) ≤ 1 ↔ algebraMap K L x ∈ B
    rw [← ValuationSubring.valuation_le_one_iff B]
    simp [B]
  have hnot : (v.comap (algebraMap K L)).valuationSubring ≠ ⊤ := by
    rw [hEq]
    exact intersectionSubring_ne_top halg B hB
  by_contra hn
  exact hnot ((v.comap (algebraMap K L)).valuationSubring_eq_top_iff.mpr hn)

/-- The quotient of a local ring by a prime is local. -/
private instance isLocalRing_quotient_of_isPrime {A : Type*} [CommRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] : IsLocalRing (A ⧸ p) :=
  .of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

/-- The quotient of a one-dimensional ring by a prime has Krull dimension at most one. -/
private lemma krullDimLE_one_quotient {A : Type*} [CommRing A] (hdim : ringKrullDim A = 1)
    (p : Ideal A) [p.IsPrime] : Ring.KrullDimLE 1 (A ⧸ p) :=
  Ring.krullDimLE_iff.mpr ((ringKrullDim_quotient_le p).trans hdim.le)

/-- Modulo a prime, a one-dimensional Noetherian local ring has an integral closure in its
fraction field which is a semilocal Dedekind domain. -/
@[ega "0 23.2.6" "special case", ega "0 23.2.7" "special case", ega "0 23.2.8" "special case"]
private lemma integralClosure_quotient_dedekind_semilocal (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hdim : ringKrullDim A = 1)
    (p : Ideal A) [p.IsPrime] :
    let B := A ⧸ p
    let C := integralClosure B (FractionRing B)
    IsDedekindDomain C ∧ Finite (MaximalSpectrum C) := by
  classical
  let B := A ⧸ p
  have : IsDomain B := Ideal.Quotient.isDomain p
  have := krullDimLE_one_quotient hdim p
  have : Ring.DimensionLEOne B := ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  let C := integralClosure B (FractionRing B)
  exact ⟨(IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
    B (FractionRing B) (FractionRing B) C).1, IsIntegralClosure.finite_maximalSpectrum B
    (FractionRing B) C⟩

/-- If the maximal ideal of a local domain contains a nonzero element, its integral closure
in the fraction field is not a field. -/
private lemma integralClosure_not_field_of_nonzero_maximal_element
    (B F C : Type*) [CommRing B] [IsDomain B] [IsLocalRing B]
    [Field F] [Algebra B F] [IsFractionRing B F]
    [CommRing C] [IsDomain C] [Algebra B C] [Algebra C F]
    [IsScalarTower B C F] [IsIntegralClosure C B F]
    (b : B) (hb : b ∈ IsLocalRing.maximalIdeal B) (hb0 : b ≠ 0) : ¬ IsField C := by
  have : Algebra.IsIntegral B C := IsIntegralClosure.isIntegral_algebra B F
  have hinj : Function.Injective (algebraMap B C) := by
    intro x y h
    apply IsFractionRing.injective B F
    simpa only [IsScalarTower.algebraMap_apply B C F] using congrArg (algebraMap C F) h
  intro hC
  let : Field B := (isField_of_isIntegral_of_isField hinj hC).toField
  exact hb (isUnit_iff_ne_zero.mpr hb0)

/-- The image of the complement of a prime in the quotient by that prime is the set of
nonzerodivisors. -/
private lemma primeCompl_map_quotient_nonZeroDivisors {A : Type*} [CommRing A]
    (p : Ideal A) [p.IsPrime] :
    p.primeCompl.map (Ideal.Quotient.mk p) = nonZeroDivisors (A ⧸ p) := by
  classical
  let B := A ⧸ p
  have : IsDomain B := Ideal.Quotient.isDomain p
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  · intro hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨a, fun ha => mem_nonZeroDivisors_iff_ne_zero.mp hy
      (Ideal.Quotient.eq_zero_iff_mem.mpr ha), rfl⟩

/-- The fraction field of the quotient by a prime is the localization at the image of the
complement of the prime. -/
private lemma isLocalization_map_primeCompl_quotient {A : Type*} [CommRing A]
    (p : Ideal A) [p.IsPrime] :
    IsLocalization (p.primeCompl.map (Ideal.Quotient.mk p)) (FractionRing (A ⧸ p)) := by
  have : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  rw [primeCompl_map_quotient_nonZeroDivisors]
  infer_instance

/-- The canonical surjection from the localization at a prime onto the fraction field of the
quotient by that prime. -/
private noncomputable def minimalLocalizationToFractionRing {A : Type*} [CommRing A]
    (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime p →+* FractionRing (A ⧸ p) := by
  classical
  letI := isLocalization_map_primeCompl_quotient p
  exact IsLocalization.map (FractionRing (A ⧸ p)) (Ideal.Quotient.mk p) p.primeCompl.le_comap_map

/-- That canonical map onto the fraction field of the quotient is surjective. -/
private lemma minimalLocalizationToFractionRing_surjective {A : Type*} [CommRing A]
    (p : Ideal A) [p.IsPrime] :
    Function.Surjective (minimalLocalizationToFractionRing p) := by
  classical
  let := isLocalization_map_primeCompl_quotient p
  simpa [minimalLocalizationToFractionRing] using
    (IsLocalization.map_surjective_of_surjective (M := p.primeCompl)
      (S := Localization.AtPrime p) (g := Ideal.Quotient.mk p)
      (Q := FractionRing (A ⧸ p)) Ideal.Quotient.mk_surjective)

/-- The product, over the minimal primes, of the fraction fields of the corresponding
quotients. -/
private abbrev minimalFractionProduct (A : Type*) [CommRing A] :=
  ∀ p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A},
    FractionRing (A ⧸ p.1.asIdeal)

/-- The product of the canonical surjections, from the product of the localizations at the
minimal primes onto the product of the fraction fields of the quotients. -/
private noncomputable def minimalLocalizationProductToFractionProduct (A : Type*)
    [CommRing A] :
    (∀ p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A},
      Localization.AtPrime p.1.asIdeal) →+* minimalFractionProduct A :=
  RingHom.pi (fun p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} =>
    (minimalLocalizationToFractionRing p.1.asIdeal).comp
      (Pi.evalRingHom (fun p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} =>
        Localization.AtPrime p.1.asIdeal) p))

/-- That product of canonical surjections is surjective. -/
private lemma minimalLocalizationProductToFractionProduct_surjective (A : Type*)
    [CommRing A] : Function.Surjective (minimalLocalizationProductToFractionProduct A) := by
  classical
  intro y
  choose x hx using fun p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} =>
    minimalLocalizationToFractionRing_surjective p.1.asIdeal (y p)
  exact ⟨x, funext hx⟩

/-- The canonical surjection sends the image of a ring element to the image of its class in
the quotient. -/
private lemma minimalLocalizationToFractionRing_algebraMap {A : Type*} [CommRing A]
    (p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}) (a : A) :
    minimalLocalizationToFractionRing p.1.asIdeal
        (algebraMap A (Localization.AtPrime p.1.asIdeal) a) =
      algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal))
        (Ideal.Quotient.mk p.1.asIdeal a) := by
  simp [minimalLocalizationToFractionRing]

/-- Finitely many valuations, each taking some value greater than one, take a value greater
than one at a common element. -/
private lemma exists_simultaneously_one_lt {R ι : Type*} [CommRing R] [Finite ι]
    (v : ι → Valuation R ℝ≥0) (hv : ∀ i, ∃ x, 1 < v i x) :
    ∃ x, ∀ i, 1 < v i x := by
  classical
  let := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, ∃ x, ∀ i ∈ s, 1 < v i x by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨x, hx⟩ := ih
    by_cases hxi : 1 < v i x
    · exact ⟨x, by simpa using And.intro hxi hx⟩
    obtain ⟨y, hy⟩ := hv i
    have hevent : ∀ᶠ n : ℕ in Filter.atTop, 0 < n ∧
        ∀ j ∈ s, v j y < v j (x ^ n) := by
      have hpow : ∀ j ∈ s, ∀ᶠ n : ℕ in Filter.atTop, v j y < v j x ^ n :=
        fun j hj => (tendsto_pow_atTop_atTop_of_one_lt (hx j hj)).eventually_gt_atTop _
      filter_upwards [Filter.eventually_gt_atTop 0,
        (Filter.eventually_all_finset s).mpr hpow] with n hn hn'
      exact ⟨hn, by simpa only [map_pow] using hn'⟩
    obtain ⟨n, hn, hny⟩ := hevent.exists
    refine ⟨x ^ n + y, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with hji | hj
    · subst j
      have hlow : v i (x ^ n) ≤ 1 := by
        rw [map_pow]
        exact pow_le_one₀ zero_le (le_of_not_gt hxi)
      rwa [(v i).map_add_eq_of_lt_right (hlow.trans_lt hy)]
    · rw [add_comm, (v j).map_add_eq_of_lt_right (hny j hj), map_pow]
      exact one_lt_pow₀ (hx j hj) hn.ne'

/-- A nontrivial valuation on a field takes a value greater than one on the image of an
integral subring. -/
private lemma integral_valuation_has_large_value {R F : Type*} [CommRing R] [Field F]
    (f : R →+* F) (hf : f.IsIntegral)
    (v : Valuation F (WithZero (Multiplicative ℤ))) [v.IsNontrivial] :
    ∃ x : R, 1 < v (f x) := by
  let E := f.range
  let g : E →+* F := f.range.subtype
  have hg : g.IsIntegral := RingHom.IsIntegral.tower_top f.rangeRestrict g hf
  let : Algebra E F := g.toAlgebra
  have : Algebra.IsIntegral E F := ⟨hg⟩
  have hfield : IsField E := isField_of_isIntegral_of_isField
    (show Function.Injective (algebraMap E F) from Subtype.val_injective) (Field.toIsField F)
  let : Field E := hfield.toField
  have : (v.comap g).IsNontrivial :=
    valuation_comap_isNontrivial_of_algebraic Algebra.IsIntegral.isAlgebraic v inferInstance
  obtain ⟨x, hx⟩ := Valuation.IsNontrivial.exists_one_lt (v := v.comap g)
  obtain ⟨a, ha⟩ := x.property
  refine ⟨a, ?_⟩
  change 1 < v (x : F) at hx
  rwa [← ha] at hx

/-- An integral subring of a finite product of fields contains an element with nonzero
components whose valuation is less than one at each of finitely many valuations. -/
private lemma exists_inverse_small_in_integral_range
    {ι : Type*} [Finite ι] (F : ι → Type*) [∀ i, Field (F i)]
    (J : ι → Type*) [∀ i, Finite (J i)] [∀ i, Nonempty (J i)]
    (v : ∀ i, J i → Valuation (F i) (WithZero (Multiplicative ℤ)))
    (hv : ∀ i j, (v i j).IsNontrivial)
    {K : Type*} [CommRing K] (f : K →+* ∀ i, F i) (hf : f.IsIntegral) :
    ∃ x : K, (∀ i, f x i ≠ 0) ∧ ∀ i j, v i j (f x i) < 1 := by
  classical
  let E := f.range
  let g : E →+* ∀ i, F i := f.range.subtype
  have hg : g.IsIntegral := RingHom.IsIntegral.tower_top f.rangeRestrict g hf
  let φ := WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)
  have hφ : StrictMono φ := WithZeroMulInt.toNNReal_strictMono (by norm_num : 1 < (2 : ℝ≥0))
  let w : (Σ i, J i) → Valuation E ℝ≥0 := fun s =>
    ((v s.1 s.2).comap ((Pi.evalRingHom F s.1).comp g)).map φ hφ.monotone
  have hw : ∀ s, ∃ x, 1 < w s x := by
    rintro ⟨i, j⟩
    have := hv i j
    have heval : Function.Surjective (Pi.evalRingHom F i) := fun a =>
      ⟨Pi.single i a, by simp⟩
    have hi : ((Pi.evalRingHom F i).comp g).IsIntegral :=
      hg.trans _ _ (RingHom.isIntegral_of_surjective _ heval)
    obtain ⟨x, hx⟩ := integral_valuation_has_large_value _ hi (v i j)
    exact ⟨x, by simpa [w] using hφ hx⟩
  obtain ⟨x, hx⟩ := exists_simultaneously_one_lt w hw
  have hxv : ∀ i j, 1 < v i j (g x i) := by
    intro i j
    have h := hx ⟨i, j⟩
    change 1 < φ (v i j (g x i)) at h
    exact hφ.lt_iff_lt.mp (by simpa only [map_one] using h)
  have hxn : ∀ i, g x i ≠ 0 := fun i heq => by
    simpa [heq] using hxv i (Classical.arbitrary _)
  have hxu : IsUnit (g x) :=
    ⟨⟨g x, fun i => (g x i)⁻¹, funext fun i => by simp [hxn], funext fun i => by simp [hxn]⟩, rfl⟩
  have : IsLocalHom g := hg.isLocalHom Subtype.val_injective
  obtain ⟨u, hu⟩ := (isUnit_map_iff g x).mp hxu
  obtain ⟨a, ha⟩ := (↑(u⁻¹) : E).property
  have heq (i) : f a i * g (↑u) i = 1 := by
    have h := congrFun (congrArg g (show (↑u⁻¹ : E) * ↑u = 1 by simp)) i
    change (↑(↑u⁻¹ : E) : ∀ i, F i) i * g (↑u) i = 1 at h
    rwa [← ha] at h
  refine ⟨a, fun i => left_ne_zero_of_mul_eq_one (heq i), fun i j => ?_⟩
  have hval := congrArg (v i j) (heq i)
  rw [hu, map_mul, map_one] at hval
  have hpos := hxv i j
  exact (mul_lt_mul_iff_left₀ (zero_lt_one.trans hpos)).mp (by simpa [hval] using hpos)

/-- A semilocal Dedekind domain has finitely many height-one primes. -/
private lemma finite_heightOneSpectrum (C : Type*) [CommRing C] [IsDedekindDomain C]
    [Finite (MaximalSpectrum C)] : Finite (IsDedekindDomain.HeightOneSpectrum C) :=
  Finite.of_injective (fun p : IsDedekindDomain.HeightOneSpectrum C =>
    (⟨p.asIdeal, p.isMaximal⟩ : MaximalSpectrum C))
    (fun _ _ h => IsDedekindDomain.HeightOneSpectrum.ext (congrArg MaximalSpectrum.asIdeal h))

/-- A Dedekind domain that is not a field has a height-one prime. -/
private lemma nonempty_heightOneSpectrum (C : Type*) [CommRing C] [IsDedekindDomain C]
    (hC : ¬ IsField C) : Nonempty (IsDedekindDomain.HeightOneSpectrum C) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm hC⟩⟩

/-- An element of the fraction field whose valuation is less than one at every height-one
prime of the integral closure has a positive power in the maximal ideal of the base. -/
private lemma exists_pow_in_maximalIdeal_of_valuations_lt_one
    (B F C : Type*) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Ring.DimensionLEOne B]
    [Field F] [Algebra B F] [IsFractionRing B F]
    [CommRing C] [IsDedekindDomain C] [Algebra B C] [Algebra C F]
    [IsScalarTower B C F] [IsIntegralClosure C B F] [IsFractionRing C F]
    (hC : ¬ IsField C) (x : F) (hx : x ≠ 0)
    (hv : ∀ q : IsDedekindDomain.HeightOneSpectrum C, q.valuation F x < 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ b ∈ IsLocalRing.maximalIdeal B, algebraMap B F b = x ^ n := by
  obtain ⟨c, hc⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    F x (fun q => (hv q).le)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hc.symm)
  have hcj : c ∈ Ring.jacobson C := by
    rw [Ring.jacobson_eq_sInf_isMaximal, Ideal.mem_sInf]
    intro m hm
    let q : IsDedekindDomain.HeightOneSpectrum C :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm hC⟩
    exact (q.valuation_lt_one_iff_mem (K := F) c).mp (by simpa [hc] using hv q)
  obtain ⟨n, b, hb⟩ :=
    IsIntegralClosure.exists_pow_mul_mem_range B F C c hc0 hcj c
  have hb' : algebraMap B C b = c ^ (n + 1) := by simpa [pow_succ] using hb
  have hbm : b ∈ IsLocalRing.maximalIdeal B := by
    show ¬ IsUnit b
    intro hbu
    have hu := hbu.map (algebraMap B C)
    rw [hb'] at hu
    have hp : c ^ (n + 1) ∈ Ring.jacobson C := Ideal.pow_mem_of_mem _ hcj (n + 1) (by omega)
    exact (Ring.jacobson_lt_top C).ne (Ideal.eq_top_of_isUnit_mem _ hp hu)
  refine ⟨n + 1, by omega, b, hbm, ?_⟩
  rw [IsScalarTower.algebraMap_apply B C F, hb', map_pow, hc]

/-- An integral subring of the product of the fraction fields of the quotients by the minimal
primes contains an element with nonzero components each of which has a positive power coming
from a nonunit of the corresponding quotient. -/
private lemma exists_fractional_parameter
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1)
    {K : Type*} [CommRing K] (f : K →+* minimalFractionProduct A) (hf : f.IsIntegral) :
    ∃ x : K, (∀ p, f x p ≠ 0) ∧ ∀ p,
      ∃ n : ℕ, 0 < n ∧ ∃ b : A ⧸ p.1.asIdeal, ¬ IsUnit b ∧
        algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal)) b = f x p ^ n := by
  classical
  let P := {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}
  have : Finite P := finite_minimalPrimePoints A
  let B := fun p : P => A ⧸ p.1.asIdeal
  let F := fun p : P => FractionRing (B p)
  let C := fun p : P => integralClosure (B p) (F p)
  have : ∀ p, IsDomain (B p) := fun p => Ideal.Quotient.isDomain p.1.asIdeal
  have : ∀ p, IsDedekindDomain (C p) := fun p =>
    (integralClosure_quotient_dedekind_semilocal A hdim p.1.asIdeal).1
  have : ∀ p, Finite (MaximalSpectrum (C p)) := fun p =>
    (integralClosure_quotient_dedekind_semilocal A hdim p.1.asIdeal).2
  have : ∀ p, IsFractionRing (C p) (F p) := fun p =>
    IsIntegralClosure.isFractionRing_of_finite_extension (B p) (F p) (F p) (C p)
  obtain ⟨a, ha, har⟩ := IsLocalRing.exists_radical_span_eq_maximalIdeal (A := A) hdim
  have han := (IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes hdim ha).mp har
  have hC : ∀ p, ¬ IsField (C p) := by
    intro p
    apply integralClosure_not_field_of_nonzero_maximal_element (B p) (F p) (C p)
      (Ideal.Quotient.mk p.1.asIdeal a)
    · have : IsLocalHom (Ideal.Quotient.mk p.1.asIdeal) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      rwa [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk p.1.asIdeal)] at ha
    · exact fun h => han _ p.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let J := fun p => IsDedekindDomain.HeightOneSpectrum (C p)
  have : ∀ p, Finite (J p) := fun p => finite_heightOneSpectrum (C p)
  have : ∀ p, Nonempty (J p) := fun p => nonempty_heightOneSpectrum (C p) (hC p)
  obtain ⟨x, hx, hxv⟩ := exists_inverse_small_in_integral_range F J
    (fun p q => q.valuation (F p)) (fun _ _ => inferInstance) f hf
  refine ⟨x, hx, fun p => ?_⟩
  have := krullDimLE_one_quotient hdim p.1.asIdeal
  have : Ring.DimensionLEOne (B p) := ⟨fun h hp => hp.isMaximal_of_ne_bot h⟩
  exact exists_pow_in_maximalIdeal_of_valuations_lt_one (B p) (F p) (C p)
    (hC p) (f x p) (hx p) (hxv p)

/-- In a one-dimensional local domain a nonzero element divides a positive power of every
nonunit. -/
private lemma exists_pow_dvd_of_nonunit {B : Type*} [CommRing B] [IsDomain B]
    [IsLocalRing B] [Ring.KrullDimLE 1 B] {t b : B} (ht : t ≠ 0) (hb : ¬ IsUnit b) :
    ∃ n : ℕ, 0 < n ∧ t ∣ b ^ n := by
  have hrad : b ∈ (Ideal.span {t} : Ideal B).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro q ⟨htq, hq⟩
    have htmem : t ∈ q := htq (Ideal.subset_span (Set.mem_singleton t))
    have hq0 : q ≠ ⊥ := by
      rintro rfl
      exact ht (Ideal.mem_bot.mp htmem)
    have hmax := hq.isMaximal_of_ne_bot hq0
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact hb
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  refine ⟨n + 1, by omega, Ideal.mem_span_singleton.mp ?_⟩
  simpa only [pow_succ] using (Ideal.span {t}).mul_mem_right b hn

/-- A Noetherian ring has, for each minimal prime, an element avoiding it and lying in every
other minimal prime. -/
private lemma exists_minimalPrime_separator
    (A : Type*) [CommRing A] [IsNoetherianRing A]
    (i : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}) :
    ∃ t : A, t ∉ i.1.asIdeal ∧ ∀ j : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A},
      j ≠ i → t ∈ j.1.asIdeal := by
  classical
  let P := {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}
  have : Finite P := finite_minimalPrimePoints A
  let := Fintype.ofFinite P
  let s := Finset.univ.erase i
  have hn : ¬ s.inf (fun p : P => p.1.asIdeal) ≤ i.1.asIdeal := by
    rw [i.2.isPrime.inf_le']
    rintro ⟨j, hj, hji⟩
    have hij : i.1.asIdeal ≤ j.1.asIdeal := i.2.2 ⟨j.2.isPrime, bot_le⟩ hji
    exact (Finset.mem_erase.mp hj).1 (Subtype.ext (PrimeSpectrum.ext (le_antisymm hji hij)))
  obtain ⟨t, ht, hti⟩ := SetLike.not_le_iff_exists.mp hn
  refine ⟨t, hti, fun j hji => ?_⟩
  have hle : s.inf (fun p : P => p.1.asIdeal) ≤ j.1.asIdeal :=
    Finset.inf_le (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  exact hle ht

/-- A nonunit power at one minimal prime comes from an element of the maximal ideal vanishing
at every other minimal prime, after passing to a further power. -/
private lemma exists_pow_mem_maximalIdeal_of_nonunit_pow
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) (p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A})
    (y : FractionRing (A ⧸ p.1.asIdeal))
    (hz : ∃ n : ℕ, 0 < n ∧ ∃ b : A ⧸ p.1.asIdeal, ¬ IsUnit b ∧
      algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal)) b = y ^ n) :
    ∃ d : ℕ, 0 < d ∧ ∃ a ∈ IsLocalRing.maximalIdeal A,
      algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal))
        (Ideal.Quotient.mk p.1.asIdeal a) = y ^ d ∧
      ∀ q : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}, q ≠ p →
        algebraMap (A ⧸ q.1.asIdeal) (FractionRing (A ⧸ q.1.asIdeal))
          (Ideal.Quotient.mk q.1.asIdeal a) = 0 := by
  obtain ⟨n, hn, b, hb, hbz⟩ := hz
  obtain ⟨t, htp, ht⟩ := exists_minimalPrime_separator A p
  let B := A ⧸ p.1.asIdeal
  have := krullDimLE_one_quotient hdim p.1.asIdeal
  obtain ⟨r, hr, c, hc⟩ := exists_pow_dvd_of_nonunit
    (show (Ideal.Quotient.mk p.1.asIdeal t : B) ≠ 0 from
      fun h => htp (Ideal.Quotient.eq_zero_iff_mem.mp h)) hb
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hta : t * a ∈ IsLocalRing.maximalIdeal A := by
    show ¬ IsUnit (t * a)
    intro hu
    have hu' := hu.map (Ideal.Quotient.mk p.1.asIdeal)
    rw [map_mul, ← hc] at hu'
    exact hb ((isUnit_pow_iff hr.ne').mp hu')
  refine ⟨n * r, Nat.mul_pos hn hr, t * a, hta, ?_, ?_⟩
  · show algebraMap B (FractionRing B) (Ideal.Quotient.mk p.1.asIdeal (t * a)) = _
    rw [map_mul, ← hc, map_pow, hbz, pow_mul]
  · intro q hqp
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (ht q hqp), zero_mul, map_zero]

/-- Compatible positive powers at the minimal primes come from one element of the maximal
ideal, after passing to a common power. -/
private lemma exists_pow_lift_of_fractional_parameters
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) (z : minimalFractionProduct A)
    (hz : ∀ p, ∃ n : ℕ, 0 < n ∧ ∃ b : A ⧸ p.1.asIdeal, ¬ IsUnit b ∧
      algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal)) b = z p ^ n) :
    ∃ n : ℕ, 0 < n ∧ ∃ a ∈ IsLocalRing.maximalIdeal A,
      ∀ p, algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal))
        (Ideal.Quotient.mk p.1.asIdeal a) = z p ^ n := by
  classical
  let P := {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}
  have : Finite P := finite_minimalPrimePoints A
  let := Fintype.ofFinite P
  let ψ := fun p : P => (algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal))).comp
    (Ideal.Quotient.mk p.1.asIdeal)
  have hs : ∀ p : P, ∃ d : ℕ, 0 < d ∧ ∃ a ∈ IsLocalRing.maximalIdeal A,
      ψ p a = z p ^ d ∧ ∀ q : P, q ≠ p → ψ q a = 0 := fun p =>
    exists_pow_mem_maximalIdeal_of_nonunit_pow A hdim p (z p) (hz p)
  choose d hd a ha haz has using hs
  let N := ∏ p : P, d p
  have hN : 0 < N := Finset.prod_pos (fun p _ => hd p)
  have hdiv : ∀ p, d p ∣ N := fun p => Finset.dvd_prod_of_mem d (Finset.mem_univ p)
  choose k hk using hdiv
  have hkpos : ∀ p, 0 < k p := fun p =>
    Nat.pos_of_ne_zero fun hk0 => hN.ne' (by rw [hk p, hk0, mul_zero])
  refine ⟨N, hN, ∑ p : P, a p ^ k p,
    (IsLocalRing.maximalIdeal A).sum_mem (fun p _ =>
      (IsLocalRing.maximalIdeal A).pow_mem_of_mem (ha p) (k p) (hkpos p)), fun p => ?_⟩
  show ψ p (∑ q : P, a q ^ k q) = _
  rw [map_sum, Finset.sum_eq_single p]
  · rw [map_pow, haz p, ← pow_mul, ← hk p]
  · intro q _ hqp
    rw [map_pow, has q p (Ne.symm hqp), zero_pow (hkpos q).ne']
  · simp

/-- An element of the product of the localizations at the minimal primes that dies in the
product of the fraction fields of the quotients is nilpotent. -/
private lemma isNilpotent_of_fractional_image_eq_zero
    (A : Type*) [CommRing A] [IsNoetherianRing A]
    (z : ∀ p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A},
      Localization.AtPrime p.1.asIdeal)
    (hz : minimalLocalizationProductToFractionProduct A z = 0) : IsNilpotent z := by
  classical
  let P := {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}
  have : Finite P := finite_minimalPrimePoints A
  let := Fintype.ofFinite P
  have hnil : ∀ p : P, IsNilpotent (z p) := by
    intro p
    have : Ring.KrullDimLE 0 (Localization.AtPrime p.1.asIdeal) :=
      Ring.KrullDimLE.of_isLocalization p.1.asIdeal p.2 _
    refine Ring.KrullDimLE.isNilpotent_iff_mem_nonunits.mpr fun hu => ?_
    have hu' := hu.map (minimalLocalizationToFractionRing p.1.asIdeal)
    have hz' : minimalLocalizationToFractionRing p.1.asIdeal (z p) = 0 := congrFun hz p
    rw [hz'] at hu'
    exact not_isUnit_zero hu'
  choose n hn using hnil
  refine ⟨∑ p : P, n p, ?_⟩
  ext p
  exact pow_eq_zero_of_le (Finset.single_le_sum (fun i _ => Nat.zero_le (n i))
    (Finset.mem_univ p)) (hn p)

/-- A nilpotent element of the product of the localizations at the minimal primes lies in the
image of the nilradical. -/
private lemma nilpotent_mem_nilradical_map
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1)
    (z : ∀ p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A},
      Localization.AtPrime p.1.asIdeal) (hz : IsNilpotent z) :
    z ∈ (nilradical A).map (algebraMap A _) := by
  classical
  let P := {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}
  let L := ∀ p : P, Localization.AtPrime p.1.asIdeal
  obtain ⟨g, hg, hrad⟩ := IsLocalRing.exists_radical_span_eq_maximalIdeal (A := A) hdim
  have hav := (IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes hdim hg).mp hrad
  obtain ⟨e₀⟩ :=
    (IsLocalRing.notMem_minimalPrimes_iff_localizationAway_equiv_pi_localizationAtPrime
      hdim hg).mp hav
  let idx : minimalPrimes A ≃ P :=
    { toFun := fun p => ⟨⟨p.1, p.2.isPrime⟩, by simp⟩
      invFun := fun p => ⟨p.1.asIdeal, p.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  let S := Localization.Away g
  let e : S ≃ₐ[A] L := e₀.trans
    (AlgEquiv.piCongrLeft A (fun p : P => Localization.AtPrime p.1.asIdeal) idx)
  have hy : e.symm z ∈ nilradical S := mem_nilradical.mpr (hz.map e.symm.toRingEquiv.toRingHom)
  have hmap : (nilradical A).map (algebraMap A S) = nilradical S := by
    simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      IsLocalization.map_radical (Submonoid.powers g) S (⊥ : Ideal A)
  rw [← hmap] at hy
  have h := Ideal.mem_map_of_mem e.toRingEquiv.toRingHom hy
  rw [Ideal.map_map] at h
  have he : e.toRingEquiv.toRingHom.comp (algebraMap A S) = algebraMap A L :=
    RingHom.ext e.commutes
  rw [he] at h
  change e (e.symm z) ∈ (nilradical A).map (algebraMap A L) at h
  simpa only [AlgEquiv.apply_symm_apply] using h

/-- An element whose class vanishes in every quotient by a minimal prime is nilpotent. -/
private lemma mem_nilradical_of_fractional_images_eq_zero
    (A : Type*) [CommRing A] (a : A)
    (ha : ∀ p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A},
      algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal))
        (Ideal.Quotient.mk p.1.asIdeal a) = 0) : a ∈ nilradical A := by
  rw [nilradical_eq_sInf_minimalPrimes, Ideal.mem_sInf]
  intro p hp
  have : p.IsPrime := hp.isPrime
  exact Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))
    (by simpa using ha ⟨⟨p, hp.isPrime⟩, hp⟩))

/- The hypotheses on `A` are those of `IsLocalRing.exists_pow_mem_range_of_sub_mem_nilradical_map`,
one of the inputs below, but this statement adds the integral ring map `f : K →+* L` out of a
second ring and concludes with an element of `A`; that lemma takes no such map and concludes with
a power of a given element of `L`. -/
/-- **Stacks Project, Tag 0AB4.** An integral subring of the product of the minimal-prime
localizations contains the image of a parameter of a one-dimensional Noetherian local ring. -/
@[stacks 0AB4]
public theorem exists_mem_maximalIdeal_radical_span_eq_of_isIntegral
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) :
    let L := ∀ p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A},
      Localization.AtPrime p.1.asIdeal
    ∀ (K : Type v) [CommRing K] (f : K →+* L), f.IsIntegral →
      ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
        (∃ x : K, f x = algebraMap A L a) ∧
        (Ideal.span {a}).radical = IsLocalRing.maximalIdeal A := by
  classical
  dsimp only
  intro K _ f hf
  let P := {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}
  let L := ∀ p : P, Localization.AtPrime p.1.asIdeal
  let ρ := minimalLocalizationProductToFractionProduct A
  let f' := ρ.comp f
  have hf' : f'.IsIntegral := hf.trans f ρ
    (RingHom.isIntegral_of_surjective ρ (minimalLocalizationProductToFractionProduct_surjective A))
  obtain ⟨x, hxn, hx⟩ := exists_fractional_parameter A hdim f' hf'
  obtain ⟨n, hn, a, ha, hea⟩ := exists_pow_lift_of_fractional_parameters A hdim (f' x) hx
  have hρ : ρ (f (x ^ n) - algebraMap A L a) = 0 := by
    rw [map_sub]
    ext p
    show ρ (f (x ^ n)) p - minimalLocalizationToFractionRing p.1.asIdeal
      (algebraMap A (Localization.AtPrime p.1.asIdeal) a) = 0
    rw [minimalLocalizationToFractionRing_algebraMap, hea p]
    simp only [f', RingHom.comp_apply, map_pow, Pi.pow_apply, sub_self]
  have hnil := isNilpotent_of_fractional_image_eq_zero A _ hρ
  have hmem := nilpotent_mem_nilradical_map A hdim _ hnil
  rw [nilradical_eq_sInf_minimalPrimes] at hmem
  obtain ⟨k, hk, b, hb⟩ :=
    IsLocalRing.exists_pow_mem_range_of_sub_mem_nilradical_map A hdim (f (x ^ n)) a ha hmem
  have hbp : ∀ p : P,
      algebraMap (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal))
        (Ideal.Quotient.mk p.1.asIdeal b) = f' x p ^ (n * k) := by
    intro p
    have h := congrArg (fun y : L => ρ y p) hb
    change minimalLocalizationToFractionRing p.1.asIdeal
      (algebraMap A (Localization.AtPrime p.1.asIdeal) b) = _ at h
    rw [minimalLocalizationToFractionRing_algebraMap] at h
    simpa only [f', RingHom.comp_apply, map_pow, Pi.pow_apply, ← pow_mul] using h
  have hba : b - a ^ k ∈ nilradical A :=
    mem_nilradical_of_fractional_images_eq_zero A _ fun p => by
      simp only [map_sub, map_pow]
      rw [hbp p, hea p, ← pow_mul, sub_self]
  have hbm : b ∈ IsLocalRing.maximalIdeal A := by
    simpa only [sub_add_cancel] using (IsLocalRing.maximalIdeal A).add_mem
      (nilradical_le_prime (IsLocalRing.maximalIdeal A) hba)
      ((IsLocalRing.maximalIdeal A).pow_mem_of_mem ha k hk)
  refine ⟨b, hbm, ⟨x ^ (n * k), ?_⟩, ?_⟩
  · simpa only [map_pow, pow_mul] using hb.symm
  · refine (IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes hdim hbm).mpr
      fun p hp hbp' => ?_
    have : p.IsPrime := hp.isPrime
    let q : P := ⟨⟨p, hp.isPrime⟩, hp⟩
    have he := hbp q
    rw [show Ideal.Quotient.mk q.1.asIdeal b = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hbp', map_zero] at he
    exact pow_ne_zero (n * k) (hxn q) he.symm

end IsLocalRing

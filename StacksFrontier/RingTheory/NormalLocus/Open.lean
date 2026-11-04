module


public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated

@[expose] public section

/-!
# Openness of the normal locus of a Noetherian domain

Let `R` be a Noetherian domain and `f ∈ R` nonzero with `R_f` normal. The normal locus
`U = {𝔭 | R_𝔭 is normal}` is open in `Spec(R)`.

The set `U` is stable under passing to smaller primes: if `𝔮 ⊆ 𝔭` then `R_𝔮` is a localization
of `R_𝔭`, and a localization of a normal domain at a multiplicative set of nonzerodivisors is
normal. Both this and the inclusion `D(f) ⊆ U` are instances of one statement: if `M ⊆ R` is a
multiplicative set disjoint from `𝔮` and `M⁻¹R` is normal, then `R_𝔮` is normal.

Consequently the complement of `U` is the union of the closed sets `V(𝔮)` over the primes `𝔮`
that are *minimally* not in `U` — those with `R_𝔮` not normal while `R_{𝔮'}` is normal for every
`𝔮' ⊊ 𝔮` — and it suffices to see that there are finitely many of them. Such a `𝔮` contains `f`
(otherwise `R_𝔮` would be a localization of `R_f`) and is an associated prime of `R/fR`, of which
there are finitely many (Lemma 00LC).

## Implementation notes

The source deduces that `𝔮` is an associated prime of `R/fR` from Serre's criterion (Lemma 031S),
which bounds `depth(R_𝔮)` by `1`, together with `depth(R_𝔮) = depth(R_𝔮/fR_𝔮) + 1`. The proof
below reaches the same conclusion without depth, hence without Serre's criterion, by exhibiting
the element of `R/fR` that `𝔮` annihilates up to radical. Write `A = R_𝔮` with maximal ideal `𝔪`
and pick `x` in the fraction field, integral over `A` but not in `A`. Its ideal of denominators
`D = {a ∈ A | ax ∈ A}` lies in no prime but `𝔪`, because at a smaller prime `x` already belongs to
the — integrally closed — localization; so `𝔪` is the radical of `D`. Rescaling `x` by `f^{n-1}`
for the least `n` with `f^n x ∈ A` puts `f` into the denominator ideal while keeping `x ∉ A`. If
`𝔪` were not an associated prime of `A/fA` then, the associated primes being finite in number and
none of them containing the denominator ideal, prime avoidance (Lemma 00LL) would produce a
denominator `b` that is a nonzerodivisor on `A/fA`; writing `fx = u` and `bx = v` in `A` gives
`ub = vf`, so `b` kills `u mod fA`, whence `u ∈ fA` and `x ∈ A`. Descending from `𝔪` to `𝔮` is
Lemma 058A: the annihilator of the corresponding element of `R/fR` has `𝔮` as a minimal prime.

This route needs no depth theory, so it is also independent of the choice of definition of depth;
the argument is the one the source gives for Lemma 031T, run at a single prime.

## Main results

* `Stacks.NormalLocus.OpenInSpectrum.solution`: the proof of [StacksProject 0332].

## References

* [StacksProject 0332](https://stacks.math.columbia.edu/tag/0332)
-/

namespace Stacks.NormalLocus.OpenInSpectrum

open IsLocalRing

section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If `𝔮` is a prime of a domain `R` disjoint from a multiplicative set `M` whose localization
`M⁻¹R` is integrally closed, then `R_𝔮` is integrally closed: it is the localization of `M⁻¹R`
at the prime corresponding to `𝔮`. -/
private theorem isIntegrallyClosed_atPrime_of_disjoint (M : Submonoid R)
    (hM : IsIntegrallyClosed (Localization M)) (q : Ideal R) [hq : q.IsPrime]
    (hd : Disjoint (M : Set R) (q : Set R)) :
    IsIntegrallyClosed (Localization.AtPrime q) := by
  have h0 : (0 : R) ∉ M := fun h => Set.disjoint_left.mp hd h q.zero_mem
  have hMle : M ≤ nonZeroDivisors R := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero (fun h => h0 (h ▸ hx))
  have : IsDomain (Localization M) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hMle
  set S := Localization M
  set P : Ideal S := q.map (algebraMap R S)
  have : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S q hq hd
  have hcomap : P.comap (algebraMap R S) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M S hq hd
  have : IsIntegrallyClosed (Localization.AtPrime P) := by
    refine isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl ?_
    intro x hx
    exact mem_nonZeroDivisors_of_ne_zero fun h => hx (h ▸ P.zero_mem)
  have hpc : (P.comap (algebraMap R S)).primeCompl = q.primeCompl :=
    Submonoid.ext fun x =>
      show x ∉ P.comap (algebraMap R S) ↔ x ∉ q by rw [hcomap]
  have : IsLocalization q.primeCompl (Localization.AtPrime P) :=
    hpc ▸ IsLocalization.isLocalization_atPrime_localization_atPrime M P
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (Localization.AtPrime P)).symm.toRingEquiv

/-- The normal locus of a domain is stable under passing to a smaller prime. -/
private theorem isIntegrallyClosed_atPrime_of_le {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hle : q ≤ p) (h : IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed (Localization.AtPrime q) :=
  isIntegrallyClosed_atPrime_of_disjoint p.primeCompl h q
    (Set.disjoint_left.mpr fun _ hx hx' => hx (hle hx'))

/-- The standard open `D(f)` is contained in the normal locus. -/
private theorem isIntegrallyClosed_atPrime_of_notMem {f : R}
    (hf' : IsIntegrallyClosed (Localization.Away f)) {q : Ideal R} [hq : q.IsPrime]
    (hfq : f ∉ q) : IsIntegrallyClosed (Localization.AtPrime q) :=
  isIntegrallyClosed_atPrime_of_disjoint (Submonoid.powers f) hf' q
    (Set.disjoint_left.mpr fun x hx hx' => by
      obtain ⟨n, rfl⟩ := hx
      exact hfq (hq.mem_of_pow_mem n hx'))

variable [IsNoetherianRing R]

/-- `ENat.toNat` is strictly monotone below `⊤`. -/
private theorem toNat_lt_toNat_of_lt {a b : ℕ∞} (h : a < b) (hb : b ≠ ⊤) :
    a.toNat < b.toNat := by
  lift b to ℕ using hb
  lift a to ℕ using ne_top_of_lt h
  simpa using h

omit [IsDomain R] in
/-- Every prime outside the normal locus contains one that is *minimally* outside it: a prime
`𝔮` with `R_𝔮` not integrally closed all of whose proper subprimes lie in the normal locus.
The induction is on the (finite) height of the prime. -/
private theorem exists_minimal_not_isIntegrallyClosed (n : ℕ) :
    ∀ (p : Ideal R) (_ : p.IsPrime), (Ideal.height p).toNat ≤ n →
      ¬ IsIntegrallyClosed (Localization.AtPrime p) →
      ∃ q : Ideal R, ∃ _ : q.IsPrime, q ≤ p ∧
        ¬ IsIntegrallyClosed (Localization.AtPrime q) ∧
        ∀ (q' : Ideal R) (_ : q'.IsPrime), q' < q →
          IsIntegrallyClosed (Localization.AtPrime q') := by
  induction n with
  | zero =>
    intro p hp hh hbad
    refine ⟨p, hp, le_rfl, hbad, fun q' hq' hlt => absurd hh (by
      have hlt' : (Ideal.height q') < Ideal.height p :=
        Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
      have hne : Ideal.height p ≠ ⊤ := Ideal.height_ne_top hp.ne_top
      have := toNat_lt_toNat_of_lt hlt' hne
      omega)⟩
  | succ n ih =>
    intro p hp hh hbad
    by_cases hmin : ∀ (q' : Ideal R) (_ : q'.IsPrime), q' < p →
        IsIntegrallyClosed (Localization.AtPrime q')
    · exact ⟨p, hp, le_rfl, hbad, hmin⟩
    · simp only [not_forall] at hmin
      obtain ⟨q', hq', hlt, hbad'⟩ := hmin
      have hbad'' : ¬ IsIntegrallyClosed (Localization.AtPrime q') := by
        simpa using hbad'
      have hlt' : (Ideal.height q') < Ideal.height p :=
        Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
      have hne : Ideal.height p ≠ ⊤ := Ideal.height_ne_top hp.ne_top
      have hlt'' := toNat_lt_toNat_of_lt hlt' hne
      obtain ⟨q, hq, hle, h1, h2⟩ := ih q' hq' (by omega) hbad''
      exact ⟨q, hq, hle.trans hlt.le, h1, h2⟩

end

section Denominators

/-- The ideal of denominators of an element `y` of the total ring of fractions of `A`: the set of
`a ∈ A` with `a • y` in the image of `A`. For `A` a domain it is the whole of `A` exactly when `y`
lies in `A`. -/
private noncomputable def denominators {A : Type*} [CommRing A]
    (y : FractionRing A) : Ideal A :=
  (LinearMap.range (Algebra.linearMap A (FractionRing A))).comap
    (LinearMap.toSpanSingleton A (FractionRing A) y)

/-- Membership in `denominators y` is the existence of a numerator. -/
private theorem mem_denominators {A : Type*} [CommRing A]
    {y : FractionRing A} {a : A} :
    a ∈ denominators y ↔ ∃ b : A, algebraMap A (FractionRing A) b = a • y := by
  simp [denominators]

/-- Multiplying by a unit does not change membership in an ideal. -/
private theorem unit_mul_mem_iff_mem {A : Type*} [CommRing A] (I : Ideal A) {u y : A}
    (hu : IsUnit u) : u * y ∈ I ↔ y ∈ I := by
  refine ⟨fun h => ?_, fun h => I.mul_mem_left u h⟩
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h' := I.mul_mem_left v h
  rwa [← mul_assoc, hv, one_mul] at h'

end Denominators

section Local

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

/-- The key step: let `A` be a Noetherian local domain which is not integrally closed, all of
whose localizations at nonmaximal primes are integrally closed, and let `f ∈ 𝔪` be nonzero. Then
`𝔪` is an associated prime of `A/fA`.

Pick `x` in the fraction field, integral over `A` but not in `A`. Its ideal of denominators `D`
is contained in no prime but `𝔪`, because at a smaller prime `x` already lies in the (integrally
closed) localization; so `𝔪` is the radical of `D`. Replacing `x` by `f^{n-1} x` for the least
`n` with `f^n x ∈ A` puts `f` into the denominator ideal `D'` while keeping `x ∉ A`. Were `𝔪` not
associated to `A/fA`, some `b ∈ D'` would be a nonzerodivisor on `A/fA`; writing `f x = u` and
`b x = v` in `A` gives `ub = vf`, so `b` kills `u mod fA`, whence `u ∈ fA` and `x ∈ A` — a
contradiction. -/
private theorem maximalIdeal_mem_associatedPrimes_of_forall_lt {f : A} (hf : f ≠ 0)
    (hfm : f ∈ maximalIdeal A) (hbad : ¬ IsIntegrallyClosed A)
    (hmin : ∀ (P : Ideal A) (_ : P.IsPrime), P < maximalIdeal A →
      IsIntegrallyClosed (Localization.AtPrime P)) :
    maximalIdeal A ∈ associatedPrimes A (A ⧸ Ideal.span {f}) := by
  classical
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  -- Step 1: an element of the fraction field, integral over `A` but not in `A`.
  obtain ⟨x, hxint, hxout⟩ : ∃ x : FractionRing A, IsIntegral A x ∧
      ∀ b : A, algebraMap A (FractionRing A) b ≠ x := by
    by_contra hc
    push Not at hc
    exact hbad ((isIntegrallyClosed_iff (FractionRing A)).mpr fun {x} hx => hc x hx)
  -- Step 2: the maximal ideal is the only prime containing the denominators of `x`.
  have hprime_eq : ∀ P : Ideal A, P.IsPrime → denominators x ≤ P → P = maximalIdeal A := by
    intro P hP hle
    by_contra hne
    have := hP
    have hlt : P < maximalIdeal A := lt_of_le_of_ne (le_maximalIdeal hP.ne_top) hne
    have := hmin P hP hlt
    have hint : IsIntegral (Localization.AtPrime P) x := hxint.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    obtain ⟨⟨a, s⟩, h1⟩ := IsLocalization.surj P.primeCompl y
    have h2 := congrArg (algebraMap (Localization.AtPrime P) (FractionRing A)) h1
    rw [map_mul, hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
    refine s.2 (hle (mem_denominators.mpr ⟨a, ?_⟩))
    rw [Algebra.smul_def, mul_comm]
    exact h2.symm
  -- Step 3: `f` is nilpotent modulo the denominators of `x`.
  have hrad : f ∈ (denominators x).radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.mpr fun J hJ => ?_
    rw [hprime_eq J hJ.2 hJ.1]
    exact hfm
  have hP : ∃ k : ℕ, f ^ k ∈ denominators x := hrad
  -- Step 4: rescale `x` so that `f` itself is a denominator.
  have hkmem : f ^ Nat.find hP ∈ denominators x := Nat.find_spec hP
  have hk0 : Nat.find hP ≠ 0 := by
    intro h
    rw [h, pow_zero] at hkmem
    obtain ⟨b, hb⟩ := mem_denominators.mp hkmem
    exact hxout b (by simpa using hb)
  have hnotmem : f ^ (Nat.find hP - 1) ∉ denominators x :=
    Nat.find_min hP (m := Nat.find hP - 1) (by omega)
  set x' : FractionRing A := f ^ (Nat.find hP - 1) • x with hx'def
  have hx'out : ∀ b : A, algebraMap A (FractionRing A) b ≠ x' := fun b hb =>
    hnotmem (mem_denominators.mpr ⟨b, by rw [hb]⟩)
  have hfden : f ∈ denominators x' := by
    obtain ⟨b, hb⟩ := mem_denominators.mp hkmem
    refine mem_denominators.mpr ⟨b, ?_⟩
    have hfind : Nat.find hP - 1 + 1 = Nat.find hP := by omega
    rw [hb, hx'def, smul_smul, ← pow_succ', hfind]
  have hDD : denominators x ≤ denominators x' := by
    intro a ha
    obtain ⟨b, hb⟩ := mem_denominators.mp ha
    refine mem_denominators.mpr ⟨f ^ (Nat.find hP - 1) * b, ?_⟩
    rw [hx'def, map_mul, hb]
    simp only [Algebra.smul_def]
    ring
  -- Step 5: the quotient `A/fA` is nonzero.
  have hspan_le : Ideal.span {f} ≤ maximalIdeal A :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm)
  have hspan_ne : Ideal.span {f} ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hspan_le))
  have : Nontrivial (A ⧸ Ideal.span {f}) := Submodule.Quotient.nontrivial_iff.mpr hspan_ne
  -- Step 6: no element of the denominators of `x'` is a nonzerodivisor on `A/fA`.
  by_contra hnot
  have hzd : ∀ b ∈ denominators x', ¬ IsSMulRegular (A ⧸ Ideal.span {f}) b := by
    intro b hb hreg
    obtain ⟨u, hu⟩ := mem_denominators.mp hfden
    obtain ⟨v, hv⟩ := mem_denominators.mp hb
    have hub : u * b = v * f := by
      refine hinj ?_
      simp only [map_mul, hu, hv, Algebra.smul_def]
      ring
    have hmem : b * u ∈ Ideal.span {f} :=
      Ideal.mem_span_singleton.mpr ⟨v, by linear_combination hub⟩
    have h0 : b • (Ideal.Quotient.mk (Ideal.span {f}) u) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    have hu0 : Ideal.Quotient.mk (Ideal.span {f}) u = 0 := hreg (by simpa using h0)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hu0)
    refine hx'out w ?_
    have hfne : algebraMap A (FractionRing A) f ≠ 0 := fun h => hf (hinj (by simpa using h))
    refine mul_left_cancel₀ hfne ?_
    rw [← map_mul, ← hw, hu, Algebra.smul_def]
  -- Step 7: prime avoidance over the (finitely many) associated primes of `A/fA`.
  have hfin : (associatedPrimes A (A ⧸ Ideal.span {f})).Finite :=
    associatedPrimes.finite A (A ⧸ Ideal.span {f})
  have hcoe : (↑hfin.toFinset : Set (Ideal A)) = associatedPrimes A (A ⧸ Ideal.span {f}) :=
    hfin.coe_toFinset
  have hsub : (↑(denominators x') : Set A) ⊆
      ⋃ i ∈ (↑hfin.toFinset : Set (Ideal A)), (↑i : Set A) := by
    rw [hcoe, biUnion_associatedPrimes_eq_compl_regular]
    exact fun b hb => hzd b hb
  obtain ⟨p, hps, hple⟩ :=
    (Ideal.subset_union_prime (f := fun i : Ideal A => i) ⊥ ⊥
      (fun i hi _ _ => (hfin.mem_toFinset.mp hi).isPrime)).mp hsub
  exact hnot (hprime_eq p (hfin.mem_toFinset.mp hps).isPrime (hDD.trans hple) ▸
    hfin.mem_toFinset.mp hps)

end Local

section Descent

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Membership in the ideal generated by the image of `f` in `R_𝔮`, read back in `R`. -/
private theorem mem_span_singleton_map_iff {q : Ideal R} [q.IsPrime] {f y : R} :
    algebraMap R (Localization.AtPrime q) y ∈
        Ideal.span {algebraMap R (Localization.AtPrime q) f} ↔
      ∃ t ∈ q.primeCompl, t * y ∈ Ideal.span {f} := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp h
    obtain ⟨⟨e, t⟩, ht⟩ := IsLocalization.surj q.primeCompl d
    refine ⟨(t : R), t.2, Ideal.mem_span_singleton.mpr ⟨e, ?_⟩⟩
    refine IsLocalization.injective (Localization.AtPrime q)
      q.primeCompl_le_nonZeroDivisors ?_
    rw [map_mul, map_mul, hd, ← ht]
    ring
  · rintro ⟨t, ht, hmem⟩
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
    have hunit : IsUnit (algebraMap R (Localization.AtPrime q) t) :=
      IsLocalization.map_units (Localization.AtPrime q) ⟨t, ht⟩
    rw [← unit_mul_mem_iff_mem _ hunit, ← map_mul]
    exact Ideal.mem_span_singleton.mpr ⟨algebraMap R _ g, by rw [hg, map_mul]⟩

/-- Associated primes descend along localization at a prime: if the maximal ideal of `R_𝔮` is an
associated prime of `R_𝔮/fR_𝔮`, then `𝔮` is an associated prime of `R/fR`.

An element `z` whose annihilator has radical `𝔪` is, up to the unit `s`, the image of some
`r ∈ R`; the computation `algebraMap c ∈ 𝔪 ↔ ∃ n, ∃ t ∉ 𝔮, t c^n r ∈ fR` then exhibits `𝔮` as a
minimal prime over the annihilator of `r mod fR`, which is what Lemma 058A asks for. -/
private theorem mem_associatedPrimes_of_maximalIdeal_mem [IsNoetherianRing R] {q : Ideal R}
    [q.IsPrime] {f : R}
    (h : maximalIdeal (Localization.AtPrime q) ∈ associatedPrimes (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ Ideal.span {algebraMap R (Localization.AtPrime q) f})) :
    q ∈ associatedPrimes R (R ⧸ Ideal.span {f}) := by
  classical
  obtain ⟨z, hz⟩ := h.eq_radical_colon
  have hchar : ∀ c : Localization.AtPrime q,
      c ∈ maximalIdeal (Localization.AtPrime q) ↔ ∃ n : ℕ, c ^ n • z = 0 := by
    intro c
    rw [hz]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using Submodule.mem_colon_singleton.mp hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Submodule.mem_colon_singleton.mpr (by simpa using hn)⟩
  obtain ⟨a, hza⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj q.primeCompl a
  have hunit : IsUnit (algebraMap R (Localization.AtPrime q) (s : R)) :=
    IsLocalization.map_units (Localization.AtPrime q) s
  have hbr : ∀ (c : R) (n : ℕ),
      (algebraMap R (Localization.AtPrime q) c) ^ n • z = 0 ↔
        ∃ t ∈ q.primeCompl, t * (c ^ n * r) ∈ Ideal.span {f} := by
    intro c n
    rw [← mem_span_singleton_map_iff (q := q) (f := f) (y := c ^ n * r), ← hza]
    have hsm : (algebraMap R (Localization.AtPrime q) c) ^ n •
        (Ideal.Quotient.mk (Ideal.span {algebraMap R (Localization.AtPrime q) f}) a)
        = Ideal.Quotient.mk (Ideal.span {algebraMap R (Localization.AtPrime q) f})
            ((algebraMap R (Localization.AtPrime q) c) ^ n * a) := rfl
    have heq : algebraMap R (Localization.AtPrime q) (s : R) *
        ((algebraMap R (Localization.AtPrime q) c) ^ n * a)
        = algebraMap R (Localization.AtPrime q) (c ^ n * r) := by
      rw [map_mul, map_pow, ← hrs]
      ring
    rw [hsm, Ideal.Quotient.eq_zero_iff_mem, ← unit_mul_mem_iff_mem _ hunit, heq]
  have hqchar : ∀ c : R, c ∈ q ↔
      ∃ n : ℕ, ∃ t ∈ q.primeCompl, t * (c ^ n * r) ∈ Ideal.span {f} := by
    intro c
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q c, hchar]
    exact exists_congr (hbr c)
  set w : R ⧸ Ideal.span {f} := Ideal.Quotient.mk (Ideal.span {f}) r
  have hJmem : ∀ c : R, c ∈ (R ∙ w).annihilator ↔ c * r ∈ Ideal.span {f} := by
    intro c
    rw [Submodule.mem_annihilator_span_singleton]
    show Ideal.Quotient.mk (Ideal.span {f}) (c * r) = 0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  have hJq : (R ∙ w).annihilator ≤ q := by
    intro c hc
    exact (hqchar c).mpr ⟨1, 1, by simp, by simpa using (hJmem c).mp hc⟩
  rw [associatedPrimes_eq_setOf_exists_mem_minimalPrimes_annihilator]
  refine ⟨w, ⟨⟨‹q.IsPrime›, hJq⟩, fun p hp hple c hc => ?_⟩⟩
  obtain ⟨n, t, ht, hmem⟩ := (hqchar c).mp hc
  have h1 : t * c ^ n ∈ (R ∙ w).annihilator := (hJmem _).mpr (by rwa [mul_assoc])
  have h2 : t * c ^ n ∈ p := hp.2 h1
  have h3 : c ^ n ∈ p := (hp.1.mem_or_mem h2).resolve_left (fun htp => ht (hple htp))
  exact hp.1.mem_of_pow_mem n h3

end Descent


section Transport

variable {R : Type*} [CommRing R]

/-- The localization of `M⁻¹R` at a prime `P` is the localization of `R` at the prime `P`
contracts to, so integral closedness transfers from the latter to the former. -/
private theorem isIntegrallyClosed_atPrime_of_under (M : Submonoid R)
    (P : Ideal (Localization M)) [P.IsPrime] (p : Ideal R) [p.IsPrime]
    (hp : p = Ideal.comap (algebraMap R (Localization M)) P)
    (h : IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed (Localization.AtPrime P) := by
  subst hp
  have := h
  have := IsLocalization.isLocalization_atPrime_localization_atPrime M P
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv
      (Ideal.comap (algebraMap R (Localization M)) P).primeCompl
      (Localization.AtPrime (Ideal.comap (algebraMap R (Localization M)) P))
      (Localization.AtPrime P)).toRingEquiv

end Transport

/-- **Stacks Tag 0332.** Let `R` be a Noetherian domain. If there is a nonzero `f ∈ R` such that
`R_f` is normal, then the set of primes `𝔭` of `R` with `R_𝔭` a normal domain is open in
`Spec(R)`. -/
public theorem solution {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {f : R}
    (hf : f ≠ 0) (hf' : IsIntegrallyClosed (Localization.Away f)) :
    IsOpen {p : PrimeSpectrum R | IsIntegrallyClosed (Localization.AtPrime p.asIdeal)} := by
  classical
  set E : Set (Ideal R) := {q : Ideal R | q ∈ associatedPrimes R (R ⧸ Ideal.span {f}) ∧
    ∀ h : q.IsPrime, ¬ IsIntegrallyClosed (@Localization.AtPrime R _ q h)}
  have hEfin : E.Finite :=
    (associatedPrimes.finite R (R ⧸ Ideal.span {f})).subset fun _ hx => hx.1
  refine isClosed_compl_iff.mp ?_
  have key : {p : PrimeSpectrum R | IsIntegrallyClosed (Localization.AtPrime p.asIdeal)}ᶜ
      = ⋃ q ∈ E, PrimeSpectrum.zeroLocus (q : Set R) := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hp
      obtain ⟨q, hq, hle, hbad, hmin⟩ :=
        exists_minimal_not_isIntegrallyClosed (Ideal.height p.asIdeal).toNat p.asIdeal
          p.isPrime le_rfl hp
      have := hq
      have hfq : f ∈ q := by
        by_contra hfq
        exact hbad (isIntegrallyClosed_atPrime_of_notMem hf' hfq)
      have hass : q ∈ associatedPrimes R (R ⧸ Ideal.span {f}) := by
        refine mem_associatedPrimes_of_maximalIdeal_mem ?_
        refine maximalIdeal_mem_associatedPrimes_of_forall_lt ?_ ?_ hbad ?_
        · exact fun hz => hf (IsLocalization.injective (Localization.AtPrime q)
            q.primeCompl_le_nonZeroDivisors (by simpa using hz))
        · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime q) q f).mpr hfq
        · intro P hP hPlt
          have := hP
          have hcp : (Ideal.comap (algebraMap R (Localization.AtPrime q)) P).IsPrime :=
            Ideal.IsPrime.comap _
          refine isIntegrallyClosed_atPrime_of_under q.primeCompl P _ rfl (hmin _ hcp ?_)
          refine lt_of_le_of_ne ?_ ?_
          · calc Ideal.comap (algebraMap R (Localization.AtPrime q)) P
                ≤ Ideal.comap (algebraMap R (Localization.AtPrime q))
                    (maximalIdeal (Localization.AtPrime q)) := Ideal.comap_mono hPlt.le
              _ = q := IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q
          · intro hcq
            refine hPlt.ne ?_
            have h1 : Ideal.map (algebraMap R (Localization.AtPrime q))
                (Ideal.comap (algebraMap R (Localization.AtPrime q)) P) = P :=
              IsLocalization.map_under q.primeCompl (Localization.AtPrime q) P
            rw [hcq, IsLocalization.AtPrime.map_eq_maximalIdeal] at h1
            exact h1.symm
      refine ⟨q, ⟨hass, fun _ => hbad⟩, ?_⟩
      exact PrimeSpectrum.mem_zeroLocus _ _ |>.mpr hle
    · rintro ⟨q, ⟨hass, hbad⟩, hmem⟩ hgood
      have : q.IsPrime := hass.isPrime
      exact hbad ‹q.IsPrime›
        (isIntegrallyClosed_atPrime_of_le
          ((PrimeSpectrum.mem_zeroLocus _ _).mp hmem) hgood)
  rw [key]
  exact hEfin.isClosed_biUnion fun q _ => PrimeSpectrum.isClosed_zeroLocus _

end Stacks.NormalLocus.OpenInSpectrum

/-!
# Openness of the normal locus of a Noetherian domain

Let `R` be a Noetherian domain. The *normal locus* of `R` is the set of primes `𝔭` of `R` at
which the local ring `R_𝔭` is a normal domain. It is open as soon as it contains one standard
open: if `f ∈ R` is nonzero and `R_f` is normal, then the normal locus is open in `Spec(R)`. The
Noetherian hypothesis alone is not known to suffice, and the source proves openness only under
this extra hypothesis.

The standard open `D(f)` is contained in the normal locus, because for `𝔭 ∈ D(f)` the ring `R_𝔭`
is a localization of the normal domain `R_f`. For the rest, Serre's criterion (Lemma 031S) says
that `𝔭` misses the normal locus only if some `𝔮 ⊆ 𝔭` has either `depth(R_𝔮) < 2` and
`dim(R_𝔮) ≥ 2`, or `dim(R_𝔮) = 1` with `R_𝔮` not regular. Such a `𝔮` contains `f`, and
`depth(R_𝔮) = depth(R_𝔮/fR_𝔮) + 1` identifies it as an embedded associated prime of `R/fR` in
the first case and as an associated prime of `R/fR` of height one in the second. There are
finitely many associated primes (Lemma 00LC), so the complement of the normal locus is the finite
union of the closed sets `V(𝔮)` over that set of primes, hence closed.

## Main results

* `PrimeSpectrum.isOpen_setOf_isIntegrallyClosed_atPrime`: the normal locus of a Noetherian
  domain having a nonzero `f` with `R_f` normal is open in `Spec(R)`.

## Implementation notes

Mathlib has no predicate for a normal ring, so "`R_𝔭` is a normal domain" is spelled
`IsIntegrallyClosed (Localization.AtPrime 𝔭)`, as for item (1) of tag 030C and the statement of
Serre's criterion (tag 031S). Those statements carry a conjunct `IsDomain (Localization.AtPrime
𝔭)` because `IsIntegrallyClosed` is Mathlib's `IsIntegrallyClosedIn R (FractionRing R)`, which
presupposes no domain hypothesis; here `R` is a domain and that conjunct is supplied by the
instance `IsLocalization.isDomain_of_local_atPrime`, so adding it would only decorate the set
with a hypothesis that always holds. The normal locus is inlined as a set-builder rather than
named, in the shape `Algebra.smoothLocus` and `Algebra.unramifiedLocus` use for the same kind of
pointwise condition on localizations.

The hypothesis on `R_f` names the canonical model `Localization.Away f`. An abstract
`[IsLocalization.Away f Rf]` would be preferable, but `Rf` occurs in no other argument and in
particular not in the conclusion, so it could never be inferred at a use site; a user holding a
normal localization away from `f` in another model transports the hypothesis along
`IsLocalization.algEquiv`.

Faithfulness to [StacksProject 0332]:

1. No dead hypothesis. `IsNoetherianRing R` runs Serre's criterion and bounds the associated
   primes of `R/fR`; `IsDomain R` is what makes a single `f` control the generic behaviour, and
   is presupposed by the source's use of the fraction field; `hf : f ≠ 0` is load-bearing because
   `Localization.Away 0` is the zero ring, which is integrally closed, so without it the
   hypothesis would be vacuous and the statement would assert openness of the normal locus for
   every Noetherian domain — a claim the source does not make.
2. The scalars and base are the source's. Integral closedness at `𝔭` is that of `R_𝔭` inside its
   own fraction field, not that of `R` inside `Q(R)`, and `R_f` is the localization of `R` at the
   powers of `f`, an `R`-algebra, not a ring with the same invariants.
3. The source names no canonical map, but it does name the local rings: they are pinned to
   `Localization.AtPrime 𝔭` with its canonical `R`-algebra structure, and `R_f` to
   `Localization.Away f`, so the conditions are about the localizations of `R` itself.
4. The instantiation is not degenerate, and the conclusion is not an emptiness or a totality
   statement in disguise. For the cusp `R = k[x, y]/(y² - x³)`, a Noetherian domain, the element
   `f = x` is nonzero and `R_f ≅ k[t, t⁻¹]` with `t = y/x` is normal, while the normal locus is
   the complement of the origin: a nonempty proper open set. Taking `f = 1` for a normal `R`
   recovers the whole spectrum, and no choice of `f` can make the locus empty, since `D(f)` lies
   inside it.

## References

* [StacksProject 0332](https://stacks.math.columbia.edu/tag/0332)
-/

@[expose] public section

/-- **Stacks Tag 0332.** Let `R` be a Noetherian domain. If there is a nonzero `f ∈ R` such that
`R_f` is normal, then the set of primes `𝔭` of `R` with `R_𝔭` a normal domain is open in
`Spec(R)`. -/
@[stacks 0332 "Normality of a localization is spelled `IsIntegrallyClosed`, Mathlib having no \
  predicate for a normal ring; the `IsDomain` conjunct of the spelling used for tags 030C (1) \
  and 031S is automatic here because `R` is a domain. `R_f` is the canonical model \
  `Localization.Away f`. See the module docstring."]
public theorem PrimeSpectrum.isOpen_setOf_isIntegrallyClosed_atPrime
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {f : R} (hf : f ≠ 0)
    (hf' : IsIntegrallyClosed (Localization.Away f)) :
    IsOpen {p : PrimeSpectrum R | IsIntegrallyClosed (Localization.AtPrime p.asIdeal)} :=
  Stacks.NormalLocus.OpenInSpectrum.solution hf hf'

end

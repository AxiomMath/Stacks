module

public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionBoundTransfer
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.RingTheory.Ideal.PrincipalRadical.Basic
public import StacksFrontier.RingTheory.Nagata.MonogenicN1

/-!
# A uniform bound on the sections of the divisor cut out by an element

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two and let `a ∈ A` be nonzero.
For a modification `f : X ⟶ Spec A` with `X` normal, let `Z ⊂ X` be the closed subscheme cut
out by `a` and put

  `M_{X,a} = Coker(A ⟶ H⁰(Z, 𝒪_Z))`.

The `A`-module lengths of the `M_{X,a}` admit a bound independent of `X`.

The argument replaces `a` by a better element and then bounds the resulting module by a
normalization. The cokernel is the `a`-torsion submodule of `H¹(X, 𝒪_X)`, so it is monotone in
divisibility and its length grows at most linearly along powers; since a nonzero element of a
two-dimensional Noetherian normal local domain divides a power of a nonzero element with reduced
principal quotient, one may assume `A ⧸ aA` reduced. In that case `A ⧸ aA` is a reduced
one-dimensional Nagata local ring, so the quotient of its integral closure `B` in its total ring
of fractions by `A ⧸ aA` has finite length, and `M_{X,a}` is a subquotient of `B / (A ⧸ aA)`.

## Main results

* `exists_ne_zero_isReduced_quotient_and_dvd_pow`: in a two-dimensional Noetherian normal local
  domain every nonzero element divides a power of a nonzero element whose principal quotient is
  reduced.
* `exists_bound_length_normalizationCokernel`: for such an element the cokernel of `A ⧸ cA` in
  its integral closure has a finite length bound.
* `AlgebraicGeometry.exists_bound_length_quotient_baseToZeroSchemeSections`: the uniform bound
  on the lengths of the `M_{X,a}`.

## Implementation notes

The reduced principal quotient is produced by Tag 0AXH applied to the finitely many minimal
primes of `aA`, all of height one; the common element it returns lies in every such prime, hence
in the radical of `aA`, which is the divisibility `a ∣ cⁿ`. Tag 0AXI states the same conclusion
without the nonvanishing of `c`, and that nonvanishing is what the identification of the cokernel
with the torsion submodule requires, so the refinement is recorded separately here.

The total ring of fractions of a reduced ring `R` is `FractionRing R`, the localization at the
nonzerodivisors, and `normalizationCokernel R` is the quotient of the integral closure of `R`
there by the image of `R`.

The passage from a bound on the normalization cokernel to a bound on `M_{X,c}` appears as the
hypothesis `hsub`: it is the identification of the closure of `Z ∩ f⁻¹(U)` with the spectrum of
a ring between `A ⧸ cA` and `B`, together with the injectivity of `H⁰(Z, 𝒪_Z)` on that closure.

## References

* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXH](https://stacks.math.columbia.edu/tag/0AXH)
* [Stacks Project, Tag 0AXI](https://stacks.math.columbia.edu/tag/0AXI)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
* [Stacks Project, Tag 0C3S](https://stacks.math.columbia.edu/tag/0C3S)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-- The cokernel of a ring inside its integral closure in its total ring of fractions, as a
module over that ring. For a reduced one-dimensional Nagata local ring this module has finite
length. -/
abbrev normalizationCokernel (R : Type u) [CommRing R] : Type u :=
  ↥(integralClosure R (FractionRing R)) ⧸
    LinearMap.range (Algebra.linearMap R ↥(integralClosure R (FractionRing R)))

/-- In a two-dimensional Noetherian normal local domain, every nonzero element divides a power
of a nonzero element whose principal quotient is reduced.

This refines [Stacks, Tag 0AXI] by recording that the element produced is nonzero. -/
theorem exists_ne_zero_isReduced_quotient_and_dvd_pow {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 2) {a : R} (ha : a ≠ 0) :
    ∃ c : R, c ≠ 0 ∧ IsReduced (R ⧸ Ideal.span {c}) ∧ ∃ n : ℕ, a ∣ c ^ n := by
  classical
  let I : Ideal R := Ideal.span {a}
  let primes : Finset (Ideal R) := I.finite_minimalPrimes_of_isNoetherianRing.toFinset
  have hprimes : ∀ p ∈ primes, p.IsPrime ∧ p.height = 1 := by
    intro p hp
    have hp' : p ∈ I.minimalPrimes := by simpa [primes] using hp
    have hpprime : p.IsPrime := hp'.isPrime
    refine ⟨hpprime, le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I p hp') ?_⟩
    rw [Order.one_le_iff_ne_zero]
    intro hpzero
    have hpbot : p = ⊥ := by
      rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot] at hpzero
      simpa using hpzero
    exact ha (by simpa [hpbot] using hp'.1.2 (Ideal.mem_span_singleton_self a))
  obtain ⟨c, hc0, hc, hred⟩ :=
    exists_nonzero_mem_isReduced_quotient_of_height_one_primes hdim primes hprimes
  refine ⟨c, hc0, hred, ?_⟩
  have hcrad : c ∈ I.radical := by
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro p hp
    exact hc p (by simpa [primes] using hp)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hcrad
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

/-- Let `A` be a two-dimensional Nagata normal local domain and let `c ∈ 𝔪` be nonzero with
`A ⧸ cA` reduced. The cokernel of `A ⧸ cA` in its integral closure in its total ring of
fractions has a finite length bound.

The quotient `A ⧸ cA` is a reduced one-dimensional Nagata local ring, so [Stacks, Tag 0C3S]
applies to it. -/
theorem exists_bound_length_normalizationCokernel {A : Type u} [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2) {c : A} (hc : c ≠ 0)
    (hcm : c ∈ IsLocalRing.maximalIdeal A) (hred : IsReduced (A ⧸ Ideal.span {c})) :
    ∃ N : ℕ, Module.length (A ⧸ Ideal.span {c})
      (normalizationCokernel (A ⧸ Ideal.span {c})) ≤ N := by
  let R := A ⧸ Ideal.span {c}
  let _ : IsReduced R := hred
  have hspan : Ideal.span {c} ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hcm))
  have : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hspan
  let _ : IsLocalRing R := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span {c})) Ideal.Quotient.mk_surjective
  have hNagata : IsNagataRing R := MonogenicN1.isNagataRing_quotient ‹_› (Ideal.span {c})
  have hdimR : ringKrullDim R = 1 := by
    have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hc) hcm
    rw [hdim, show (2 : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) by
      norm_num] at h
    exact (ENat.WithBot.add_natCast_cancel (c := 1)).mp (by simpa using h)
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp
    (Module.length_ne_top_iff.mpr (isFiniteLength_integralClosure_quotient hNagata hdimR))
  exact ⟨N, hN.ge⟩

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0AXJ.** Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension
two and let `a ∈ A` be nonzero. There is an integer `N` such that for every modification
`f : X ⟶ Spec A` with `X` normal the `A`-module

  `M_{X,a} = Coker(A ⟶ H⁰(Z, 𝒪_Z))`,

for `Z ⊂ X` the closed subscheme cut out by `a`, has length at most `N`.

A unit `a` cuts out the empty subscheme, so the cokernel vanishes. Otherwise `a` is replaced by
an element with reduced principal quotient: the cokernel is the `a`-torsion submodule of
`H¹(X, 𝒪_X)`, which is monotone in divisibility and whose length grows at most linearly along
powers, and `a` divides a power of a nonzero `c ∈ 𝔪` with `A ⧸ cA` reduced. For such a `c` the
bound is the length of the cokernel `B / (A ⧸ cA)` of the integral closure `B` of `A ⧸ cA` in
its total ring of fractions, and the hypothesis `hsub` converts a bound on that cokernel into
one on `M_{X,c}`. -/
@[stacks 0AXJ "`hsub` carries the subquotient step: `M_{X,c}` embeds into `B / (A ⧸ cA)` \
because the closure of `Z ∩ f⁻¹(U)` is a spectrum between them (Stacks 0AB7) and \
`H⁰(Z, 𝒪_Z)` injects on it (Stacks 0AXB, absent from this library)"]
theorem exists_bound_length_quotient_baseToZeroSchemeSections {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2) {a : A}
    (ha : a ≠ 0)
    (hsub : ∀ c : A, c ≠ 0 → c ∈ IsLocalRing.maximalIdeal A →
        _root_.IsReduced (A ⧸ Ideal.span {c}) → ∀ N : ℕ,
      Module.length (A ⧸ Ideal.span {c}) (normalizationCokernel (A ⧸ Ideal.span {c})) ≤ N →
        ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
          Module.length A (globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f c) ⧸
            LinearMap.range (baseToZeroSchemeSections X f c)) ≤ N) :
    ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      Module.length A (globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f a) ⧸
        LinearMap.range (baseToZeroSchemeSections X f a)) ≤ N := by
  by_cases hu : IsUnit a
  · refine ⟨0, fun X _ f hf => ?_⟩
    rw [length_quotient_baseToZeroSchemeSections_eq X f hf ha]
    have hbot : Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a = ⊥ :=
      le_bot_iff.mp (Submodule.torsionBy_one (R := A)
        (M := firstCohomologyAsBaseModule X f) ▸
        Submodule.torsionBy_le_torsionBy_of_dvd a 1 hu.dvd)
    rw [hbot]
    simp
  · have ham : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal a).mpr hu
    obtain ⟨c, hc0, hcred, n, hacn⟩ := exists_ne_zero_isReduced_quotient_and_dvd_pow hdim ha
    have hcm : c ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem n
        (Ideal.mem_of_dvd _ hacn ham)
    obtain ⟨N, hN⟩ := exists_bound_length_normalizationCokernel hdim hc0 hcm hcred
    exact exists_bound_length_quotient_baseToZeroSchemeSections_of_dvd_pow ha hc0 hacn
      ⟨N, hsub c hc0 hcm hcred N hN⟩

end AlgebraicGeometry

end

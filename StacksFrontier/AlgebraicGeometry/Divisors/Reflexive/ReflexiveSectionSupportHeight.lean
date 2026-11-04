module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# The support of `M ⧸ A·s` has codimension at most one

Let `A` be a Noetherian normal domain, `M` a finite reflexive `A`-module and `s ∈ M` nonzero.
Every prime associated to `M ⧸ A·s` has height at most one, hence so does every minimal prime of
the support of `M ⧸ A·s`, and therefore every prime in that support contains a prime of height
at most one which is again in it.

This is the affine, unconditional form of the upper bound of [Stacks, Tag 0EBP]: on
`X = Spec(A)` with `ℱ = M^~` the complement of the locus `U` of [Stacks, Tag 0EBN] is the
support of `M ⧸ A·s`, the irreducible components of that support are the `V(𝔭)` for `𝔭` minimal
in it, and the codimension of `V(𝔭)` is the height of `𝔭`.

## Main results

* `one_le_depth_localized_quotient_of_two_le_height`: at a prime of height at least two the
  localization of `M ⧸ A·s` has positive depth.
* `height_le_one_of_mem_associatedPrimes`, `height_le_one_of_mem_minimalPrimes`: the height
  bound at an associated prime and at a minimal prime of the support.
* `exists_le_of_mem_support`: every prime of the support of `M ⧸ A·s` lies over a prime of
  height at most one in that support.

## Implementation notes

**Why no shrinking step is needed.** The scheme-level argument of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/SectionLocusCodimension.lean` replaces `X` by a
neighbourhood of the generic point of a component, a reduction carried there as the hypothesis
`hshrink`. Affinely the reduction is just localization at the prime, which costs nothing: the
short exact sequence `0 → A_𝔭 → M_𝔭 → (M ⧸ A·s)_𝔭 → 0` is available at every prime, and the
depth inequality of [Stacks, Tag 00LX] applied to it is what rules out height at least two.

**The rank one hypothesis is not used,** and no `@[stacks]` attribute is carried: what is proved
is the upper bound only. The matching lower bound — the minimal primes of the support have
height at least one — is where rank one enters, and it is proved in
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/ReflexiveHeightOnePrimes.lean`, which combines
the two into the first display of [Stacks, Tag 0EBQ].

## References

* [Stacks Project, Tag 0EBP](https://stacks.math.columbia.edu/tag/0EBP)
* [Stacks Project, Tag 0EBA](https://stacks.math.columbia.edu/tag/0EBA)
* [Stacks Project, Tag 00LX](https://stacks.math.columbia.edu/tag/00LX)
* [Stacks Project, Tag 00LL](https://stacks.math.columbia.edu/tag/00LL)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
-/

@[expose] public section

universe u v

namespace Stacks.AlgebraicGeometry.ReflexiveSectionSupport

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- `Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed` read at a prime of height at least
two of a Noetherian normal domain: the localization there is again a Noetherian normal local
domain, and its Krull dimension is the height of the prime. -/
theorem two_le_depth_localization [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (hp : 2 ≤ p.height) :
    (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) := by
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ _ p.primeCompl_le_nonZeroDivisors
  refine Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed _ ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
  exact (WithBot.coe_le_coe.mpr hp : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (p.height : WithBot ℕ∞))

/-- **The depth bound behind the codimension one statement.** For `A` a Noetherian normal domain,
`M` a finite reflexive `A`-module and `s ∈ M` nonzero, the localization of `M ⧸ A·s` at a prime
of height at least two has positive depth.

The short exact sequence `0 → A_𝔭 → M_𝔭 → (M ⧸ A·s)_𝔭 → 0` has both of its first two terms of
depth at least two -- the ring by Serre's condition `(S₂)`, the module because it is reflexive
([Stacks, Tag 0EBA]) -- so [Stacks, Tag 00LX] bounds the depth of the third below by
`min(2, 2 - 1) = 1`. -/
theorem one_le_depth_localized_quotient_of_two_le_height [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Module.Finite A M] [Module.IsReflexive A M] {s : M} (hs : s ≠ 0)
    (p : Ideal A) [p.IsPrime] (hp : 2 ≤ p.height) :
    1 ≤ Module.depth (Localization.AtPrime p)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (LocalizedModule p.primeCompl (M ⧸ (A ∙ s))) := by
  have htf : Module.IsTorsionFree A M :=
    (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := A) (M := M)).1 inferInstance
  have hex0 : Function.Exact (LinearMap.toSpanSingleton A M s) (A ∙ s).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, LinearMap.range_toSpanSingleton]
  have hf0 : Function.Injective (LinearMap.toSpanSingleton A M s) := smul_left_injective A hs
  have hg0 : Function.Surjective (A ∙ s).mkQ := Submodule.mkQ_surjective _
  have hex := IsLocalizedModule.map_exact p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl A) (LocalizedModule.mkLinearMap p.primeCompl M)
    (LocalizedModule.mkLinearMap p.primeCompl (M ⧸ (A ∙ s))) _ _ hex0
  have hf := IsLocalizedModule.map_injective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl A) (LocalizedModule.mkLinearMap p.primeCompl M)
    _ hf0
  have hg := IsLocalizedModule.map_surjective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)
    (LocalizedModule.mkLinearMap p.primeCompl (M ⧸ (A ∙ s))) _ hg0
  have key := Module.min_depth_le_depth_of_exact
    (R := Localization.AtPrime p) (IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (f := (IsLocalizedModule.map p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl A)
        (LocalizedModule.mkLinearMap p.primeCompl M)
        (LinearMap.toSpanSingleton A M s)).extendScalarsOfIsLocalization p.primeCompl
          (Localization.AtPrime p))
    (g := (IsLocalizedModule.map p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
        (LocalizedModule.mkLinearMap p.primeCompl (M ⧸ (A ∙ s)))
        (A ∙ s).mkQ).extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p))
    hex hf hg
  have hA : Module.depth (Localization.AtPrime p)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (LocalizedModule p.primeCompl A) =
      Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) :=
    Module.depth_eq_depth_of_linearEquiv _
      ((IsLocalizedModule.linearEquiv p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl A)
        (Algebra.linearMap A (Localization.AtPrime p))).extendScalarsOfIsLocalization
          p.primeCompl (Localization.AtPrime p))
  have h2A : (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (LocalizedModule p.primeCompl A) := by
    rw [hA]; exact two_le_depth_localization p hp
  have h2M : (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (LocalizedModule p.primeCompl M) :=
    (depth_localized_ge_two_and_propertyS2_of_isReflexive (M := M) p).1
      (two_le_depth_localization p hp)
  refine le_trans (le_min (le_trans one_le_two h2M) ?_) key.2.1
  exact le_trans (le_of_eq (show (1 : ℕ∞) = 2 - 1 from rfl)) (tsub_le_tsub_right h2A 1)

/-- Every prime associated to `M ⧸ A·s` has height at most one: at a prime of height at least two
the localization of `M ⧸ A·s` has positive depth, whereas at an associated prime its depth
vanishes ([Stacks, Tag 00LL]). -/
theorem height_le_one_of_mem_associatedPrimes [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Module.Finite A M] [Module.IsReflexive A M] {s : M} (hs : s ≠ 0)
    {p : Ideal A} (hp : p ∈ associatedPrimes A (M ⧸ (A ∙ s))) : p.height ≤ 1 := by
  have hprime : p.IsPrime := hp.isPrime
  by_contra hgt
  have h2 : (2 : ℕ∞) ≤ p.height := by
    have h1 : (1 : ℕ∞) < p.height := not_le.mp hgt
    simpa only [show (2 : ℕ∞) = 1 + 1 from rfl] using Order.add_one_le_of_lt h1
  have h0 := (Module.depth_localized_eq_zero_iff (M := M ⧸ (A ∙ s)) ⟨p, hprime⟩).2 hp
  have h1 := one_le_depth_localized_quotient_of_two_le_height (M := M) hs p h2
  rw [h0] at h1
  exact absurd h1 (by simp)

/-- Every minimal prime of the support of `M ⧸ A·s` has height at most one: a minimal prime over
the annihilator of a finite module is associated to it. -/
theorem height_le_one_of_mem_minimalPrimes [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Module.Finite A M] [Module.IsReflexive A M] {s : M} (hs : s ≠ 0)
    {p : Ideal A} (hp : p ∈ (Module.annihilator A (M ⧸ (A ∙ s))).minimalPrimes) :
    p.height ≤ 1 :=
  height_le_one_of_mem_associatedPrimes hs
    (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A _ hp)

/-- **The affine codimension one statement.** Every prime in the support of `M ⧸ A·s` contains a
prime of height at most one which is again in that support, namely a minimal prime of the
support below it. -/
theorem exists_le_of_mem_support [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Module.Finite A M] [Module.IsReflexive A M] {s : M} (hs : s ≠ 0) {q : PrimeSpectrum A}
    (hq : q ∈ Module.support A (M ⧸ (A ∙ s))) :
    ∃ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 ∧
      p ∈ Module.support A (M ⧸ (A ∙ s)) ∧ p ≤ q := by
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
    (Module.mem_support_iff_of_finite.mp hq)
  exact ⟨⟨p, hp.isPrime⟩, height_le_one_of_mem_minimalPrimes (M := M) hs hp,
    Module.mem_support_iff_of_finite.mpr hp.1.2, hpq⟩

end Stacks.AlgebraicGeometry.ReflexiveSectionSupport

end

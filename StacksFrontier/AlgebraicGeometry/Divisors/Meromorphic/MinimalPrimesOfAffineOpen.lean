module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.PullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing

/-!
# Minimal primes of an affine open under the hypotheses of Stacks 0EN6

Let `X` be a scheme. The two standing hypotheses of Stacks 0EN6 — every weakly associated
point of `X` is a generic point of an irreducible component, and every quasi-compact open of
`X` has finitely many irreducible components — say, read on a ring `A` presenting an affine
open of `X`, exactly that

* `A` has finitely many minimal primes, and
* every zerodivisor of `A` lies in one of them.

Those two statements are the hypotheses of `IsLocalization.nonZeroDivisors_of_etale`, which is
the ring-theoretic content of Stacks 0EN6: for `A → B` étale the localization of `B` at the
image of the nonzerodivisors of `A` is already the total ring of fractions of `B`. This file
performs that translation.

## Main results

* `AlgebraicGeometry.exists_mem_minimalPrimes_of_notMem_nonZeroDivisors`: if every weakly
  associated point of `X` is a generic point of an irreducible component, then every
  zerodivisor of the ring of sections over an affine open lies in a minimal prime of that ring.
* `AlgebraicGeometry.finite_minimalPrimes_appTop`: if every quasi-compact open of an affine
  scheme has finitely many irreducible components, then its ring of global sections has
  finitely many minimal primes.

## Implementation notes

A zerodivisor `a` of `Γ(X, U)` kills a nonzero section `m`, so it lies in the annihilator of
`m`, and that annihilator is proper and therefore has a minimal prime `q` above it. The prime
`q` names a point of `U`, which is weakly associated to the structure sheaf precisely because
`q` is minimal over that annihilator (Stacks 056M), hence is a generic point of an irreducible
component by hypothesis, hence `q` is a minimal prime of `Γ(X, U)`.

The translation of the last step, from a generic point of `X` lying in an affine open to a
minimal prime of the ring of sections there, is
`AlgebraicGeometry.primeIdealOf_mem_minimalPrimes_of_mem_genericPoints`.

The finiteness statement is the case `U = ⊤` of
`AlgebraicGeometry.finite_minimalPrimes_of_affine_open`, which is Stacks 035P.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 056M](https://stacks.math.columbia.edu/tag/056M)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- **Hypothesis (a) of Stacks 0EN6 on an affine open.** If every weakly associated point of a
scheme `X` is a generic point of an irreducible component, then every zerodivisor of the ring
of sections over an affine open lies in a minimal prime of that ring. -/
theorem exists_mem_minimalPrimes_of_notMem_nonZeroDivisors {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U)
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (a : Γ(X, U)) (ha : a ∉ Γ(X, U)⁰) :
    ∃ q ∈ minimalPrimes Γ(X, U), a ∈ q := by
  rw [mem_nonZeroDivisors_iff_right] at ha
  push Not at ha
  obtain ⟨m, hma, hm0⟩ := ha
  have hIne : (Γ(X, U) ∙ m).annihilator ≠ ⊤ := by
    simpa [Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot] using hm0
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hIne
  have haI : a ∈ (Γ(X, U) ∙ m).annihilator := by
    rwa [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
  let x : X := hU.fromSpec ⟨q, hq.isPrime⟩
  have hxU : x ∈ U := hU.range_fromSpec.subset ⟨_, rfl⟩
  have hqx : q = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    (congrArg PrimeSpectrum.asIdeal <| hU.fromSpec.isOpenEmbedding.injective
      (hU.fromSpec_primeIdealOf ⟨x, hxU⟩)).symm
  have hxwa : x ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints X := by
    rw [Stacks.Divisors.mem_schemeWeaklyAssociatedPoints_iff,
      ← AlgebraicGeometry.isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) U hU x hxU, ← hqx]
    exact ⟨m, hq⟩
  exact ⟨q, hqx ▸ primeIdealOf_mem_minimalPrimes_of_mem_genericPoints U hU x hxU (hass hxwa),
    hq.1.2 haI⟩

/-- **Hypothesis (b) of Stacks 0EN6 on an affine scheme.** If every quasi-compact open of an
affine scheme has finitely many irreducible components, then its ring of global sections has
finitely many minimal primes.

This is the case `U = ⊤` of Stacks 035P, `AlgebraicGeometry.finite_minimalPrimes_of_affine_open`,
the presenting isomorphism being `AlgebraicGeometry.Scheme.isoSpec`. -/
theorem finite_minimalPrimes_appTop (X : Scheme.{u}) [IsAffine X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    (minimalPrimes Γ(X, ⊤)).Finite :=
  finite_minimalPrimes_of_affine_open hX ⊤ (X.isoSpec.symm ≪≫ (Scheme.topIso X).symm)

end AlgebraicGeometry

end

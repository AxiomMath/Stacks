module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.Topology.Profinite.Defs

/-!
# Profinite spectra and incomparable primes in the fibres

Let `A → B` be a homomorphism of commutative rings whose source has profinite prime spectrum. If
no two distinct comparable prime ideals of `B` lie over the same prime ideal of `A`, then the prime
spectrum of `B` is profinite as well: profiniteness of a spectrum is the absence of nontrivial
inclusions between primes, and such an inclusion in `B` would have to sit inside a single fibre
once the corresponding inclusion in `A` has collapsed.

Quasi-finite algebras satisfy that fibrewise condition, and unramified and étale algebras are
quasi-finite, so profiniteness of the spectrum goes up along each of these three classes of maps.

## Main results

* `AlgebraicGeometry.ProEtale.isProfiniteStacks_primeSpectrum_of_fiberwise_incomparable`:
  fibrewise incomparability of primes preserves profiniteness of spectra.
* `AlgebraicGeometry.ProEtale.isProfiniteStacks_primeSpectrum_of_quasiFinite`: a quasi-finite
  algebra over a ring with profinite spectrum has profinite spectrum.
* `AlgebraicGeometry.ProEtale.isProfiniteStacks_primeSpectrum_of_unramified`: the same for an
  unramified algebra.
* `AlgebraicGeometry.ProEtale.isProfiniteStacks_primeSpectrum_of_etale`: the same for an étale
  algebra.

## Implementation notes

Profiniteness is taken in the form `IsProfiniteStacks`, and the passage between it and the
absence of nontrivial inclusions between primes goes through
`isProfiniteStacks_iff_compact_t2_totallyDisconnected` and `spec_profinite_tfae`. The two rings
are allowed to live in different universes, which is why the characterisation of
`IsProfiniteStacks` is used at a free universe rather than at `Type`.

Fibrewise incomparability is expressed by saying that comparable prime ideals with equal
contractions are equal. Since the condition is quantified over both orders of a pair of primes,
this is equivalent to the source's assertion that distinct primes in a fibre are incomparable.

Unramifiedness and étaleness are expressed by Mathlib's `Algebra.Unramified` and `Algebra.Etale`
classes, and quasi-finiteness by `Algebra.QuasiFinite`, which records the finite-fibre condition
the result uses; the statements therefore do not carry the additional finite-type hypothesis in
the Stacks Project's definition of a quasi-finite map.

## References

* [Stacks Project, Tag 0978](https://stacks.math.columbia.edu/tag/0978)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry.ProEtale

/-- If the spectrum of `A` is profinite and distinct prime ideals of `B` lying over the same
prime ideal of `A` are incomparable, then the spectrum of `B` is profinite. -/
@[stacks 0978 "fiberwise_incomparable"]
theorem isProfiniteStacks_primeSpectrum_of_fiberwise_incomparable
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] (f : A →+* B)
    (hA : IsProfiniteStacks (PrimeSpectrum A))
    (hfiber : ∀ q q' : Ideal B, q.IsPrime → q'.IsPrime →
      Ideal.comap f q = Ideal.comap f q' → q ≤ q' → q = q') :
    IsProfiniteStacks (PrimeSpectrum B) := by
  have hT2 : T2Space (PrimeSpectrum A) :=
    ((isProfiniteStacks_iff_compact_t2_totallyDisconnected (PrimeSpectrum A)).1 hA).2.1
  have hincA : ∀ p q : Ideal A, p.IsPrime → q.IsPrime → p ≤ q → p = q :=
    ((spec_profinite_tfae A).out 2 5).mp hT2
  have hincB : ∀ p q : Ideal B, p.IsPrime → q.IsPrime → p ≤ q → p = q := fun p q hp hq hpq =>
    hfiber p q hp hq (hincA _ _ (hp.comap f) (hq.comap f) (Ideal.comap_mono hpq)) hpq
  exact (isProfiniteStacks_iff_compact_t2_totallyDisconnected (PrimeSpectrum B)).2
    (((spec_profinite_tfae B).out 5 1).mp hincB)

/-- A quasi-finite algebra over a ring with profinite prime spectrum has profinite prime
spectrum. -/
@[stacks 0978 "quasi_finite"]
theorem isProfiniteStacks_primeSpectrum_of_quasiFinite
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.QuasiFinite A B] (hA : IsProfiniteStacks (PrimeSpectrum A)) :
    IsProfiniteStacks (PrimeSpectrum B) :=
  isProfiniteStacks_primeSpectrum_of_fiberwise_incomparable A B (algebraMap A B) hA
    (fun q q' hq hq' heq hle =>
      @Algebra.QuasiFinite.eq_of_le_of_under_eq A B _ _ _ _ q q' hq hq' hle heq)

/-- An unramified algebra over a ring with profinite prime spectrum has profinite prime
spectrum. -/
@[stacks 0978 "unramified"]
theorem isProfiniteStacks_primeSpectrum_of_unramified
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Unramified A B] (hA : IsProfiniteStacks (PrimeSpectrum A)) :
    IsProfiniteStacks (PrimeSpectrum B) :=
  isProfiniteStacks_primeSpectrum_of_quasiFinite A B hA

/-- An étale algebra over a ring with profinite prime spectrum has profinite prime spectrum. -/
@[stacks 0978 "etale"]
theorem isProfiniteStacks_primeSpectrum_of_etale
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (hA : IsProfiniteStacks (PrimeSpectrum A)) :
    IsProfiniteStacks (PrimeSpectrum B) :=
  @isProfiniteStacks_primeSpectrum_of_quasiFinite A B _ _ _
    (RingHom.quasiFinite_algebraMap.mp
      (RingHom.Etale.quasiFinite (algebraMap A B)
        (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)))) hA

end AlgebraicGeometry.ProEtale

module

public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.Finiteness
public import StacksFrontier.RingTheory.Flat.ClosedSubset
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs

/-!
# The relative flat locus of a finite module

Let `R → S` be a ring map of finite presentation and let `M` be a *finite* `S`-module. The
relative flat locus of `M` is the set

`U = {q ⊂ S prime | M_q is flat over R} ⊆ Spec S`.

For a *finitely presented* `M` this set is open and `M` is finitely presented on it, with no
hypothesis on `R`; that is Stacks 00RC, `Module.isOpen_setOf_flat_localizedModule_atPrime`. For a
merely finite `M` openness becomes a condition on the base, and it holds as soon as `R` has only
finitely many weakly associated primes.

This file makes the single local statement from which the openness and finite-presentation
assertions of Stacks 05IL follow formally:
`Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime`, the affine content of
Stacks 05IK — around a prime of relative flatness there is a basic open on which `M` becomes
finitely presented over the localized ring and flat over `R`.

## Main definitions

* `Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime` is the local form of
  Stacks 05IK, quantified over the rings and modules of three universes.

The two assertions of Stacks 05IL it yields are in
`StacksFrontier/RingTheory/Flat/FlatLocusFiniteModuleOpenness.lean`, which is where they have to
live: the theorem discharging the definition,
`Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime`, is proved through the geometry
of Stacks 05I5 and 05I7 and is therefore below this module.

## Implementation notes

The local statement is a `Prop`-valued definition rather than an argument of each theorem, so
that it is named once and discharged once. In the source it is proved as follows. Let `q` be a
prime with `M_q` flat over `R`. By Stacks 05I7 the localization `M_q` is finitely presented over
`S_q`, so by Stacks 05GJ (`Module.exists_finite_isLocalizedModule_comp_atPrime`) there are a
finitely presented `S`-module `M'` and a map `φ : M' → M` inducing an isomorphism `M'_q ≅ M_q`.
Then `M'` is flat over `R` at `q`, so by Stacks 00RC
(`Module.isOpen_setOf_flat_localizedModule_atPrime`) it is flat over `R` on a basic open around
`q`; as `M` is finite, `φ` becomes surjective on a smaller basic open. By Stacks 05IJ together
with Stacks 05AF the weakly associated primes of `M'` on that basic open are finitely many, so by
prime avoidance one may shrink once more and assume they are all contained in `q`. The kernel `K`
of `φ` then satisfies `WeakAss(K) ⊆ WeakAss(M')` (Stacks 0548,
`Module.weaklyAssociatedPrimes_subset_of_injective`) while `K_p = 0` for every `p ⊆ q`, because
`φ_q` is an isomorphism; hence `WeakAss(K) = ∅` and `K = 0` by Stacks 0588
(`weakAss_empty_iff_zero`).

The conclusion of the definition is shaped like that of
`Module.exists_away_finitePresentation_flat_of_flat_atPrime`, the local form of Stacks 053A, and
that is deliberate: Stacks 053A reaches the same conclusion from weaker hypotheses on `R` — it
asks only for finitely many detecting primes, which finitely many weakly associated primes supply
by Stacks 05GS — but it asks the module to be finitely presented after localizing at every prime
of the base, which a finite module need not be, already for `S = R` and `M = R/I` with `I` not
finitely generated.

What the definition yields is formal, and is carried out in
`StacksFrontier/RingTheory/Flat/FlatLocusFiniteModuleOpenness.lean`.

## References

* [Stacks Project, Tag 05IL](https://stacks.math.columbia.edu/tag/05IL)
* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
-/

@[expose] public section

universe u v w

namespace Stacks.Flatness

/-- **The local form of Stacks 05IK.** For every ring map `R → S` of finite presentation whose
source has finitely many weakly associated primes, every finite `S`-module `M` and every prime
`q` of `S` at which `M` is flat over `R`, there is a `g ∉ q` such that the localization `M_g` is
a finitely presented `S_g`-module and is flat over `R`.

This is the affine content of Stacks 05IK, from which the whole of Stacks, Section 38.8 follows
formally; see the implementation notes of this file for the proof in the source and for the
results it rests on. -/
def ExistsAwayFlatFinitePresentationOfFlatAtPrime : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
      [Algebra.FinitePresentation R S] (M : Type w) [AddCommGroup M] [Module S M] [Module R M]
      [IsScalarTower R S M] [Module.Finite S M],
    (weaklyAssociatedPrimes R R).Finite → ∀ q : PrimeSpectrum S,
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) →
      ∃ g ∉ q.asIdeal,
        Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M) ∧
          Module.Flat R (LocalizedModule.Away g M)

end Stacks.Flatness

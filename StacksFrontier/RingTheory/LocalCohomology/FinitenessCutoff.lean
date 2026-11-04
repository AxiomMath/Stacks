module

public import Mathlib.RingTheory.Ideal.Height
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Depth.AlgebraMap

/-!
# The local cohomology finiteness cutoff

For an ideal `I` of a commutative ring `A` and an `A`-module `M`, the local cohomology
finiteness cutoff is

`s_{A,I}(M) = min_{𝔭 ∉ V(I), 𝔮 ∈ V(I), 𝔭 ⊆ 𝔮} (depth(M_𝔭) + dim((A/𝔭)_𝔮))`,

the minimum being over pairs of primes `𝔭 ⊆ 𝔮` with `𝔭` outside and `𝔮` inside the closed set
cut out by `I`. It is the cutoff of Stacks 0BJR: for a finite module over a Noetherian ring the
local cohomology modules `H^i_{V(I)}(M)` are finite for `i < s_{A,I}(M)`.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyCutoff` — this cutoff, with values in `ℕ∞`.

## Main results

* `Stacks.LocalCohomology.le_localCohomologyCutoff_iff` — characterizes lower bounds for the
  cutoff.
* `Stacks.LocalCohomology.localCohomologyCutoff_le` — the cutoff's upper bound attached to each
  admissible pair of primes.
* `Stacks.LocalCohomology.localCohomologyCutoff_bot` and
  `Stacks.LocalCohomology.localCohomologyCutoff_top` — the two empty-locus cases.

## Implementation notes

The minimum is represented by an infimum in `ℕ∞`; in particular, an empty set of admissible
pairs has cutoff `∞`. The dimension of `(A/𝔭)_𝔮` is the height of the image `𝔮/𝔭` of `𝔮` in
`A/𝔭`; this is the identification `IsLocalization.AtPrime.ringKrullDim_eq_height` applied after
quotienting by `𝔭`. Although the source introduces the cutoff for a finite module over a
Noetherian ring, its defining expression makes sense without either finiteness hypothesis, so
the definition is given in that generality.

## References

* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
-/

@[expose] public section

namespace Stacks.LocalCohomology

/-- The local cohomology finiteness cutoff
`s_{A,I}(M) = min_{p ∉ V(I), q ∈ V(I), p ⊆ q} (depth(Mₚ) + dim((A / p)ₒ))`. -/
@[stacks 0BJR]
public noncomputable def localCohomologyCutoff (A : Type*) [CommRing A] (I : Ideal A)
    (M : Type*) [AddCommGroup M] [Module A M] : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ p q : PrimeSpectrum A,
    ¬ I ≤ p.asIdeal ∧ I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal ∧
      n = Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height}

/-- An element is a lower bound for the local cohomology cutoff exactly when it is a lower
bound for the value attached to every admissible pair of primes. -/
public theorem le_localCohomologyCutoff_iff (A : Type*) [CommRing A] (I : Ideal A)
    (M : Type*) [AddCommGroup M] [Module A M] (n : ℕ∞) :
    n ≤ localCohomologyCutoff A I M ↔
      ∀ p q : PrimeSpectrum A, ¬ I ≤ p.asIdeal → I ≤ q.asIdeal →
        p.asIdeal ≤ q.asIdeal →
          n ≤ Module.depth (Localization.AtPrime p.asIdeal)
              (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M) +
            (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  rw [localCohomologyCutoff, le_sInf_iff]
  aesop

/-- Every admissible pair of primes gives an upper bound for the local cohomology cutoff. -/
public theorem localCohomologyCutoff_le (A : Type*) [CommRing A] (I : Ideal A)
    (M : Type*) [AddCommGroup M] [Module A M] (p q : PrimeSpectrum A)
    (hp : ¬ I ≤ p.asIdeal) (hq : I ≤ q.asIdeal) (hpq : p.asIdeal ≤ q.asIdeal) :
    localCohomologyCutoff A I M ≤
      Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
  sInf_le ⟨p, q, hp, hq, hpq, rfl⟩

/-- When `I = ⊥`, there is no prime outside `V(I)`, so the cutoff is infinite. -/
@[simp]
public theorem localCohomologyCutoff_bot (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M] :
    localCohomologyCutoff A ⊥ M = ⊤ := by
  apply top_unique
  rw [le_localCohomologyCutoff_iff]
  aesop

/-- When `I = ⊤`, there is no prime in `V(I)`, so the cutoff is infinite. -/
@[simp]
public theorem localCohomologyCutoff_top (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M] :
    localCohomologyCutoff A ⊤ M = ⊤ :=
  top_unique <| (le_localCohomologyCutoff_iff A ⊤ M ⊤).2 fun _ q _ hq _ ↦
    (q.isPrime.ne_top (top_unique hq)).elim

end Stacks.LocalCohomology

end

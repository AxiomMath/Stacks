module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.Topology.Specialization.Defs

/-!
# The bootstrap situation for algebraization

The bootstrap theorems of the chapter on algebraic and formal geometry all run in one standing
situation: a Noetherian ring `A` with a dualizing complex, an ideal `I`, a finite `A`-module
`M`, a specialization-stable subset `T` of the adic locus `V(I)`, and two integer bounds `s`
and `d` controlling cohomological dimension and depth.

Two of the four assumptions are depth estimates. The first concerns a chain of three primes
`p ⊆ r ⊆ q` with `q ∈ T`, `r ∈ V(I) \ T` and `p ∉ V(I)`: either the depth of `M_p` is at least
`s`, or that depth plus the dimension of the fibre of `Spec(A_q) → Spec(A/p)` exceeds `d + s`.
The second concerns the completed localization `A_q^∧` at a point `q` of `T`: every prime `p'`
of it outside the adic locus whose only common specialization with the adic locus is the closed
point has `depth((M_q^∧)_{p'}) > s`.

## Main definitions

* `Stacks.Algebraization.BootstrapSituation` — the standing data together with all four
  assumptions.

## Implementation notes

The source numbers its assumptions (1), (3), (4) and (6); the corresponding fields are
`dualizing`, `cohomologicalDimension_le`, `depth_or_depth_add_dimension` and
`completedLocalDepth`. Depth and dimension bounds are compared in the extended integers
through `enatToEInt` and `krullDimToEInt`, which keeps negative values of `s` and `d`
meaningful. The closed point of a completed localization is the extension of the maximal ideal
of the localized ring, so the condition singling out `p'` is phrased with that ideal.

The module lives in its own universe, and the dualizing complex in the universe `max u w`,
which contains the ring universe and is preserved by derived extension of scalars to a
localization.

## References

* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-- The standing bootstrap situation for algebraization: a Noetherian ring with a dualizing
complex, an ideal, a finite module, a specialization-stable subset of the adic locus, and the two
integer bounds against which depth and cohomological dimension are measured. -/
@[stacks 0EFU]
public structure BootstrapSituation where
  /-- The base ring. -/
  A : Type u
  /-- The commutative-ring structure on `A`. -/
  [commRing : CommRing A]
  /-- The Noetherian hypothesis on `A`. -/
  [isNoetherianRing : IsNoetherianRing A]
  /-- The ideal cutting out the adic locus. -/
  I : Ideal A
  /-- The module the bootstrap theorems are stated for. -/
  M : Type v
  /-- The additive-group structure on `M`. -/
  [addCommGroup : AddCommGroup M]
  /-- The `A`-module structure on `M`. -/
  [module : Module A M]
  /-- Finiteness of `M` over `A`. -/
  [finite : Module.Finite A M]
  /-- The locus the bootstrap conclusion is asserted over. -/
  T : Set (PrimeSpectrum A)
  /-- `T` is contained in the adic locus `V(I)`. -/
  subset_adicLocus : T ⊆ PrimeSpectrum.zeroLocus (I : Set A)
  /-- `T` is stable under specialization. -/
  stableUnderSpecialization : StableUnderSpecialization T
  /-- The depth bound. -/
  s : ℤ
  /-- The cohomological-dimension bound. -/
  d : ℤ
  /-- Assumption (1): `A` admits a dualizing complex. -/
  dualizing : ∃ K : DerivedCategory (ModuleCat.{max u w} A), Dualizing.IsDualizingComplex K
  /-- Assumption (3): the cohomological dimension of `I` is at most `d`. -/
  cohomologicalDimension_le :
    Stacks.LocalCohomology.cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) ≤ d
  /-- Assumption (4): for a chain `p ⊆ r ⊆ q` of primes with `q ∈ T`, `r ∈ V(I) \ T` and
  `p ∉ V(I)`, either `M_p` has depth at least `s`, or that depth plus the dimension of
  `A_q ⧸ p A_q` exceeds `d + s`. -/
  depth_or_depth_add_dimension :
    ∀ p r q : PrimeSpectrum A,
      p.asIdeal ≤ r.asIdeal → r.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      r ∈ PrimeSpectrum.zeroLocus (I : Set A) → r ∉ T → q ∈ T →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) ≥ (s : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
        ((d + s : ℤ) : EInt))
  /-- Assumption (6): for `q ∈ T`, every prime `p'` of the `I_q`-adic completion of `A_q` that
  lies outside the adic locus and whose only common specialization with the adic locus is the
  closed point has `depth((M_q^∧)_{p'}) > s`. -/
  completedLocalDepth :
    ∀ q : PrimeSpectrum A, q ∈ T →
      let Aq := Localization.AtPrime q.asIdeal
      let Iq := I.map (algebraMap A Aq)
      let Mq := LocalizedModule q.asIdeal.primeCompl M
      let A' := AdicCompletion Iq Aq
      let I' := Iq.map (algebraMap Aq A')
      let m' := (maximalIdeal Aq).map (algebraMap Aq A')
      ∀ p' : PrimeSpectrum A',
        ¬ I' ≤ p'.asIdeal →
        {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} = {m'} →
        enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq))) >
          (s : EInt)

attribute [instance] BootstrapSituation.commRing BootstrapSituation.isNoetherianRing
  BootstrapSituation.addCommGroup BootstrapSituation.module BootstrapSituation.finite

end Stacks.Algebraization

end

module

public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.HartshorneLichtenbaumExcellent
public import StacksFrontier.RingTheory.LocalCohomology.DimensionBoundUnconditional
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# The cohomological dimension of the ramification locus of a normal excellent ring

Let `A` be an excellent normal Noetherian ring of Krull dimension at most `d ≥ 2`, and let
`I ⊆ A` be an ideal. Suppose that at every prime `𝔭` of height at least two the zero locus of `I`
in `Spec A_𝔭` has dimension at least one, which is to say that `Spec A_𝔭 ∖ V(I)` is strictly
smaller than the punctured spectrum of `A_𝔭`. Then `cd(A, I) ≤ d - 1`.

This is the middle of the proof of [Stacks, Tag 0ECD], where `Spec A = X` is an affine
neighbourhood in a normal scheme of finite type over an excellent regular base of dimension `d`
and `V = Spec A ∖ V(I)` is the locus where the structure morphism is étale. Written in terms of
the largest degree `e(V)` in which `H ⁱ(V, 𝒪_V)` is nonzero, which is `cd(A, I) - 1`, the
conclusion is the source's bound `e(V) ≤ max(0, d - 2)`.

The two cases of the source's argument are the two cases below. At a prime of height at most one
the bound `cd(A_𝔭, I A_𝔭) ≤ 1` is [Stacks, Tag 0DXC]. At a prime of height `h ≥ 2` the local
ring is excellent ([Stacks, Tag 07QU]) and normal ([Stacks, Tag 037C]), so Hartshorne–Lichtenbaum
vanishing ([Stacks, Tag 0EB7]) sharpens that bound to `cd(A_𝔭, I A_𝔭) < h ≤ d`. Globalizing over
the primes is [Stacks, Tag 0DXB].

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_le_sub_one_of_isExcellent_of_isNormalRing`

## What is *not* proved here

The positivity hypothesis `hpos`. In [Stacks, Tag 0ECD] it is supplied by purity of the
ramification locus ([Stacks, Tag 0EA4]): at a point `x` of `X` with `dim(𝒪_{X,x}) ≥ 2` outside
the étale locus, purity forbids the étale locus from containing the whole punctured spectrum of
`𝒪_{X,x}`, so its closed complement there has dimension at least one. As stated here `hpos` is
asked at every prime of height at least two, including those where `I` becomes the unit ideal;
the proof of [Stacks, Tag 0ECD] in
`StacksFrontier/AlgebraicGeometry/Etale/AffineMaximalEtaleOpen.lean` therefore runs the same case
analysis directly, asking positivity only at the primes outside the étale locus.

## Implementation notes

The hypothesis is stated at every prime whose localization has Krull dimension at least two,
rather than at every prime of height at least two; the two agree, since
`dim A_𝔭 = ht 𝔭`, and the former is the form in which the globalization
`Stacks.LocalCohomology.cohomologicalDimension_le_of_forall_localization_le` presents each prime.

Dimensions live in `WithBot ℕ∞`, so the case split is on the decidable proposition
`2 ≤ dim A_𝔭` and the low case is closed by
`Stacks.LocalCohomology.withBotENat_le_of_lt_succ`. In the high case the natural number that
[Stacks, Tag 0EB7] wants for the dimension of the local ring comes from
`Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim`, the Krull dimension of
a Noetherian local ring being finite.

The finite-generation argument of `Stacks.LocalCohomology.cohomologicalDimension` is a
proposition, so the proof term `Ideal.fg_of_isNoetherianRing` used by [Stacks, Tag 0EB7] and the
proof term `IsFinitelyGenerated.map` expected by the globalization are interchangeable; the
intermediate steps are restated at the latter so that the arithmetic is syntactically uniform.

## References

* [Stacks Project, Tag 0ECD](https://stacks.math.columbia.edu/tag/0ECD)
* [Stacks Project, Tag 0EB7](https://stacks.math.columbia.edu/tag/0EB7)
* [Stacks Project, Tag 0DXB](https://stacks.math.columbia.edu/tag/0DXB)
* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.LocalCohomology

/-- **The cohomological-dimension bound of [Stacks, Tag 0ECD].** Let `A` be an excellent normal
Noetherian ring of Krull dimension at most `d`, with `d ≥ 2`, and let `I ⊆ A` be an ideal. Assume
that for every prime `𝔭` with `dim A_𝔭 ≥ 2` the zero locus of `I A_𝔭` has dimension at least
one. Then `cd(A, I) ≤ d - 1`.

Equivalently `H ⁿ(Spec A ∖ V(I), 𝒪) = 0` for `n ≥ d - 1`, which is the hypothesis under which
[Stacks, Tag 0ECC] concludes that the complement is affine. The positivity assumption is what
purity of the ramification locus supplies in the source; see the module documentation. -/
theorem cohomologicalDimension_le_sub_one_of_isExcellent_of_isNormalRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hA : IsExcellent A)
    (hnormal : IsNormalRing A) (I : Ideal A) (d : ℕ) (hd2 : 2 ≤ d)
    (hdim : ringKrullDim A ≤ (d : WithBot ℕ∞))
    (hpos : ∀ p : PrimeSpectrum A,
      (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p.asIdeal) →
      (1 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p.asIdeal ⧸
        I.map (algebraMap A (Localization.AtPrime p.asIdeal)))) :
    cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) ≤ (d : ℤ) - 1 := by
  classical
  have hfg : I.FG := Ideal.fg_of_isNoetherianRing I
  refine cohomologicalDimension_le_of_forall_localization_le A I hfg ((d : ℤ) - 1)
    (by omega) fun p => ?_
  have hp : p.asIdeal.IsPrime := p.isPrime
  have hlr : IsLocalRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p.asIdeal) p.asIdeal
  have hnoeth : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  have hle : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ (d : WithBot ℕ∞) :=
    (ringKrullDim_localizationAtPrime_le A p).trans hdim
  by_cases h2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p.asIdeal)
  · have hex : IsExcellent (Localization.AtPrime p.asIdeal) := by
      have : Algebra.EssFiniteType A (Localization.AtPrime p.asIdeal) :=
        Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl
      exact (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2 hA
    have hnl : IsNormalRing (Localization.AtPrime p.asIdeal) :=
      hnormal.isLocalization p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    obtain ⟨m, hr⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
      (Localization.AtPrime p.asIdeal)
    have hmd : m ≤ d := by rw [hr] at hle; exact_mod_cast hle
    have hlt : cohomologicalDimension (Localization.AtPrime p.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (hfg.map (algebraMap A (Localization.AtPrime p.asIdeal))) < (m : ℤ) :=
      cohomologicalDimension_lt_of_isExcellent_of_isNormalRing
        (Localization.AtPrime p.asIdeal) hex hnl m hr
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal))) (hpos p h2)
    omega
  · have hlt2 : ringKrullDim (Localization.AtPrime p.asIdeal) < ((1 + 1 : ℕ) : WithBot ℕ∞) := by
      have := not_le.mp h2
      simpa using this
    have h1 : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
      withBotENat_le_of_lt_succ _ 1 hlt2
    have hcd : cohomologicalDimension (Localization.AtPrime p.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (hfg.map (algebraMap A (Localization.AtPrime p.asIdeal))) ≤ ((1 : ℕ) : ℤ) :=
      cohomologicalDimension_le_of_isLocalRing (Localization.AtPrime p.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (hfg.map (algebraMap A (Localization.AtPrime p.asIdeal))) 1 h1
    omega

end Stacks.LocalCohomology

end

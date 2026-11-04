module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.CutoffCriterionAffineZeroLocus
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterion

/-!
# The depth–dimension criterion for coherence of the higher direct images, along `Z`

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and put `X = Spec A`, `Z = V(I)`,
`U = X ∖ Z`, with `j : U → X` the inclusion. Let `M` be a finite `A`-module and let
`ℱ = M̃|_U`, a coherent `𝒪_U`-module. Fix a natural number `n`, assume `A` is universally
catenary and assume the formal fibres of `𝒪_{X,q}` satisfy Serre's condition `(Sₙ)` for every
`q ∈ Z`. Then the following are equivalent:

* for every pair of primes `𝔭 ⊆ 𝔮` of `A` with `𝔭 ∉ Z`, `𝔮 ∈ Z` and `M_𝔭 ≠ 0`, one has
  `depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > n`;
* `R^pj_*ℱ` is coherent for every `0 ≤ p < n`.

This is [Stacks, Tag 0BJY] over an affine base, with the formal-fibres hypothesis imposed along
`Z`.

## Main results

* `LocalCohomologySequence.forall_lt_depth_add_height_iff_forall_isCoherent_rightDerivedZeroLocus`
  — the equivalence above.

## References

* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.LocalCohomologyTilde

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-- **[Stacks, Tag 0BJY] over an affine base, formal fibres along `Z`.** Let `A` be a
universally catenary Noetherian ring, let `I ⊆ A` be an ideal, put `X = Spec A`, `Z = V(I)`,
`U = X ∖ Z` and let `j : U → X` be the inclusion. Let `M` be a finite `A`-module, let
`ℱ = M̃|_U` and let `n` be a natural number. Assume the formal fibres of `𝒪_{X,q}` satisfy
Serre's condition `(Sₙ)` for every `q ∈ Z`. Then `depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > n` for
every pair of primes `𝔭 ⊆ 𝔮` with `𝔭 ∉ Z`, `𝔮 ∈ Z` and `M_𝔭 ≠ 0` if and only if `R^pj_*ℱ` is
coherent for every `0 ≤ p < n`. -/
public theorem forall_lt_depth_add_height_iff_forall_isCoherent_rightDerivedZeroLocus
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hA : Ring.IsUniversallyCatenary (ToType A)) (n : ℕ)
    (hformal : ∀ q : PrimeSpectrum (ToType A), I ≤ q.asIdeal →
      Stacks.LocalCohomology.FormalFibersHavePropertySk
        (Localization.AtPrime q.asIdeal) n) :
    (∀ p q : PrimeSpectrum (ToType A), ¬ I ≤ p.asIdeal → I ≤ q.asIdeal →
        p.asIdeal ≤ q.asIdeal →
        Nontrivial (LocalizedModule p.asIdeal.primeCompl M) →
        (n : ℕ∞) < Module.depth (Localization.AtPrime p.asIdeal)
              (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M) +
            (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height) ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
          ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent := by
  have hn := ENat.natCast_ne_top n
  refine Iff.trans ?_
    (lt_localCohomologyCutoff_iff_forall_isCoherent_rightDerivedZeroLocus I M hA n hformal)
  refine Iff.trans ?_ (ENat.add_one_le_iff hn)
  rw [Stacks.LocalCohomology.le_localCohomologyCutoff_iff]
  refine ⟨fun h p q hp hq hpq => ?_, fun h p q hp hq hpq _ => ?_⟩
  · rw [ENat.add_one_le_iff hn]
    rcases subsingleton_or_nontrivial (LocalizedModule p.asIdeal.primeCompl M) with hsub | hnt
    · rw [Module.depth_eq_top_of_subsingleton]
      exact lt_of_lt_of_le hn.lt_top le_self_add
    · exact h p q hp hq hpq hnt
  · rw [← ENat.add_one_le_iff hn]
    exact h p q hp hq hpq

end Stacks.LocalCohomologySequence

end

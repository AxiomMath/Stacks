module

public import StacksFrontier.Algebra.Module.DepthSubsingleton
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.CutoffCriterionAffine

/-!
# The depth–dimension criterion for coherence of the higher direct images

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and put `X = Spec A`, `Z = V(I)`,
`U = X ∖ Z`, with `j : U → X` the inclusion. Let `M` be a finite `A`-module and let
`ℱ = M̃|_U`, a coherent `𝒪_U`-module. Fix a natural number `n`, assume `A` is universally
catenary and assume the formal fibres of the local rings of `A` satisfy Serre's condition
`(Sₙ)`. Then the following are equivalent:

* for every pair of primes `𝔭 ⊆ 𝔮` of `A` with `𝔭 ∉ Z`, `𝔮 ∈ Z` and `M_𝔭 ≠ 0`, one has
  `depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > n`;
* `R^pj_*ℱ` is coherent for every `0 ≤ p < n`.

This is [Stacks, Tag 0BJY] over an affine base. The points `𝔭 ∉ Z` with `M_𝔭 ≠ 0` are the
points of `Supp(ℱ)`, the primes `𝔮 ⊇ 𝔭` in `Z` are the points of `Z ∩ closure{𝔭}`,
`depth_{A_𝔭}(M_𝔭)` is the depth of the stalk `ℱ_𝔭` over `𝒪_{X,𝔭}`, and `dim((A/𝔭)_𝔮)` is the
dimension of the local ring of the reduced closure of `𝔭` at `𝔮`.

## Main results

* `Stacks.LocalCohomologySequence.forall_lt_depth_add_height_iff_forall_isCoherent_rightDerived` —
  the equivalence above.

## Implementation notes

Over the affine base the two sides of the equivalence are read in the vocabulary of `A`: the
depth of the stalk `ℱ_𝔭` is the depth of the localization `M_𝔭` by
`AlgebraicGeometry.depth_stalk_eq_depth_localizedModule`, and the dimension of the local ring
of the reduced closure of `𝔭` at `𝔮` is the height of the image of `𝔮` in `A ⧸ 𝔭` by
`topCodim_closureSingleton_eq_height_map_quotientMk`.

Serre's condition on the formal fibres is imposed at every prime of `A`, not only at the primes
of `Z`; this is the form in which [Stacks, Tag 0BJW] is available.

Every coherent `𝒪_U`-module is a restriction `M̃|_U` with `M` a finite `A`-module, by clause (1)
of [Stacks, Tag 0BK0] in the form
`AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl`; the statement below fixes
`M`, because the left-hand condition is a condition on `M`.

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

/-- **[Stacks, Tag 0BJY] over an affine base.** Let `A` be a universally catenary Noetherian
ring, let `I ⊆ A` be an ideal, put `X = Spec A`, `Z = V(I)`, `U = X ∖ Z` and let
`j : U → X` be the inclusion. Let `M` be a finite `A`-module, let `ℱ = M̃|_U` and let `n` be a
natural number. Assume the formal fibres of the local rings of `A` satisfy Serre's condition
`(Sₙ)`. Then `depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > n` for every pair of primes `𝔭 ⊆ 𝔮` with
`𝔭 ∉ Z`, `𝔮 ∈ Z` and `M_𝔭 ≠ 0` if and only if `R^pj_*ℱ` is coherent for every `0 ≤ p < n`.

The dimension of `(A/𝔭)_𝔮` appears as the height of the image of `𝔮` in `A ⧸ 𝔭`, and the
depth of `ℱ_𝔭` as the depth of `M_𝔭` over `A_𝔭`. -/
public theorem forall_lt_depth_add_height_iff_forall_isCoherent_rightDerived
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hA : Ring.IsUniversallyCatenary (ToType A)) (n : ℕ)
    (hformal : ∀ q : PrimeSpectrum (ToType A),
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
  refine Iff.trans ?_
    (lt_localCohomologyCutoff_iff_forall_isCoherent_rightDerived I M hA n hformal)
  refine Iff.trans ?_ (ENat.add_one_le_iff (ENat.natCast_ne_top n))
  rw [Stacks.LocalCohomology.le_localCohomologyCutoff_iff]
  refine ⟨fun h p q hp hq hpq => ?_, fun h p q hp hq hpq _ => ?_⟩
  · rw [ENat.add_one_le_iff (ENat.natCast_ne_top n)]
    rcases subsingleton_or_nontrivial (LocalizedModule p.asIdeal.primeCompl M) with hsub | hnt
    · have := hsub
      rw [Module.depth_eq_top_of_subsingleton]
      exact lt_of_lt_of_le (ENat.natCast_lt_top n) le_self_add
    · exact h p q hp hq hpq hnt
  · rw [← ENat.add_one_le_iff (ENat.natCast_ne_top n)]
    exact h p q hp hq hpq

end Stacks.LocalCohomologySequence

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesEssSurj

/-!
# Ramanujam--Samuel for finite étale covers of a power series ring, unconditionally

Let `(A, 𝔪)` be a Noetherian local ring of depth at least two and let `B = A[[x_1, …, x_d]]`
with `d ≥ 1`. For an open `V ⊆ Y = Spec B` which contains every prime `𝔮` of `B` with
`𝔮 ∩ A ≠ 𝔪` and contains the prime `𝔪B`, the functor `FÉt_Y ⟶ FÉt_V` is an equivalence; in
particular purity holds for `B`. This is [Stacks, Tag 0EYA].

The two halves are already in the library: full faithfulness, under the density of `V`, in
`Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_mvPowerSeries`, and essential
surjectivity in `Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_mvPowerSeries`. The
density of `V` is `Stacks.FundamentalGroup.dense_of_comap_ne_maximalIdeal_mem_of_flat`, since `B`
is flat over `A` ([Stacks, Tag 059T]). Purity for `B` is the case where `V` is the punctured
spectrum of `B`.

## Main results

* `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_and_hasPurity_mvPowerSeries` —
  **[Stacks, Tag 0EYA]**, with no hypothesis beyond the tag's.

## References

* [Stacks Project, Tag 059T](https://stacks.math.columbia.edu/tag/059T)
* [Stacks Project, Tag 0EYA](https://stacks.math.columbia.edu/tag/0EYA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.FundamentalGroup

/-- **[Stacks, Tag 0EYA]** (Ramanujam--Samuel for finite étale covers). Let `(A, 𝔪)` be a
Noetherian local ring of depth at least two and let `B = A[[x_1, …, x_d]]` with `d ≥ 1`. Let
`V ⊆ Y = Spec B` be an open which contains every prime `𝔮` of `B` with `𝔮 ∩ A ≠ 𝔪` (`hV₁`)
and contains the prime `𝔪B` (`hV₂`). Then the restriction functor `FÉt_Y ⟶ FÉt_V` is an
equivalence, and purity holds for `B`.

The equivalence is `isEquivalence_finiteEtaleBaseChange_mvPowerSeries` with its two hypotheses
discharged: the density of `V` by `dense_of_comap_ne_maximalIdeal_mem_of_flat`, `B` being flat
over `A` ([Stacks, Tag 059T]) and `A` of positive depth, and essential surjectivity by
`essSurj_finiteEtaleBaseChange_mvPowerSeries`. Purity for `B` is the equivalence for the
punctured spectrum of `B`, which satisfies both conditions on `V`
(`mem_puncturedSpectrum_of_comap_ne_maximalIdeal`, `mem_puncturedSpectrum_of_eq_map_maximalIdeal`;
the latter is where `d ≥ 1` is used). -/
@[stacks 0EYA "the full statement under the tag's hypotheses: for every open `V` containing the \
primes `𝔮` with `𝔮 ∩ A ≠ 𝔪` and the prime `𝔪B`, the restriction `FÉt_Y ⟶ FÉt_V` is an \
equivalence, and purity holds for `B`.", sga "1 XIII 4.7" "special case"]
public theorem isEquivalence_finiteEtaleBaseChange_and_hasPurity_mvPowerSeries (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (d : ℕ) (hd : 0 < d)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV₁ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) ≠ maximalIdeal A →
        q ∈ V)
    (hV₂ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal = Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)
        (maximalIdeal A) → q ∈ V) :
    (finiteEtaleBaseChange V.ι).IsEquivalence ∧ HasPurity (MvPowerSeries (Fin d) A) := by
  have hCA : algebraMap A (MvPowerSeries (Fin d) A) =
      (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) := by
    ext a; simp [MvPowerSeries.algebraMap_apply]
  have : Module.Flat A (MvPowerSeries (Fin d) A) :=
    (Module.flat_and_mittagLeffler_mvPowerSeries A d).1
  have hdepth₁ : (1 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A :=
    le_trans (by norm_num) hdepth
  have hequiv (W : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
      (hW₁ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
        q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) ≠ maximalIdeal A →
          q ∈ W)
      (hW₂ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
        q.asIdeal = Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)
          (maximalIdeal A) → q ∈ W) :
      (finiteEtaleBaseChange W.ι).IsEquivalence :=
    isEquivalence_finiteEtaleBaseChange_mvPowerSeries A d hd hdepth W hW₁ hW₂
      (dense_of_comap_ne_maximalIdeal_mem_of_flat A (MvPowerSeries (Fin d) A) hdepth₁ W
        fun q hq => hW₁ q (hCA ▸ hq))
      (essSurj_finiteEtaleBaseChange_mvPowerSeries A d hd hdepth W hW₁ hW₂)
  exact ⟨hequiv V hV₁ hV₂,
    (hequiv _ (mem_puncturedSpectrum_of_comap_ne_maximalIdeal A d)
      (mem_puncturedSpectrum_of_eq_map_maximalIdeal A d hd)).essSurj⟩

end Stacks.FundamentalGroup

end

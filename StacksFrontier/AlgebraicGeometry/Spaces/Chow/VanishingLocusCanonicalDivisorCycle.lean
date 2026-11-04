module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusTopCycle

/-!
# `i_*[D]_{n-1} = div_ℒ(s)` at the canonical grading

In Situation 0EDT let `X/B` be good and integral with `n = dim_δ(X) = k + 1`, let `ℒ` be an
invertible `𝒪_X`-module and let `σ ∈ Γ(X, ℒ)` be a nonzero global section with vanishing locus
`i : D = Z(σ) → X`.  `cycleGroupClosedPushforward_vanishingLocusTopCycle_eq_sectionWeilDivisor`
identifies `i_*[D]_{n-1}` with the Weil divisor of Stacks 0EQE in the spelling
`AlgebraicGeometry.Space.sectionWeilDivisor`, graded `n - 1`.  Section 0EQU and the cap product
of Stacks 0EQJ use the spelling `AlgebraicGeometry.Space.canonicalDivisorCycleAt`, graded `k`.

The two spellings have the same coefficient family: both are
`AlgebraicGeometry.Space.divisorCycleCoefficients` at the canonical ratio family of Stacks 0EPR
(`AlgebraicGeometry.Space.canonicalLocalRatioFamily`), and they differ only in the proof of
`IsDecentSpace` written down, so they agree definitionally.

## Main results

* `AlgebraicGeometry.Space.sectionWeilDivisor_eq_canonicalDivisorCycleAt`: the two spellings of
  `div_ℒ(s)` agree.
* `cycleGroupClosedPushforward_vanishingLocusTopCycle_eq_canonicalDivisorCycleAt`:
  `i_*[D]_{n-1} = div_ℒ(σ)` with the right-hand side in the spelling of Section 0EQU.

## References

* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- **The two spellings of `div_ℒ(s)` agree.**  `AlgebraicGeometry.Space.sectionWeilDivisor`
(Stacks 0EQE part (1), graded `n - 1`) and
`AlgebraicGeometry.Space.canonicalDivisorCycleAt` (the same cycle graded `k` for `n = k + 1`)
have the same coefficient family: `AlgebraicGeometry.Space.divisorCycleCoefficients` at the
canonical ratio family of Stacks 0EPR. -/
theorem sectionWeilDivisor_eq_canonicalDivisorCycleAt
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)
    (hs0 : s ≠ 0) {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    (sectionWeilDivisor D sX hX hint L hL hn s hs0).1 =
      (canonicalDivisorCycleAt D sX hX hint L hL s hs hn).1 :=
  rfl

/-- **`i_*[D]_{n-1} = div_ℒ(σ)`, with the right-hand side in the spelling of Section 0EQU.**  For
`σ ∈ Γ(X, ℒ)` a nonzero global section of an invertible module on a good integral algebraic space
of δ-dimension `k + 1`, the pushforward along `i : D = Z(σ) → X` of the cycle `[D]_{n-1}` of
Stacks 0EE9 formed on `D` is the Weil divisor of Stacks 0EQE of the meromorphic section of `σ`,
at the canonical ratios of Stacks 0EPR. -/
theorem cycleGroupClosedPushforward_vanishingLocusTopCycle_eq_canonicalDivisorCycleAt
    (hL : IsInvertibleSheaf D sX hX L) {σ : L.sections} (hσ : σ ≠ 0) {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    (cycleGroupClosedPushforward D hX.1 (vanishingLocus D sX hX L σ).2.1
          (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L σ).2.2 sX hX.2.2
          ((vanishingLocus D sX hX L σ).1.ι ≫ sX) rfl (k + 1 - 1)
          (vanishingLocusTopCycle D sX hX hint L hL hσ hn)).1 =
      (canonicalDivisorCycleAt D sX hX hint L hL
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ)
        (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
          (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ)) hn).1 :=
  congrArg Subtype.val
    (cycleGroupClosedPushforward_vanishingLocusTopCycle_eq_sectionWeilDivisor D sX hX hint L hL
      hσ hn)

end AlgebraicGeometry.Space

end

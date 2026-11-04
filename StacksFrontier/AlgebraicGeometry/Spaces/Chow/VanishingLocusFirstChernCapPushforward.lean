module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChernRuleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusCanonicalDivisorCycle

/-!
# `i_*(c₁(𝒩) ∩ [D]_{n-1}) = c₁(𝒩) ∩ div_ℒ(σ)`

In Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = k + 2`, let `ℒ` be an
invertible `𝒪_X`-module with a nonzero global section `σ` and let `i : D = Z(σ) → X` be the
closed immersion of the vanishing locus of Stacks 0845.  The right-hand side
`c₁(𝒩) ∩ [D]_{n-1}` of Stacks 0ER9 is a cap product of Stacks 0EQJ formed **on `D`**, while the
key formula of Stacks 0EQV is an identity on `X`; this file carries it across.

Two facts combine.  Stacks 0EQT along the closed immersion `i`, at the level of cycles and with
nothing assumed, is `AlgebraicGeometry.Space.cycleGroupClosedPushforward_firstChernCapCycleMap`:

`i_*(c₁ ∩ β) = c₁ ∩ i_*β`,

the cap product on `D` being formed at the transported rule
`AlgebraicGeometry.Space.closedSubspaceChernRule`.  And `i_*[D]_{n-1} = div_ℒ(σ)`, which is
`cycleGroupClosedPushforward_vanishingLocusTopCycle_eq_canonicalDivisorCycleAt`. Together:

**`i_*(c₁(𝒩) ∩ [D]_{n-1}) = c₁(𝒩) ∩ div_ℒ(σ)`** in `Z_k(X)`, with nothing assumed.

The right-hand side is exactly the left-hand side of the first cycle identity of Section 0EQU,
which presents it as `∑_i ord_{B_i}(f_i) (Z_i → X)_* div_{𝒩|_{Z_i}}(t_i|_{Z_i})`.  This is the
second display of step 3 of the proof of Stacks 0ER9, carried to `X`.

## Main definitions

* `AlgebraicGeometry.Space.vanishingLocusTopCycleAt`: the cycle `[D]_{n-1}` of Stacks 0EE9 formed
  on `D`, graded `k + 1` rather than `n - 1`, which is the grading the cap product of Stacks 0EQJ
  into `Z_k` demands of its argument.

## Main results

* `AlgebraicGeometry.Space.cycleGroupClosedPushforward_vanishingLocusTopCycleAt`: `i_*[D]_{n-1} =
  div_ℒ(σ)` at that grading.
* `cycleGroupClosedPushforward_firstChernCapCycleMap_vanishingLocusTopCycleAt`:
  **`i_*(c₁(𝒩) ∩ [D]_{n-1}) = c₁(𝒩) ∩ div_ℒ(σ)`**.

## References

* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
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
    (hL : IsInvertibleSheaf D sX hX L)

/-- **The cycle `[D]_{n-1}` of Stacks 0EE9 on `D = Z(σ)`, graded `k + 1`.**  Same coefficient
family as `AlgebraicGeometry.Space.vanishingLocusTopCycle`; the two gradings `(k + 1 + 1) - 1`
and `k + 1` are equal but not syntactically so, and the cap product of Stacks 0EQJ into `Z_k`
needs the second. -/
def vanishingLocusTopCycleAt {σ : L.sections} (hσ : σ ≠ 0) {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt)) :
    CycleGroup D ((vanishingLocus D sX hX L σ).1.ι ≫ sX) (k + 1) :=
  ⟨(vanishingLocusTopCycle D sX hX hint L hL hσ hn).1, by
    simpa only [add_sub_cancel_right] using (vanishingLocusTopCycle D sX hX hint L hL hσ hn).2⟩

/-- **`i_*[D]_{n-1} = div_ℒ(σ)` at the grading of Stacks 0EQJ.**  The pushforward along
`i : D → X` of `AlgebraicGeometry.Space.vanishingLocusTopCycleAt` is the Weil divisor of
Stacks 0EQE of the meromorphic section of `σ`, in the spelling of Section 0EQU. -/
theorem cycleGroupClosedPushforward_vanishingLocusTopCycleAt {σ : L.sections} (hσ : σ ≠ 0) {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt)) :
    cycleGroupClosedPushforward D hX.1 (vanishingLocus D sX hX L σ).2.1
        (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L σ).2.2 sX hX.2.2
        ((vanishingLocus D sX hX L σ).1.ι ≫ sX) rfl (k + 1)
        (vanishingLocusTopCycleAt D sX hX hint L hL hσ hn) =
      canonicalDivisorCycleAt D sX hX hint L hL
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ)
        (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
          (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ)) hn :=
  Subtype.ext
    (cycleGroupClosedPushforward_vanishingLocusTopCycle_eq_canonicalDivisorCycleAt D sX hX hint L
      hL hσ hn)

/-- **`i_*(c₁(𝒩) ∩ [D]_{n-1}) = c₁(𝒩) ∩ div_ℒ(σ)` in `Z_k(X)`, with nothing assumed.**  In
Situation 0EDT let `X/B` be good and integral of δ-dimension `k + 2`, let `ℒ` be invertible with
a nonzero global section `σ`, let `i : D = Z(σ) → X` be the vanishing locus and let `chern` be a
component rule of Stacks 0EQJ on `X`.  Then the cap product of Stacks 0EQJ formed on `D` at the
transported rule `AlgebraicGeometry.Space.closedSubspaceChernRule`, applied to `[D]_{n-1}` and
pushed forward to `X`, is the cap product formed on `X` applied to `div_ℒ(σ)`.

This is Stacks 0EQT along `i` (`cycleGroupClosedPushforward_firstChernCapCycleMap`) composed
with `i_*[D]_{n-1} = div_ℒ(σ)`.  It puts the right-hand side of Stacks 0ER9 on `X`, where the
key formula of Stacks 0EQV lives and where Section 0EQU presents it as
`∑_i ord_{B_i}(f_i) (Z_i → X)_* div_{𝒩|_{Z_i}}(t_i|_{Z_i})`. -/
theorem cycleGroupClosedPushforward_firstChernCapCycleMap_vanishingLocusTopCycleAt
    {σ : L.sections} (hσ : σ ≠ 0) {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (chern : FirstChernComponentCycleRule D sX k) :
    cycleGroupClosedPushforward D hX.1 (vanishingLocus D sX hX L σ).2.1
        (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L σ).2.2 sX hX.2.2
        ((vanishingLocus D sX hX L σ).1.ι ≫ sX) rfl k
        (firstChernCapCycleMap D ((vanishingLocus D sX hX L σ).1.ι ≫ sX)
          (isGood_ι_of_isClosedSubspace D sX hX (vanishingLocus D sX hX L σ).1
            (vanishingLocus D sX hX L σ).2) k
          (closedSubspaceChernRule D sX hX (vanishingLocus D sX hX L σ).1
            (vanishingLocus D sX hX L σ).2 k chern)
          (vanishingLocusTopCycleAt D sX hX hint L hL hσ hn)) =
      firstChernCapCycleMap D sX hX k chern
        (canonicalDivisorCycleAt D sX hX hint L hL
          (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ)
          (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
            (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ)) hn) := by
  rw [cycleGroupClosedPushforward_firstChernCapCycleMap D sX hX (vanishingLocus D sX hX L σ).1
      (vanishingLocus D sX hX L σ).2 k chern (vanishingLocusTopCycleAt D sX hX hint L hL hσ hn),
    cycleGroupClosedPushforward_vanishingLocusTopCycleAt D sX hX hint L hL hσ hn]

end AlgebraicGeometry.Space

end

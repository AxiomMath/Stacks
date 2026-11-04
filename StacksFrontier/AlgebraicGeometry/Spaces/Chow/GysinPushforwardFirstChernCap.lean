module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusCanonicalDivisorCycle

/-!
# The pushforward of the refined Gysin map is a cap product of Stacks 0EQJ

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module with a global section
`σ` and let `i : D = Z(σ) → X` be the closed immersion of the vanishing locus of Stacks 0845.
Stacks 0ER1 defines the refined Gysin map `i^* : Z_{k+1}(X) ⟶ Z_k(D)` by the dichotomy "`[D ∩ W]_k`
if `W ⊄ D`, `i'_*(c₁(ℒ|_W) ∩ [W])` if `W ⊆ D`", the second clause being the free component rule
`chern` of Stacks 0EQJ that Definition 0ER1 takes it to be in this library.

`AlgebraicGeometry.Space.cycleClosedPushforward_gysinCycleMap_eq_finsum` computes the pushforward
`i_*(i^* α)` as the weighted sum `∑_W α(W) (W → X)_* c_W` and
`AlgebraicGeometry.Space.gysinPushforwardComponentCoeff_of_not_le_eq_sectionWeilDivisor`
identifies `c_W` for `W ⊄ D` with the Weil divisor `div_{ℒ|_W}(σ|_W)` of Stacks 0EQE — which is
Lemma 82.17.2 (Stacks 0EQF) for the triple `(W, ℒ|_W, σ|_W)`.  That is *exactly* the shape of the
cap product of Stacks 0EQJ, so:

**`i_*(i^* α) = c₁ ∩ α` in `Z_k(X)`**, the cap product being the one of Stacks 0EQJ at the
component rule which is `div_{ℒ|_W}(σ|_W)` off `D` and the given `chern` on `D`.

This file builds that rule and proves the identity, with nothing assumed.  It is the first
display of step 3 of the proof of Stacks 0ER9 — "`i^*div_𝒩(t) = ∑ ord_{B_i}(g_i)
div_{ℒ|_{Z_i}}(s_i|_{Z_i})`" — at the level of cycles on `X`, before Section 0EQU reindexes the
sum over the chosen family of prime divisors: the source's choice "`s_i = s` if `Z_i ⊄ D`" is what
makes the rule off `D` the restricted global section, and that choice is forced here rather than
made.

## Main definitions

* `AlgebraicGeometry.Space.restrictedSectionChernRule`: the component rule of Stacks 0EQJ whose
  value at an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` is the Weil divisor
  `div_{ℒ|_W}(σ|_W)` of the restriction of `σ` when `W ⊄ D`, and `chern W` when `W ⊆ D`.

## Main results

* `AlgebraicGeometry.Space.gysinPushforwardComponentCoeff_eq_firstChernComponentCycle`: the
  component of the pushed-forward Gysin map at `W` is the component cycle of that rule at `W`.
* `AlgebraicGeometry.Space.cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap`:
  **`i_*(i^* α) = c₁ ∩ α`** in `Z_k(X)`, with nothing assumed.

## Implementation notes

The off-`D` branch of the rule is phrased at
`AlgebraicGeometry.Space.canonicalDivisorCycleAt` rather than at
`AlgebraicGeometry.Space.sectionWeilDivisor` because a component rule of Stacks 0EQJ is graded
`k` while Stacks 0EQE is graded `n - 1`; the two have the same coefficient family, which is
`AlgebraicGeometry.Space.sectionWeilDivisor_eq_canonicalDivisorCycleAt`.

## References

* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)
    (chern : FirstChernComponentCycleRule D p k)

/-- **The component rule of Stacks 0EQJ given by restricting the global section.**  At an integral
closed subspace `W ⊆ X` of δ-dimension `k + 1` not contained in `D = Z(σ)` the value is the Weil
divisor `div_{ℒ|_W}(σ|_W)` of Stacks 0EQE part (1) of the restriction of `σ` to `W`, which is a
regular meromorphic section of `ℒ|_W` because `σ|_W ≠ 0`
(`AlgebraicGeometry.Space.closedSubspaceRestrictSection_ne_zero`); at a `W ⊆ D` it is the given
rule `chern`, which is the free parameter clause (1)(b) of Definition 0ER1 leaves open.

This is the source's choice "`s_i = s` whenever `Z_i ⊄ D`" of Section 0EQU, made once and for
all rather than member by member. -/
def restrictedSectionChernRule : FirstChernComponentCycleRule D p k := fun W hW =>
  if hWE : W.subspace ≤ (vanishingLocus D p hp L s).1 then chern W hW
  else
    canonicalDivisorCycleAt D (W.subspace.ι ≫ p)
      (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩) W.isIntegralSpace
      (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
      (isInvertible_closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩ hL)
      (globalSectionMeromorphic D.site D.base D.base_mem W.isClosedSubspace.1
        (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
        (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩))
      (isRegularMeromorphicSection_of_ne_zero_of_isGood D (W.subspace.ι ≫ p)
        (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩) W.isIntegralSpace
        (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
        (isInvertible_closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩ hL)
        (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D (W.subspace.ι ≫ p)
          (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
          (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
          (isInvertible_closedSubspaceRestrictSheaf D p hp L
            ⟨W.subspace, W.isClosedSubspace⟩ hL)
          (closedSubspaceRestrictSection_ne_zero D p hp L s hL
            ⟨W.subspace, W.isClosedSubspace⟩ hWE)))
      ((deltaDimensionClosed_univ_integralClosedSubspace D p hp W).trans
        (congrArg (fun m : ℤ => (m : EInt)) hW))

/-- On `W ⊆ D` the rule is the given one. -/
theorem restrictedSectionChernRule_of_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1) :
    restrictedSectionChernRule D p hp L s hL k chern W hW = chern W hW := by
  rw [restrictedSectionChernRule, dif_pos hWE]

/-- On `W ⊄ D` the rule is the Weil divisor of the restricted global section, whose coefficient
family is that of `AlgebraicGeometry.Space.sectionWeilDivisor` on `W`. -/
theorem restrictedSectionChernRule_of_not_le_coe
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    (restrictedSectionChernRule D p hp L s hL k chern W hW).1 =
      (sectionWeilDivisor D (W.subspace.ι ≫ p)
        (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩) W.isIntegralSpace
        (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
        (isInvertible_closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩ hL)
        ((deltaDimensionClosed_univ_integralClosedSubspace D p hp W).trans
          (congrArg (fun m : ℤ => (m : EInt)) hW))
        (globalSectionMeromorphic D.site D.base D.base_mem W.isClosedSubspace.1
          (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
          (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩))
        (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D (W.subspace.ι ≫ p)
          (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
          (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
          (isInvertible_closedSubspaceRestrictSheaf D p hp L
            ⟨W.subspace, W.isClosedSubspace⟩ hL)
          (closedSubspaceRestrictSection_ne_zero D p hp L s hL
            ⟨W.subspace, W.isClosedSubspace⟩ hWE))).1 := by
  rw [restrictedSectionChernRule, dif_neg hWE]
  exact (sectionWeilDivisor_eq_canonicalDivisorCycleAt D (W.subspace.ι ≫ p) _
    W.isIntegralSpace _ _ _ _ _ _).symm

/-- **The component of the pushed-forward Gysin map is the component cycle of the rule.**  For
every integral closed subspace `W ⊆ X` the coefficient family
`AlgebraicGeometry.Space.gysinPushforwardComponentCoeff` of `(W → X)_* c_W` is the one of the
component cycle of Stacks 0EQJ at `AlgebraicGeometry.Space.restrictedSectionChernRule`.

At a `W` of δ-dimension other than `k + 1` both are zero.  At a `W ⊆ D` both are the pushforward
of `chern W`.  At a `W ⊄ D` the Gysin component is the pushforward of the Weil divisor
`div_{ℒ|_W}(σ|_W)`, by Stacks 0EQF for `(W, ℒ|_W, σ|_W)`
(`AlgebraicGeometry.Space.gysinPushforwardComponentCoeff_of_not_le_eq_sectionWeilDivisor`), and
that is the value of the rule there. -/
theorem gysinPushforwardComponentCoeff_eq_firstChernComponentCycle
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    gysinPushforwardComponentCoeff D p hp L s k chern W =
      (firstChernComponentCycle D p hp k
        (restrictedSectionChernRule D p hp L s hL k chern) W).1 := by
  by_cases hW : deltaDimension D p W = k + 1
  · rw [firstChernComponentCycle_of_deltaDimension_eq D p hp k _ hW]
    by_cases hWE : W.subspace ≤ (vanishingLocus D p hp L s).1
    · rw [gysinPushforwardComponentCoeff_of_le D p hp L s k chern hW hWE,
        restrictedSectionChernRule_of_le D p hp L s hL k chern hW hWE]
    · rw [gysinPushforwardComponentCoeff_of_not_le_eq_sectionWeilDivisor D p hp L s k chern hL
          hW hWE,
        show (integralClosedSubspacePushforward D p hp W k
              (restrictedSectionChernRule D p hp L s hL k chern W hW)).1 =
            cycleClosedPushforward D hp.1 W.isClosedSubspace.1
              (D.isDecentSpace_of_isGood p hp) W.isClosedSubspace.2
              (restrictedSectionChernRule D p hp L s hL k chern W hW).1 from rfl,
        restrictedSectionChernRule_of_not_le_coe D p hp L s hL k chern hW hWE]
  · rw [gysinPushforwardComponentCoeff_of_deltaDimension_ne D p hp L s k chern hW,
      firstChernComponentCycle_of_deltaDimension_ne D p hp k _ hW]
    rfl

/-- **The pushforward of the refined Gysin map of Stacks 0ER1 is a cap product of Stacks 0EQJ.**
In Situation 0EDT let `X/B` be good, let `ℒ` be invertible with a global section `σ` and let
`i : D = Z(σ) → X` be the vanishing locus.  For every `(k+1)`-cycle `α` on `X`,

`i_*(i^* α) = c₁ ∩ α`  in  `Z_k(X)`,

the cap product being the one of Stacks 0EQJ at
`AlgebraicGeometry.Space.restrictedSectionChernRule` — the component rule which is the Weil
divisor `div_{ℒ|_W}(σ|_W)` of the restricted global section at every `W ⊄ D` and the free rule
`chern` of Definition 0ER1 clause (1)(b) at every `W ⊆ D`.  Nothing is assumed.

This is the first display of step 3 of the proof of Stacks 0ER9, at the level of cycles on `X`:
with `α = div_𝒩(t)` the left-hand side is the pushforward of `i^*div_𝒩(t)` and the right-hand
side is the cycle Section 0EQU presents as
`∑_i ord_{B_i}(g_i) (Z_i → X)_* div_{ℒ|_{Z_i}}(s_i|_{Z_i})` for the source's choice `s_i = σ` at
the members `Z_i ⊄ D`.  Both sides are coefficientwise weighted sums over the integral closed
subspaces of `X` — the left by
`AlgebraicGeometry.Space.cycleClosedPushforward_gysinCycleMap_eq_finsum`, the right by the
definition of the cap product — with the same terms, by
`AlgebraicGeometry.Space.gysinPushforwardComponentCoeff_eq_firstChernComponentCycle`. -/
theorem cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap
    (α : CycleGroup D p (k + 1)) :
    cycleGroupClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
        (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2 p hp.2.2
        ((vanishingLocus D p hp L s).1.ι ≫ p) rfl k
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
            (isGood_vanishingLocus D p hp L s) k chern) α) =
      firstChernCapCycleMap D p hp k (restrictedSectionChernRule D p hp L s hL k chern) α := by
  refine Subtype.ext (funext fun V => ?_)
  show cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
      (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2
      (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
        (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k chern) α).1 V = _
  rw [cycleClosedPushforward_gysinCycleMap_eq_finsum D p hp L s k chern α V,
    firstChernCapCycleMap_apply]
  exact finsum_congr fun W => by
    rw [gysinPushforwardComponentCoeff_eq_firstChernComponentCycle D p hp L s hL k chern W]

end AlgebraicGeometry.Space

end

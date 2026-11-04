module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardRationalEquivalence

/-!
# Stacks 0EQT: proper pushforward and intersecting with an invertible sheaf, on Chow groups

In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be a proper morphism over `B`,
let `ℒ` be an invertible `𝒪_Y`-module and let `α ∈ Z_{k+1}(X)`. Stacks 0EQT is the projection
formula

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`   in `CH_k(Y)`.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapCanonical` proves it
granted that proper pushforward respects rational equivalence; that is Stacks 0EQC
(`AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_properCyclePushforward`), and
this file discharges it.

## Main results

* `AlgebraicGeometry.Space.chowGroupCanonicalProperPushforward_canonicalFirstChernCapCanonical`:
  **Stacks 0EQT**.
* `AlgebraicGeometry.Space.chowClassCanonical_properCyclePushforward_firstChernCapCycleMap`: the
  same, read on cycle representatives.

## References

* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Projection

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    (q : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (hqB : q.hom ≫ sY = sX) (hq : IsProper D.site D.base D.base_mem q.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) (k : ℤ)

/-- **Stacks 0EQT, on cycle representatives.** For every `α ∈ Z_{k+1}(X)` the class in
`CH_k(Y)` of the proper pushforward of the cycle `c₁(p^*ℒ) ∩ α` of Stacks 0EQJ is
`c₁(ℒ) ∩ p_*α`.

The cap product with the canonical rule at `p^*ℒ` and the one with the rule of the pulled-back
sections are rationally equivalent on `X`
(`AlgebraicGeometry.Space.chowClassCanonical_firstChernCapCycleMap_chernPulledRule`), proper
pushforward respects rational equivalence (Stacks 0EQC,
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_properCyclePushforward`), and for
the second rule the formula holds on cycles
(`AlgebraicGeometry.Space.properCyclePushforward_firstChernCapCycleMap_chernPulledRule`). -/
theorem chowClassCanonical_properCyclePushforward_firstChernCapCycleMap
    (α : CycleGroup D sX (k + 1)) :
    chowClassCanonical.{u + 1} D sY hY k
        (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 k
          (firstChernCapCycleMap D sX hX k
            (canonicalFirstChernRule D sX hX ((modulePullback D.site D.base D.base_mem q).obj L)
              (modulePullbackInvertible q L hL) k) α)) =
      canonicalFirstChernCapCanonical.{u + 1} D sY hY L hL k
        (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 (k + 1) α) :=
  chowClassCanonical_properPushforward_canonicalFirstChernCap_of_component D hX hY q hqB hq L hL k
    (fun β h => isRationallyEquivalentToZeroCanonical_properCyclePushforward D sX hX sY hY hqB hq k
      β h) α

/-- **Stacks 0EQT.** In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be a proper
morphism over `B`, let `α ∈ Z_{k+1}(X)` and let `ℒ` be an invertible `𝒪_Y`-module. Then

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`   in `CH_k(Y)`.

Every object is the constructed one, nothing is a parameter:

* `p^*ℒ` is the inverse image `(modulePullback p).obj ℒ` of Stacks 03LU, invertible by Stacks
  0B8P (`AlgebraicGeometry.Space.modulePullbackInvertible`);
* `c₁(-) ∩ -` is the cap product of Stacks 0EQJ, `Z_{k+1} → CH_k`, at the canonical component
  rule (`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical`), on `X` for `p^*ℒ` and on `Y`
  for `ℒ`;
* on the left `p_*` is proper pushforward on Chow groups, `CH_k(X) → CH_k(Y)`, of Stacks 0EQC
  (`AlgebraicGeometry.Space.chowGroupCanonicalProperPushforward`); on the right it is proper
  pushforward of cycles `Z_{k+1}(X) → Z_{k+1}(Y)` of Stacks 0EP1;
* `CH_k` is the Chow group of Stacks 0EQ6 (`AlgebraicGeometry.Space.chowGroupCanonical`).

The proof is the source's: the formula is reduced to a single integral closed subspace `W` and
its image `W'`, where it is Stacks 0EQS for `W ⟶ W'` when the δ-dimension is preserved; the case
where it drops, which the source passes over, is
`properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop`. -/
@[stacks 0EQT]
theorem chowGroupCanonicalProperPushforward_canonicalFirstChernCapCanonical
    (α : CycleGroup D sX (k + 1)) :
    chowGroupCanonicalProperPushforward.{u + 1} D sX hX sY hY hqB hq k
        (canonicalFirstChernCapCanonical.{u + 1} D sX hX
          ((modulePullback D.site D.base D.base_mem q).obj L) (modulePullbackInvertible q L hL) k
          α) =
      canonicalFirstChernCapCanonical.{u + 1} D sY hY L hL k
        (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 (k + 1) α) :=
  chowClassCanonical_properCyclePushforward_firstChernCapCycleMap D hX hY q hqB hq L hL k α

end Projection

end AlgebraicGeometry.Space

end

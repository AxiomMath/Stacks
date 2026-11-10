module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionWeilDivisorCoefficient

/-!
# Flat pullback of the Weil divisor of a meromorphic section (Stacks 0EQQ)

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be a flat morphism of relative
dimension `r`. Let `ℒ` be an invertible `𝒪_Y`-module, assume `Y` is integral with
`n = dim_δ(Y)`, and let `s` be a nonzero meromorphic section of `ℒ`. **Stacks 0EQQ** is the
identity

  `f^* div_ℒ(s) = ∑ n_i div_{f^*ℒ|_{X_i}}(s_i)`

in `Z_{n + r - 1}(X)`, the sum running over the irreducible components `X_i ⊂ X` of δ-dimension
`n + r`, with `s_i = f|_{X_i}^*(s)` the pullback of `s` and `n_i = m_{X_i, X}` the multiplicity
of `X_i` in `X`.

## The objects

* `f^*` is the flat pullback of cycles of Stacks 0EP8, `AlgebraicGeometry.Space.flatPullbackMap`.
* `div_ℒ(s)` is the Weil divisor of Stacks 0EQE, `AlgebraicGeometry.Space.sectionWeilDivisor`.
* `f^*ℒ|_{X_i}` is the pullback `f|_{X_i}^*ℒ` of `ℒ` along the restriction of `f` to `X_i`
  (`AlgebraicGeometry.Space.componentModule`, the inverse image of Stacks 03LU), which is
  invertible (Stacks 0B8P); `s_i` is the pullback of Stacks 0ENC, part (1), of `s` along `f|_{X_i}`
  (`AlgebraicGeometry.Space.componentSection`), defined because `X_i` dominates `Y`.
* `div_{f^*ℒ|_{X_i}}(s_i)` is Stacks 0EQE on the integral space `X_i`, an `(n + r - 1)`-cycle on
  `X_i` (`AlgebraicGeometry.Space.componentDivisor`), regarded as a cycle on `X` by pushforward
  along the closed immersion `X_i → X`.
* `m_{X_i, X}` is the multiplicity of Stacks 0EE9, part (1), the length of `𝒪_{X, x̄}` at a
  geometric point over the generic point of `X_i` (`AlgebraicGeometry.Space.spaceMultiplicity`).
* The sum is the locally finite sum of Stacks 0EQ6, part (1), over the irreducible components of
  δ-dimension `n + r` (`AlgebraicGeometry.Space.componentDivisorSum`).

## Main results

* `AlgebraicGeometry.Space.flatPullbackMap_sectionWeilDivisor_eq_componentDivisorSum`:
  `f^* div_ℒ(s) = ∑ n_i div_{f^*ℒ|_{X_i}}(s_i)` in `Z_{n + r - 1}(X)`.

## References

* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) {n : ℤ}
    (hn : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (hL : IsInvertibleSheaf D sY hY L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L) (hs : s ≠ 0)

/-- In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be a morphism over `B` which
is flat of relative dimension `r`, let `ℒ` be an invertible `𝒪_Y`-module, assume `Y` is integral
with `n = dim_δ(Y)`, and let `s` be a nonzero meromorphic section of `ℒ`. Then

  `f^* div_ℒ(s) = ∑ n_i div_{f^*ℒ|_{X_i}}(s_i)`

in `Z_{n + r - 1}(X)`: the left-hand side is the flat pullback (Stacks 0EP8) of the Weil divisor
`div_ℒ(s)` (Stacks 0EQE); on the right the sum runs over the irreducible components `X_i ⊂ X`
of δ-dimension `n + r`, `s_i = f|_{X_i}^*(s)` is the pullback of `s` (Stacks 0ENC), a nonzero
meromorphic section of the invertible module `f^*ℒ|_{X_i} = f|_{X_i}^*ℒ`,
`div_{f^*ℒ|_{X_i}}(s_i)` is its Weil divisor on `X_i` pushed forward to `X`, and
`n_i = m_{X_i, X}` is the multiplicity of `X_i` in `X` (Stacks 0EE9). -/
@[stacks 0EQQ]
theorem flatPullbackMap_sectionWeilDivisor_eq_componentDivisorSum :
    flatPullbackMap D sX hX sY hY f hbase r hflat hr (n - 1) (n + r - 1) (by ring)
        (sectionWeilDivisor D sY hY hintY L hL hn s hs) =
      componentDivisorSum D sX hX sY hY f r hflat hintY (n := n) L hL s hs := by
  refine Subtype.ext (funext fun Z => ?_)
  by_cases hZ : deltaDimension D sX Z = n + r - 1
  · obtain ⟨d, u, hU, hV, hu, e, hecompat, hebij⟩ :=
      exists_affine_chartDiagram_generator_through D.site D.base D.base_mem
        (X := ⟨X, hX.1⟩) (Y := ⟨Y, hY.1⟩) (ObjectProperty.homMk f) L hL
        (Z.ambientGenericPoint D.site D.base D.base_mem)
    have hcodim := codimension_integralClosedSubspaceSupport_eq_one_of_isFlat D sX hX sY hY f
      hbase r hflat hr hintY hn Z hZ
    have huP : chartSchemeToPoints D.site D.base D.base_mem X d.U u =
        (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcodim).genericPoint D.site D.base
          D.base_mem X := by
      rw [PrimeDivisor.genericPoint_eq_ambientGenericPoint D hX.1,
        IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor]
      exact hu
    have hdimA : ringKrullDim ((chartScheme d.U).presheaf.stalk u) = 1 :=
      (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcodim).ringKrullDim_chartStalk D.site
        D.base D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) d.U u huP
    have : IsNoetherianRing ((chartScheme d.U).presheaf.stalk u) := by
      have := isLocallyNoetherian_chartScheme D.site D.base D.base_mem
        (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) d.U
      infer_instance
    have : Ring.KrullDimLE 1 ((chartScheme d.U).presheaf.stalk u) :=
      Ring.krullDimLE_iff.mpr (by rw [hdimA]; exact_mod_cast le_rfl)
    exact (flatPullbackMap_sectionWeilDivisor_apply_eq_ordTotalFracInt D sX hX sY hY f hbase r
      hflat hr hintY hn L hL s hs Z hZ d hV e hecompat hebij u hu).trans
      (componentDivisorSum_apply_eq_ordTotalFracInt D sX hX sY hY f hbase r hflat hr hintY hn L
        hL s hs Z hZ d hU hV e hecompat hebij u hu hdimA).symm
  · have key (k : ℤ) (c : CycleGroup D sX k) (hZ : deltaDimension D sX Z ≠ k) : c.1 Z = 0 :=
      by_contra fun h => hZ (c.2.2 Z h)
    rw [key _ _ hZ, key _ _ hZ]

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernClassOfRankOne

/-!
# The Segre operations of an invertible module

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module, with projective
bundle `(π : P = 𝐏(ℒ) ⟶ X, 𝒪_P(1))` of relative dimension `0`. The tautological surjection
`π^*ℒ ⟶ 𝒪_P(1)` is an isomorphism, so `c₁(𝒪_P(1)) ∩ π^*α = c₁(π^*ℒ) ∩ π^*α = π^*(c₁(ℒ) ∩ α)`
(Stacks 0EQR), and the Segre operations `t_i(ℒ) ∩ α = π_*(c₁(𝒪_P(1))^i ∩ π^*α)` satisfy

  `t_{n+1}(ℒ) = t_n(ℒ) ∘ (c₁(ℒ) ∩ -)`   on `CH_*(X)`.

This is the case `ℱ = 0` of the relation `t_{n+1}(ℰ) = t_{n+1}(ℱ) + t_n(ℰ) ∘ (c₁(ℒ) ∩ -)` for
`0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0`, from which Stacks 0ES8 follows.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.segreCapOfModule_succ_of_isInvertibleModule`:
  `t_{n+1}(ℒ) = t_n(ℒ) ∘ (c₁(ℒ) ∩ -)`.

## References

* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] modulesMonoidalCategory

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **The Segre operations of an invertible module**: `t_{n+1}(ℒ) = t_n(ℒ) ∘ (c₁(ℒ) ∩ -)` on
`CH_*(X)`, the twist of `𝐏(ℒ)` being the pullback of `ℒ`. -/
theorem segreCapOfModule_succ_of_isInvertibleModule
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (h : IsFiniteLocallyFreeOfRank D sX hX L 1)
    (hL : IsInvertibleModule (goodSpace hX) L) (n : ℕ) :
    segreCapOfModule.{u, u + 1} L 1 h (n + 1) =
      (segreCapOfModule.{u, u + 1} L 1 h n).comp (firstChernCapChow.{u, u + 1} D sX hX L hL) := by
  let := isQuasicoherentOnSite_of_rank L h
  have hfree := isFiniteLocallyFreeOnSite_of_rank L h
  let P := projectiveBundleDatum L 0 h
  have hπL := modulePullbackInvertible
    (ObjectProperty.homMk P.proj : (⟨P.space, P.isGood.1⟩ : AlgebraicSpaces D.site D.base
      D.base_mem) ⟶ ⟨X, hX.1⟩) L hL
  have := isIso_projectiveBundleTautological (Z := goodSpace hX) L hfree hL
  have e : P.twist ≅ (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk P.proj : (⟨P.space, P.isGood.1⟩ : AlgebraicSpaces D.site D.base
        D.base_mem) ⟶ ⟨X, hX.1⟩)).obj L :=
    (asIso (projectiveBundleTautological (X := goodSpace hX) L hfree).hom).symm
  have e1 : P.twistCap = firstChernCapChow.{u, u + 1} D P.toBase P.isGood
      (pullbackLine D P.toBase P.isGood sX hX P.proj L) hπL :=
    firstChernCapChow_congr_iso D P.toBase P.isGood _ _ _ hπL e
  change P.segreCap (n + 1) = (P.segreCap n).comp (firstChernCapChow.{u, u + 1} D sX hX L hL)
  refine AddMonoidHom.ext fun α => ?_
  have e2 := flatPullbackChow_firstChernCapChow D P.toBase P.isGood sX hX P.proj P.proj_comp 0
    P.isFlat P.hasRelativeDimension L hL α
  change P.pushforwardChow ((P.twistCap ^ (0 + (n + 1))) (P.pullbackChow α)) =
    P.pushforwardChow ((P.twistCap ^ (0 + n))
      (P.pullbackChow (firstChernCapChow.{u, u + 1} D sX hX L hL α)))
  rw [show 0 + (n + 1) = 0 + n + 1 by omega, pow_succ]
  change P.pushforwardChow ((P.twistCap ^ (0 + n)) (P.twistCap (P.pullbackChow α))) = _
  rw [e1]
  exact congrArg _ (congrArg _ e2.symm)

end AlgebraicGeometry.Space.PrivateChern

end

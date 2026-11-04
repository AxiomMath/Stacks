module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.CompletionCriterion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.CompletionReduction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LiftFromHypersurfaceComplete
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.DenseOpenGenericPoint
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# Lifting a finite étale cover from the hypersurface section in depth at least three

Work in the local Lefschetz situation of Tag 0BLF: `A` is a Noetherian local ring with maximal
ideal `𝔪`, `f ∈ 𝔪`, `X = Spec A`, `X₀ = Spec (A / fA)`, and `U`, `U₀` are the punctured spectra
of `A` and of `A / fA`. If `A` has depth at least `3`, a finite étale `V ⟶ U` whose restriction
`V ×_U U₀` comes from a finite étale `Y₀ ⟶ X₀` comes from a finite étale `Y ⟶ X`. This is
[Stacks, Tag 0BLM], with no further hypothesis.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_lift_of_three_le_depth` —
  **[Stacks, Tag 0BLM]**.

## Implementation notes

The source deduces Tag 0BLM from Tag 0BLS, which it proves by reduction to the complete case
through Tag 0BLL. Here the reduction is made for Tag 0BLM directly, by
`AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicCompleteCase`
(Tag 0BLL) for the predicate "depth at least `3`": the `𝔪`-adic completion `Â` of `A`
(`AlgebraicGeometry.LocalLefschetzSituation.completion`) is `f`-adically complete and has the
depth of `A` (Tag 07NW), so the complete case
`…LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicComplete_of_three_le_depth`
applies to it.

## References

* [Stacks Project, Tag 0BLM](https://stacks.math.columbia.edu/tag/0BLM)
* [Stacks Project, Tag 0BLL](https://stacks.math.columbia.edu/tag/0BLL)
* [Stacks Project, Tag 0BLS](https://stacks.math.columbia.edu/tag/0BLS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

namespace LocalLefschetzSituation

variable (S : LocalLefschetzSituation.{u})

/-- **[Stacks, Tag 0BLM]** In the local Lefschetz situation let `V` be finite étale over `U`
and assume (1) `A` has depth at least `3`, and (2) `V ×_U U₀` is `Y₀ ×_{X₀} U₀` for some
`Y₀ → X₀` finite étale. Then `V = Y ×_X U` for some `Y → X` finite étale.

The reduction to the complete case is by Tag 0BLL, as in the source's proof of Tag 0BLS
(`AlgebraicGeometry.LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicCompleteCase`):
the completion `Â` has the same depth (Tag 07NW) and is `f`-adically complete, and the base change
of `Y₀` to `Spec (Â / fÂ)` witnesses hypothesis (2) for the base change of `V`. -/
@[stacks 0BLM]
theorem exists_finiteEtale_lift_of_three_le_depth
    (hdepth : 3 ≤ Module.depth S.A (maximalIdeal S.A) S.A)
    (V : Scheme.{u}) (pi : V ⟶ S.U) [IsFinite pi] [Etale pi]
    (Y₀ : Scheme.{u}) (f₀ : Y₀ ⟶ S.X₀) [IsFinite f₀] [Etale f₀]
    (g₀ : pullback pi S.U₀ToU ⟶ Y₀)
    (h₀ : IsPullback (pullback.snd pi S.U₀ToU) g₀ S.U₀Open.ι f₀) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S.X) (g : V ⟶ Y),
      IsFinite p ∧ Etale p ∧ IsPullback pi g S.UOpen.ι p := by
  refine S.exists_finiteEtale_extension_of_isAdicCompleteCase
    (fun T => 3 ≤ Module.depth T.A (maximalIdeal T.A) T.A) hdepth
    (fun h => h.trans_eq (depth_adicCompletion_maximalIdeal (A := S.A))) ?_ V pi Y₀ f₀ g₀ h₀
  intro T hT hTd W p hp hp' Z₀ q₀ hq hq' e₀ he₀
  exact T.exists_finiteEtale_extension_of_isAdicComplete_of_three_le_depth hTd hT W p Z₀ q₀ e₀ he₀

end LocalLefschetzSituation

end AlgebraicGeometry

end

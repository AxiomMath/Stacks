module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffineModels

/-!
# Base change of a descent situation along a quasi-compact quasi-separated algebraic space

A descent situation is a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, together with a chosen limit
`X` and a chosen index `0`. Its base change along a morphism `u : T ⟶ Y` from a quasi-compact
quasi-separated algebraic space `T` to a quasi-separated algebraic space `Y` — the stages
`X_i ×_Y T` and the limit `X ×_Y T` — is again a descent situation.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.baseChangeAlong`: the descent situation base changed
  along `u : T ⟶ Y`, for `T` a quasi-compact quasi-separated algebraic space and `Y` a
  quasi-separated algebraic space the system maps to.
* `AlgebraicGeometry.Space.DescentSituation.stagesBaseChangeAlong`: the descent situation
  restricted to its stages and base changed along `u : T ⟶ X_0`; its stages are the
  `T ×_{X_0} X_i` and its limit is `T ×_{X_0} X`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.baseChangeAlong_system_obj`: the stages of the base
  change are the fibre products `X_i ×_Y T`.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeAlong_limitCone_pt`: the limit of the base
  change is `X ×_Y T`.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeAlong_base`: the base change keeps the
  chosen index.

## References

* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.8.3 (Tag 073B)](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u})) {T Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
  (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
  (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (g : D.limitCone.pt ⟶ Y)
  (hg : ∀ j, D.limitCone.π.app j ≫ t.app j = g)
  (hT : IsAlgebraicSpace B S hS T) (hTqc : IsQuasiCompactSpace B S hS T)
  (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T) (u : T ⟶ Y)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks in this presheaf category exceeds the default limit
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_DescentSituationBaseChangeSpace :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_DescentSituationBaseChangeSpace
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A descent situation base changed along a quasi-compact quasi-separated algebraic space
over `Y`.** If the stages of the situation map compatibly to a quasi-separated algebraic space
`Y`, and `u : T ⟶ Y` has quasi-compact quasi-separated algebraic-space source, then the base
changes `X_i ×_Y T`, with limit `X ×_Y T`, again form a descent situation. -/
def DescentSituation.baseChangeAlong : DescentSituation B S hS hZ I :=
  haveI : Nonempty I := ⟨D.base⟩
  { system := baseChangeOverSystem B S hS D.system t u
    algebraicSpace := fun i ↦
      isAlgebraicSpace_pullback B S hS (t.app (op i)) u (D.algebraicSpace i) hT hY
    transition_affine := fun {i j} φ ↦
      isAffineHom_of_isPullback
        (isPullback_baseChangeOverMap B S hS (t.app i) (t.app j) (D.system.map φ)
          (by simp) u).flip (D.transition_affine φ)
    quasiCompact := fun i ↦
      isQuasiCompactSpace_pullback B S hS hZ (t.app (op i)) u (D.algebraicSpace i) hY
        (D.quasiCompact i) hTqc hYqs
    quasiSeparated := fun i ↦
      isAbsolutelyQuasiSeparated_pullback B S hS hZ (t.app (op i)) u (D.algebraicSpace i)
        hT hY (D.quasiSeparated i) hTqs
    limitCone := baseChangeOverCone B S hS D.system t u D.limitCone g hg
    isLimit := isLimit_baseChangeOverCone B S hS D.system t u D.limitCone g hg D.isLimit
    limitAlgebraicSpace := isAlgebraicSpace_pullback B S hS g u D.limitAlgebraicSpace hT hY
    base := D.base }

/-- Each stage of the base change is the fibre product of the corresponding stage with `T` over
`Y`. -/
theorem DescentSituation.baseChangeAlong_system_obj (j : Iᵒᵖ) :
    (D.baseChangeAlong B S hS hZ hY hYqs t g hg hT hTqc hTqs u).system.obj j =
      pullback (t.app j) u := rfl

/-- The limit of the base change is the base change of the limit. -/
theorem DescentSituation.baseChangeAlong_limitCone_pt :
    (D.baseChangeAlong B S hS hZ hY hYqs t g hg hT hTqc hTqs u).limitCone.pt =
      pullback g u := rfl

/-- The base change keeps the chosen index. -/
theorem DescentSituation.baseChangeAlong_base :
    (D.baseChangeAlong B S hS hZ hY hYqs t g hg hT hTqc hTqs u).base = D.base := rfl

/-! ### Base change along a quasi-compact quasi-separated algebraic space over the chosen stage -/

section Stages

variable {B S hS hZ} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A descent situation restricted to its stages and base changed along a quasi-compact
quasi-separated algebraic space `u : T ⟶ X_0` over its chosen stage.** Its stages are the
`T ×_{X_0} X_i` and its limit is `T ×_{X_0} X`. -/
abbrev DescentSituation.stagesBaseChangeAlong (hT : IsAlgebraicSpace B S hS T)
    (hTqc : IsQuasiCompactSpace B S hS T) (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T)
    (u : T ⟶ (stagesSystem D).obj (op (baseStage D))) :
    DescentSituation B S hS hZ D.Stages :=
  (stagesSituation D).baseChangeAlong B S hS hZ (D.algebraicSpace D.base)
    (D.quasiSeparated D.base) (stagesToBase D) ((stagesCone D).π.app (op (baseStage D)))
    (stagesCone_π_comp D) hT hTqc hTqs u

end Stages

end AlgebraicGeometry.Space

end

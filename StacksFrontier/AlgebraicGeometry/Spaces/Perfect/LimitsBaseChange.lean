module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationBaseChangeSpace

/-!
# Restricting Situation 09RH to an étale object of the base stage

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms, a limit `X` and a chosen index `0` — the proofs
of Stacks 09RI and 09RJ run the induction principle of Stacks 08GP over the quasi-compact and
quasi-separated objects `U₀` of `(X₀)_{spaces,étale}`, applying the statement to the system

`U_i = X_i ×_{X₀} U₀` (`i ≥ 0`), with limit `U = X ×_{X₀} U₀`.

This file constructs that system as a descent situation.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.laterStages`: the same situation indexed by the stages
  `i ≥ 0` only; its limit is the same limit, the inclusion of the later stages being cofinal.
* `AlgebraicGeometry.Space.DescentSituation.laterStagesToBaseStage`: the transition morphisms
  `X_i ⟶ X₀`, `i ≥ 0`, as a natural transformation to the constant system.
* `AlgebraicGeometry.Space.DescentSituation.restrictTo`: **the situation `U_i = X_i ×_{X₀} U₀`**,
  for `U₀` a quasi-compact quasi-separated algebraic space over `X₀`, the base change
  `AlgebraicGeometry.Space.DescentSituation.baseChangeAlong` of the later stages along
  `U₀ ⟶ X₀`.

## References

* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- The stages at or beyond the chosen index are directed. -/
instance isDirected_laterStages : IsDirected {i : I // D.base ≤ i} (· ≤ ·) where
  directed i j := by
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩

/-- The inclusion of the stages at or beyond the chosen index, as a functor. -/
abbrev laterStagesInclusion : {i : I // D.base ≤ i} ⥤ I :=
  (Subtype.mono_coe (fun i : I => D.base ≤ i)).functor

/-- The inclusion of the later stages is cofinal. -/
instance final_laterStagesInclusion : (laterStagesInclusion D).Final :=
  (Monotone.final_functor_iff _).2 fun i => by
    obtain ⟨k, hik, hbk⟩ := directed_of (· ≤ ·) i D.base
    exact ⟨⟨k, hbk⟩, hik⟩

/-- **Situation 09RH indexed by the later stages.**  The system restricted to the stages `i ≥ 0`,
with the same limit: the inclusion of the later stages is cofinal, so the restricted cone is
still limiting. -/
def laterStages : DescentSituation B S hS hZ {i : I // D.base ≤ i} where
  system := (laterStagesInclusion D).op ⋙ D.system
  algebraicSpace i := D.algebraicSpace i.1
  transition_affine _ := D.transition_affine _
  quasiCompact i := D.quasiCompact i.1
  quasiSeparated i := D.quasiSeparated i.1
  limitCone := D.limitCone.whisker (laterStagesInclusion D).op
  isLimit := (Functor.Initial.isLimitWhiskerEquiv (laterStagesInclusion D).op D.limitCone).symm
    D.isLimit
  limitAlgebraicSpace := D.limitAlgebraicSpace
  base := ⟨D.base, le_rfl⟩

/-- The stage of the later-stage system at `i ≥ 0` is the stage `X_i` of the original system. -/
@[simp]
theorem laterStages_system_obj (i : {i : I // D.base ≤ i}) :
    (laterStages D).system.obj (op i) = D.system.obj (op i.1) := rfl

/-- The limit of the later-stage system is the limit `X` of the original system. -/
@[simp]
theorem laterStages_limitCone_pt : (laterStages D).limitCone.pt = D.limitCone.pt := rfl

/-- The transition morphisms `X_i ⟶ X₀` of the later stages to the chosen one, as a natural
transformation from the system of later stages to the constant system at `X₀`. -/
def laterStagesToBaseStage :
    (laterStages D).system ⟶ (Functor.const _).obj (D.system.obj (op D.base)) where
  app i := D.system.map (homOfLE i.unop.2).op
  naturality {i j} φ := by
    dsimp [laterStages]
    rw [Category.comp_id, ← Functor.map_comp]
    rfl

/-- The projections of the limit composed with the transition morphisms to the chosen stage are
the projection to the chosen stage. -/
theorem limitCone_π_comp_laterStagesToBaseStage (i : {i : I // D.base ≤ i}ᵒᵖ) :
    (laterStages D).limitCone.π.app i ≫ (laterStagesToBaseStage D).app i =
      D.limitCone.π.app (op D.base) :=
  D.limitCone.w (homOfLE i.unop.2).op

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_LimitsBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_LimitsBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAlgebraicSpace B S hS U₀)
  (hU₀qc : IsQuasiCompactSpace B S hS U₀) (hU₀qs : IsAbsolutelyQuasiSeparated B S hS hZ U₀)
  (u : U₀ ⟶ D.system.obj (op D.base))

/-- **The restriction of Situation 09RH to an algebraic space `U₀` over the chosen stage**: the
system `U_i = X_i ×_{X₀} U₀`, `i ≥ 0`, with limit `X ×_{X₀} U₀`, for `U₀` quasi-compact and
quasi-separated.  These are the systems to which the proofs of Stacks 09RI and 09RJ apply the
induction principle of Stacks 08GP. -/
def restrictTo : DescentSituation B S hS hZ {i : I // D.base ≤ i} :=
  (laterStages D).baseChangeAlong B S hS hZ (D.algebraicSpace D.base) (D.quasiSeparated D.base)
    (laterStagesToBaseStage D) (D.limitCone.π.app (op D.base))
    (limitCone_π_comp_laterStagesToBaseStage D) hU₀ hU₀qc hU₀qs u

/-- The stages of the restricted situation are the fibre products `X_i ×_{X₀} U₀`. -/
theorem restrictTo_system_obj (i : {i : I // D.base ≤ i}) :
    (D.restrictTo hU₀ hU₀qc hU₀qs u).system.obj (op i) =
      pullback (D.system.map (homOfLE i.2).op) u := rfl

/-- The limit of the restricted situation is the fibre product `X ×_{X₀} U₀`. -/
theorem restrictTo_limitCone_pt :
    (D.restrictTo hU₀ hU₀qc hU₀qs u).limitCone.pt =
      pullback (D.limitCone.π.app (op D.base)) u := rfl

/-- The chosen index of the restricted situation is the chosen index. -/
theorem restrictTo_base : (D.restrictTo hU₀ hU₀qc hU₀qs u).base = ⟨D.base, le_rfl⟩ := rfl

end AlgebraicGeometry.Space.DescentSituation

end

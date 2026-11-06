module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituationSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget

/-!
# Supplement to `SeparatedMorphismDescent`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `Stages`
* `stagesInclusion`
* `stagesInclusion_final`
* `stagesBase`
* `stagesBase_map_comp_baseAtToInitial`
* `stagesBaseToInitial`
* `stagesBaseCone`
* `isLimitStagesBaseCone`
* `stagesBaseCone_π_comp`
* `mk_stages_op_lt`
* `mk_over_stages_op_lt`
* `chartsBounded_stagesBase`
* `isQuasiCompactSpace_base`
* `isAbsolutelyQuasiSeparated_base`
* `baseDescentSituation`
* `isAffineHom_limit_π_initial`
* `stagesSourceSystem`
* `chartsBounded_stagesSourceSystem`
* `sourceCone`
* `stagesSourceDescentSituation`
* `sourceToTargetInitial`
* `sourceLimitToTargetInitial`
* `sourceCone_π_comp`
* `isAffineHom_targetLimit_snd`
* `exists_isSeparated_mapAt_of_isSeparated_mapLimit`
-/

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_of_chartsBounded` (or `OfChartsBounded` for a definition). -/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry.Space

namespace MorphismDescentSystemOfChartsBounded

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_SeparatedMorphismDescentSupplement
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The indices of a morphism descent system at or beyond its distinguished stage. -/
abbrev Stages : Type u := {i : I // D.initial ≤ i}

/-- The inclusion of the stages at or beyond the distinguished one into the index set. -/
def stagesInclusion : D.Stages ⥤ I := (Subtype.mono_coe fun i => D.initial ≤ i).functor

/-- The inclusion of the stages at or beyond the distinguished one is final, the index set
being directed. -/
instance stagesInclusion_final : (stagesInclusion D).Final := by
  refine (Monotone.final_functor_iff (Subtype.mono_coe fun i => D.initial ≤ i)).2 fun k => ?_
  obtain ⟨m, h₀, hk⟩ := exists_ge_ge D.initial k
  exact ⟨⟨m, h₀⟩, hk⟩

/-- The inverse system of bases, restricted to the stages at or beyond the distinguished one. -/
noncomputable def stagesBase (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    (D.Stages)ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (stagesInclusion D).op ⋙ D.base

/-- A transition morphism of the restricted system of bases, followed by the transition
morphism to the distinguished stage, is the transition morphism to the distinguished stage. -/
theorem stagesBase_map_comp_baseAtToInitial (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    {j k : (D.Stages)ᵒᵖ} (φ : j ⟶ k) :
    (stagesBase D).map φ ≫ D.baseAtToInitial k.unop.1 k.unop.2 =
      D.baseAtToInitial j.unop.1 j.unop.2 :=
  (D.base.map_comp ((stagesInclusion D).op.map φ) (homOfLE k.unop.2).op).symm.trans
    (congrArg D.base.map (Subsingleton.elim _ _))

/-- The transition morphisms to the distinguished stage, as a natural transformation from the
restricted system of bases to the constant system at `B₀`. -/
noncomputable def stagesBaseToInitial (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    stagesBase D ⟶ (Functor.const (D.Stages)ᵒᵖ).obj (D.base.obj (op D.initial)) where
  app j := D.baseAtToInitial j.unop.1 j.unop.2
  naturality {_ _} φ :=
    (stagesBase_map_comp_baseAtToInitial D φ).trans (Category.comp_id _).symm

/-- The limit cone of the system of bases, restricted to the stages at or beyond the
distinguished one; it is still limiting because the inclusion of the stages is final. -/
noncomputable def stagesBaseCone : Cone (stagesBase D) :=
  (limit.cone D.base).whisker (stagesInclusion D).op

/-- The restricted cone of bases is limiting. -/
noncomputable def isLimitStagesBaseCone : IsLimit (stagesBaseCone D) :=
  (Functor.Initial.isLimitWhiskerEquiv (stagesInclusion D).op (limit.cone D.base)).symm
    (limit.isLimit D.base)

/-- The projections of the restricted cone of bases are compatible with the transition
morphisms to the distinguished stage. -/
theorem stagesBaseCone_π_comp (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (j : (D.Stages)ᵒᵖ) :
    (stagesBaseCone D).π.app j ≫ (stagesBaseToInitial D).app j =
      limit.π D.base (op D.initial) :=
  limit.w D.base (homOfLE j.unop.2).op

/-- The stages at or beyond the distinguished one are fewer than the site's size cutoff, being
a subtype of the index set. -/
theorem mk_stages_op_lt : #(D.Stages)ᵒᵖ < B.cutoff :=
  calc #(D.Stages)ᵒᵖ = #D.Stages := mk_congr (Opposite.equivToOpposite (α := D.Stages)).symm
    _ ≤ #I := mk_subtype_le _
    _ = #Iᵒᵖ := mk_congr (Opposite.equivToOpposite (α := I))
    _ < B.cutoff := D.chartsBounded.mk_lt

/-- Every slice of the index category of the restricted system is smaller than the site's size
cutoff, the stages being fewer than the cutoff and the index category being a preorder and
hence thin. -/
theorem mk_over_stages_op_lt (j : (D.Stages)ᵒᵖ) : #(Over j) < B.cutoff :=
  mk_over_lt_of_mk_lt B.aleph0_lt_cutoff (mk_stages_op_lt D)
    (fun k k' =>
      have : Finite (k ⟶ k') := Finite.of_subsingleton
      (lt_aleph0_of_finite _).le) j

/-- **The systems of affine charts of the restricted system of bases are size-bounded.** The
transition morphisms of the restricted system are transition morphisms of the whole system, so
the bound of the whole system serves; the two conditions on the index category hold because the
stages are a subtype of the index set and the index category is thin. -/
theorem chartsBounded_stagesBase : ChartsBounded B S hS (stagesBase D) :=
  D.chartsBounded.comp (stagesInclusion D).op (mk_stages_op_lt D) (mk_over_stages_op_lt D)

/-- Every base at or beyond the distinguished stage is quasi-compact, the transition morphism
to the distinguished stage being affine. -/
theorem isQuasiCompactSpace_base (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (j : D.Stages) :
    IsQuasiCompactSpace B S hS (D.base.obj (op j.1)) :=
  isQuasiCompactSpace_source_of_isQuasiCompact B S hS
    (D.base_isAlgebraicSpace D.initial) D.base₀_quasiCompact
    (isQuasiCompact_of_isAffineHom' B S hS (D.baseAtToInitial j.1 j.2)
      (D.base_isAlgebraicSpace j.1) (D.base_isAlgebraicSpace D.initial)
      (D.transition_affine (homOfLE j.2).op))

/-- Every base at or beyond the distinguished stage is quasi-separated, the transition morphism
to the distinguished stage being affine. -/
theorem isAbsolutelyQuasiSeparated_base (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (j : D.Stages) :
    IsAbsolutelyQuasiSeparated B S hS hZ (D.base.obj (op j.1)) :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
    (D.base_isAlgebraicSpace j.1) D.base₀_quasiSeparated
    (isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_isAffineHom B S hS (D.baseAtToInitial j.1 j.2)
        (D.base_isAlgebraicSpace j.1) (D.base_isAlgebraicSpace D.initial)
        (D.transition_affine (homOfLE j.2).op)))

/-- **The bases `B_i` at or beyond the distinguished stage, as a descent situation.** -/
noncomputable def baseDescentSituation (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    DescentSituation B S hS hZ D.Stages where
  system := stagesBase D
  algebraicSpace j := D.base_isAlgebraicSpace j.1
  transition_affine _ := D.transition_affine _
  quasiCompact j := D.isQuasiCompactSpace_base j
  quasiSeparated j := D.isAbsolutelyQuasiSeparated_base j
  limitCone := stagesBaseCone D
  isLimit := isLimitStagesBaseCone D
  limitAlgebraicSpace := D.limit_isAlgebraicSpace
  base := ⟨D.initial, le_refl _⟩

/-- **Stacks 07SF, part (1), at the distinguished stage of a morphism descent system.** The
projection `B ⟶ B₀` from the limit of the system of bases is affine. -/
theorem isAffineHom_limit_π_initial (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    IsAffineHom B S hS (limit.π D.base (op D.initial)) :=
  (baseDescentSituation D).isAffineHom_limitCone_π_of_chartsBounded (chartsBounded_stagesBase D)
    (op ⟨D.initial, le_refl _⟩)

/-- The inverse system of the sources `X_i` of the base changes of `f₀` to the stages. -/
noncomputable def stagesSourceSystem (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    (D.Stages)ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  baseChangeOverSystem B S hS (stagesBase D) (stagesBaseToInitial D) D.sourceToBase

/-- **The systems of affine charts of the system of sources are size-bounded**, the system of
sources being a base change of the restricted system of bases. -/
theorem chartsBounded_stagesSourceSystem : ChartsBounded B S hS (stagesSourceSystem D) :=
  (chartsBounded_stagesBase D).baseChangeOver (stagesBaseToInitial D) D.sourceToBase

/-- The cone over the system of sources with vertex the source `X` of the base change of `f₀`
to the limit. -/
noncomputable def sourceCone : Cone (stagesSourceSystem D) :=
  baseChangeOverCone B S hS (stagesBase D) (stagesBaseToInitial D) D.sourceToBase
    (stagesBaseCone D) (limit.π D.base (op D.initial)) (stagesBaseCone_π_comp D)

/-- **The sources `X_i` of the base changes of `f₀`, as a descent situation.** They form a
directed inverse system of quasi-compact quasi-separated algebraic spaces with affine
transition morphisms whose limit is the source `X` of the base change of `f₀` to the limit. -/
noncomputable def stagesSourceDescentSituation
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    DescentSituation B S hS hZ D.Stages where
  system := stagesSourceSystem D
  algebraicSpace j := isAlgebraicSpace_pullback B S hS _ _
    (D.base_isAlgebraicSpace j.1) D.source₀_isAlgebraicSpace
    (D.base_isAlgebraicSpace D.initial)
  transition_affine {j k} φ := isAffineHom_of_isPullback
    (isPullback_baseChangeOverMap B S hS ((stagesBaseToInitial D).app j)
      ((stagesBaseToInitial D).app k) ((stagesBase D).map φ) (by simp) D.sourceToBase).flip
    (D.transition_affine _)
  quasiCompact j := isQuasiCompactSpace_pullback B S hS hZ _ D.sourceToBase
    (D.base_isAlgebraicSpace j.1) (D.base_isAlgebraicSpace D.initial)
    (D.isQuasiCompactSpace_base j) D.source₀_quasiCompact D.base₀_quasiSeparated
  quasiSeparated j := isAbsolutelyQuasiSeparated_pullback B S hS hZ _ D.sourceToBase
    (D.base_isAlgebraicSpace j.1) D.source₀_isAlgebraicSpace
    (D.base_isAlgebraicSpace D.initial)
    (D.isAbsolutelyQuasiSeparated_base j) D.source₀_quasiSeparated
  limitCone := sourceCone D
  isLimit := isLimit_baseChangeOverCone B S hS (stagesBase D) (stagesBaseToInitial D)
    D.sourceToBase (stagesBaseCone D) (limit.π D.base (op D.initial))
    (stagesBaseCone_π_comp D) (isLimitStagesBaseCone D)
  limitAlgebraicSpace := D.sourceLimit_isAlgebraicSpace
  base := ⟨D.initial, le_refl _⟩

/-- The structure morphisms of the sources `X_i` over the fixed target `Y₀`. -/
noncomputable def sourceToTargetInitial (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    stagesSourceSystem D ⟶ (Functor.const (D.Stages)ᵒᵖ).obj D.target₀ where
  app j := pullback.snd ((stagesBaseToInitial D).app j) D.sourceToBase ≫ D.map₀
  naturality {_ _} φ :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun x => x ≫ D.map₀) (baseChangeOverSystem_map_snd B S hS (stagesBase D)
        (stagesBaseToInitial D) D.sourceToBase φ))).trans (Category.comp_id _).symm

/-- The structure morphism of the source `X` of the base change to the limit over the fixed
target `Y₀`. -/
noncomputable def sourceLimitToTargetInitial : D.sourceLimit ⟶ D.target₀ :=
  pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase ≫ D.map₀

/-- The projections of the cone of sources are compatible with the structure morphisms to the
fixed target `Y₀`. -/
theorem sourceCone_π_comp (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (j : (D.Stages)ᵒᵖ) :
    (sourceCone D).π.app j ≫ (sourceToTargetInitial D).app j = sourceLimitToTargetInitial D :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun x => x ≫ D.map₀)
      (baseChangeOverMap_snd B S hS (limit.π D.base (op D.initial))
        ((stagesBaseToInitial D).app j) ((stagesBaseCone D).π.app j)
        (stagesBaseCone_π_comp D j) D.sourceToBase))

/-- The projection `Y ⟶ Y₀` from the target of the base change to the limit is affine, being
a base change of the projection `B ⟶ B₀`. -/
theorem isAffineHom_targetLimit_snd (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    IsAffineHom B S hS (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase) :=
  isAffineHom_of_isPullback D.targetLimit_isPullback (isAffineHom_limit_π_initial D)

/-- **Stacks 0851.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is separated, then the base change `f_i` of `f₀` to some stage `B_i` is separated. -/
theorem exists_isSeparated_mapAt_of_isSeparated_mapLimit
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) (hf : IsSeparated B S hS D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), IsSeparated B S hS (D.mapAt i hi) := by
  have hcomp : IsSeparated B S hS (sourceLimitToTargetInitial D) := by
    have h := isSeparated_comp B S hS D.mapLimit
      (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase) hf
      (isSeparated_of_isAffineHom B S hS _ D.targetLimit_isAlgebraicSpace
        D.target₀_isAlgebraicSpace (isAffineHom_targetLimit_snd D))
    rwa [D.mapLimit_snd] at h
  obtain ⟨i, -, hi⟩ := DescentSituation.exists_isSeparated_system_app_of_chartsBounded B S hS hZ
    (stagesSourceDescentSituation D) (chartsBounded_stagesSourceSystem D)
    D.target₀_isAlgebraicSpace
    D.target₀_quasiSeparated (sourceToTargetInitial D) (sourceLimitToTargetInitial D)
    (sourceCone_π_comp D) hcomp
  refine ⟨i.1, i.2, isSeparated_of_comp B S hS (D.mapAt i.1 i.2)
    (pullback.snd (D.baseAtToInitial i.1 i.2) D.targetToBase) ?_⟩
  rw [D.mapAt_snd]
  exact hi i le_rfl

end MorphismDescentSystemOfChartsBounded

end AlgebraicGeometry.Space

end

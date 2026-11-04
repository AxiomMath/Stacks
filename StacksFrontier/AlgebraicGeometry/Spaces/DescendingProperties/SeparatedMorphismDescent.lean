module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget

/-!
# Separatedness of a morphism descends to a stage of a limit of bases

Let `B = lim B_i` be a directed inverse limit of algebraic spaces with affine transition
morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated algebraic spaces
over `B₀`, and let `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` be the base changes of `f₀` to `B_i` and
to `B`. If `f` is separated then `f_i` is separated for some `i ≥ 0`.

The source deduces this from the descent of closed immersions applied to the relative diagonal
of `f₀`. The proof here instead reads separatedness over the fixed target `Y₀`: the projection
`Y_i ⟶ Y₀` is a base change of a transition morphism, hence affine and so separated, so
`f_i` is separated exactly when the composite `X_i ⟶ Y₀` is. The stages `X_i` for `i ≥ 0` form
a directed inverse system of quasi-compact quasi-separated algebraic spaces over `Y₀` with
affine transition morphisms and limit `X`, so the statement is the descent of separatedness
over a base algebraic space.

## Main results

* `AlgebraicGeometry.Space.MorphismDescentSystem.exists_isSeparated_mapAt_of_isSeparated_mapLimit`:
  **Stacks 0851**.

## Implementation notes

The descent system of sources and its underlying functor are named after the stage set indexing
them, and the result above carries its hypothesis in its name, because a second development of
the same descent system is in progress elsewhere: it names the corresponding objects
`sourceSystem` and `sourceDescentSituation` in this namespace, and reserves
`exists_isSeparated_mapAt` for the statement with the *finiteness* hypothesis. Stacks 0851 is
the statement with the *separatedness* hypothesis, which is the one proved here. When that
development lands, the two objects here should be deleted in favour of its public ones.

The index set of the system of sources is the upper set of the distinguished stage, the
transition morphisms of the whole system being defined only there; the inclusion of that upper
set is final because the index set is directed, so the limit of the restricted system of bases
is still `B`.

## References

* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

/-- An upper set of a directed preorder is directed. -/
instance isDirected_subtype_le {α : Type*} [Preorder α] [IsDirected α (· ≤ ·)] (a : α) :
    IsDirected {x : α // a ≤ x} (· ≤ ·) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨m, hxm, hym⟩ := exists_ge_ge x.1 y.1
  exact ⟨⟨m, x.2.trans hxm⟩, hxm, hym⟩

namespace AlgebraicGeometry.Space.MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

/-- The source of an affine morphism of algebraic spaces into a quasi-compact, quasi-separated
one is quasi-compact and quasi-separated. -/
private theorem isQuasiCompactSpace_and_quasiSeparated_of_isAffineHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsAffineHom B S hS f)
    (hYc : IsQuasiCompactSpace B S hS Y) (hYs : IsAbsolutelyQuasiSeparated B S hS hZ Y) :
    IsQuasiCompactSpace B S hS X ∧ IsAbsolutelyQuasiSeparated B S hS hZ X :=
  ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYc
      (isQuasiCompact_of_isAffineHom' B S hS f hX hY hf),
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hYs
      (isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isAffineHom B S hS f hX hY hf))⟩

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
noncomputable def stagesBase : (D.Stages)ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (stagesInclusion D).op ⋙ D.base

/-- A transition morphism of the restricted system of bases, followed by the transition
morphism to the distinguished stage, is the transition morphism to the distinguished stage. -/
theorem stagesBase_map_comp_baseAtToInitial {j k : (D.Stages)ᵒᵖ} (φ : j ⟶ k) :
    (stagesBase D).map φ ≫ D.baseAtToInitial k.unop.1 k.unop.2 =
      D.baseAtToInitial j.unop.1 j.unop.2 :=
  (D.base.map_comp ((stagesInclusion D).op.map φ) (homOfLE k.unop.2).op).symm.trans
    (congrArg D.base.map (Subsingleton.elim _ _))

/-- The transition morphisms to the distinguished stage, as a natural transformation from the
restricted system of bases to the constant system at `B₀`. -/
noncomputable def stagesBaseToInitial :
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
theorem stagesBaseCone_π_comp (j : (D.Stages)ᵒᵖ) :
    (stagesBaseCone D).π.app j ≫ (stagesBaseToInitial D).app j =
      limit.π D.base (op D.initial) :=
  limit.w D.base (homOfLE j.unop.2).op

/-- The cardinality bound of the system passes to the stages at or beyond the distinguished
one, a subtype of the index set. -/
theorem mk_stages_lt : #D.Stages < B.cutoff.ord.cof :=
  lt_of_le_of_lt (mk_subtype_le _) D.indexSize

/-- Every base at or beyond the distinguished stage is quasi-compact, the transition morphism
to the distinguished stage being affine. -/
theorem isQuasiCompactSpace_base (j : D.Stages) :
    IsQuasiCompactSpace B S hS (D.base.obj (op j.1)) :=
  (isQuasiCompactSpace_and_quasiSeparated_of_isAffineHom (D.baseAtToInitial j.1 j.2)
    (D.base_isAlgebraicSpace j.1) (D.base_isAlgebraicSpace D.initial)
    (D.transition_affine (homOfLE j.2).op) D.base₀_quasiCompact D.base₀_quasiSeparated).1

/-- Every base at or beyond the distinguished stage is quasi-separated, the transition morphism
to the distinguished stage being affine. -/
theorem isAbsolutelyQuasiSeparated_base (j : D.Stages) :
    IsAbsolutelyQuasiSeparated B S hS hZ (D.base.obj (op j.1)) :=
  (isQuasiCompactSpace_and_quasiSeparated_of_isAffineHom (D.baseAtToInitial j.1 j.2)
    (D.base_isAlgebraicSpace j.1) (D.base_isAlgebraicSpace D.initial)
    (D.transition_affine (homOfLE j.2).op) D.base₀_quasiCompact D.base₀_quasiSeparated).2

/-- **The bases `B_i` at or beyond the distinguished stage, as a descent situation.** -/
noncomputable def baseDescentSituation : DescentSituation B S hS hZ D.Stages where
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
theorem isAffineHom_limit_π_initial :
    IsAffineHom B S hS (limit.π D.base (op D.initial)) :=
  (baseDescentSituation D).isAffineHom_limitCone_π (mk_stages_lt D)
    (op ⟨D.initial, le_refl _⟩)

/-- The inverse system of the sources `X_i` of the base changes of `f₀` to the stages. -/
noncomputable def stagesSourceSystem : (D.Stages)ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  baseChangeOverSystem B S hS (stagesBase D) (stagesBaseToInitial D) D.sourceToBase

/-- The cone over the system of sources with vertex the source `X` of the base change of `f₀`
to the limit. -/
noncomputable def sourceCone : Cone (stagesSourceSystem D) :=
  baseChangeOverCone B S hS (stagesBase D) (stagesBaseToInitial D) D.sourceToBase
    (stagesBaseCone D) (limit.π D.base (op D.initial)) (stagesBaseCone_π_comp D)

/-- **The sources `X_i` of the base changes of `f₀`, as a descent situation.** They form a
directed inverse system of quasi-compact quasi-separated algebraic spaces with affine
transition morphisms whose limit is the source `X` of the base change of `f₀` to the limit. -/
noncomputable def stagesSourceDescentSituation : DescentSituation B S hS hZ D.Stages where
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
noncomputable def sourceToTargetInitial :
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
theorem sourceCone_π_comp (j : (D.Stages)ᵒᵖ) :
    (sourceCone D).π.app j ≫ (sourceToTargetInitial D).app j = sourceLimitToTargetInitial D :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun x => x ≫ D.map₀)
      (baseChangeOverMap_snd B S hS (limit.π D.base (op D.initial))
        ((stagesBaseToInitial D).app j) ((stagesBaseCone D).π.app j)
        (stagesBaseCone_π_comp D j) D.sourceToBase))

/-- The projection `Y ⟶ Y₀` from the target of the base change to the limit is affine, being
a base change of the projection `B ⟶ B₀`. -/
theorem isAffineHom_targetLimit_snd :
    IsAffineHom B S hS (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase) :=
  isAffineHom_of_isPullback D.targetLimit_isPullback (isAffineHom_limit_π_initial D)

end AlgebraicGeometry.Space.MorphismDescentSystem

/-! ### The situation of Stacks 084W

The same results for `AlgebraicGeometry.Space.MorphismDescentSituation`, which imposes no
condition on the size of the index; the descent results then take the explicit
hypothesis `hb : AlgebraicGeometry.Space.IsSiteSmall B S hS D.base`. -/

namespace AlgebraicGeometry.Space.MorphismDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

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
noncomputable def stagesBase : (D.Stages)ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (stagesInclusion D).op ⋙ D.base

/-- A transition morphism of the restricted system of bases, followed by the transition
morphism to the distinguished stage, is the transition morphism to the distinguished stage. -/
theorem stagesBase_map_comp_baseAtToInitial {j k : (D.Stages)ᵒᵖ} (φ : j ⟶ k) :
    (stagesBase D).map φ ≫ D.baseAtToInitial k.unop.1 k.unop.2 =
      D.baseAtToInitial j.unop.1 j.unop.2 :=
  (D.base.map_comp ((stagesInclusion D).op.map φ) (homOfLE k.unop.2).op).symm.trans
    (congrArg D.base.map (Subsingleton.elim _ _))

/-- The transition morphisms to the distinguished stage, as a natural transformation from the
restricted system of bases to the constant system at `B₀`. -/
noncomputable def stagesBaseToInitial :
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
theorem stagesBaseCone_π_comp (j : (D.Stages)ᵒᵖ) :
    (stagesBaseCone D).π.app j ≫ (stagesBaseToInitial D).app j =
      limit.π D.base (op D.initial) :=
  limit.w D.base (homOfLE j.unop.2).op

/-- The cardinality bound of the system passes to the stages at or beyond the distinguished
one, a subtype of the index set. -/
theorem mk_stages_lt (hI : #I < B.cutoff.ord.cof) : #D.Stages < B.cutoff.ord.cof :=
  lt_of_le_of_lt (mk_subtype_le _) hI

/-- **Smallness for the site passes to the restricted system of bases.** Under the cofinality
alternative the stages at or beyond the distinguished one form a subtype of the index set, so
the bound passes to it, and the morphism types of a preorder are subsingletons; under the other
alternative the transition morphisms of the restricted system are transition morphisms of the
original one. -/
theorem isSiteSmall_stagesBase (hb : IsSiteSmall B S hS D.base) :
    IsSiteSmall B S hS (stagesBase D) := by
  rcases hb with ⟨hI, -⟩ | hmono
  · rw [Cardinal.mk_congr (show Iᵒᵖ ≃ I from ⟨unop, op, fun _ ↦ rfl, fun _ ↦ rfl⟩)] at hI
    exact .of_lt_cof_op (lt_of_le_of_lt (mk_subtype_le _) hI)
  · exact .of_mono fun {_ _} φ => hmono _

/-- Every base at or beyond the distinguished stage is quasi-compact, the transition morphism
to the distinguished stage being affine. -/
theorem isQuasiCompactSpace_base (j : D.Stages) :
    IsQuasiCompactSpace B S hS (D.base.obj (op j.1)) :=
  (MorphismDescentSystem.isQuasiCompactSpace_and_quasiSeparated_of_isAffineHom
    (D.baseAtToInitial j.1 j.2) (D.base_isAlgebraicSpace j.1) (D.base_isAlgebraicSpace D.initial)
    (D.transition_affine (homOfLE j.2).op) D.base₀_quasiCompact D.base₀_quasiSeparated).1

/-- Every base at or beyond the distinguished stage is quasi-separated, the transition morphism
to the distinguished stage being affine. -/
theorem isAbsolutelyQuasiSeparated_base (j : D.Stages) :
    IsAbsolutelyQuasiSeparated B S hS hZ (D.base.obj (op j.1)) :=
  (MorphismDescentSystem.isQuasiCompactSpace_and_quasiSeparated_of_isAffineHom
    (D.baseAtToInitial j.1 j.2) (D.base_isAlgebraicSpace j.1) (D.base_isAlgebraicSpace D.initial)
    (D.transition_affine (homOfLE j.2).op) D.base₀_quasiCompact D.base₀_quasiSeparated).2

/-- **The bases `B_i` at or beyond the distinguished stage, as a descent situation.** -/
noncomputable def baseDescentSituation : DescentSituation B S hS hZ D.Stages where
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
theorem isAffineHom_limit_π_initial (hb : IsSiteSmall B S hS D.base) :
    IsAffineHom B S hS (limit.π D.base (op D.initial)) :=
  (baseDescentSituation D).isAffineHom_limitCone_π_of_isSiteSmall (D.isSiteSmall_stagesBase hb)
    (op ⟨D.initial, le_refl _⟩)

/-- The inverse system of the sources `X_i` of the base changes of `f₀` to the stages. -/
noncomputable def stagesSourceSystem : (D.Stages)ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  baseChangeOverSystem B S hS (stagesBase D) (stagesBaseToInitial D) D.sourceToBase

/-- **Smallness for the site passes to the system of sources**, which is the system of bases
base changed along the structure morphism of `X₀`. -/
theorem isSiteSmall_stagesSourceSystem (hb : IsSiteSmall B S hS D.base) :
    IsSiteSmall B S hS (stagesSourceSystem D) :=
  isSiteSmall_baseChangeOverSystem B S hS (stagesBase D) (stagesBaseToInitial D) D.sourceToBase
    (D.isSiteSmall_stagesBase hb)

/-- The cone over the system of sources with vertex the source `X` of the base change of `f₀`
to the limit. -/
noncomputable def sourceCone : Cone (stagesSourceSystem D) :=
  baseChangeOverCone B S hS (stagesBase D) (stagesBaseToInitial D) D.sourceToBase
    (stagesBaseCone D) (limit.π D.base (op D.initial)) (stagesBaseCone_π_comp D)

/-- **The sources `X_i` of the base changes of `f₀`, as a descent situation.** They form a
directed inverse system of quasi-compact quasi-separated algebraic spaces with affine
transition morphisms whose limit is the source `X` of the base change of `f₀` to the limit. -/
noncomputable def stagesSourceDescentSituation : DescentSituation B S hS hZ D.Stages where
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
noncomputable def sourceToTargetInitial :
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
theorem sourceCone_π_comp (j : (D.Stages)ᵒᵖ) :
    (sourceCone D).π.app j ≫ (sourceToTargetInitial D).app j = sourceLimitToTargetInitial D :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun x => x ≫ D.map₀)
      (baseChangeOverMap_snd B S hS (limit.π D.base (op D.initial))
        ((stagesBaseToInitial D).app j) ((stagesBaseCone D).π.app j)
        (stagesBaseCone_π_comp D j) D.sourceToBase))

/-- The projection `Y ⟶ Y₀` from the target of the base change to the limit is affine, being
a base change of the projection `B ⟶ B₀`. -/
theorem isAffineHom_targetLimit_snd (hb : IsSiteSmall B S hS D.base) :
    IsAffineHom B S hS (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase) :=
  isAffineHom_of_isPullback D.targetLimit_isPullback (isAffineHom_limit_π_initial D hb)

/-- **Stacks 0851.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is separated, then the base change `f_i` of `f₀` to some stage `B_i` is separated.

The hypothesis `hb` is the one Stacks 07SF asks for, `AlgebraicGeometry.Space.IsSiteSmall` of
the inverse system of bases: Situation 70.6.1 does not state it and
`AlgebraicGeometry.Space.MorphismDescentSituation` therefore does not carry it, but without it the
limit `B` need not be an algebraic space at all, so the conclusion is not even stated. An index
category below the cofinality of the site's size cutoff supplies it through
`AlgebraicGeometry.Space.IsSiteSmall.of_lt_cof_op`, and so — with nothing asked of the index —
do monomorphic transition morphisms through
`AlgebraicGeometry.Space.IsSiteSmall.of_mono`. -/
@[sga "3 VIB 10.1" "partial"]
theorem exists_isSeparated_mapAt_of_isSeparated_mapLimit (hb : IsSiteSmall B S hS D.base)
    (hf : IsSeparated B S hS D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), IsSeparated B S hS (D.mapAt i hi) := by
  have hcomp : IsSeparated B S hS (sourceLimitToTargetInitial D) := by
    have h := isSeparated_comp B S hS D.mapLimit
      (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase) hf
      (isSeparated_of_isAffineHom B S hS _ D.targetLimit_isAlgebraicSpace
        D.target₀_isAlgebraicSpace (isAffineHom_targetLimit_snd D hb))
    rw [D.mapLimit_snd] at h
    exact h
  obtain ⟨i, -, hi⟩ := DescentSituation.exists_isSeparated_system_app_of_isSiteSmall B S hS hZ
    (stagesSourceDescentSituation D) (D.isSiteSmall_stagesSourceSystem hb)
    D.target₀_isAlgebraicSpace
    D.target₀_quasiSeparated (sourceToTargetInitial D) (sourceLimitToTargetInitial D)
    (sourceCone_π_comp D) hcomp
  refine ⟨i.1, i.2, isSeparated_of_comp B S hS (D.mapAt i.1 i.2)
    (pullback.snd (D.baseAtToInitial i.1 i.2) D.targetToBase) ?_⟩
  rw [D.mapAt_snd]
  exact hi i le_rfl

end AlgebraicGeometry.Space.MorphismDescentSituation


namespace AlgebraicGeometry.Space.MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

/-- **Stacks 0851.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is separated, then the base change `f_i` of `f₀` to some stage `B_i` is separated. -/
@[stacks 0851]
theorem exists_isSeparated_mapAt_of_isSeparated_mapLimit (hf : IsSeparated B S hS D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), IsSeparated B S hS (D.mapAt i hi) :=
  D.toSituation.exists_isSeparated_mapAt_of_isSeparated_mapLimit
    (IsSiteSmall.of_lt_cof_op D.indexSize) hf

end AlgebraicGeometry.Space.MorphismDescentSystem

end

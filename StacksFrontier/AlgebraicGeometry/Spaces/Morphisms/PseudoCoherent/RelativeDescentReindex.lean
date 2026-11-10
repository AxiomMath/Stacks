module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentAffineModel

/-!
# Reindexing Situation 0DKU at a later stage

In Situation 0DKU, let `i ≥ i₀` be a later stage.  The base change `Xᵢ ⟶ Yᵢ` of the flat finitely
presented morphism `X₀ ⟶ Y₀` is again flat and of finite presentation, and the base changes
`Xⱼ`, `j ≥ i`, and `X` of `X₀` are also the base changes of `Xᵢ`.  So the inverse system with the
chosen stage moved to `i` is again a Situation 0DKU, `RelativeDescentSituation.reindex`; its stages
and its limit are those of the original situation, definitionally.

The limit of the reindexed situation is again a limit of schemes on affine charts: the
projection `Y ⟶ Yᵢ` is affine, since `Y ⟶ Y₀` is and `Yᵢ ⟶ Y₀` is affine, and for an affine
chart `z : Z ⟶ Yᵢ` the base changes `Yⱼ ×_{Yᵢ} Z` are the fibre products of the base changes
`Yⱼ ×_{Y₀} Z` with `Z` over `Yᵢ ×_{Y₀} Z`, along the graph section of `z`; fibre products along a
morphism to the least stage commute with limits of schemes.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.reindex`: Situation 0DKU with the chosen
  stage moved to a later stage `i`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_comp_of_isAffineHom`: affineness of morphisms of
  presheaves on the big fppf site cancels against an affine morphism.
* `AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_reindex`: if the limit of
  Situation 0DKU is a limit of schemes on affine charts, so is that of the reindexed situation.

## References

* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Affineness cancels against an affine morphism.** If `f ≫ g` and `g` are affine morphisms of
presheaves on the big fppf site of `S`, so is `f`: over an affine chart `z` of the source of `g`,
the base change of `f` is the fibre product of the affine base change of `f ≫ g` along `z ≫ g` with
`Z` over the affine base change of `g`, along the graph section of `z`. -/
theorem isAffineHom_of_comp_of_isAffineHom {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H) (hfg : IsAffineHom B S hS (f ≫ g))
    (hg : IsAffineHom B S hS g) : IsAffineHom B S hS f := by
  intro Z z
  obtain ⟨WG, pG, qG, hG⟩ := hg Z (z ≫ g)
  obtain ⟨WF, pF, qF, hF⟩ := hfg Z (z ≫ g)
  let s : (BigAffineFppf.inclusion B S hS).obj Z ⟶ (BigAffineFppf.inclusion B S hS).obj WG :=
    yoneda.preimage (hG.lift z (𝟙 _) (by rw [Category.id_comp]))
  have hs : yoneda.map s ≫ pG = z := by
    simp only [s, Functor.map_preimage, IsPullback.lift_fst]
  let t : (BigAffineFppf.inclusion B S hS).obj WF ⟶ (BigAffineFppf.inclusion B S hS).obj WG :=
    yoneda.preimage (hG.lift (pF ≫ f) (yoneda.map qF) (by rw [Category.assoc, hF.w]))
  have ht₁ : yoneda.map t ≫ pG = pF ≫ f := by
    simp only [t, Functor.map_preimage, IsPullback.lift_fst]
  have ht₂ : yoneda.map t ≫ yoneda.map qG = yoneda.map qF := by
    simp only [t, Functor.map_preimage, IsPullback.lift_snd]
  have hA : IsPullback pF (yoneda.map t) f pG :=
    IsPullback.of_bot (by rwa [ht₂]) ht₁.symm hG
  let T := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  have : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj WF)) := WF.property
  have : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj WG)) := WG.property
  have : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
  have : AlgebraicGeometry.IsAffineHom (T.map t) :=
    AlgebraicGeometry.IsAffineHom.of_comp (T.map t) (terminal.from _)
  have : HasLimit (cospan t s) :=
    (AlgebraicGeometry.hasPullbacks_bigFppfOver B S hS).has_limit (cospan t s)
  have hP : IsAffine (T.obj (pullback t s)) :=
    IsAffine.of_isIso (PreservesPullback.iso T t s).hom
  refine ⟨⟨pullback t s, hP⟩, yoneda.map (pullback.fst t s) ≫ pF, pullback.snd t s, ?_⟩
  have h := ((IsPullback.of_hasPullback t s).map yoneda).paste_horiz hA
  rwa [hs] at h

namespace RelativeDescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- A stage at or beyond a later stage `i` is at or beyond the chosen one. -/
theorem le_of_laterIndex_le (i : D.LaterIndex) {j : I} (hj : i.1 ≤ j) : D.i₀ ≤ j :=
  i.2.trans hj

/-- The base change `Xⱼ ⟶ Xᵢ` of the transition `Yⱼ ⟶ Yᵢ` along `Xᵢ ⟶ Yᵢ` is cartesian. -/
theorem isPullback_transition (i : D.LaterIndex) (j : I) (hj : i.1 ≤ j) :
    IsPullback (D.toYᵢ j (D.le_of_laterIndex_le i hj)) (D.fᵢⱼ i.1 j i.2 _ hj)
      (D.Y.map (homOfLE hj).op) (D.toYᵢ i.1 i.2) := by
  refine IsPullback.of_bot ?_ (D.fᵢⱼ_toYᵢ i.1 j i.2 _ hj).symm (D.stage_isPullback i.1 i.2)
  rw [D.fᵢⱼ_toX₀, ← D.Y.map_comp]
  exact D.stage_isPullback j _

/-- The base change `X ⟶ Xᵢ` of the projection `Y ⟶ Yᵢ` along `Xᵢ ⟶ Yᵢ` is cartesian. -/
theorem isPullback_projection (i : D.LaterIndex) :
    IsPullback D.toLimit (D.fᵢ i.1 i.2) (D.limitCone.π.app (op i.1)) (D.toYᵢ i.1 i.2) := by
  refine IsPullback.of_bot ?_ (D.fᵢ_toYᵢ i.1 i.2).symm (D.stage_isPullback i.1 i.2)
  rw [D.fᵢ_toX₀, D.limitCone.w]
  exact D.limit_isPullback

/-- The cartesian square of a later stage, read in the category of algebraic spaces. -/
theorem stage_isPullback_algebraicSpaces (i : D.LaterIndex) :
    IsPullback (ObjectProperty.homMk (D.toYᵢ i.1 i.2) :
        D.stageSource i ⟶ ⟨_, D.stage_isAlgebraicSpace i.1⟩) (D.stageToInitial i)
      (ObjectProperty.homMk (D.Y.map (homOfLE i.2).op) :
        (⟨_, D.stage_isAlgebraicSpace i.1⟩ : AlgebraicSpaces B S hS) ⟶ D.initialTarget)
      D.initialStructure :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.stage_isPullback i.1 i.2)

/-- The cartesian square of the limit, read in the category of algebraic spaces. -/
theorem limit_isPullback_algebraicSpaces :
    IsPullback (ObjectProperty.homMk D.toLimit :
        D.limitSource ⟶ ⟨_, D.limit_isAlgebraicSpace⟩) D.limitToInitial
      (ObjectProperty.homMk (D.limitCone.π.app (op D.i₀)) :
        (⟨_, D.limit_isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ D.initialTarget)
      D.initialStructure :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) D.limit_isPullback

/-- The base change `Xᵢ ⟶ Yᵢ` of the chosen flat morphism is flat (Stacks 03MO). -/
theorem stage_isFlat (i : D.LaterIndex) : IsFlat B S hS (D.toYᵢ i.1 i.2) :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (D.stage_isPullback_algebraicSpaces i).flip D.initial_isFlat

/-- The base change `Xᵢ ⟶ Yᵢ` of the chosen morphism of finite presentation is of finite
presentation (Stacks 03XR). -/
theorem stage_isFinitePresentation (i : D.LaterIndex) :
    IsFinitePresentation B S hS (D.toYᵢ i.1 i.2) :=
  (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (D.stage_isPullback_algebraicSpaces i).flip D.initial_isFinitePresentation

/-- The base change `X ⟶ Y` of the chosen flat morphism is flat (Stacks 03MO). -/
theorem limit_isFlat : IsFlat B S hS D.toLimit :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    D.limit_isPullback_algebraicSpaces.flip D.initial_isFlat

/-- The base change `X ⟶ Y` of the chosen morphism of finite presentation is of finite
presentation (Stacks 03XR). -/
theorem limit_isFinitePresentation : IsFinitePresentation B S hS D.toLimit :=
  (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    D.limit_isPullback_algebraicSpaces.flip D.initial_isFinitePresentation

/-! ### The bases of the situation as algebraic spaces -/

/-- The stage `Yᵢ` of the inverse system at a later stage, as an object of the category of
algebraic spaces. -/
abbrev stageTarget (i : D.LaterIndex) : AlgebraicSpaces B S hS :=
  ⟨D.Y.obj (op i.1), D.stage_isAlgebraicSpace i.1⟩

/-- The limit `Y` of the inverse system, as an object of the category of algebraic spaces. -/
abbrev limitTarget : AlgebraicSpaces B S hS := ⟨D.limitCone.pt, D.limit_isAlgebraicSpace⟩

/-- The base change `Xᵢ ⟶ Yᵢ` of the chosen flat morphism, as a morphism of algebraic spaces. -/
abbrev stageStructure (i : D.LaterIndex) : D.stageSource i ⟶ D.stageTarget i :=
  ObjectProperty.homMk (D.toYᵢ i.1 i.2)

/-- The base change `X ⟶ Y` of the chosen flat morphism, as a morphism of algebraic spaces. -/
abbrev limitStructure : D.limitSource ⟶ D.limitTarget := ObjectProperty.homMk D.toLimit

/-- The transition `Yⱼ ⟶ Yᵢ` of the inverse system, for `i ≤ j`, as a morphism of algebraic
spaces. -/
abbrev targetTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.stageTarget j ⟶ D.stageTarget i :=
  ObjectProperty.homMk (D.Y.map (homOfLE h).op)

/-- The projection `Y ⟶ Yᵢ` of the limit, as a morphism of algebraic spaces. -/
abbrev targetProjection (i : D.LaterIndex) : D.limitTarget ⟶ D.stageTarget i :=
  ObjectProperty.homMk (D.limitCone.π.app (op i.1))

/-- The square of algebraic spaces exhibiting `Xⱼ` as `Yⱼ ×_{Yᵢ} Xᵢ` is cartesian. -/
theorem isPullback_sourceTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    IsPullback (D.sourceTransition h) (D.stageStructure j) (D.stageStructure i)
      (D.targetTransition h) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_transition i j.1 h).flip

/-- The square of algebraic spaces exhibiting `X` as `Y ×_{Yᵢ} Xᵢ` is cartesian. -/
theorem isPullback_sourceProjection (i : D.LaterIndex) :
    IsPullback (D.sourceProjection i) D.limitStructure (D.stageStructure i)
      (D.targetProjection i) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_projection i).flip

/-- **Situation 0DKU reindexed at a later stage `i`.**  The inverse system and its limit are
unchanged, the chosen stage is `i`, the flat finitely presented space over it is the base change
`Xᵢ ⟶ Yᵢ`, and the base changes at the stages `j ≥ i` and at the limit are those of the original
situation, with the transitions `f_{ji} : Xⱼ ⟶ Xᵢ` and `fᵢ : X ⟶ Xᵢ` as projections to the new
initial space. -/
abbrev reindex (i : D.LaterIndex) : RelativeDescentSituation B S hS hZ I where
  Y := D.Y
  limitCone := D.limitCone
  isLimit := D.isLimit
  stage_isAlgebraicSpace := D.stage_isAlgebraicSpace
  limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
  stage_isQuasiCompact := D.stage_isQuasiCompact
  stage_isQuasiSeparated := D.stage_isQuasiSeparated
  transition_isAffine := D.transition_isAffine
  i₀ := i.1
  X₀ := D.Xᵢ i.1 i.2
  p₀ := D.toYᵢ i.1 i.2
  initial_isAlgebraicSpace := D.stageX_isAlgebraicSpace i.1 i.2
  initial_isFlat := D.stage_isFlat i
  initial_isFinitePresentation := D.stage_isFinitePresentation i
  Xᵢ j hj := D.Xᵢ j (D.le_of_laterIndex_le i hj)
  stageX_isAlgebraicSpace j _ := D.stageX_isAlgebraicSpace j _
  toX₀ j hj := D.fᵢⱼ i.1 j i.2 _ hj
  toYᵢ j _ := D.toYᵢ j _
  stage_isPullback j hj := D.isPullback_transition i j hj
  fᵢⱼ j k _ _ hjk := D.fᵢⱼ j k _ _ hjk
  fᵢⱼ_toYᵢ j k _ _ hjk := D.fᵢⱼ_toYᵢ j k _ _ hjk
  fᵢⱼ_toX₀ _ _ hj _ hjk := D.transition_comp_transition i.2 _ _ hj hjk
  X := D.X
  X_isAlgebraicSpace := D.X_isAlgebraicSpace
  toInitial := D.fᵢ i.1 i.2
  toLimit := D.toLimit
  limit_isPullback := D.isPullback_projection i
  fᵢ j _ := D.fᵢ j _
  fᵢ_toYᵢ j _ := D.fᵢ_toYᵢ j _
  fᵢ_toX₀ _ hj := D.projection_comp_transition i.2 _ hj

variable (i : D.LaterIndex)

/-! ### The reindexed situation has the same stages and limit -/

/-- A stage at or beyond `i`, read as a stage at or beyond the chosen one. -/
abbrev reindexLaterIndex (j : (D.reindex i).LaterIndex) : D.LaterIndex :=
  ⟨j.1, D.le_of_laterIndex_le i j.2⟩

/-- The inverse system of the reindexed situation is that of the original one. -/
theorem reindex_Y : (D.reindex i).Y = D.Y := rfl

/-- The limit cone of the reindexed situation is that of the original one. -/
theorem reindex_limitCone : (D.reindex i).limitCone = D.limitCone := rfl

/-- The chosen stage of the reindexed situation is `i`. -/
theorem reindex_i₀ : (D.reindex i).i₀ = i.1 := rfl

/-- The initial space of the reindexed situation is the base change `Xᵢ`. -/
theorem reindex_X₀ : (D.reindex i).X₀ = D.Xᵢ i.1 i.2 := rfl

/-- The initial morphism of the reindexed situation is the base change `Xᵢ ⟶ Yᵢ`. -/
theorem reindex_p₀ : (D.reindex i).p₀ = D.toYᵢ i.1 i.2 := rfl

/-- The base change to the limit in the reindexed situation is `X`. -/
theorem reindex_X : (D.reindex i).X = D.X := rfl

/-- The morphism `X ⟶ Y` of the reindexed situation is that of the original one. -/
theorem reindex_toLimit : (D.reindex i).toLimit = D.toLimit := rfl

/-- The projection of `X` to the initial space of the reindexed situation is `fᵢ : X ⟶ Xᵢ`. -/
theorem reindex_toInitial : (D.reindex i).toInitial = D.fᵢ i.1 i.2 := rfl

/-- The initial space of the reindexed situation, as an algebraic space, is `Xᵢ`. -/
theorem reindex_initialSource : (D.reindex i).initialSource = D.stageSource i := rfl

/-- The initial base of the reindexed situation, as an algebraic space, is `Yᵢ`. -/
theorem reindex_initialTarget : (D.reindex i).initialTarget =
    ⟨D.Y.obj (op i.1), D.stage_isAlgebraicSpace i.1⟩ := rfl

/-- The base change to the limit in the reindexed situation, as an algebraic space, is `X`. -/
theorem reindex_limitSource : (D.reindex i).limitSource = D.limitSource := rfl

/-- The base change at a stage `j ≥ i` in the reindexed situation, as an algebraic space, is
`Xⱼ`. -/
theorem reindex_stageSource (j : (D.reindex i).LaterIndex) :
    (D.reindex i).stageSource j = D.stageSource (D.reindexLaterIndex i j) := rfl

/-- The projection `Xⱼ ⟶ Xᵢ` to the initial space of the reindexed situation is the transition
`f_{ji}` of the original one. -/
theorem reindex_stageToInitial (j : (D.reindex i).LaterIndex) :
    (D.reindex i).stageToInitial j =
      D.sourceTransition (i := i) (j := D.reindexLaterIndex i j) j.2 :=
  rfl

/-- The projection `X ⟶ Xᵢ` to the initial space of the reindexed situation is `fᵢ`. -/
theorem reindex_limitToInitial : (D.reindex i).limitToInitial = D.sourceProjection i := rfl

/-- The transitions `Xₖ ⟶ Xⱼ` of the reindexed situation are those of the original one. -/
theorem reindex_sourceTransition {j k : (D.reindex i).LaterIndex} (h : j.1 ≤ k.1) :
    (D.reindex i).sourceTransition h =
      D.sourceTransition (i := D.reindexLaterIndex i j) (j := D.reindexLaterIndex i k) h :=
  rfl

/-- The projections `X ⟶ Xⱼ` of the reindexed situation are those of the original one. -/
theorem reindex_sourceProjection (j : (D.reindex i).LaterIndex) :
    (D.reindex i).sourceProjection j = D.sourceProjection (D.reindexLaterIndex i j) := rfl

/-- The initial morphism of the reindexed situation, as a morphism of algebraic spaces, is
`Xᵢ ⟶ Yᵢ`. -/
theorem reindex_initialStructure : (D.reindex i).initialStructure = D.stageStructure i := rfl

/-- The morphisms `Xⱼ ⟶ Yⱼ` of the reindexed situation are those of the original one. -/
theorem reindex_stageStructure (j : (D.reindex i).LaterIndex) :
    (D.reindex i).stageStructure j = D.stageStructure (D.reindexLaterIndex i j) := rfl

/-- The morphism `X ⟶ Y` of the reindexed situation, as a morphism of algebraic spaces, is that
of the original one. -/
theorem reindex_limitStructure : (D.reindex i).limitStructure = D.limitStructure := rfl

/-! ### The reindexed situation is a limit of schemes on affine charts -/

namespace AffineBaseChangeRepresentation

variable {D} {Z : BigAffineFppf B S hS}
  {z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.Y.obj (op D.i₀)}
  (R : D.AffineBaseChangeRepresentation Z z)

/-- The square formed by a transition of a representation of the base changes and the
transition of the stages is cartesian. -/
theorem isPullback_map {j k : D.LaterIndex} (h : j ≤ k) :
    IsPullback (R.p k) (yoneda.map (R.W.map (homOfLE h).op)) (D.Y.map (homOfLE h).op)
      (R.p j) := by
  refine IsPullback.of_bot ?_ (R.map_p j k h).symm (R.isPullback j)
  rw [← Functor.map_comp, R.map_q j k h, D.stage_map_comp h]
  exact R.isPullback k

/-- The square formed by a leg of the cone of a representation of the base changes and the
projection of the limit is cartesian. -/
theorem isPullback_π (j : D.LaterIndex) :
    IsPullback R.pc (yoneda.map (R.c.π.app (op j))) (D.limitCone.π.app (op j.1)) (R.p j) := by
  refine IsPullback.of_bot ?_ (R.π_p j).symm (R.isPullback j)
  rw [← Functor.map_comp, R.π_q j, D.limitCone_π_comp j]
  exact R.isPullback_pt

end AffineBaseChangeRepresentation

section Reindex

variable {D i} {Z : BigAffineFppf B S hS}
  {z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.Y.obj (op i.1)}
  (R : (D.reindex i).AffineBaseChangeRepresentation Z z)
  (R' : D.AffineBaseChangeRepresentation Z (z ≫ D.Y.map (homOfLE i.2).op))

/-- The graph section `Z ⟶ Yᵢ ×_{Y₀} Z` of the chart `z : Z ⟶ Yᵢ`. -/
def reindexSection : (BigAffineFppf.inclusion B S hS).obj Z ⟶ R'.W.obj (op i) :=
  yoneda.preimage ((R'.isPullback i).lift z (𝟙 _) (by rw [Category.id_comp]))

/-- The graph section followed by the projection to `Yᵢ` is the chart `z`. -/
theorem reindexSection_p : yoneda.map (reindexSection (z := z) R') ≫ R'.p i = z := by
  rw [reindexSection, Functor.map_preimage, IsPullback.lift_fst]

/-- The graph section followed by the projection to `Z` is the identity. -/
theorem reindexSection_q : reindexSection (z := z) R' ≫ R'.q i = 𝟙 _ := by
  apply yoneda.map_injective
  rw [Functor.map_comp, reindexSection, Functor.map_preimage, IsPullback.lift_snd, yoneda.map_id]

/-- The two morphisms `Yⱼ ×_{Yᵢ} Z ⟶ Y₀`, through `Yⱼ` and through `Z ⟶ Yᵢ`, agree. -/
theorem reindex_stage_w (j : (D.reindex i).LaterIndex) :
    R.p j ≫ D.Y.map (homOfLE (D.reindexLaterIndex i j).2).op =
      yoneda.map (R.q j) ≫ z ≫ D.Y.map (homOfLE i.2).op := by
  have e : D.Y.map (homOfLE (D.reindexLaterIndex i j).2).op =
      D.Y.map (homOfLE (show i.1 ≤ j.1 from j.2)).op ≫ D.Y.map (homOfLE i.2).op := by
    rw [← Functor.map_comp]
    rfl
  rw [e, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ D.Y.map (homOfLE i.2).op) (R.isPullback j).w

/-- The comparison `Yⱼ ×_{Yᵢ} Z ⟶ Yⱼ ×_{Y₀} Z`. -/
def reindexComparison (j : (D.reindex i).LaterIndex) :
    R.W.obj (op j) ⟶ R'.W.obj (op (D.reindexLaterIndex i j)) :=
  yoneda.preimage ((R'.isPullback (D.reindexLaterIndex i j)).lift (R.p j) (yoneda.map (R.q j))
    (reindex_stage_w R j))

/-- The comparison `Yⱼ ×_{Yᵢ} Z ⟶ Yⱼ ×_{Y₀} Z` commutes with the projections to `Yⱼ`. -/
theorem reindexComparison_p (j : (D.reindex i).LaterIndex) :
    yoneda.map (reindexComparison R R' j) ≫ R'.p (D.reindexLaterIndex i j) = R.p j := by
  rw [reindexComparison, Functor.map_preimage, IsPullback.lift_fst]

/-- The comparison `Yⱼ ×_{Yᵢ} Z ⟶ Yⱼ ×_{Y₀} Z` commutes with the projections to `Z`. -/
theorem reindexComparison_q (j : (D.reindex i).LaterIndex) :
    reindexComparison R R' j ≫ R'.q (D.reindexLaterIndex i j) = R.q j := by
  apply yoneda.map_injective
  rw [Functor.map_comp, reindexComparison, Functor.map_preimage, IsPullback.lift_snd]

/-- The two morphisms `Y ×_{Yᵢ} Z ⟶ Y₀`, through `Y` and through `Z ⟶ Yᵢ`, agree. -/
theorem reindex_limit_w :
    R.pc ≫ D.limitCone.π.app (op D.i₀) = yoneda.map R.qc ≫ z ≫ D.Y.map (homOfLE i.2).op := by
  rw [← D.limitCone_π_comp i, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ D.Y.map (homOfLE i.2).op) R.isPullback_pt.w

/-- The comparison `Y ×_{Yᵢ} Z ⟶ Y ×_{Y₀} Z`. -/
def reindexComparisonPt : R.c.pt ⟶ R'.c.pt :=
  yoneda.preimage (R'.isPullback_pt.lift R.pc (yoneda.map R.qc) (reindex_limit_w R))

/-- The comparison `Y ×_{Yᵢ} Z ⟶ Y ×_{Y₀} Z` commutes with the projections to `Y`. -/
theorem reindexComparisonPt_p : yoneda.map (reindexComparisonPt R R') ≫ R'.pc = R.pc := by
  rw [reindexComparisonPt, Functor.map_preimage, IsPullback.lift_fst]

/-- The comparison `Y ×_{Yᵢ} Z ⟶ Y ×_{Y₀} Z` commutes with the projections to `Z`. -/
theorem reindexComparisonPt_q : reindexComparisonPt R R' ≫ R'.qc = R.qc := by
  apply yoneda.map_injective
  rw [Functor.map_comp, reindexComparisonPt, Functor.map_preimage, IsPullback.lift_snd]

/-- A comparison to a base change `V₂` that is compatible with a section `s` of `V₂ ⟶ T` is
cartesian over `V₂` and `T`, as soon as it is so after composing with the cartesian map `V₁ ⟶ V₂`
of base changes. -/
private theorem isPullback_of_section_of_isPullback {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E) {A T V₁ V₂ : C} {Y₁ Y₂ Y₃ : E} {m : A ⟶ V₁} {q : A ⟶ T} {w : V₁ ⟶ V₂}
    {s : T ⟶ V₂} [F.Faithful] [ReflectsLimit (cospan w s) F] {r : V₂ ⟶ T}
    {p₁ : F.obj V₁ ⟶ Y₁} {p₂ : F.obj V₂ ⟶ Y₂} {a : F.obj A ⟶ Y₁}
    {t : Y₁ ⟶ Y₂} {g : Y₂ ⟶ Y₃} {u : F.obj T ⟶ Y₂} {z : F.obj T ⟶ Y₃}
    (h₂ : IsPullback p₂ (F.map r) g z) (hw : IsPullback p₁ (F.map w) t p₂)
    (hA : IsPullback a (F.map q) t u) (hm : F.map m ≫ p₁ = a) (hs : F.map s ≫ p₂ = u)
    (hsr : s ≫ r = 𝟙 T) (hmq : m ≫ w ≫ r = q) : IsPullback m q w s := by
  have hcomm : F.map m ≫ F.map w = F.map q ≫ F.map s := by
    refine h₂.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hs, ← hw.w, ← Category.assoc, hm]
      exact hA.w
    · simp only [Category.assoc, ← F.map_comp, hmq, hsr, Category.comp_id]
  refine .of_map_of_faithful F (.of_right ?_ hcomm hw)
  rw [hm, hs]
  exact hA

/-- `Yⱼ ×_{Yᵢ} Z` is the fibre product of `Yⱼ ×_{Y₀} Z` with `Z` over `Yᵢ ×_{Y₀} Z`, along the
graph section. -/
theorem isPullback_reindexComparison (j : (D.reindex i).LaterIndex) :
    IsPullback (reindexComparison R R' j) (R.q j)
      (R'.W.map (homOfLE (show i ≤ D.reindexLaterIndex i j from j.2)).op)
      (reindexSection R') :=
  isPullback_of_section_of_isPullback yoneda (R'.isPullback i)
    (R'.isPullback_map (show i ≤ D.reindexLaterIndex i j from j.2)) (R.isPullback j)
    (reindexComparison_p R R' j) (reindexSection_p R') (reindexSection_q R')
    (by rw [R'.map_q, reindexComparison_q])

/-- `Y ×_{Yᵢ} Z` is the fibre product of `Y ×_{Y₀} Z` with `Z` over `Yᵢ ×_{Y₀} Z`, along the
graph section. -/
theorem isPullback_reindexComparisonPt :
    IsPullback (reindexComparisonPt R R') R.qc (R'.c.π.app (op i)) (reindexSection R') :=
  isPullback_of_section_of_isPullback yoneda (R'.isPullback i) (R'.isPullback_π i)
    R.isPullback_pt (reindexComparisonPt_p R R') (reindexSection_p R') (reindexSection_q R')
    (by rw [R'.π_q, reindexComparisonPt_q])

/-- The comparisons `Yⱼ ×_{Yᵢ} Z ⟶ Yⱼ ×_{Y₀} Z` commute with the transitions. -/
theorem reindexComparison_map {j k : (D.reindex i).LaterIndex} (h : j ≤ k) :
    R.W.map (homOfLE h).op ≫ reindexComparison R R' j =
      reindexComparison R R' k ≫
        R'.W.map (homOfLE (show D.reindexLaterIndex i j ≤ D.reindexLaterIndex i k from h)).op := by
  refine R'.hom_ext ?_ ?_
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, reindexComparison_p,
      R'.map_p, ← Category.assoc, reindexComparison_p]
    exact R.map_p j k h
  · rw [Category.assoc, Category.assoc, reindexComparison_q, R'.map_q, reindexComparison_q]
    exact R.map_q j k h

/-- The comparisons at the stages and at the limit commute with the legs of the cones. -/
theorem reindexComparison_π (j : (D.reindex i).LaterIndex) :
    R.c.π.app (op j) ≫ reindexComparison R R' j =
      reindexComparisonPt R R' ≫ R'.c.π.app (op (D.reindexLaterIndex i j)) := by
  refine R'.hom_ext ?_ ?_
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, reindexComparison_p,
      R'.π_p, ← Category.assoc, reindexComparisonPt_p]
    exact R.π_p j
  · rw [Category.assoc, Category.assoc, reindexComparison_q, R'.π_q, reindexComparisonPt_q]
    exact R.π_q j

variable (D i) in
/-- The stages at or beyond `i`, as a subsystem of the stages at or beyond the chosen one. -/
abbrev reindexInclusion : (D.reindex i).LaterIndex ⥤ D.LaterIndex :=
  Monotone.functor (f := D.reindexLaterIndex i) fun _ _ h => h

/-- The stages at or beyond `i` are cofinal among the stages at or beyond the chosen one. -/
instance final_reindexInclusion : (D.reindexInclusion i).Final := by
  have := (D.reindex i).isDirected_laterIndex
  have := (D.reindex i).nonempty_laterIndex
  refine Functor.final_of_exists_of_isFiltered _ (fun d => ?_)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, Subsingleton.elim _ _⟩)
  obtain ⟨k, hk, hk'⟩ := directed_of (· ≤ ·) d.1 i.1
  exact ⟨⟨k, hk'⟩, ⟨homOfLE hk⟩⟩

/-- **A representation of the base changes along a chart of a later stage is a limit of
schemes** when a representation along the induced chart of the chosen stage is. -/
def isLimitReindex (hR' : IsLimit ((BigFppfOver.toScheme B S hS).mapCone R'.c)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone R.c) := by
  let T := BigFppfOver.toScheme B S hS
  haveI : PreservesLimitsOfShape WalkingCospan T := comp_preservesLimitsOfShape _ _
  let ι := D.reindexInclusion i
  let hL : IsLimit ((T.mapCone R'.c).whisker ι.op) :=
    (Functor.Initial.isLimitWhiskerEquiv ι.op (T.mapCone R'.c)).symm hR'
  exact isLimitOfIsPullbackOfIsLimit (Y' := ι.op ⋙ R'.W ⋙ T) (D.reindex i).initialLaterIndex
    (fun k => k.2) hL (T.map (reindexSection R')) (T.mapCone R.c)
    (fun k => T.map (reindexComparison R R' k)) (fun k => T.map (R.q k))
    (fun k => (isPullback_reindexComparison R R' k).map T)
    (fun j k h => by
      simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
      rw [← T.map_comp, ← T.map_comp, reindexComparison_map R R' h]
      rfl)
    (fun j k h => by
      simp only [Functor.comp_map]
      rw [← T.map_comp, R.map_q j k h])
    (T.map (reindexComparisonPt R R')) (T.map R.qc)
    ((isPullback_reindexComparisonPt R R').map T)
    (fun k => by
      simp only [Functor.mapCone_π_app, Cone.whisker_π, Functor.whiskerLeft_app]
      rw [← T.map_comp, ← T.map_comp, reindexComparison_π R R' k]
      rfl)
    (fun k => by
      simp only [Functor.mapCone_π_app]
      rw [← T.map_comp, R.π_q k])

end Reindex

/-- **The reindexed situation is a limit of schemes on affine charts.**  If the limit of
Situation 0DKU is a limit of schemes on affine charts, so is the limit of the situation reindexed
at a later stage `i`: the projection `Y ⟶ Yᵢ` is affine, as `Y ⟶ Y₀` is and `Yᵢ ⟶ Y₀` is affine,
and a representation of the base changes along a chart `z : Z ⟶ Yᵢ` is the fibre product with
`Z`, along the graph section, of a representation along `Z ⟶ Yᵢ ⟶ Y₀`. -/
theorem isSchemeLimit_reindex (hD : D.IsSchemeLimit) : (D.reindex i).IsSchemeLimit := by
  refine ⟨?_, fun Z z R => ?_⟩
  · refine isAffineHom_of_comp_of_isAffineHom (D.limitCone.π.app (op i.1))
      (D.Y.map (homOfLE i.2).op) ?_ (D.transition_isAffine _ _ i.2)
    rw [D.limitCone_π_comp i]
    exact hD.1
  · let R' := D.affineBaseChangeRepresentation Z (z ≫ D.Y.map (homOfLE i.2).op) hD.1
    obtain ⟨hR'⟩ := hD.2 Z _ R'
    exact ⟨isLimitReindex R R' hR'⟩

end RelativeDescentSituation

end AlgebraicGeometry.Space

end

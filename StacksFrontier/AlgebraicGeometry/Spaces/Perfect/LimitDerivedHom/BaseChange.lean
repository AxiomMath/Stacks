module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.Canonical

/-!
# Base change of the stages of Situation 09RH along a morphism onto the chosen stage

In Situation 09RH let `g : W₀ ⟶ X₀` be a morphism of algebraic spaces onto the chosen stage.
The fibre products `W_i = X_i ×_{X₀} W₀` for `i ≥ 0`, with the base changes of the transition
morphisms, and `W = X ×_{X₀} W₀` with the base changes of the projections, form a system of
algebraic spaces over `W₀` in the sense of `CategoryTheory.PullbackData.LimitSystem`.

This is the system whose colimit statement is the property the source's proof of Stacks 09RI
runs the induction principle of Stacks 08GP on: there `W₀` ranges over the quasi-compact and
quasi-separated objects of `(X₀)_{spaces,étale}`, and the property of `W₀` is that

`colim_{i ≥ 0} Hom_{D(𝒪_{W_i})}(E₀|_{W_i}, K₀|_{W_i}) ⟶ Hom_{D(𝒪_W)}(E₀|_W, K₀|_W)`

is an isomorphism, which is `CategoryTheory.PullbackData.LimitSystem.IsColim` for this system
at the restrictions of `E₀` and `K₀` to `W₀`.  Nothing here is étale-specific, so the
construction takes an arbitrary `g`.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.baseChangeStage` and `baseChangeLimit` are the
  algebraic spaces `W_i = X_i ×_{X₀} W₀` and `W = X ×_{X₀} W₀`.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeToBase`, `baseChangeLimitToBase`,
  `baseChangeToStage`, `baseChangeToLimitSpace`, `baseChangeTransition` and
  `baseChangeProjection` are the projections of those fibre products and the base changes of
  the transition morphisms and of the projections of Situation 09RH.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeSystem` is the system of those spaces
  over `W₀`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.baseChange_hom_ext`: a morphism into a base-changed
  stage is determined by its two projections.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeTransition_comp_toStage`,
  `baseChangeTransition_comp_toBase`, `baseChangeProjection_comp_toStage` and
  `baseChangeProjection_comp_toBase`: the base changes of the transition morphisms and of the
  projections lie over `X_i` and over `W₀`.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeSystem_stage`,
  `baseChangeSystem_limit`, `baseChangeSystem_toBase`, `baseChangeSystem_limitToBase`,
  `baseChangeSystem_transition` and `baseChangeSystem_proj` read off the data of the system.

## Implementation notes

The fibre products are the presheaf fibre products, which are algebraic spaces by Stacks 02X2
(`AlgebraicGeometry.Space.isAlgebraicSpace_pullback`); the category of algebraic spaces over the
base has no `CategoryTheory.Limits.HasPullbacks` instance, so the spaces are assembled by hand
and the morphisms between them are `CategoryTheory.ObjectProperty.homMk` of morphisms of
presheaves.  Accordingly every identity between them is proved by
`CategoryTheory.ObjectProperty.hom_ext` followed by `CategoryTheory.Limits.pullback.hom_ext`,
and the two inputs at the level of presheaves are the composition law of the inverse system and
the naturality of the chosen limiting cone.

A `CategoryTheory.PullbackData.LimitSystem` carries no limiting property of its vertex, and none
is proved here: the base-changed cone is again limiting because the index category of a directed
system is connected, which is
`AlgebraicGeometry.Space.isLimit_baseChangeOverCone`, and it is needed only for the affine case
of the dévissage, not for the induction itself.

## References

* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {W₀ : AlgebraicSpaces B S hS}

/-! ### The base-changed stages -/

/-- **The stage `W_i = X_i ×_{X₀} W₀`** of the base change of Situation 09RH along a morphism
`g : W₀ ⟶ X₀` onto the chosen stage. -/
abbrev baseChangeStage (g : W₀ ⟶ D.stage D.base) (i : D.Stages) : AlgebraicSpaces B S hS :=
  ⟨pullback (D.transition i.2).hom g.hom,
    isAlgebraicSpace_pullback B S hS _ _ (D.stage i.1).property W₀.property
      (D.stage D.base).property⟩

/-- **The vertex `W = X ×_{X₀} W₀`** of the base change of Situation 09RH along a morphism
`g : W₀ ⟶ X₀` onto the chosen stage. -/
abbrev baseChangeLimit (g : W₀ ⟶ D.stage D.base) : AlgebraicSpaces B S hS :=
  ⟨pullback (D.projection D.base).hom g.hom,
    isAlgebraicSpace_pullback B S hS _ _ D.limitSpace.property W₀.property
      (D.stage D.base).property⟩

variable (g : W₀ ⟶ D.stage D.base)

/-- The projection `W_i ⟶ W₀` of the base-changed stage. -/
def baseChangeToBase (i : D.Stages) : baseChangeStage g i ⟶ W₀ :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The projection `W ⟶ W₀` of the base-changed vertex. -/
def baseChangeLimitToBase : baseChangeLimit g ⟶ W₀ :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The projection `W_i ⟶ X_i` of the base-changed stage. -/
def baseChangeToStage (i : D.Stages) : baseChangeStage g i ⟶ D.stage i.1 :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The projection `W ⟶ X` of the base-changed vertex. -/
def baseChangeToLimitSpace : baseChangeLimit g ⟶ D.limitSpace :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- **The base change `W_j ⟶ W_i` of the transition morphism `f_{ji}`**, for `i ≤ j` among the
stages. -/
def baseChangeTransition {i j : D.Stages} (h : i ≤ j) :
    baseChangeStage g j ⟶ baseChangeStage g i :=
  ObjectProperty.homMk (pullback.lift
    (pullback.fst _ _ ≫ (D.transition (show i.1 ≤ j.1 from h)).hom) (pullback.snd _ _) (by
      rw [Category.assoc, show (D.transition (show i.1 ≤ j.1 from h)).hom ≫
        (D.transition i.2).hom = (D.transition j.2).hom from
          congrArg (fun f => f.hom) (D.transition_comp i.2 h j.2)]
      exact pullback.condition))

/-- **The base change `W ⟶ W_i` of the projection `f_i`**, for a stage `i ≥ 0`. -/
def baseChangeProjection (i : D.Stages) : baseChangeLimit g ⟶ baseChangeStage g i :=
  ObjectProperty.homMk (pullback.lift
    (pullback.fst _ _ ≫ (D.projection i.1).hom) (pullback.snd _ _) (by
      rw [Category.assoc, show (D.projection i.1).hom ≫ (D.transition i.2).hom =
        (D.projection D.base).hom from
          congrArg (fun f => f.hom) (D.projection_comp_transition i.2)]
      exact pullback.condition))

/-! ### Morphisms into a base-changed stage -/

/-- **A morphism into a base-changed stage is determined by its two projections.** -/
theorem baseChange_hom_ext {T : AlgebraicSpaces B S hS} {i : D.Stages}
    {a b : T ⟶ baseChangeStage g i}
    (h₁ : a ≫ baseChangeToStage g i = b ≫ baseChangeToStage g i)
    (h₂ : a ≫ baseChangeToBase g i = b ≫ baseChangeToBase g i) : a = b := by
  apply ObjectProperty.hom_ext
  refine pullback.hom_ext ?_ ?_
  · exact congrArg (fun f => f.hom) h₁
  · exact congrArg (fun f => f.hom) h₂

/-- The base change of a transition morphism lies over `X_i`. -/
theorem baseChangeTransition_comp_toStage {i j : D.Stages} (h : i ≤ j) :
    baseChangeTransition g h ≫ baseChangeToStage g i =
      baseChangeToStage g j ≫ D.transition (show i.1 ≤ j.1 from h) :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The base change of a transition morphism lies over `W₀`. -/
theorem baseChangeTransition_comp_toBase {i j : D.Stages} (h : i ≤ j) :
    baseChangeTransition g h ≫ baseChangeToBase g i = baseChangeToBase g j :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- The base change of a projection lies over `X_i`. -/
theorem baseChangeProjection_comp_toStage (i : D.Stages) :
    baseChangeProjection g i ≫ baseChangeToStage g i =
      baseChangeToLimitSpace g ≫ D.projection i.1 :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The base change of a projection lies over `W₀`. -/
theorem baseChangeProjection_comp_toBase (i : D.Stages) :
    baseChangeProjection g i ≫ baseChangeToBase g i = baseChangeLimitToBase g :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-! ### The base-changed system -/

/-- **The base change of the system of stages of Situation 09RH along a morphism
`g : W₀ ⟶ X₀` onto the chosen stage**: the fibre products `W_i = X_i ×_{X₀} W₀` for `i ≥ 0`
with their projections to `W₀`, the base changes of the transition morphisms, and
`W = X ×_{X₀} W₀` with the base changes of the projections.

Its colimit statement `CategoryTheory.PullbackData.LimitSystem.IsColim` at the restrictions of
`E₀` and `K₀` to `W₀` is the property of `W₀` that the source's proof of Stacks 09RI runs the
induction principle of Stacks 08GP on. -/
def baseChangeSystem : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W₀ D.Stages where
  stage i := baseChangeStage g i
  toBase i := baseChangeToBase g i
  transition h := baseChangeTransition g h
  transition_toBase h := baseChangeTransition_comp_toBase g h
  transition_comp h h' := by
    refine baseChange_hom_ext g ?_ ?_
    · rw [Category.assoc, baseChangeTransition_comp_toStage, ← Category.assoc,
        baseChangeTransition_comp_toStage, Category.assoc, D.transition_comp,
        baseChangeTransition_comp_toStage]
    · rw [Category.assoc, baseChangeTransition_comp_toBase, baseChangeTransition_comp_toBase,
        baseChangeTransition_comp_toBase]
  limit := baseChangeLimit g
  limitToBase := baseChangeLimitToBase g
  proj i := baseChangeProjection g i
  proj_toBase i := baseChangeProjection_comp_toBase g i
  proj_transition h := by
    refine baseChange_hom_ext g ?_ ?_
    · rw [Category.assoc, baseChangeTransition_comp_toStage, ← Category.assoc,
        baseChangeProjection_comp_toStage, Category.assoc, D.projection_comp_transition,
        baseChangeProjection_comp_toStage]
    · rw [Category.assoc, baseChangeTransition_comp_toBase, baseChangeProjection_comp_toBase,
        baseChangeProjection_comp_toBase]

/-- The stage of `baseChangeSystem g` at `i` is `baseChangeStage g i`. -/
@[simp]
theorem baseChangeSystem_stage (i : D.Stages) :
    (baseChangeSystem g).stage i = baseChangeStage g i := rfl

/-- The limit of `baseChangeSystem g` is `baseChangeLimit g`. -/
@[simp]
theorem baseChangeSystem_limit : (baseChangeSystem g).limit = baseChangeLimit g := rfl

/-- The structure morphism of `baseChangeSystem g` at `i` is `baseChangeToBase g i`. -/
@[simp]
theorem baseChangeSystem_toBase (i : D.Stages) :
    (baseChangeSystem g).toBase i = baseChangeToBase g i := rfl

/-- The structure morphism of the limit of `baseChangeSystem g` is `baseChangeLimitToBase g`. -/
@[simp]
theorem baseChangeSystem_limitToBase :
    (baseChangeSystem g).limitToBase = baseChangeLimitToBase g := rfl

/-- The transition morphisms of `baseChangeSystem g` are `baseChangeTransition g h`. -/
@[simp]
theorem baseChangeSystem_transition {i j : D.Stages} (h : i ≤ j) :
    (baseChangeSystem g).transition h = baseChangeTransition g h := rfl

/-- The projections of `baseChangeSystem g` are `baseChangeProjection g i`. -/
@[simp]
theorem baseChangeSystem_proj (i : D.Stages) :
    (baseChangeSystem g).proj i = baseChangeProjection g i := rfl

end DescentSituation

end AlgebraicGeometry.Space

end

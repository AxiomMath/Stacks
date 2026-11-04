module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationBaseChangeSpace
public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystemIsoLift

/-!
# Homomorphisms between perfect objects along a base change of Situation 09RH

In Situation 09RH let `y : W ⟶ X₀` be a morphism from a quasi-compact quasi-separated algebraic
space, and let `j ↦ W_j` be a directed system over `W` with a cone `W_∞`, presented as the base
change of the situation along `y`: each `W_j` is a fibre product `X_j ×_{X₀} W` and `W_∞` is
`X ×_{X₀} W`, compatibly with the transition morphisms and the projections
(`AlgebraicGeometry.Space.DescentSituation.BaseChangeData`).  This file proves that for perfect
objects `E` and `K` of `D(𝒪_W)` the homomorphisms between their derived pullbacks to the `W_j`
form a filtered colimit with vertex the homomorphisms between their derived pullbacks to `W_∞`.

The system is identified with the base change
`AlgebraicGeometry.Space.DescentSituation.stagesBaseChangeAlong` of Situation 09RH along `y`,
which is again Situation 09RH, and the statement is
`AlgebraicGeometry.Space.DescentSituation.homDescent_toRelative_of_isPerfect` there, transported
along the identification.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.BaseChangeData`: a presentation of a directed system
  over `W` as the base change of Situation 09RH along `W ⟶ X₀`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.BaseChangeData.isColim_of_isPerfect`.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **A directed system over `W` presented as the base change of Situation 09RH along
`y : W ⟶ X₀`**: morphisms `W_j ⟶ X_j` making each stage a fibre product `X_j ×_{X₀} W`, and
`W_∞ ⟶ X` making the vertex the fibre product `X ×_{X₀} W`, compatibly with the transition
morphisms and the projections. -/
structure BaseChangeData {W : AlgebraicSpaces B S hS} (y : W ⟶ D.stage D.base)
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W D.Stages) where
  /-- The morphism `W_j ⟶ X_j`. -/
  fst : ∀ j : D.Stages, Sys.stage j ⟶ D.stage j.1
  /-- Each stage `W_j` is the fibre product `X_j ×_{X₀} W`. -/
  isPullback : ∀ j : D.Stages,
    IsPullback (fst j).hom (Sys.toBase j).hom (D.transition j.2).hom y.hom
  /-- The morphisms `W_j ⟶ X_j` commute with the transition morphisms. -/
  fst_transition : ∀ {i j : D.Stages} (h : i ≤ j),
    Sys.transition h ≫ fst i = fst j ≫ D.transition (show i.1 ≤ j.1 from h)
  /-- The morphism `W_∞ ⟶ X`. -/
  limitFst : Sys.limit ⟶ D.limitSpace
  /-- The vertex `W_∞` is the fibre product `X ×_{X₀} W`. -/
  limit_isPullback : IsPullback limitFst.hom Sys.limitToBase.hom (D.projection D.base).hom y.hom
  /-- The morphisms `W_∞ ⟶ X` and `W_j ⟶ X_j` commute with the projections. -/
  limitFst_proj : ∀ j : D.Stages, Sys.proj j ≫ fst j = limitFst ≫ D.projection j.1

/-! ### The base change of Situation 09RH along `y` as a system -/

section StagesBaseChange

variable {D} {W : AlgebraicSpaces B S hS} (hWqc : IsQuasiCompactSpace B S hS W.1)
  (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) (y : W ⟶ D.stage D.base)

variable (D) in
/-- A morphism `W ⟶ X₀`, read as a point of the chosen stage of the restricted system of
Situation 09RH. -/
def stagePoint (y : W ⟶ D.stage D.base) : W.1 ⟶ (stagesSystem D).obj (op (baseStage D)) :=
  y.hom

/-- The projection of a stage of the base change along `y` to `W`. -/
def stagesBaseChangeSnd (j : D.Stages) :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).stage j ⟶ W :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The projection of a stage of the base change along `y` to the stage of Situation 09RH. -/
def stagesBaseChangeFst (j : D.Stages) :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).stage j ⟶ D.stage j.1 :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The projection of the limit of the base change along `y` to `W`. -/
def stagesBaseChangeLimitSnd :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).limitSpace ⟶ W :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The projection of the limit of the base change along `y` to the limit of Situation 09RH. -/
def stagesBaseChangeLimitFst :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).limitSpace ⟶ D.limitSpace :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- A stage of the base change along `y` is the fibre product of the stage of Situation 09RH and
`W` over `X₀`. -/
theorem isPullback_stagesBaseChange (j : D.Stages) :
    IsPullback (stagesBaseChangeFst hWqc hWqs y j).hom (stagesBaseChangeSnd hWqc hWqs y j).hom
      ((stagesToBase D).app (op j)) (stagePoint D y) :=
  IsPullback.of_hasPullback _ _

/-- The limit of the base change along `y` is the fibre product of the limit of Situation 09RH
and `W` over `X₀`. -/
theorem isPullback_stagesBaseChangeLimit :
    IsPullback (stagesBaseChangeLimitFst hWqc hWqs y).hom (stagesBaseChangeLimitSnd hWqc hWqs y).hom
      ((stagesCone D).π.app (op (baseStage D))) (stagePoint D y) :=
  IsPullback.of_hasPullback _ _

/-- The projections to `W` of the stages of the base change along `y` commute with the
transition morphisms. -/
@[reassoc]
theorem stagesBaseChange_transition_snd {i j : D.Stages} (h : i ≤ j) :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).transition h ≫
        stagesBaseChangeSnd hWqc hWqs y i = stagesBaseChangeSnd hWqc hWqs y j :=
  ObjectProperty.hom_ext _ (baseChangeOverSystem_map_snd B S hS (stagesSystem D) (stagesToBase D)
    (stagePoint D y) (homOfLE h).op)

/-- The projections of the stages of the base change along `y` to the stages of Situation 09RH
commute with the transition morphisms. -/
@[reassoc]
theorem stagesBaseChange_transition_fst {i j : D.Stages} (h : i ≤ j) :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).transition h ≫
        stagesBaseChangeFst hWqc hWqs y i =
      stagesBaseChangeFst hWqc hWqs y j ≫ D.transition (show i.1 ≤ j.1 from h) :=
  ObjectProperty.hom_ext _ (baseChangeOverSystem_map_fst B S hS (stagesSystem D) (stagesToBase D)
    (stagePoint D y) (homOfLE h).op)

/-- The projection to `W` of the limit of the base change along `y` factors through each stage. -/
@[reassoc]
theorem stagesBaseChange_projection_snd (j : D.Stages) :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).projection j ≫
        stagesBaseChangeSnd hWqc hWqs y j = stagesBaseChangeLimitSnd hWqc hWqs y :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- The projections of the limit and the stages of the base change along `y` to Situation 09RH
commute with the projections from the limits. -/
@[reassoc]
theorem stagesBaseChange_projection_fst (j : D.Stages) :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).projection j ≫
        stagesBaseChangeFst hWqc hWqs y j =
      stagesBaseChangeLimitFst hWqc hWqs y ≫ D.projection j.1 :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

end StagesBaseChange

/-! ### Full faithfulness for a base change -/

section BaseChangeData

variable {D} {W : AlgebraicSpaces B S hS} {hWqc : IsQuasiCompactSpace B S hS W.1}
  {hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1} {y : W ⟶ D.stage D.base}
  {Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W D.Stages}
  (β : D.BaseChangeData y Sys)

namespace BaseChangeData

/-- Each stage `W_j` of the presented system is the fibre product of the stage `X_j` of the
restricted system of Situation 09RH and `W` over `X₀`. -/
theorem isPullback_stagesToBase (j : D.Stages) :
    IsPullback (β.fst j).hom (Sys.toBase j).hom ((stagesToBase D).app (op j)) (stagePoint D y) :=
  β.isPullback j

/-- The vertex `W_∞` of the presented system is the fibre product of the limit `X` and `W` over
`X₀`. -/
theorem limit_isPullback_stagesCone :
    IsPullback β.limitFst.hom Sys.limitToBase.hom ((stagesCone D).π.app (op (baseStage D)))
      (stagePoint D y) :=
  β.limit_isPullback

/-- The stage of the presented system is the stage of the base change of Situation 09RH. -/
def stageIso (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) (j : D.Stages) :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).stage j ≅ Sys.stage j :=
  ObjectProperty.isoMk _ ((isPullback_stagesBaseChange hWqc hWqs y j).isoIsPullback _ _
    (β.isPullback_stagesToBase j))

/-- The isomorphism `stageIso` is compatible with the projections to `W`. -/
@[reassoc]
theorem stageIso_hom_toBase (j : D.Stages) :
    (β.stageIso hWqc hWqs j).hom ≫ Sys.toBase j = stagesBaseChangeSnd hWqc hWqs y j :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_snd _ _ _ _)

/-- The isomorphism `stageIso` is compatible with the morphisms to the stage of Situation 09RH. -/
@[reassoc]
theorem stageIso_hom_fst (j : D.Stages) :
    (β.stageIso hWqc hWqs j).hom ≫ β.fst j = stagesBaseChangeFst hWqc hWqs y j :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- The vertex of the presented system is the limit of the base change of Situation 09RH. -/
def limitIso (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) :
    (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).limitSpace ≅ Sys.limit :=
  ObjectProperty.isoMk _ ((isPullback_stagesBaseChangeLimit hWqc hWqs y).isoIsPullback _ _
    β.limit_isPullback_stagesCone)

/-- The isomorphism `limitIso` is compatible with the projections to `W`. -/
@[reassoc]
theorem limitIso_hom_toBase :
    (β.limitIso hWqc hWqs).hom ≫ Sys.limitToBase = stagesBaseChangeLimitSnd hWqc hWqs y :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_snd _ _ _ _)

/-- The isomorphism `limitIso` is compatible with the morphisms to the limit of Situation 09RH. -/
@[reassoc]
theorem limitIso_hom_fst :
    (β.limitIso hWqc hWqs).hom ≫ β.limitFst = stagesBaseChangeLimitFst hWqc hWqs y :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- Two morphisms into a stage `W_j` agree when their composites to `X_j` and to `W` agree. -/
theorem stage_hom_ext (j : D.Stages) {T : AlgebraicSpaces B S hS} {a b : T ⟶ Sys.stage j}
    (h₁ : a ≫ β.fst j = b ≫ β.fst j) (h₂ : a ≫ Sys.toBase j = b ≫ Sys.toBase j) : a = b :=
  ObjectProperty.hom_ext _ ((β.isPullback j).hom_ext (congrArg (fun φ => φ.hom) h₁)
    (congrArg (fun φ => φ.hom) h₂))

/-- **The base change of Situation 09RH along `y`, read over `W`, maps isomorphically onto the
presented system** (on the stages beyond the chosen one, which are all of them). -/
def homToSystem (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) :
    PullbackData.LimitSystem.Hom
      ((D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).toRelative.toLimitSystem.comp
        (stagesBaseChangeSnd hWqc hWqs y (baseStage D)))
      (Sys.restrictIndex (baseStage D)) where
  app k := (β.stageIso hWqc hWqs k.1).hom
  app_toBase k := by
    change (β.stageIso hWqc hWqs k.1).hom ≫ Sys.toBase k.1 =
      (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).transition
          (show baseStage D ≤ k.1 from k.2) ≫ stagesBaseChangeSnd hWqc hWqs y (baseStage D)
    rw [stageIso_hom_toBase, stagesBaseChange_transition_snd]
  app_transition {i j} h := by
    change (β.stageIso hWqc hWqs j.1).hom ≫ Sys.transition h =
      (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).transition h ≫
        (β.stageIso hWqc hWqs i.1).hom
    refine β.stage_hom_ext i.1 ?_ ?_
    · rw [Category.assoc, β.fst_transition, stageIso_hom_fst_assoc, Category.assoc,
        stageIso_hom_fst, stagesBaseChange_transition_fst]
    · rw [Category.assoc, Sys.transition_toBase, stageIso_hom_toBase, Category.assoc,
        stageIso_hom_toBase, stagesBaseChange_transition_snd]
  limitApp := (β.limitIso hWqc hWqs).hom
  limitApp_toBase := by
    change (β.limitIso hWqc hWqs).hom ≫ Sys.limitToBase =
      (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).projection (baseStage D) ≫
        stagesBaseChangeSnd hWqc hWqs y (baseStage D)
    rw [limitIso_hom_toBase, stagesBaseChange_projection_snd]
  limitApp_proj k := by
    change (β.limitIso hWqc hWqs).hom ≫ Sys.proj k.1 =
      (D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).projection k.1 ≫
        (β.stageIso hWqc hWqs k.1).hom
    refine β.stage_hom_ext k.1 ?_ ?_
    · rw [Category.assoc, β.limitFst_proj, limitIso_hom_fst_assoc, Category.assoc,
        stageIso_hom_fst, stagesBaseChange_projection_fst]
    · rw [Category.assoc, Sys.proj_toBase, limitIso_hom_toBase, Category.assoc,
        stageIso_hom_toBase, stagesBaseChange_projection_snd]

include β in
/-- **Stacks 09RI for perfect objects, along a base change of Situation 09RH**: for perfect
objects `E` and `K` of `D(𝒪_W)`, `Hom(Lk^*E, Lk^*K)` is the filtered colimit of the
`Hom(Lk_j^*E, Lk_j^*K)`. -/
theorem isColim_of_isPerfect (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (hWqc : IsQuasiCompactSpace B S hS W.1) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (X Y : @DerivedCategory (Modules.{u, u} B S hS W.1 W.2) _ _ (HasDerivedCategory.standard _))
    (hX : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS W.1 W.2)
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect X)
    (hY : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS W.1 W.2)
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect Y) :
    Sys.IsColim (DerivedPullbackComposition.canonical B S hS).toPullbackData X Y := by
  have hP := (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
  set Db := D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)
  set f := stagesBaseChangeSnd hWqc hWqs y (baseStage D)
  have hF := Db.homDescent_toRelative_of_isPerfect
    (D.siteContainsBaseChangeLimits_stagesBaseChangeAlong hconv W.2 hWqc hWqs (stagePoint D y)) _ _
    (isPerfect_smallEtaleDerivedModulePullback f X hX)
    (isPerfect_smallEtaleDerivedModulePullback f Y hY)
  have hF' := (Db.toRelative.homDescent_iff_isColim _ _ _).1 hF
  have h₂ := (PullbackData.LimitSystem.isColim_comp_iff (S := Db.toRelative.toLimitSystem)
    hP f X Y).2 hF'
  have h₃ := (PullbackData.LimitSystem.Hom.isColim_iff (β.homToSystem hWqc hWqs) X Y hP
    (fun k => PullbackData.bijective_factorHom_of_fullyFaithful _ _
      (smallEtaleDerivedModulePullbackEquivalence B S hS
        (β.stageIso hWqc hWqs k.1)).fullyFaithfulFunctor _ _)
    (PullbackData.bijective_factorHom_of_fullyFaithful _ _
      (smallEtaleDerivedModulePullbackEquivalence B S hS
        (β.limitIso hWqc hWqs)).fullyFaithfulFunctor _ _)).2 h₂
  exact PullbackData.LimitSystem.isColim_of_restrictIndex hP (baseStage D) h₃

end BaseChangeData

end BaseChangeData

end DescentSituation

end AlgebraicGeometry.Space

end

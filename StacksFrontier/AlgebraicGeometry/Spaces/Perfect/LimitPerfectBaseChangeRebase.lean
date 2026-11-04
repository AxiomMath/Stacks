module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectHomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# Presentations of directed systems as base changes of Situation 09RH

In Situation 09RH a directed system `j ↦ W_j` over an algebraic space `W` with a cone `W_∞` is
*presented* along `y : W ⟶ X₀` when each `W_j` is `X_j ×_{X₀} W` and `W_∞` is `X ×_{X₀} W`
(`AlgebraicGeometry.Space.DescentSituation.BaseChangeData`).  This file records three ways of
producing presentations and one consequence.

* Situation 09RH presents its own stages along the identity of `X₀`.
* A presentation pulls back: if `W'_j` is `W' ×_W W_j` for a morphism `W' ⟶ W`, compatibly with
  the transition morphisms and the projections, then the system `j ↦ W'_j` is presented along
  `W' ⟶ W ⟶ X₀`.
* A presentation may be read beyond one of its stages: the stages `W_j` for `j ≥ i` form a
  system over `W_i` presented along `W_i ⟶ X_i`, for Situation 09RH with its chosen index moved
  to `i`.
* If `W` is quasi-compact and quasi-separated, then so is every stage `W_j`: it is a stage of the
  base change of Situation 09RH along `y`.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.withBase`: Situation 09RH with its chosen index moved.
* `AlgebraicGeometry.Space.DescentSituation.stagesLimitSystem` and `stagesBaseChangeData`: the
  stages of Situation 09RH as a presented system over the chosen stage.
* `AlgebraicGeometry.Space.DescentSituation.BaseChangeData.ofIsPullback`: pulling a presentation
  back.
* `AlgebraicGeometry.Space.DescentSituation.rebaseSystem` and `BaseChangeData.rebase`: a
  presentation read beyond one of its stages.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.BaseChangeData.isQuasiCompactSpace_stage` and
  `isAbsolutelyQuasiSeparated_stage`.

## References

* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Situation 09RH with its chosen index moved to `i`.** -/
abbrev withBase (i : I) : DescentSituation B S hS hZ I := { D with base := i }

/-- A stage beyond `i`, for `i` a stage of Situation 09RH, read as a stage of Situation 09RH. -/
abbrev stageOfLE (i : D.Stages) (j : (D.withBase i.1).Stages) : D.Stages := ⟨j.1, i.2.trans j.2⟩

/-- The stage `D.stageOfLE i j` lies beyond `i`. -/
theorem le_stageOfLE (i : D.Stages) (j : (D.withBase i.1).Stages) : i ≤ D.stageOfLE i j := j.2

/-! ### The stages of Situation 09RH as a presented system -/

/-- **The stages of Situation 09RH, as a system over the chosen stage.** -/
abbrev stagesLimitSystem :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) (D.stage D.base) D.Stages where
  stage j := D.stage j.1
  toBase j := D.transition j.2
  transition {i j} h := D.transition (show i.1 ≤ j.1 from h)
  transition_toBase _ := D.transition_comp _ _ _
  transition_comp _ _ := D.transition_comp _ _ _
  limit := D.limitSpace
  limitToBase := D.projection D.base
  proj j := D.projection j.1
  proj_toBase _ := D.projection_comp_transition _
  proj_transition _ := D.projection_comp_transition _

/-- **Situation 09RH presents its own stages**, along the identity of the chosen stage. -/
def stagesBaseChangeData : D.BaseChangeData (𝟙 _) D.stagesLimitSystem where
  fst _ := 𝟙 _
  isPullback j := IsPullback.id_horiz (D.transition j.2).hom
  fst_transition _ := (Category.comp_id _).trans (Category.id_comp _).symm
  limitFst := 𝟙 _
  limit_isPullback := IsPullback.id_horiz (D.projection D.base).hom
  limitFst_proj _ := (Category.comp_id _).trans (Category.id_comp _).symm

variable {D}

/-! ### Pulling a presentation back -/

/-- **A presentation pulls back.**  If `W'_j = W' ×_W W_j` and `W'_∞ = W' ×_W W_∞` for a
morphism `y' : W' ⟶ W`, compatibly with the transition morphisms and the projections, then the
system `j ↦ W'_j` is presented along `y' ≫ y`. -/
def BaseChangeData.ofIsPullback {W W' : AlgebraicSpaces B S hS} {y : W ⟶ D.stage D.base}
    {Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W D.Stages}
    (β : D.BaseChangeData y Sys) (y' : W' ⟶ W) {y'' : W' ⟶ D.stage D.base} (hy : y' ≫ y = y'')
    {Sys' : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W' D.Stages}
    (g : ∀ j, Sys'.stage j ⟶ Sys.stage j)
    (hg : ∀ j, IsPullback (g j).hom (Sys'.toBase j).hom (Sys.toBase j).hom y'.hom)
    (hgt : ∀ {i j : D.Stages} (h : i ≤ j), Sys'.transition h ≫ g i = g j ≫ Sys.transition h)
    (gl : Sys'.limit ⟶ Sys.limit)
    (hgl : IsPullback gl.hom Sys'.limitToBase.hom Sys.limitToBase.hom y'.hom)
    (hglp : ∀ j, Sys'.proj j ≫ g j = gl ≫ Sys.proj j) :
    D.BaseChangeData y'' Sys' where
  fst j := g j ≫ β.fst j
  isPullback j := by
    subst hy
    exact (hg j).paste_horiz (β.isPullback j)
  fst_transition h := by
    rw [reassoc_of% (hgt h), β.fst_transition, Category.assoc]
  limitFst := gl ≫ β.limitFst
  limit_isPullback := by
    subst hy
    exact hgl.paste_horiz β.limit_isPullback
  limitFst_proj j := by
    rw [reassoc_of% (hglp j), β.limitFst_proj, Category.assoc]

/-! ### A presentation read beyond one of its stages -/

variable {W : AlgebraicSpaces B S hS}

variable (D) in
/-- **A system over `W` read beyond its stage `i`**, as a system over `W_i` indexed by the stages
of Situation 09RH with its chosen index moved to `i`. -/
abbrev rebaseSystem (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W D.Stages)
    (i : D.Stages) :
    PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) (Sys.stage i) (D.withBase i.1).Stages
    where
  stage j := Sys.stage (D.stageOfLE i j)
  toBase j := Sys.transition (D.le_stageOfLE i j)
  transition {j k} h := Sys.transition (show D.stageOfLE i j ≤ D.stageOfLE i k from h)
  transition_toBase _ := Sys.transition_comp _ _
  transition_comp _ _ := Sys.transition_comp _ _
  limit := Sys.limit
  limitToBase := Sys.proj i
  proj j := Sys.proj (D.stageOfLE i j)
  proj_toBase _ := Sys.proj_transition _
  proj_transition _ := Sys.proj_transition _

variable {y : W ⟶ D.stage D.base}
  {Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) W D.Stages}

/-- **A presentation read beyond its stage `i`**: the stages `W_j` for `j ≥ i` are presented
along `W_i ⟶ X_i`, for Situation 09RH with its chosen index moved to `i`. -/
def BaseChangeData.rebase (β : D.BaseChangeData y Sys) (i : D.Stages) :
    (D.withBase i.1).BaseChangeData (β.fst i) (D.rebaseSystem Sys i) where
  fst j := β.fst (D.stageOfLE i j)
  isPullback j := by
    have h₁ : IsPullback (β.fst (D.stageOfLE i j)).hom
        ((Sys.transition (D.le_stageOfLE i j)).hom ≫ (Sys.toBase i).hom)
        ((D.transition j.2).hom ≫ (D.transition i.2).hom) y.hom := by
      have h := β.isPullback (D.stageOfLE i j)
      rwa [← Sys.transition_toBase (D.le_stageOfLE i j),
        ← D.transition_comp i.2 j.2 (i.2.trans j.2)] at h
    exact h₁.of_bot (congrArg (fun φ => φ.hom) (β.fst_transition (D.le_stageOfLE i j))).symm
      (β.isPullback i)
  fst_transition h := β.fst_transition h
  limitFst := β.limitFst
  limit_isPullback := by
    have h₁ : IsPullback β.limitFst.hom ((Sys.proj i).hom ≫ (Sys.toBase i).hom)
        ((D.projection i.1).hom ≫ (D.transition i.2).hom) y.hom := by
      have h := β.limit_isPullback
      rwa [← Sys.proj_toBase i, ← D.projection_comp_transition i.2] at h
    exact h₁.of_bot (congrArg (fun φ => φ.hom) (β.limitFst_proj i)).symm (β.isPullback i)
  limitFst_proj j := β.limitFst_proj (D.stageOfLE i j)

/-! ### Finiteness of the stages -/

/-- **The stages of a presented system over a quasi-compact quasi-separated algebraic space are
quasi-compact.** -/
theorem BaseChangeData.isQuasiCompactSpace_stage (β : D.BaseChangeData y Sys)
    (hWqc : IsQuasiCompactSpace B S hS W.1) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (j : D.Stages) : IsQuasiCompactSpace B S hS (Sys.stage j).1 :=
  isQuasiCompactSpace_of_iso B S hS ((ObjectProperty.ι _).mapIso (β.stageIso hWqc hWqs j))
    ((D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).quasiCompact j)

/-- **The stages of a presented system over a quasi-compact quasi-separated algebraic space are
quasi-separated.** -/
theorem BaseChangeData.isAbsolutelyQuasiSeparated_stage (β : D.BaseChangeData y Sys)
    (hWqc : IsQuasiCompactSpace B S hS W.1) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (j : D.Stages) : IsAbsolutelyQuasiSeparated B S hS hZ (Sys.stage j).1 :=
  isAbsolutelyQuasiSeparated_of_iso B S hS hZ (Sys.stage j).2
    ((ObjectProperty.ι _).mapIso (β.stageIso hWqc hWqs j)).symm
    ((D.stagesBaseChangeAlong W.2 hWqc hWqs (stagePoint D y)).quasiSeparated j)

end DescentSituation

end AlgebraicGeometry.Space

end

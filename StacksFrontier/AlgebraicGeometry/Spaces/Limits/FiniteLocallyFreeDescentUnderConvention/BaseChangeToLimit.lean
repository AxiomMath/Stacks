module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.LinearAlgebra.Basis.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.AlgebraicGeometry.Limits.EtaleChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeStageModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StructureSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# Base changes of the charts of a stage to the limit

For a cofiltered system of algebraic spaces satisfying the chapter's convention, the base change
to the limit of an étale chart of a stage, its comparison with the base changes to the later
stages, and the descent of regular functions on it to a stage.
-/

/-! ## The base changes of the charts of a stage to the limit -/

noncomputable section

open CategoryTheory Opposite Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hconv : SiteContainsBaseChangeLimits B S hS D)
  (hQcL : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-- The limit of the system, as an object of the category of algebraic spaces over `S`; it is
an algebraic space by Stacks 07SF under the chapter's convention. -/
private def convLimitSpace : AlgebraicSpaces B S hS :=
  ⟨limit D, isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD hAffine hQcL⟩

/-- The projection of the limit to a stage, as a morphism of algebraic spaces over `S`. -/
private def convLimitProjection (i : I) :
    convLimitSpace B S hS D hconv hQcL hD hAffine ⟶ stageAlgebraicSpace B S hS D hD i :=
  ObjectProperty.homMk (limit.π D i)

include hAffine in
private theorem Conv.rep_limitProjection (i : I) :
    yoneda.relativelyRepresentable (convLimitProjection B S hS D hconv hQcL hD hAffine i).hom :=
  relativelyRepresentable_hom_of_isAffineHom B S hS _
    (isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D hconv hAffine i)

variable {j : I} (T : SmallEtale B S hS (D.obj j))

/-- The base change of an étale chart of a stage to the limit. -/
private abbrev Conv.limChart : SmallEtale B S hS (convLimitSpace B S hS D hconv hQcL hD hAffine).1
    :=
  (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine j)
    (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j)).obj T

private theorem Conv.limToStage_cond (s : Over j) :
    ((Conv.limChart B S hS D hconv hQcL hD hAffine T).obj.hom ≫ limit.π D s.left) ≫
        (stageTransition B S hS D hD s.hom).hom =
      yoneda.map (sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j) T) ≫
        T.obj.hom :=
  (Category.assoc _ _ _).trans ((congrArg _ (limit.w D s.hom)).trans
    (sbc_w (convLimitProjection B S hS D hconv hQcL hD hAffine j)
      (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j) T).symm)

/-- The projection of the base change to the limit onto the base change to a stage. -/
private def Conv.limToStage (s : Over j) :
    (Conv.limChart B S hS D hconv hQcL hD hAffine T).obj.left ⟶
      (laterStageChart B S hS D hD hAffine T s).obj.left :=
  (rep_stageTransition B S hS D hD hAffine s.hom).lift _ _
    (Conv.limToStage_cond B S hS D hconv hQcL hD hAffine T s)

@[reassoc]
private theorem Conv.limToStage_proj (s : Over j) :
    Conv.limToStage B S hS D hconv hQcL hD hAffine T s ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T =
      sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j) T :=
  Functor.relativelyRepresentable.lift_snd _ _ _ _

@[reassoc]
private theorem Conv.limToStage_chart (s : Over j) :
    yoneda.map (Conv.limToStage B S hS D hconv hQcL hD hAffine T s) ≫
        (laterStageChart B S hS D hD hAffine T s).obj.hom =
      (Conv.limChart B S hS D hconv hQcL hD hAffine T).obj.hom ≫ limit.π D s.left :=
  Functor.relativelyRepresentable.lift_fst _ _ _ _

private theorem Conv.limToStage_stageToStage {s s' : Over j} (d : s' ⟶ s) :
    Conv.limToStage B S hS D hconv hQcL hD hAffine T s' ≫ stageToStage B S hS D hD hAffine T d =
      Conv.limToStage B S hS D hconv hQcL hD hAffine T s := by
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · show yoneda.map (Conv.limToStage B S hS D hconv hQcL hD hAffine T s' ≫
        stageToStage B S hS D hD hAffine T d) ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom =
      yoneda.map (Conv.limToStage B S hS D hconv hQcL hD hAffine T s) ≫
        (laterStageChart B S hS D hD hAffine T s).obj.hom
    exact (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom)
      (Functor.map_comp yoneda _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (stageToStage_chart B S hS D hD hAffine T d)).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.map d.left) (Conv.limToStage_chart B S hS D hconv hQcL hD hAffine T
          s')).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (limit.w D d.left)).trans
      (Conv.limToStage_chart B S hS D hconv hQcL hD hAffine T s).symm))))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (stageToStage_proj B S hS D hD hAffine T d)).trans
      ((Conv.limToStage_proj B S hS D hconv hQcL hD hAffine T s').trans
        (Conv.limToStage_proj B S hS D hconv hQcL hD hAffine T s).symm))

/-- The base change to the limit of the base change to a stage. -/
private abbrev Conv.stageLimChart (s : Over j) :
    SmallEtale B S hS (convLimitSpace B S hS D hconv hQcL hD hAffine).1 :=
  (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s.left)
    (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)).obj
    (laterStageChart B S hS D hD hAffine T s)

private theorem Conv.stageToLim_cond (s : Over j) :
    yoneda.map (sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s) ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T) ≫ T.obj.hom =
      (Conv.stageLimChart B S hS D hconv hQcL hD hAffine T s).obj.hom ≫
        (convLimitProjection B S hS D hconv hQcL hD hAffine j).hom :=
  calc _ = yoneda.map (sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s)) ≫
        (yoneda.map (sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T) ≫ T.obj.hom) := by
        rw [Functor.map_comp, Category.assoc]
    _ = yoneda.map (sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s)) ≫ ((laterStageChart B S hS D hD hAffine T
            s).obj.hom ≫
          D.map s.hom) :=
        congrArg (_ ≫ ·) (sbc_w (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom) T)
    _ = (yoneda.map (sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T
            s)) ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom) ≫
          D.map s.hom := (Category.assoc _ _ _).symm
    _ = ((Conv.stageLimChart B S hS D hconv hQcL hD hAffine T s).obj.hom ≫ limit.π D s.left) ≫
          D.map s.hom :=
        congrArg (· ≫ D.map s.hom) (sbc_w (convLimitProjection B S hS D hconv hQcL hD hAffine
            s.left)
          (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
          (laterStageChart B S hS D hD hAffine T s))
    _ = _ := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (limit.w D s.hom))

/-- The comparison of the base change to the limit of the base change to a stage with the base
change to the limit. -/
private def Conv.stageToLim (s : Over j) :
    Conv.stageLimChart B S hS D hconv hQcL hD hAffine T s ⟶ Conv.limChart B S hS D hconv hQcL hD
        hAffine T :=
  sbcLift _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j) _
    (Conv.stageToLim_cond B S hS D hconv hQcL hD hAffine T s)

private theorem Conv.stageToLim_proj (s : Over j) :
    (Conv.stageToLim B S hS D hconv hQcL hD hAffine T s).hom.left ≫
        sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j) T =
      sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
          (laterStageChart B S hS D hD hAffine T s) ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T :=
  sbcLift_proj _ _ _ _

/-- **The comparison followed by the projection to the stage is the projection.** -/
private theorem Conv.stageToLim_limToStage (s : Over j) :
    (Conv.stageToLim B S hS D hconv hQcL hD hAffine T s).hom.left ≫
        Conv.limToStage B S hS D hconv hQcL hD hAffine T s =
      sbcProj _ (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s) := by
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · have h1 := Conv.limToStage_chart B S hS D hconv hQcL hD hAffine T s
    have h2 := CostructuredArrow.w (Conv.stageToLim B S hS D hconv hQcL hD hAffine T s).hom
    have h3 := sbc_w (convLimitProjection B S hS D hconv hQcL hD hAffine s.left)
      (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
      (laterStageChart B S hS D hD hAffine T s)
    exact (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom)
      (Functor.map_comp yoneda _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ limit.π D s.left) h2).trans h3.symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (Conv.limToStage_proj B S hS D hconv hQcL hD hAffine T s)).trans
      (Conv.stageToLim_proj B S hS D hconv hQcL hD hAffine T s))

/-! ### Naturality in the chart -/

section Naturality

variable {T} {T' : SmallEtale B S hS (D.obj j)} (h : T ⟶ T')

private theorem Conv.limToStage_naturality (s : Over j) :
    ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine j)
        (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j)).map h).hom.left ≫
        Conv.limToStage B S hS D hconv hQcL hD hAffine T' s =
      Conv.limToStage B S hS D hconv hQcL hD hAffine T s ≫
        ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom)).map h).hom.left := by
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · have h1 := Conv.limToStage_chart B S hS D hconv hQcL hD hAffine T' s
    have h2 := Conv.limToStage_chart B S hS D hconv hQcL hD hAffine T s
    have h3 := CostructuredArrow.w ((smallBaseChange B S hS (convLimitProjection B S hS D hconv
      hQcL hD hAffine j) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j)).map h).hom
    have h4 := CostructuredArrow.w ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom)).map h).hom
    exact (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T' s).obj.hom)
      (Functor.map_comp yoneda _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ limit.π D s.left) h3).trans (h2.symm.trans
      ((congrArg (_ ≫ ·) h4).symm.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T' s).obj.hom)
        (Functor.map_comp yoneda _ _).symm))))))))
  · have h1 := Conv.limToStage_proj B S hS D hconv hQcL hD hAffine T' s
    have h2 := Conv.limToStage_proj B S hS D hconv hQcL hD hAffine T s
    have h3 := smallBaseChange_map_proj (convLimitProjection B S hS D hconv hQcL hD hAffine j)
      (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j) h
    have h4 := smallBaseChange_map_proj (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom) h
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans (h3.trans
      ((congrArg (· ≫ h.hom.left) h2).symm.trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h4).symm.trans (Category.assoc _ _ _).symm)))))

private theorem Conv.stageToLim_naturality (s : Over j) :
    (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s.left)
        (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)).map
        ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom)).map h) ≫
        Conv.stageToLim B S hS D hconv hQcL hD hAffine T' s =
      Conv.stageToLim B S hS D hconv hQcL hD hAffine T s ≫
        (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine j)
          (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j)).map h := by
  apply sbc_hom_ext
  have h1 := Conv.stageToLim_proj B S hS D hconv hQcL hD hAffine T' s
  have h2 := Conv.stageToLim_proj B S hS D hconv hQcL hD hAffine T s
  have h3 := smallBaseChange_map_proj (convLimitProjection B S hS D hconv hQcL hD hAffine j)
    (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j) h
  have h4 := smallBaseChange_map_proj (stageTransition B S hS D hD s.hom)
    (rep_stageTransition B S hS D hD hAffine s.hom) h
  have h5 := smallBaseChange_map_proj (convLimitProjection B S hS D hconv hQcL hD hAffine s.left)
    (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)
    ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom)).map h)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h5).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h4).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h.hom.left) h2).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h3).symm.trans
      (Category.assoc _ _ _).symm)))))))))

end Naturality

/-! ### The system of base changes as a diagram of presheaves -/

/-- The base change to the limit represents the presheaf base change. -/
private def Conv.limChartIso :
    yoneda.obj (Conv.limChart B S hS D hconv hQcL hD hAffine T).obj.left ≅ (stageChartCone B S hS D
        T).pt :=
  ((Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j).isPullback T.obj.hom).isoPullback

private theorem Conv.limChartIso_comp (s : Over j) :
    (Conv.limChartIso B S hS D hconv hQcL hD hAffine T).hom ≫ (stageChartCone B S hS D T).π.app s =
      yoneda.map (Conv.limToStage B S hS D hconv hQcL hD hAffine T s) ≫
        (stageChartIso B S hS D hD hAffine T s).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, stageChartCone_π_fst, Category.assoc]
    refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
    exact (congrArg (· ≫ limit.π D s.left) (IsPullback.isoPullback_hom_fst _)).trans
      ((Conv.limToStage_chart B S hS D hconv hQcL hD hAffine T s).symm.trans
        (congrArg (_ ≫ ·) (IsPullback.isoPullback_hom_fst _).symm))
  · rw [Category.assoc, stageChartCone_π_snd, Category.assoc]
    exact (IsPullback.isoPullback_hom_snd _).trans ((congrArg yoneda.map
      (Conv.limToStage_proj B S hS D hconv hQcL hD hAffine T s).symm).trans
      ((Functor.map_comp yoneda _ _).trans
        (congrArg (_ ≫ ·) (IsPullback.isoPullback_hom_snd _).symm)))

/-! ### Descent of regular functions -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
  (hTqc : IsQuasiCompactSpace B S hS (yoneda.obj T.obj.left))
  (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T.obj.left))

/-- The transition morphisms of the base changes of a chart to the later stages are base changes
of the transition morphisms of the system. -/
private theorem stageChartDiagram_isPullback {s s' : Over j} (d : s' ⟶ s) :
    IsPullback ((stageChartDiagram B S hS D T).map d) (pullback.fst _ _) (pullback.fst _ _)
      (D.map d.left) := by
  have t : IsPullback (pullback.snd _ _) (pullback.fst _ _) T.obj.hom (D.map s.hom) :=
    (IsPullback.of_hasPullback (D.map s.hom) T.obj.hom).flip
  have outer : IsPullback ((stageChartDiagram B S hS D T).map d ≫ pullback.snd _ _)
      (pullback.fst _ _) T.obj.hom (D.map d.left ≫ D.map s.hom) := by
    rw [stageChartDiagram_map_snd]
    show IsPullback (pullback.snd (D.map s'.hom) T.obj.hom)
      (pullback.fst (D.map s'.hom) T.obj.hom) T.obj.hom (D.map d.left ≫ D.map s.hom)
    rw [← D.map_comp, Over.w d]
    exact (IsPullback.of_hasPullback _ T.obj.hom).flip
  exact IsPullback.of_right outer (stageChartDiagram_map_fst B S hS D T d) t

/-- **The base changes of a chart to the later stages satisfy the chapter's convention**, when
the system does: they form a cartesian system over the stages above `j`, and the slices of the
stages above `j` are those of the index. -/
private theorem stageChartDiagram_conv (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    SiteContainsBaseChangeLimits B S hS (stageChartDiagram B S hS D T) := by
  have : ∀ s : Over j, (Over.post (X := s) (Over.forget j)).Initial := fun s =>
    Functor.initial_of_adjunction (Over.iteratedSliceEquiv s).toAdjunction
  exact SiteContainsBaseChangeLimits.of_isPullback (Over.forget j)
    { app := fun s => pullback.fst _ _
      naturality := fun {s s'} d => stageChartDiagram_map_fst B S hS D T d }
    (fun d => stageChartDiagram_isPullback B S hS D T d) hAffine hconv

include hconv hQcL hD hAffine hZ hQc hQs hTqc hTqs in
/-- **Every regular function on the base change to the limit comes from a stage.** -/
private theorem Conv.exists_gpb_limToStage_eq
    (y : Γ((BigFppfOver.toScheme B S hS).obj (Conv.limChart B S hS D hconv hQcL hD hAffine
        T).obj.left, ⊤)) :
    ∃ (s : Over j) (x : Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine T s).obj.left, ⊤)),
      gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine T s) x = y := by
  let G := (Conv.limChartIso B S hS D hconv hQcL hD hAffine T).inv ≫ yoneda.map (fnEquiv _ y)
  obtain ⟨s₀, t, s, a, a', h1, -⟩ :=
      exists_stage_map_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ
    (stageChartDiagram B S hS D T) (stageChartCone B S hS D T) (stageChartConeIsLimit B S hS D T)
    (stageChartDiagram_conv B S hS D T hconv hAffine)
    (stageChartDiagram_alg B S hS D hD T) (stageChartDiagram_qc B S hS D hD T hZ hQc hQs hTqc)
    (stageChartDiagram_qs B S hS D hD hAffine T hZ hTqs)
    (stageChartDiagram_affine B S hS D hAffine T)
    (isAlgebraicSpace_pullback B S hS _ _ ((convLimitSpace B S hS D hconv hQcL hD hAffine).2)
      (isAlgebraicSpace_yoneda B S hS _) (hD j))
    (isAlgebraicSpace_yoneda B S hS (affineLineBigFppfOver B S hS))
    (isAlgebraicSpace_yoneda B S hS (baseTerminal B S hS))
    (yoneda.map (affineLineToBase B S hS)) (isLocallyOfFinitePresentation_affineLineToBase B S hS)
    G (Over.mk (𝟙 j)) ((baseTerminal_yonedaIsTerminal B S hS).from _)
    ((baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _)
  let t' : yoneda.obj (laterStageChart B S hS D hD hAffine T s).obj.left ⟶
      yoneda.obj (affineLineBigFppfOver B S hS) :=
    (stageChartIso B S hS D hD hAffine T s).hom ≫ (stageChartDiagram B S hS D T).map a ≫ t
  refine ⟨s, (fnEquiv _).symm (yoneda.preimage t'), ?_⟩
  apply (fnEquiv _).injective
  rw [fnEquiv_gpb, Equiv.apply_symm_apply]
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_preimage]
  calc yoneda.map (Conv.limToStage B S hS D hconv hQcL hD hAffine T s) ≫ t'
      = (Conv.limChartIso B S hS D hconv hQcL hD hAffine T).hom ≫
          ((stageChartCone B S hS D T).π.app s ≫ (stageChartDiagram B S hS D T).map a ≫ t) := by
        simp only [t', ← Category.assoc, Conv.limChartIso_comp]
    _ = (Conv.limChartIso B S hS D hconv hQcL hD hAffine T).hom ≫ G := by rw [h1]
    _ = _ := by simp only [G, Iso.hom_inv_id_assoc]

include hconv hQcL hD hAffine hZ hQc hQs hTqc hTqs in
/-- **Two regular functions on a stage which agree on the base change to the limit agree on a
later stage.** -/
private theorem Conv.exists_gpb_stageToStage_eq {s : Over j}
    (x₁ x₂ : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T
        s).obj.left, ⊤))
    (h : gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine T s) x₁ =
      gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine T s) x₂) :
    ∃ (s' : Over j) (d : s' ⟶ s), gpb (stageToStage B S hS D hD hAffine T d) x₁ =
      gpb (stageToStage B S hS D hD hAffine T d) x₂ := by
  let r : (stageChartDiagram B S hS D T).obj s ⟶ yoneda.obj (affineLineBigFppfOver B S hS) :=
    (stageChartIso B S hS D hD hAffine T s).inv ≫ yoneda.map (fnEquiv _ x₁)
  let r' : (stageChartDiagram B S hS D T).obj s ⟶ yoneda.obj (affineLineBigFppfOver B S hS) :=
    (stageChartIso B S hS D hD hAffine T s).inv ≫ yoneda.map (fnEquiv _ x₂)
  have hl : ∀ x, (Conv.limChartIso B S hS D hconv hQcL hD hAffine T).hom ≫
      (stageChartCone B S hS D T).π.app s ≫ (stageChartIso B S hS D hD hAffine T s).inv ≫
        yoneda.map (fnEquiv _ x) =
      yoneda.map (fnEquiv _ (gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine T s) x)) := by
    intro x
    rw [fnEquiv_gpb, Functor.map_comp, ← Category.assoc, ← Category.assoc, Conv.limChartIso_comp,
      Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  obtain ⟨s', d, hd⟩ :=
      exists_stage_eq_of_relativelyLimitPreserving_of_siteContainsBaseChangeLimits B S hS hZ
    (stageChartDiagram B S hS D T) (stageChartCone B S hS D T) (stageChartConeIsLimit B S hS D T)
    (stageChartDiagram_conv B S hS D T hconv hAffine)
    (stageChartDiagram_alg B S hS D hD T) (stageChartDiagram_qc B S hS D hD T hZ hQc hQs hTqc)
    (stageChartDiagram_qs B S hS D hD hAffine T hZ hTqs)
    (stageChartDiagram_affine B S hS D hAffine T)
    (isAlgebraicSpace_pullback B S hS _ _ ((convLimitSpace B S hS D hconv hQcL hD hAffine).2)
      (isAlgebraicSpace_yoneda B S hS _) (hD j))
    (isAlgebraicSpace_yoneda B S hS (affineLineBigFppfOver B S hS))
    (isAlgebraicSpace_yoneda B S hS (baseTerminal B S hS))
    (yoneda.map (affineLineToBase B S hS)) (isLocallyOfFinitePresentation_affineLineToBase B S hS)
    s r r' (by
      apply (cancel_epi (Conv.limChartIso B S hS D hconv hQcL hD hAffine T).hom).1
      simp only [r, r']
      rw [hl, hl, h])
    ((baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _)
  refine ⟨s', d, ?_⟩
  apply (fnEquiv _).injective
  rw [fnEquiv_gpb, fnEquiv_gpb]
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  have e : ∀ x, yoneda.map (stageToStage B S hS D hD hAffine T d) ≫ yoneda.map (fnEquiv _ x) =
      (stageChartIso B S hS D hD hAffine T s').hom ≫ (stageChartDiagram B S hS D T).map d ≫
        (stageChartIso B S hS D hD hAffine T s).inv ≫ yoneda.map (fnEquiv _ x) := by
    intro x
    rw [← Category.assoc, stageChartIso_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [e, e]
  exact congrArg ((stageChartIso B S hS D hD hAffine T s').hom ≫ ·) hd

end Descent

end AlgebraicGeometry.Space

end

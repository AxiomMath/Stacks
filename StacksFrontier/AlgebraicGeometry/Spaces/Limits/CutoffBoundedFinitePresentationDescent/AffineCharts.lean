module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Affine charts of a system bounded by the cutoff

This is the first part of Stacks 07SK, the description of the algebraic spaces of finite
presentation over the limit of a cofiltered inverse system of quasi-compact, absolutely
quasi-separated algebraic spaces with affine transition morphisms as the colimit of those over the
stages, for a system satisfying `AlgebraicGeometry.Space.IsCutoffBoundedSystem` in place of the
bound of the index category by the cofinality of the cutoff which the registered forms in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent` ask for. The output of
Stacks 07SU can only satisfy the former: no system of fewer stages than that cofinality has limit
`Spec F` for a field `F` whose cardinality is the cofinality.

The registered proof uses its bound in exactly three places: Stacks 07SF, part (1), for the
projections of the limit; the limit being an algebraic space; and the containment in the site of
the limit of the affine charts `affineStageChart` of the stages over a chart of one stage, which
it obtains from the size of the slice of the index category below the cofinality. Here the first
two are `AlgebraicGeometry.Space.isAffineHom_limitπ_of_isCutoffBoundedSystem` and
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isCutoffBoundedSystem`, and the third is
`AlgebraicGeometry.Space.IsCutoffBoundedSystem.isLimit_toScheme_chart`: the charts are base changes
of the stages along one test morphism, so `AlgebraicGeometry.Space.BaseChangeSizeBounded` bounds
all of them by one cardinal `μ` below the cutoff, and their limit has size at most
`max ℵ₀ (#(Over i₀) * μ)`, below the cutoff with no regularity needed. The declarations of the
registered proof carrying the bound are repeated here and in the later parts with that one change;
everything the bound does not enter is used from that file.

This part proves that the limit is an algebraic space, builds the cone of affine charts of the
stages over a chart of one stage and its limit in the site, and proves the statements over one
affine chart which the later parts assemble: eventual equality and existence of morphisms, models
of finite presentation over the chart, eventual étaleness, eventual equality on a quasi-compact
source and the factorization through an atlas at a stage.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isCutoffBoundedSystem`: the limit of a
  system bounded by the cutoff is an algebraic space.

Nothing here is registered: Stacks 07SK is registered on the forms bounded by the cofinality.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- **The limit of a system bounded by the cutoff is an algebraic space.** This is
`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_baseChangeSizeBounded` with its size
hypotheses read off `AlgebraicGeometry.Space.IsCutoffBoundedSystem`. -/
theorem isAlgebraicSpace_limit_of_isCutoffBoundedSystem (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hConv : IsCutoffBoundedSystem B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    IsAlgebraicSpace B S hS (limit D) :=
  let ⟨hSize, ⟨_, hν, hHomSize⟩, hB⟩ := hConv
  isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hD hAffine hB

namespace IsCutoffBoundedSystem

/-- The site contains the limit of a cofiltered diagram of affine schemes of the site indexed by
fewer objects than the cutoff, when one cardinal below the cutoff bounds all their sizes. The
limit has size at most `max ℵ₀ (#J * μ)`
(`AlgebraicGeometry.Scheme.size_le_of_isLimit_of_isAffine`). -/
private theorem preservesLimit_inclusion_of_size_le (B : AlgebraicGeometry.BigFppfSite.{u})
    {J : Type u} [Category.{u} J] [IsCofiltered J] (hJ : Cardinal.mk J < B.cutoff)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (E : J ⥤ B.Schemes)
    [∀ j, IsAffine (B.inclusion.obj (E.obj j))] (hE : ∀ j, (B.inclusion.obj (E.obj j)).size ≤ μ) :
    PreservesLimit E B.inclusion := by
  let : ∀ j, IsAffine ((E ⋙ B.inclusion).obj j) :=
    fun j => (inferInstance : IsAffine (B.inclusion.obj (E.obj j)))
  let : HasLimit (E ⋙ B.inclusion) := hasLimit_of_affine_diagram _
  have hle := Scheme.size_le_of_isLimit_of_isAffine (E ⋙ B.inclusion) (fun j => inferInstance)
    (μ := μ) hE (limit.isLimit (E ⋙ B.inclusion))
  have hL : (limit (E ⋙ B.inclusion)).size < B.cutoff := hle.trans_lt
    (max_lt B.aleph0_lt_cutoff (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le hJ hμ))
  let : CreatesLimit E B.inclusion :=
    createsLimitOfFullyFaithfulOfIso ⟨limit (E ⋙ B.inclusion), hL⟩ (Iso.refl _)
  let : HasLimit E := hasLimit_of_created E B.inclusion
  infer_instance

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private theorem affineStageChartMap_toStage {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
        (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage =
      (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage ≫ D.map e.left := by
  simp [affineStageChartMap]

private theorem affineStageChartMap_toChart {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart =
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart := by
  simp [affineStageChartMap]

private noncomputable def affineStageChartOverDiagram {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    Over i₀ ⥤ Over ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) where
  obj j := Over.mk (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart
  map e := Over.homMk (affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) (by
    apply yoneda.map_injective
    simpa only [yoneda.map_comp, Over.mk_left, Over.mk_hom] using
      affineStageChartMap_toChart B S hS D
        i₀ U₀ q₀ hAff e)
  map_id j := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback.hom_ext
    · simp [affineStageChartMap]
    · simp [affineStageChartMap]
  map_comp {j k l} e f := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAff l).isPullback.hom_ext
    · simp [affineStageChartMap, Category.assoc]
    · simp [affineStageChartMap, Category.assoc]

/-- The lift into the chart `affineStageChart` followed by its map to the stage. -/
private theorem affineStageChartLift_toStage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) (j : Over i₀) :
    yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
        (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage = p ≫ limit.π D j.left := by
  simp [affineStageChartLift]

/-- The lift into the chart `affineStageChart` followed by its map to the base chart. -/
private theorem affineStageChartLift_toChart
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) (j : Over i₀) :
    yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q := by
  simp [affineStageChartLift]

private noncomputable def affineStageChartCone {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    Cone (affineStageChartOverDiagram B S hS D
      i₀ U₀ q₀ hAff) where
  pt := Over.mk q
  π := {
    app j := Over.homMk (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j) (by
      apply yoneda.map_injective
      exact affineStageChartLift_toChart B S hS D i₀ U₀ q₀ hAff U p q h j)
    naturality j k e := by
      simp only [Functor.const_obj_map]
      apply Over.OverMorphism.ext
      apply yoneda.map_injective
      apply (affineStageChart B S hS D i₀ U₀ q₀ hAff k).isPullback.hom_ext
      · change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage =
            yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
              (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toStage
        simp [affineStageChartLift, affineStageChartMap, Category.assoc, limit.w]
      · change yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart =
            yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMap B S hS D i₀ U₀ q₀ hAff e) ≫
              yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff k).toChart
        simp [affineStageChartLift, affineStageChartMap, Category.assoc]
  }

private noncomputable def affineStageChartConeIsLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    IsLimit (affineStageChartCone B S hS D
      i₀ U₀ q₀ hAff U p q h) := by
  let E := affineStageChartOverDiagram B S hS D
    i₀ U₀ q₀ hAff
  let c := affineStageChartCone B S hS D
    i₀ U₀ q₀ hAff U p q h
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget T)
  apply isLimitOfReflects yoneda
  let p' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ Over.forget i₀ ⋙ D := {
    app j := (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toStage
    naturality _ _ e := affineStageChartMap_toStage B S hS D i₀ U₀ q₀ hAff e
  }
  let q' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ (Functor.const _).obj (yoneda.obj T) := {
    app j := yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAff j).toChart
    naturality j k e := by
      simpa [E, T, affineStageChartOverDiagram] using
        (affineStageChartMap_toChart B S hS D
          i₀ U₀ q₀ hAff e)
  }
  exact isLimit_of_cartesian_cone D i₀ (yoneda.obj T) q₀ _ _ p' q'
    (fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback)
    p (yoneda.map q) h
    (affineStageChartLift_toStage B S hS D i₀ U₀ q₀ hAff U p q h)
    (affineStageChartLift_toChart B S hS D i₀ U₀ q₀ hAff U p q h)


/-- The charts `affineStageChart` of the stages over an affine chart of the stage `i₀` lie in the
site, for a system bounded by the cutoff, together with their limit: they are base changes of
the stages along the chart, so `AlgebraicGeometry.Space.BaseChangeSizeBounded` bounds them all by
one cardinal below the cutoff, and the slice over `i₀` has fewer objects than the cutoff. -/
private theorem preservesLimit_chart {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hConv : IsCutoffBoundedSystem B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    PreservesLimit ((affineStageChartOverDiagram B S hS D i₀ U₀ q₀ hAff ⋙
      Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)) ⋙
        Over.forget (B.obj hS)) B.inclusion := by
  obtain ⟨hI, ⟨ν, hν, hHom⟩, hB⟩ := hConv
  obtain ⟨μ, hμ, hbound⟩ := hB i₀ ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) q₀
  let : ∀ j : Over i₀, IsAffine (B.inclusion.obj (((affineStageChartOverDiagram B S hS D i₀ U₀ q₀
      hAff ⋙ Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)) ⋙
        Over.forget (B.obj hS)).obj j)) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAff j).U.property
  exact preservesLimit_inclusion_of_size_le B
    (mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hI hν hHom i₀) hμ _
    (fun j => hbound j _ _ _ (affineStageChart B S hS D i₀ U₀ q₀ hAff j).isPullback)

/-- The limit of the charts `affineStageChart` of the stages over an affine chart of the stage
`i₀` is a limit of schemes, for a system bounded by the cutoff. This replaces, in the proof of
Stacks 07SK, the containment of that limit in the site which the registered forms obtain from
the bound of the index category by the cofinality of the cutoff. -/
private noncomputable def isLimit_toScheme_chart {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hConv : IsCutoffBoundedSystem B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (c : Cone (affineStageChartOverDiagram B S hS D i₀ U₀ q₀ hAff ⋙
      Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)))
    (hc : IsLimit c) : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c) := by
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  let : PreservesLimit ((affineStageChartOverDiagram B S hS D i₀ U₀ q₀ hAff ⋙
      Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)) ⋙
        Over.forget (B.obj hS)) B.inclusion :=
    preservesLimit_chart B S hS D hConv i₀ U₀ q₀ hAff
  exact isLimitOfPreserves (AlgebraicGeometry.BigFppfOver.toScheme B S hS) hc

/-- The image in schemes of the cone `affineStageChartCone`, over an affine chart of the stage
`i₀`, is a limit cone, for a system bounded by the cutoff. -/
private noncomputable def isLimit_toScheme_affineStageChartCone {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hConv : IsCutoffBoundedSystem B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone
      ((Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)).mapCone
        (affineStageChartCone B S hS D i₀ U₀ q₀ hAff U p q h))) :=
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  isLimit_toScheme_chart B S hS D hConv i₀ U₀ q₀ hAff _
    (isLimitOfPreserves (Over.forget _)
      (affineStageChartConeIsLimit B S hS D i₀ U₀ q₀ hAff U p q h))

/-- A model over a chart of a stage of a finitely presented morphism to the limit of the charts
descends to a model in the site, finitely presented over the stage, which is a base change of the
stage's chart. -/
private theorem exists_site_model_of_chart_model (hZ : B.Contains (⊤_ Scheme.{u}))
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (i : I) (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj) (j : Over i)
    (V₀ : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj))
    (hV₀ : AlgebraicGeometry.FinitePresentation V₀.hom)
    (e : Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
      (Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        ((affineStageChartCone B S hS D i U₀ p₀ hAffine U.obj p q hp).π.app j).left)).obj V₀) :
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS)
      (f : V ⟶ (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS
        (yoneda.map f ≫ (affineStageChart B S hS D i U₀ p₀ hAffine j).toStage) ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) ≅ V₀) ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p)
        (yoneda.map f ≫ (affineStageChart B S hS D i U₀ p₀ hAffine j).toStage)
        (limit.π D j.left) := by
  let c := affineStageChartCone B S hS D
    i U₀ p₀ hAffine U.obj p q hp
  let Cj := affineStageChart B S hS D i U₀ p₀ hAffine j
  let b : U.obj ⟶ Cj.U.obj := (c.π.app j).left
  obtain ⟨V, f, a, hf, ⟨eV⟩, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  have hbp := affineStageChartLift_toStage B S hS D i U₀ p₀ hAffine U.obj p q hp j
  have hbq := affineStageChartLift_toChart B S hS D i U₀ p₀ hAffine U.obj p q hp j
  have hU : IsPullback (yoneda.map b) p Cj.toStage (limit.π D j.left) := by
    apply IsPullback.of_right (h₂₂ := D.map j.hom) _ hbp Cj.isPullback.flip
    rw [hbq, limit.w]
    exact hp.flip
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (etaleInverseImageIsStableUnderComposition _)
  have hpc : P.presheaf Cj.toStage := P.presheaf.of_isPullback Cj.isPullback.flip hp₀
  let : IsAffine (Q.obj Cj.U.obj) := Cj.U.property
  let : LocallyOfFinitePresentation (Q.map f) := hf.1
  let : QuasiCompact (Q.map f) := hf.2.1
  let : QuasiSeparated (Q.map f) := hf.2.2
  have hVqc : CompactSpace (Q.obj V) := QuasiCompact.compactSpace_of_compactSpace (Q.map f)
  have hVqs : QuasiSeparatedSpace (Q.obj V) :=
    quasiSeparatedSpace_of_quasiSeparated (Q.map f)
  exact ⟨V, f, a,
    isFinitePresentation_of_scheme_chart B S hS hZ (hD j.left) (hQs j.left)
      V Cj.U.obj hVqc hVqs f Cj.toStage hpc hf.1, ⟨eV⟩, (ha.map yoneda).paste_vert hU⟩

/-- Two morphisms from an affine chart to a space locally of finite presentation over a space `G`,
which agree over `G` and on the limit chart `U`, agree on the chart of some stage. -/
private theorem eventually_eq_of_eq_on_limit_chart
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hConv : IsCutoffBoundedSystem B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {G Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (b : D.obj i₀ ⟶ G)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀ ≫ b) (hg : g ≫ a = q₀ ≫ b)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  obtain ⟨U, p, q, h⟩ :=
    isAffineHom_limitπ_of_isCutoffBoundedSystem B S hS D hConv hAffine i₀ U₀ q₀
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagram B S hS D
    i₀ U₀ q₀ hAffine
  let c := affineStageChartCone B S hS D
    i₀ U₀ q₀ hAffine _ p q h
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  have hh : yoneda.map q ≫ f = yoneda.map q ≫ g := by
    simpa using congrArg (fun k => h.isoPullback.hom ≫ k) hfg
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg hG
    a ha T (q₀ ≫ b) E c
    (isLimit_toScheme_affineStageChartCone B S hS D hConv i₀ U₀ q₀ hAffine _ p q h)
    hE U.property f g hf hg hh

variable (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hD hAffine hQc hQs

omit hQc hQs in
private theorem eventually_eq_on_affine_chart
    (hConv : IsCutoffBoundedSystem B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀) (hg : g ≫ a = q₀)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  exact eventually_eq_of_eq_on_limit_chart B S hS D hAffine hConv i₀ U₀ q₀ (hD i₀) (𝟙 _) hZalg a
    ha f g (by simpa using hf) (by simpa using hg) hfg

omit hQc hQs in
private theorem exists_hom_on_affine_chart
    (hConv : IsCutoffBoundedSystem B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj U₀.obj ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback (limit.π D i₀) q₀ ⟶ Z)
    (hf : f ≫ a = pullback.fst _ _ ≫ limit.π D i₀) :
    ∃ (j : Over i₀) (g : yoneda.obj
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.obj ⟶ Z),
      g ≫ a = (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toStage ≫ D.map j.hom ∧
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) ≫ g = f := by
  obtain ⟨U, p, q, h⟩ :=
    isAffineHom_limitπ_of_isCutoffBoundedSystem B S hS D hConv hAffine i₀ U₀ q₀
  let E := affineStageChartOverDiagram B S hS D
    i₀ U₀ q₀ hAffine
  let c := affineStageChartCone B S hS D
    i₀ U₀ q₀ hAffine _ p q h
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).U.property
  obtain ⟨j, g, hg, he⟩ := exists_hom_of_locallyOfFinitePresentation B S hS hZalg
    (hD i₀) a ha U₀.obj q₀ E c
    (isLimit_toScheme_affineStageChartCone B S hS D hConv i₀ U₀ q₀ hAffine _ p q h)
    hE U.property (h.isoPullback.hom ≫ f) (by
      show (h.isoPullback.hom ≫ f) ≫ a = yoneda.map q ≫ q₀
      rw [Category.assoc, hf, IsPullback.isoPullback_hom_fst_assoc]
      exact h.w)
  refine ⟨j, g, hg.trans (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.w.symm, ?_⟩
  apply (Iso.cancel_iso_hom_left h.isoPullback _ _).mp
  have hh : h.isoPullback.hom ≫
      (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) =
      yoneda.map (affineStageChartLift B S hS D i₀ U₀ q₀ hAffine _ p q h j) := by
    apply (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).isPullback.hom_ext
    · simp [affineStageChartLift]
    · simp [affineStageChartLift]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ g) hh).trans he)

omit hD hQc hQs in
private theorem eventually_eq_on_affine_chart_over
    (hConv : IsCutoffBoundedSystem B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    {G Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (b : D.obj i₀ ⟶ G)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ Z)
    (hf : f ≫ a = q₀ ≫ b) (hg : g ≫ a = q₀ ≫ b)
    (hfg : pullback.snd (limit.π D i₀) q₀ ≫ f =
      pullback.snd (limit.π D i₀) q₀ ≫ g) :
    ∃ j : Over i₀,
      yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChart B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  exact eventually_eq_of_eq_on_limit_chart B S hS D hAffine hConv i₀ U₀ q₀ hG b hZalg a ha f g hf hg
    hfg

omit hD hQc hQs in
private theorem exists_model_over_affine_chart
    (hConv : IsCutoffBoundedSystem B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    let c := affineStageChartCone B S hS D
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagram B S hS D
    i U₀ p₀ hAffine
  let c := affineStageChartCone B S hS D
    i U₀ p₀ hAffine U.obj p q hp
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hF : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (F.obj j)) :=
    fun j => (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  let : ∀ j, IsAffine (G.obj j) := hF
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (G.map e) :=
    fun {_ _} _ => inferInstance
  let : ∀ j : Over i, CompactSpace (G.obj j) := fun _ => inferInstance
  let : ∀ j : Over i, QuasiSeparatedSpace (G.obj j) := fun _ => inferInstance
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc :=
    isLimit_toScheme_affineStageChartCone B S hS D hConv i U₀ p₀ hAffine _ p q hp
  exact scheme_model_of_finitePresentation G sc hsc
    (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg

omit hD hQc hQs in
private theorem exists_affine_model_over_affine_chart
    (hConv : IsCutoffBoundedSystem B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    let c := affineStageChartCone B S hS D
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧ IsAffine Wj.left ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagram B S hS D
    i U₀ p₀ hAffine
  let c := affineStageChartCone B S hS D
    i U₀ p₀ hAffine U.obj p q hp
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hF : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (F.obj j)) :=
    fun j => (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  let : ∀ j, IsAffine (G.obj j) := hF
  let : ∀ {j k : Over i} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (G.map e) :=
    fun {_ _} _ => inferInstance
  let : ∀ j : Over i, CompactSpace (G.obj j) := fun _ => inferInstance
  let : ∀ j : Over i, QuasiSeparatedSpace (G.obj j) := fun _ => inferInstance
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc :=
    isLimit_toScheme_affineStageChartCone B S hS D hConv i U₀ p₀ hAffine _ p q hp
  exact scheme_affine_model_of_finitePresentation G sc hsc
    (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)›

omit hQc in
private theorem exists_site_model_over_affine_chart
    (hConv : IsCutoffBoundedSystem B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ D.obj j.left) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  obtain ⟨j, V₀, hV₀, ⟨e⟩⟩ := exists_model_over_affine_chart B S hS D hAffine
    hConv i U₀ p₀ U p q hp W g hg
  obtain ⟨V, f, a, hf, -, ha⟩ := exists_site_model_of_chart_model B S hS hZ D hD hAffine hQs i U₀
    p₀ hp₀ U p q hp W g j V₀ hV₀ e
  exact ⟨j, V, _, a, hf, ha⟩

omit hQc in
private theorem exists_affine_site_model_over_affine_chart
    (hConv : IsCutoffBoundedSystem B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (hp₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p₀)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    ∃ (j : Over i) (V : AlgebraicGeometry.BigFppfOver B S hS)
      (v : yoneda.obj V ⟶ D.obj j.left) (a : W ⟶ V),
      AlgebraicGeometry.Space.IsFinitePresentation B S hS v ∧
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V) ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  obtain ⟨j, V₀, hV₀, hV₀aff, ⟨e⟩⟩ := exists_affine_model_over_affine_chart B S hS D hAffine
    hConv i U₀ p₀ U p q hp W g hg
  obtain ⟨V, f, a, hf, ⟨eV⟩, ha⟩ := exists_site_model_of_chart_model B S hS hZ D hD hAffine hQs i
    U₀ p₀ hp₀ U p q hp W g j V₀ hV₀ e
  refine ⟨j, V, _, a, hf, ?_, ha⟩
  let : IsAffine V₀.left := hV₀aff
  let : IsIso eV.hom.left :=
    inferInstanceAs (IsIso ((Over.forget ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChart B S hS D i U₀ p₀ hAffine j).U.obj)).map eV.hom))
  exact IsAffine.of_isIso eV.hom.left

omit hD hQc hQs in
private theorem eventually_etale_over_affine_chart
    (hConv : IsCutoffBoundedSystem B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (X : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U₀.obj))
    (hX : AlgebraicGeometry.FinitePresentation X.hom)
    [Etale ((Over.pullback ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)).obj X).hom] :
    ∃ j : Over i, Etale ((Over.pullback
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (affineStageChart B S hS D i U₀ p₀ hAffine j).toChart)).obj X).hom := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let E := affineStageChartOverDiagram B S hS D
    i U₀ p₀ hAffine
  let c := affineStageChartCone B S hS D
    i U₀ p₀ hAffine U.obj p q hp
  let F := E ⋙ Over.forget U₀.obj
  let E' := E ⋙ Over.post Q
  let sc := (Over.post Q).mapCone c
  have hF (j : Over i) : IsAffine (Q.obj (F.obj j)) :=
    (affineStageChart B S hS D i U₀ p₀ hAffine j).U.property
  have hsc : IsLimit ((Over.forget (Q.obj U₀.obj)).mapCone sc) :=
    isLimit_toScheme_affineStageChartCone B S hS D hConv i U₀ p₀ hAffine _ p q hp
  let : ∀ j, IsAffine (E'.obj j).left := hF
  let : ∀ {j k : Over i} (a : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E'.map a).left :=
    fun _ => inferInstance
  let : Etale ((Over.pullback sc.pt.hom).obj X).hom :=
    ‹Etale ((Over.pullback (Q.map q)).obj X).hom›
  exact scheme_eventually_etale_pullback E' sc hsc X hX


omit hQc hQs in
private theorem eventually_eq_on_quasiCompact_source
    (hConv : IsCutoffBoundedSystem B S hS D) (i : I)
    {Y Z G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y)
    (r : Y ⟶ D.obj i) (a : Z ⟶ G) (b : D.obj i ⟶ G)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f g : Y ⟶ Z) (hf : f ≫ a = r ≫ b) (hg : g ≫ a = r ≫ b)
    (hfg : pullback.fst r (limit.π D i) ≫ f =
      pullback.fst r (limit.π D i) ≫ g) :
    ∃ (j : I) (e : j ⟶ i),
      pullback.fst r (D.map e) ≫ f = pullback.fst r (D.map e) ≫ g := by
  classical
  obtain ⟨U₀, q₀, hU₀, hsurj, het⟩ := exists_affine_etale_atlas B S hS Y hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  have hh : pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ f =
      pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀ ≫ g := by
    let k : pullback (limit.π D i) (q₀ ≫ r) ⟶ pullback r (limit.π D i) :=
      pullback.lift (pullback.snd (limit.π D i) (q₀ ≫ r) ≫ q₀)
      (pullback.fst (limit.π D i) (q₀ ≫ r))
      (by simp only [Category.assoc, pullback.condition])
    simpa [k] using congrArg (fun t => k ≫ t) hfg
  obtain ⟨j, hj⟩ := eventually_eq_on_affine_chart_over B S hS D hAffine
    hConv i U (q₀ ≫ r) hG b hZalg a ha
    (q₀ ≫ f) (q₀ ≫ g) (by simp [hf]) (by simp [hg]) hh
  refine ⟨j.left, j.hom, ?_⟩
  let C := affineStageChart B S hS D i U (q₀ ≫ r) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback r (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst r (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback r (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  apply hom_ext_of_surjective_etale_atlas B S hS
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS r (D.map j.hom) hY (hD j.left) (hD i))
    hZalg.isSheaf p
    (P.presheaf.of_isPullback hp hsurj)
    (Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ het))
  simpa [p, Category.assoc] using hj


omit hQc hQs in
private theorem exists_stage_atlas_factorization
    (hConv : IsCutoffBoundedSystem B S hS D) (i : I)
    (Y : Over (D.obj i))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y.left)
    (hYqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS Y.left)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback Y.hom (limit.π D i) ⟶ Z)
    (hf : f ≫ a = pullback.fst Y.hom (limit.π D i) ≫ Y.hom) :
    ∃ (j : Over i) (U : AlgebraicGeometry.BigAffineFppf B S hS)
      (p : yoneda.obj U.obj ⟶ pullback Y.hom (D.map j.hom))
      (g : yoneda.obj U.obj ⟶ Z),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      g ≫ a = p ≫ pullback.snd Y.hom (D.map j.hom) ≫ D.map j.hom ∧
      pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ g =
        pullback.lift
          (pullback.fst (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ≫ p)
          (pullback.snd (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left))
          (by simpa only [Over.pullback_obj_hom, Category.assoc] using
            (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
              (g := limit.π D j.left))) ≫
        (iteratedBaseChangeIso (D.map j.hom) (limit.π D j.left) (limit.π D i)
          (limit.w D j.hom) Y).hom.left ≫ f := by
  classical
  obtain ⟨U₀, q₀, hU₀, hs, he⟩ := exists_affine_etale_atlas B S hS Y.left hY hYqc
  let U : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  let k : pullback (limit.π D i) (q₀ ≫ Y.hom) ⟶ pullback Y.hom (limit.π D i) :=
    pullback.lift (pullback.snd _ _ ≫ q₀) (pullback.fst _ _)
      (by simp only [Category.assoc, pullback.condition])
  obtain ⟨j, g, hg, hgf⟩ := exists_hom_on_affine_chart B S hS D hD hAffine
    hConv i U (q₀ ≫ Y.hom) hZalg a ha (k ≫ f) (by
      rw [Category.assoc, hf]
      simpa [k, Category.assoc] using (pullback.condition (f := limit.π D i)
        (g := q₀ ≫ Y.hom)).symm)
  let C := affineStageChart B S hS D i U (q₀ ≫ Y.hom) hAffine j
  let p : yoneda.obj C.U.obj ⟶ pullback Y.hom (D.map j.hom) :=
    pullback.lift (yoneda.map C.toChart ≫ q₀) C.toStage
      (by simpa only [Category.assoc] using C.isPullback.w.symm)
  have hp : IsPullback (yoneda.map C.toChart) p q₀
      (pullback.fst Y.hom (D.map j.hom)) := by
    apply IsPullback.of_bot _ (by simp [p]) (IsPullback.of_hasPullback Y.hom (D.map j.hom))
    simpa [p] using C.isPullback.flip
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderBaseChange := P.relative_isStableUnderBaseChange (F := yoneda)
  let : Q.presheaf.IsStableUnderBaseChange := Q.relative_isStableUnderBaseChange (F := yoneda)
  let : P.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition P (surjectiveInverseImageIsStableUnderComposition _)
  let : Q.presheaf.IsStableUnderComposition :=
    presheafIsStableUnderComposition Q (etaleInverseImageIsStableUnderComposition _)
  refine ⟨j, C.U, p, g, P.presheaf.of_isPullback hp hs,
    Q.presheaf.of_isPullback hp (represented_etale_of_isEtale B S hS q₀ he),
    by simpa [p] using hg, ?_⟩
  let v : pullback (p ≫ pullback.snd Y.hom (D.map j.hom)) (limit.π D j.left) ⟶
      pullback (limit.π D i) (q₀ ≫ Y.hom) :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ yoneda.map C.toChart) (by
      simp only [Category.assoc]
      rw [← C.isPullback.w, ← limit.w D j.hom]
      simp only [← Category.assoc]
      congr 1
      have hpcomp : p ≫ pullback.snd Y.hom (D.map j.hom) = C.toStage := by simp [p]
      rw [← hpcomp]
      exact pullback.condition.symm)
  let l := C.isPullback.lift
    (pullback.fst (limit.π D i) (q₀ ≫ Y.hom) ≫ limit.π D j.left)
    (pullback.snd (limit.π D i) (q₀ ≫ Y.hom))
    (by rw [Category.assoc, limit.w]; exact pullback.condition)
  have hv : v ≫ l = pullback.fst _ _ := by
    apply C.isPullback.hom_ext
    · simp only [Category.assoc, l, IsPullback.lift_fst, v, pullback.lift_fst_assoc]
      simpa [p, Category.assoc] using
        (pullback.condition (f := p ≫ pullback.snd Y.hom (D.map j.hom))
          (g := limit.π D j.left)).symm
    · simp [l, v]
  conv_lhs => rw [← hv, Category.assoc, hgf]
  simp only [← Category.assoc]
  apply congrArg (fun t => t ≫ f)
  apply pullback.hom_ext
  · simp [v, k, iteratedBaseChangeIso_hom_left, p, Category.assoc]
  · simp [v, k, iteratedBaseChangeIso_hom_left, Category.assoc]

end IsCutoffBoundedSystem

end AlgebraicGeometry.Space

end

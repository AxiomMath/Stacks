module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSiteLimitCone
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentRealised
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent

/-!
# Affine stage charts of an inverse system of algebraic spaces

For a cofiltered inverse system of algebraic spaces with affine transition morphisms, the
system of base changes of an affine chart of one stage to the later stages, its cone over the
limit, the structure `LimitFacts` of the three facts about the limit the descent argument uses,
and the first consequences on affine charts: eventual equality and existence of morphisms, the
scheme diagram of the charts, and models of finite-presentation schemes over a chart.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! The two projections of an explicit fibre product out of a lift into it are not `simp`
lemmas in Mathlib, where `pullback.hom_ext` is the preferred interface; the explicit cones
built below are compared projection by projection throughout. -/

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-! ### Morphism-property interfaces

The descent below repeatedly needs that the inverse images of étaleness and surjectivity of
morphisms of schemes along the structure functor of the site are stable under composition and
respect isomorphisms. None of these is available to instance synthesis as stated, so each is
named once here.
-/

/- The algebraic-space proof reduces finite presentation to descent for scheme
   charts.  Keep the scheme-level interface here in the exact shape used by
   the chart diagrams below. -/

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
variable (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))

include hD hAffine hQc hQs

/- Given an affine chart of one stage, every later transition pulls it back to
   an affine chart. This is the scheme diagram underlying the presentation of
   the limit algebraic space. -/
structure AffineStageChartOfLimitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (j : Over i₀) where
  U : AlgebraicGeometry.BigAffineFppf B S hS
  toStage : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U) ⟶ D.obj j.left
  toChart : (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U ⟶
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  isPullback : IsPullback toStage (yoneda.map toChart) (D.map j.hom) q₀

noncomputable def affineStageChartOfLimitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (j : Over i₀) : AffineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ j := by
  classical
  let h := hAff j.hom U₀ q₀
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))⟩

noncomputable def affineStageChartMapOfLimitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).U ⟶
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k).U := by
  classical
  let Cj := affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j
  let Ck := affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k
  have hcomm : Cj.toStage ≫ D.map e.left ≫ D.map k.hom =
      yoneda.map Cj.toChart ≫ q₀ := by
    calc
      Cj.toStage ≫ D.map e.left ≫ D.map k.hom =
          Cj.toStage ≫ D.map (e.left ≫ k.hom) := by rw [← D.map_comp]
      _ = Cj.toStage ≫ D.map j.hom := by rw [Over.w e]
      _ = yoneda.map Cj.toChart ≫ q₀ := Cj.isPullback.w
  exact yoneda.preimage (Ck.isPullback.lift
    (Cj.toStage ≫ D.map e.left) (yoneda.map Cj.toChart) hcomm)

omit [IsCofiltered I] hD hAffine hQc hQs in
theorem affineStageChartMap_toStage_of_limitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff e) ≫
        (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k).toStage =
      (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toStage ≫ D.map e.left := by
  simp [affineStageChartMapOfLimitFacts]

omit [IsCofiltered I] hD hAffine hQc hQs in
theorem affineStageChartMap_toChart_of_limitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    yoneda.map (affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff e) ≫
        yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k).toChart =
      yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toChart := by
  simp [affineStageChartMapOfLimitFacts]

/-- The map from a pullback chart over the limit to the affine chart at a later stage,
named so that its two defining identities can be stated and used without unfolding the
`yoneda.preimage` that produces it. -/
noncomputable def affineStageChartLiftOfLimitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) (j : Over i₀) :
    U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).U := by
  classical
  exact yoneda.preimage ((affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).isPullback.lift
    (p ≫ limit.π D j.left) (yoneda.map q) (by
      rw [Category.assoc, limit.w]
      exact h.w))

noncomputable def affineStageChartOverDiagramOfLimitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    Over i₀ ⥤ Over ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) where
  obj j := Over.mk (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toChart
  map e := Over.homMk (affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff e) (by
    apply yoneda.map_injective
    simpa only [yoneda.map_comp, Over.mk_left, Over.mk_hom] using
      affineStageChartMap_toChart_of_limitFacts B S hS D
        i₀ U₀ q₀ hAff e)
  map_id j := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).isPullback.hom_ext
    · simp [affineStageChartMapOfLimitFacts]
    · simp [affineStageChartMapOfLimitFacts]
  map_comp {j k l} e f := by
    apply Over.OverMorphism.ext
    apply yoneda.map_injective
    apply (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff l).isPullback.hom_ext
    · simp [affineStageChartMapOfLimitFacts, Category.assoc]
    · simp [affineStageChartMapOfLimitFacts, Category.assoc]

noncomputable def affineStageChartConeOfLimitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    Cone (affineStageChartOverDiagramOfLimitFacts B S hS D
      i₀ U₀ q₀ hAff) where
  pt := Over.mk q
  π := {
    app j := Over.homMk (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h j) (by
      apply yoneda.map_injective
      change yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q
      simp [affineStageChartLiftOfLimitFacts])
    naturality j k e := by
      simp only [Functor.const_obj_map]
      apply Over.OverMorphism.ext
      apply yoneda.map_injective
      apply (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k).isPullback.hom_ext
      · change yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k).toStage =
            yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff e) ≫
              (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k).toStage
        simp [affineStageChartLiftOfLimitFacts, affineStageChartMapOfLimitFacts, Category.assoc,
          limit.w]
      · change yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h k) ≫
              yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k).toChart =
            yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h j ≫
                affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff e) ≫
              yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k).toChart
        simp [affineStageChartLiftOfLimitFacts, affineStageChartMapOfLimitFacts, Category.assoc]
  }

private noncomputable def affineStageChartConeIsLimitOfLimitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀) :
    IsLimit (affineStageChartConeOfLimitFacts B S hS D
      i₀ U₀ q₀ hAff U p q h) := by
  let E := affineStageChartOverDiagramOfLimitFacts B S hS D
    i₀ U₀ q₀ hAff
  let c := affineStageChartConeOfLimitFacts B S hS D
    i₀ U₀ q₀ hAff U p q h
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget T)
  apply isLimitOfReflects yoneda
  let p' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ Over.forget i₀ ⋙ D := {
    app j := (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toStage
    naturality j k e := by
      exact (affineStageChartMap_toStage_of_limitFacts B S hS D
        i₀ U₀ q₀ hAff e)
  }
  let q' : (E ⋙ Over.forget T) ⋙ yoneda ⟶ (Functor.const _).obj (yoneda.obj T) := {
    app j := yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toChart
    naturality j k e := by
      simpa [E, T, affineStageChartOverDiagramOfLimitFacts] using
        (affineStageChartMap_toChart_of_limitFacts B S hS D
          i₀ U₀ q₀ hAff e)
  }
  exact isLimit_of_cartesian_cone D i₀ (yoneda.obj T) q₀ _ _ p' q'
    (fun j => (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).isPullback)
    p (yoneda.map q) h
    (fun j => by
      change yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toStage = p ≫ limit.π D j.left
      simp [affineStageChartLiftOfLimitFacts])
    (fun j => by
      change yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h j) ≫
          yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).toChart = yoneda.map q
      simp [affineStageChartLiftOfLimitFacts])

/-- **The three facts about a cofiltered system of algebraic spaces with affine transition
morphisms that a cardinality bound on the index category is used for.** The limit is an
algebraic space, the projections from the limit are affine, and the affine chart system over a
stage has its limit computed in schemes. Stating the development against these rather than
against the bound lets it be used both for a bounded index category
(`AlgebraicGeometry.Space.exists_model_of_finitePresentation`) and for a system whose limit is
given at the level of schemes, where no bound is available. -/
structure LimitFacts (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The limit of the system is an algebraic space. -/
  limAlg : AlgebraicGeometry.IsAlgebraicSpace B S hS (limit D)
  /-- Every projection from the limit to a stage is an affine morphism. -/
  piAff : ∀ i : I, AlgebraicGeometry.Space.IsAffineHom B S hS (limit.π D i)
  /-- The affine chart system over a stage has its limit computed in schemes. -/
  chartLim : ∀ (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (i₀ : I) (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (p : yoneda.obj U ⟶ limit D)
    (q : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀)
    (h : IsPullback p (yoneda.map q) (limit.π D i₀) q₀),
    IsLimit ((Over.forget ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⋙
        AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone
      (affineStageChartConeOfLimitFacts B S hS D i₀ U₀ q₀ hAff U p q h))

omit hD hQc hQs in
theorem eventually_eq_on_affine_chart_over_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i₀ : I)
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
      yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  obtain ⟨U, p, q, h⟩ :=
    hFacts.piAff i₀ U₀ q₀
  let T := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀
  let E := affineStageChartOverDiagramOfLimitFacts B S hS D
    i₀ U₀ q₀ hAffine
  let c := affineStageChartConeOfLimitFacts B S hS D
    i₀ U₀ q₀ hAffine _ p q h
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).U.property
  have hh : yoneda.map q ≫ f = yoneda.map q ≫ g := by
    simpa using congrArg (fun k => h.isoPullback.hom ≫ k) hfg
  exact eventually_eq_homs_of_locallyOfFinitePresentation B S hS hZalg hG
    a ha T (q₀ ≫ b) E c
    (hFacts.chartLim hAffine i₀ U₀ q₀ _ p q h)
    hE U.property f g hf hg hh

omit hQc hQs in
theorem eventually_eq_on_affine_chart_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i₀ : I)
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
      yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ f =
        yoneda.map (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).toChart ≫ g := by
  exact eventually_eq_on_affine_chart_over_of_limitFacts B S hS D hAffine
    hFacts i₀ U₀ q₀ (hD i₀) (𝟙 _) hZalg a ha f g (by simpa using hf) (by simpa using hg) hfg

omit hQc hQs in
theorem exists_hom_on_affine_chart_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj U₀.obj ⟶ D.obj i₀)
    {Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZalg : AlgebraicGeometry.IsAlgebraicSpace B S hS Z) (a : Z ⟶ D.obj i₀)
    (ha : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a)
    (f : pullback (limit.π D i₀) q₀ ⟶ Z)
    (hf : f ≫ a = pullback.fst _ _ ≫ limit.π D i₀) :
    ∃ (j : Over i₀) (g : yoneda.obj
      (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).U.obj ⟶ Z),
      g ≫ a = (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).toStage ≫ D.map j.hom ∧
      (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) ≫ g = f := by
  obtain ⟨U, p, q, h⟩ :=
    hFacts.piAff i₀ U₀ q₀
  let E := affineStageChartOverDiagramOfLimitFacts B S hS D
    i₀ U₀ q₀ hAffine
  let c := affineStageChartConeOfLimitFacts B S hS D
    i₀ U₀ q₀ hAffine _ p q h
  have hE : ∀ j, IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (E.obj j).left) :=
    fun j => (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).U.property
  obtain ⟨j, g, hg, he⟩ := exists_hom_of_locallyOfFinitePresentation B S hS hZalg
    (hD i₀) a ha U₀.obj q₀ E c
    (hFacts.chartLim hAffine i₀ U₀ q₀ _ p q h)
    hE U.property (h.isoPullback.hom ≫ f) (by
      change (h.isoPullback.hom ≫ f) ≫ a = yoneda.map q ≫ q₀
      rw [Category.assoc, hf, IsPullback.isoPullback_hom_fst_assoc]
      exact h.w)
  refine ⟨j, g,
    hg.trans (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).isPullback.w.symm, ?_⟩
  apply (Iso.cancel_iso_hom_left h.isoPullback _ _).mp
  have hh : h.isoPullback.hom ≫
      (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).isPullback.lift
        (pullback.fst _ _ ≫ limit.π D j.left) (pullback.snd _ _)
        (by rw [Category.assoc, limit.w]; exact pullback.condition) =
      yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i₀ U₀ q₀ hAffine _ p q h j) := by
    apply (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAffine j).isPullback.hom_ext
    · simp [affineStageChartLiftOfLimitFacts]
    · simp [affineStageChartLiftOfLimitFacts]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ g) hh).trans he)

noncomputable def affineStageChartDiagramOfLimitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) :
    Over i₀ ⥤ Scheme.{u} := {
  obj j := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).U)
  map e := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
    (affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff e)
  map_id j := by
    let Cj := affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j
    have hsrc : affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff (𝟙 j) = 𝟙 _ := by
      apply yoneda.map_injective
      apply Cj.isPullback.hom_ext
      · simp [affineStageChartMapOfLimitFacts, Cj]
      · simp [affineStageChartMapOfLimitFacts, Cj]
    simpa using congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS |>.map) hsrc
  map_comp {j k l} e f := by
    let Cj := affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j
    let Ck := affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k
    let Cl := affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff l
    have hsrc : affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff (e ≫ f) =
        affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff e ≫
          affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff f := by
      apply yoneda.map_injective
      apply Cl.isPullback.hom_ext
      · rw [affineStageChartMap_toStage_of_limitFacts B S hS D
          i₀ U₀ q₀ hAff (e ≫ f)]
        rw [yoneda.map_comp, Category.assoc]
        rw [affineStageChartMap_toStage_of_limitFacts B S hS D
          i₀ U₀ q₀ hAff f]
        rw [← Category.assoc,
          affineStageChartMap_toStage_of_limitFacts B S hS D
            i₀ U₀ q₀ hAff e]
        rw [Category.assoc, ← D.map_comp]
        simp only [Over.comp_left]
      · rw [affineStageChartMap_toChart_of_limitFacts B S hS D
          i₀ U₀ q₀ hAff (e ≫ f)]
        rw [yoneda.map_comp, Category.assoc]
        rw [affineStageChartMap_toChart_of_limitFacts B S hS D
          i₀ U₀ q₀ hAff f]
        exact (affineStageChartMap_toChart_of_limitFacts B S hS D
          i₀ U₀ q₀ hAff e).symm
    simpa [Functor.map_comp] using
      congrArg (AlgebraicGeometry.BigFppfOver.toScheme B S hS |>.map) hsrc
}

omit [IsCofiltered I] hD hAffine hQc hQs in
theorem affineStageChartDiagram_map_isAffineHom_of_limitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    {j k : Over i₀} (e : j ⟶ k) :
    _root_.AlgebraicGeometry.IsAffineHom ((affineStageChartDiagramOfLimitFacts B S hS D
      i₀ U₀ q₀ hAff).map e) := by
  let Cj := affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j
  let Ck := affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff k
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Cj.U)) := Cj.U.property
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Ck.U)) := Ck.U.property
  change _root_.AlgebraicGeometry.IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
    (affineStageChartMapOfLimitFacts B S hS D i₀ U₀ q₀ hAff e))
  exact AlgebraicGeometry.isAffineHom_of_isAffine _

omit [IsCofiltered I] hD hAffine hQc hQs in
theorem affineStageChartDiagram_obj_isAffine_of_limitFacts (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    IsAffine ((affineStageChartDiagramOfLimitFacts B S hS D
      i₀ U₀ q₀ hAff).obj j) := by
  change IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).U))
  exact (affineStageChartOfLimitFacts B S hS D i₀ U₀ q₀ hAff j).U.property

omit hD hAffine hQc hQs in
theorem affineStageChartDiagram_obj_compact_of_limitFacts
    (_hFacts : LimitFacts B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    CompactSpace ((affineStageChartDiagramOfLimitFacts B S hS D
      i₀ U₀ q₀ hAff).obj j) := by
  let := affineStageChartDiagram_obj_isAffine_of_limitFacts B S hS D
    i₀ U₀ q₀ hAff j
  infer_instance

omit hD hAffine hQc hQs in
theorem affineStageChartDiagram_obj_quasiSeparated_of_limitFacts
    (_hFacts : LimitFacts B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f)) (j : Over i₀) :
    QuasiSeparatedSpace ((affineStageChartDiagramOfLimitFacts B S hS D
      i₀ U₀ q₀ hAff).obj j) := by
  let := affineStageChartDiagram_obj_isAffine_of_limitFacts B S hS D
    i₀ U₀ q₀ hAff j
  infer_instance

omit hD hAffine hQc hQs in
theorem affineStageChartScheme_model_of_finitePresentation_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i₀ : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS)
    (q₀ : yoneda.obj ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (hAff : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f))
    (c : Cone (affineStageChartDiagramOfLimitFacts B S hS D
      i₀ U₀ q₀ hAff))
    (hc : IsLimit c) (X : Over c.pt) (hFp : AlgebraicGeometry.FinitePresentation X.hom) :
    ∃ (j : Over i₀) (Xⱼ : Over ((affineStageChartDiagramOfLimitFacts B S hS D
      i₀ U₀ q₀ hAff).obj j)),
      AlgebraicGeometry.FinitePresentation Xⱼ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  let E := affineStageChartDiagramOfLimitFacts B S hS D
    i₀ U₀ q₀ hAff
  let : ∀ {j k : Over i₀} (e : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (E.map e) := by
    intro j k e
    exact affineStageChartDiagram_map_isAffineHom_of_limitFacts B S hS D
      i₀ U₀ q₀ hAff e
  let : ∀ j : Over i₀, CompactSpace (E.obj j) := fun j =>
    affineStageChartDiagram_obj_compact_of_limitFacts B S hS D hFacts
      i₀ U₀ q₀ hAff j
  let : ∀ j : Over i₀, QuasiSeparatedSpace (E.obj j) := fun j =>
    affineStageChartDiagram_obj_quasiSeparated_of_limitFacts B S hS D hFacts
      i₀ U₀ q₀ hAff j
  exact scheme_model_of_finitePresentation E c hc X hFp

omit hAffine hQs in
theorem exists_affine_limit_atlas_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I) :
    ∃ (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
      (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
      (q : U.obj ⟶ U₀.obj),
      IsPullback p (yoneda.map q) (limit.π D i) p₀ ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p := by
  obtain ⟨U₀, p₀, hU₀, hs, he⟩ := exists_affine_etale_atlas B S hS (D.obj i) (hD i) (hQc i)
  let U₀' : AlgebraicGeometry.BigAffineFppf B S hS := ⟨U₀, hU₀⟩
  obtain ⟨U, p, q, hp⟩ := hFacts.piAff i U₀' p₀
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
  exact ⟨U₀', p₀, U, p, q, hp, P.presheaf.of_isPullback hp.flip hs,
    Q.presheaf.of_isPullback hp.flip (represented_etale_of_isEtale B S hS p₀ he)⟩

omit hD hQc hQs in
theorem exists_model_over_affine_chart_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    let c := affineStageChartConeOfLimitFacts B S hS D
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧
      (IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W) → IsAffine Wj.left) ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (c.π.app j).left)).obj Wj) := by
  dsimp only
  let E := affineStageChartOverDiagramOfLimitFacts B S hS D
    i U₀ p₀ hAffine
  let c := affineStageChartConeOfLimitFacts B S hS D
    i U₀ p₀ hAffine U.obj p q hp
  let F := E ⋙ Over.forget U₀.obj
  let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : ∀ j, IsAffine (G.obj j) := fun j =>
    (affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j).U.property
  let sc := (Over.forget U₀.obj ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone c
  have hsc : IsLimit sc := hFacts.chartLim hAffine i U₀ p₀ _ p q hp
  by_cases hW : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)
  · obtain ⟨j, Wj, hWj, hWa, e⟩ := scheme_affine_model_of_finitePresentation G sc hsc
      (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg hW
    exact ⟨j, Wj, hWj, fun _ => hWa, e⟩
  · obtain ⟨j, Wj, hWj, e⟩ := scheme_model_of_finitePresentation G sc hsc
      (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) hg
    exact ⟨j, Wj, hWj, fun h => (hW h).elim, e⟩

omit hD hQc hQs in
theorem exists_affine_model_over_affine_chart_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I)
    (U₀ : AlgebraicGeometry.BigAffineFppf B S hS) (p₀ : yoneda.obj U₀.obj ⟶ D.obj i)
    (U : AlgebraicGeometry.BigAffineFppf B S hS) (p : yoneda.obj U.obj ⟶ limit D)
    (q : U.obj ⟶ U₀.obj) (hp : IsPullback p (yoneda.map q) (limit.π D i) p₀)
    (W : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ U.obj)
    (hg : AlgebraicGeometry.FinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g))
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W)] :
    let c := affineStageChartConeOfLimitFacts B S hS D
      i U₀ p₀ hAffine U.obj p q hp
    ∃ (j : Over i) (Wj : Over ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      (affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j).U.obj)),
      AlgebraicGeometry.FinitePresentation Wj.hom ∧ IsAffine Wj.left ∧
      Nonempty (Over.mk ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ≅
        (Over.pullback
          ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (c.π.app j).left)).obj Wj) := by
  dsimp only
  obtain ⟨j, Wj, hWj, hWa, e⟩ := exists_model_over_affine_chart_of_limitFacts B S hS D
    hAffine hFacts i U₀ p₀ U p q hp W g hg
  exact ⟨j, Wj, hWj, hWa ‹_›, e⟩

omit hQc in
theorem exists_site_model_over_affine_chart_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I)
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
      (IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W) →
        IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V)) ∧
      IsPullback (yoneda.map a) (yoneda.map g ≫ p) v (limit.π D j.left) := by
  let c := affineStageChartConeOfLimitFacts B S hS D
    i U₀ p₀ hAffine U.obj p q hp
  obtain ⟨j, V₀, hV₀, hV₀aff, ⟨e⟩⟩ := exists_model_over_affine_chart_of_limitFacts B S hS D
    hAffine hFacts i U₀ p₀ U p q hp W g hg
  let Cj := affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j
  let b : U.obj ⟶ Cj.U.obj := (c.π.app j).left
  obtain ⟨V, f, a, hf, ⟨eV⟩, ha⟩ := exists_site_pullback_model B S hS b g V₀ hV₀ e
  have hbp : yoneda.map b ≫ Cj.toStage = p ≫ limit.π D j.left := by
    change yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        (affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j).toStage = p ≫ limit.π D j.left
    simp [affineStageChartLiftOfLimitFacts]
  have hbq : yoneda.map b ≫ yoneda.map Cj.toChart = yoneda.map q := by
    change yoneda.map (affineStageChartLiftOfLimitFacts B S hS D i U₀ p₀ hAffine U.obj p q hp j) ≫
        yoneda.map (affineStageChartOfLimitFacts B S hS D i U₀ p₀ hAffine j).toChart = yoneda.map q
    simp [affineStageChartLiftOfLimitFacts]
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
  refine ⟨j, V, yoneda.map f ≫ Cj.toStage, a,
    isFinitePresentation_of_scheme_chart B S hS hZ (hD j.left) (hQs j.left)
      V Cj.U.obj hVqc hVqs f Cj.toStage hpc hf.1, fun hW => ?_,
    (ha.map yoneda).paste_vert hU⟩
  let : IsAffine V₀.left := hV₀aff hW
  let : IsIso eV.hom.left :=
    inferInstanceAs (IsIso ((Over.forget ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      Cj.U.obj)).map eV.hom))
  exact IsAffine.of_isIso eV.hom.left

omit hQc in
theorem exists_affine_site_model_over_affine_chart_of_limitFacts
    (hFacts : LimitFacts B S hS D) (i : I)
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
  obtain ⟨j, V, v, a, hv, hV, ha⟩ := exists_site_model_over_affine_chart_of_limitFacts B S hS hZ D
    hD hAffine hQs hFacts i U₀ p₀ hp₀ U p q hp W g hg
  exact ⟨j, V, v, a, hv, hV ‹_›, ha⟩

end AlgebraicGeometry.Space

end

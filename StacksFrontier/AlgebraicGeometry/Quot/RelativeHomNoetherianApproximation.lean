module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAffineApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Quot.SpacePointsOverBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
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
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
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
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit

/-!
# Noetherian approximation of the relative Hom functor over an affine base

Over the base `Spec ℤ` (the terminal scheme of the site), let `f : X ⟶ T` be a morphism of finite
presentation from an algebraic space to an affine scheme `T` of the site, and let `F`, `G` be
`𝒪_X`-modules of finite presentation with `G` flat over `T` and with support proper over `T`.
Write `Γ(T) = colim ℤ[i]` as the filtered colimit of its finitely generated subrings. This file
carries out the approximation step of the proof of Stacks 08K6:

* `f` descends to a morphism of finite presentation `f_j : X_j ⟶ Spec ℤ[j]` at some stage
  (Stacks 07SK);
* `F` and `G` descend to modules of finite presentation on `X_j ×_{Spec ℤ[j]} Spec ℤ[k]` at a
  later stage (Stacks 07V7), and the descended `G` may be taken flat over `Spec ℤ[k]` with support
  proper over `Spec ℤ[k]` (Stacks 08K0, Stacks 08K2);
* the relative Hom functor of `(X, F, G)` is then the base change, along `T ⟶ Spec ℤ[k]`, of the
  relative Hom functor of the descended situation (Stacks 08JW).

So `Hom(F, G)` is an algebraic space affine and of finite presentation over `T` as soon as the
relative Hom functor is one over every affine scheme of finite type over `ℤ`, which is the case
Stacks 08JY treats.

## Main results

* `AlgebraicGeometry.Space.exists_stageModel_of_isFinitePresentation`: Stacks 07SK over an affine
  target, without a separation condition.
* `Space.HomSituation.isAffineFinitePresentationAlgebraicSpaceOverBase_of_stages`: the
  approximation step of the proof of Stacks 08K6.

## References

* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry.Space.QuasiCoherentDescent (pullbackComparison)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 07SK over an affine target.** Let `f : X ⟶ T` be a morphism of finite presentation
of algebraic spaces over `Spec ℤ` whose target is an affine object `T` of the site. Then at some
stage `Spec ℤ[j]` of `Γ(T)` there is a morphism of finite presentation `f_j : X_j ⟶ Spec ℤ[j]`
of which `f` is the base change along `T ⟶ Spec ℤ[j]`. -/
theorem exists_stageModel_of_isFinitePresentation (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ)
    {X : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
    (f : X ⟶ (schemeSpaceFunctor B _ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T))
    (hf : IsFinitePresentation B _ hZ f.hom) :
    ∃ (j : (Finset (affineRing hZ T))ᵒᵖ) (Xj : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
      (fj : Xj ⟶ (stageSystem hZ T).obj j) (k : X.1 ⟶ Xj),
      IsAlgebraicSpace B _ hZ Xj ∧ IsFinitePresentation B _ hZ fj ∧
      IsPullback k f.hom fj
        (yoneda.map ((BigAffineFppf.inclusion _ _ hZ).map ((finsetStageCone hZ T).π.app j))) := by
  classical
  let D' := stageSystem hZ T
  let ι := stageLimitIso hZ T
  have hlimAlg : IsAlgebraicSpace B _ hZ (limit D') :=
    isAlgebraicSpace_of_iso B _ hZ ι.symm
      (isAlgebraicSpace_yoneda B _ hZ ((BigAffineFppf.inclusion _ _ hZ).obj T))
  let φ : ((schemeSpaceFunctor B _ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T)).1 ⟶
      limit D' := ι.inv
  have hφfp : IsFinitePresentation B _ hZ (f.hom ≫ φ) := by
    refine isFinitePresentation_of_isPullback' (g' := 𝟙 _) (g := ι.hom)
      (IsPullback.of_horiz_isIso
        ⟨by erw [Category.assoc, ι.inv_hom_id, Category.id_comp]⟩)
      X.2 X.2 hlimAlg
      ((schemeSpaceFunctor B _ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T)).2 hf
  obtain ⟨i, Yi, hYi, hYifp, ⟨e⟩⟩ :=
    exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits B _ hZ hZ D'
      (stageSystem_isAlgebraicSpace hZ T) (stageSystem_isAffineHom hZ T)
      (stageSystem_isQuasiCompactSpace hZ T) (stageSystem_isAbsolutelyQuasiSeparated hZ T)
      (stageSystem_siteContainsBaseChangeLimits hZ T) hlimAlg (Over.mk (f.hom ≫ φ)) X.2 hφfp
  let a : X.1 ⟶ Yi.left := e.hom.left ≫ pullback.fst Yi.hom (limit.π D' i)
  have hw : e.hom.left ≫ pullback.snd Yi.hom (limit.π D' i) = f.hom ≫ φ := Over.w e.hom
  have hsqi : IsPullback a (f.hom ≫ φ) Yi.hom (limit.π D' i) := by
    refine IsPullback.of_iso_pullback (CommSq.mk ?_) ((Over.forget _).mapIso e) rfl hw
    rw [Category.assoc, pullback.condition, reassoc_of% hw]
    exact (Category.assoc _ _ _).symm
  have hb : φ ≫ limit.π D' i =
      yoneda.map ((BigAffineFppf.inclusion _ _ hZ).map ((finsetStageCone hZ T).π.app i)) :=
    stageLimitIso_inv_π hZ T i
  refine ⟨i, Yi.left, Yi.hom, a, hYi, hYifp, ?_⟩
  have : IsIso φ := Iso.isIso_inv ι
  have h₁ : IsPullback (𝟙 X.1) f.hom (f.hom ≫ φ) φ :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h₂ := h₁.paste_horiz hsqi
  rw [Category.id_comp, hb] at h₂
  exact h₂

namespace HomSituation

open CoherentSituation in
/-- **The approximation step of the proof of Stacks 08K6.**  Over `Spec ℤ`, let `u` be a
relative Hom situation whose base is (isomorphic to) an affine scheme `T` of the site, with `f`
of finite presentation, `F` and `G` of finite presentation, `G` flat over the base and with
support proper over the base. If the relative Hom functor is an algebraic space affine and of
finite presentation over the base for every such situation over an affine scheme of finite type
over `ℤ` (Stacks 08JY), then so is the relative Hom functor of `u`.

Write `Γ(T) = colim ℤ[i]`. The morphism `f` descends to `f_j : X_j ⟶ Spec ℤ[j]` (Stacks 07SK),
`F` and `G` to modules of finite presentation on `X_j ×_{Spec ℤ[j]} Spec ℤ[k]` (Stacks 07V7),
the descended `G` is flat with proper support at a later stage `m` (Stacks 08K0, Stacks 08K2),
and the relative Hom functor of `u` is the base change along `T ⟶ Spec ℤ[m]` of the one of the
descended situation (Stacks 08JW). -/
theorem isAffineFinitePresentationAlgebraicSpaceOverBase_of_stages
    (hstage : ∀ (T₀ : BigAffineFppf B (⊤_ Scheme.{u}) hZ),
      LocallyOfFiniteType (terminal.from ((BigAffineFppf.toScheme _ _ hZ).obj T₀)) →
      ∀ (v : HomSituation B (⊤_ Scheme.{u}) hZ),
        v.base = (schemeSpaceFunctor B _ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T₀) →
        IsFinitePresentation B _ hZ v.f.hom → v.F.IsFinitePresentationOnSite →
        v.G.IsFinitePresentationOnSite → IsFlatOver B _ hZ v.X.2 v.f.hom v.G →
        HasProperSupportOver v.f v.G →
        v.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B _ hZ))
    (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ) (u : HomSituation B (⊤_ Scheme.{u}) hZ)
    (eY : u.base ≅ (schemeSpaceFunctor B _ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T))
    (hf : IsFinitePresentation B _ hZ u.f.hom) (hF : u.F.IsFinitePresentationOnSite)
    (hG : u.G.IsFinitePresentationOnSite) (hflat : IsFlatOver B _ hZ u.X.2 u.f.hom u.G)
    (hproper : HasProperSupportOver u.f u.G) :
    u.IsAffineFinitePresentationAlgebraicSpaceOverBase (modulePushforwardCoherence B _ hZ) := by
  classical
  let incl := BigAffineFppf.inclusion B (⊤_ Scheme.{u}) hZ
  let E := finsetStageDiagram hZ (affineRing hZ T)
  let c := finsetStageCone hZ T
  have hc : IsLimit ((BigAffineFppf.toScheme _ _ hZ).mapCone c) := isLimit_finsetStageCone hZ T
  obtain ⟨j, Xj, fj, k, hXj, hfj, hP⟩ :=
    exists_stageModel_of_isFinitePresentation hZ T (u.f ≫ eY.hom)
      (isFinitePresentation_comp_iso u.X.2 u.base.2
        ((schemeSpaceFunctor B _ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T)).2 u.f.hom
        ((ObjectProperty.ι _).mapIso eY) hf)
  let D₀ : CoherentSituation B (⊤_ Scheme.{u}) hZ :=
    { X := ⟨Xj, hXj⟩
      Y := (schemeSpaceFunctor B _ hZ).obj (incl.obj (E.obj j))
      f := ObjectProperty.homMk fj
      finitePresentation := hfj }
  let g : (schemeSpaceFunctor B _ hZ).obj (incl.obj (E.obj j)) ⟶ D₀.Y := 𝟙 _
  let sys := D₀.stageTestSystem E g
  let cT := D₀.stageTestCone E c g
  have hb : cT.pt.hom.hom = yoneda.map (incl.map (c.π.app j)) := Category.comp_id _
  have hP' : IsPullback k (u.f ≫ eY.hom).hom fj cT.pt.hom.hom := hb ▸ hP
  have sqX : IsPullback (ObjectProperty.homMk k : u.X ⟶ D₀.X) (u.f ≫ eY.hom) D₀.f cT.pt.hom :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hP'.w) hP'
  let ψ : u.X ≅ D₀.space cT.pt :=
    sqX.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B _ hZ D₀.f cT.pt.hom)
  have hψ : ψ.hom ≫ D₀.projection cT.pt = u.f ≫ eY.hom :=
    sqX.isoIsPullback_hom_snd _ _ _
  have hψinv : IsPullback ψ.inv (D₀.projection cT.pt) u.f eY.inv :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ (Iso.isIso_inv ψ) (Iso.isIso_inv eY)
      ⟨(Iso.inv_comp_eq ψ).2 ((Category.comp_id _).symm.trans
        ((congrArg (u.f ≫ ·) eY.hom_inv_id.symm).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ eY.inv) hψ.symm).trans (Category.assoc _ _ _)))))⟩
  let F' := (modulePullback B _ hZ ψ.inv).obj u.F
  let G' := (modulePullback B _ hZ ψ.inv).obj u.G
  have hF' : F'.IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePullback B _ hZ _ _ hF
  have hG' : G'.IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePullback B _ hZ _ _ hG
  have hG'flat : IsFlatOver B _ hZ (D₀.space cT.pt).2 (D₀.projection cT.pt).hom G' :=
    isFlatOver_modulePullback_of_isFinitePresentationOnSite B _ hZ hψinv u.G hG hflat
  have hG'proper : HasProperSupportOver (D₀.projection cT.pt) G' :=
    hproper.of_isPullback hψinv hG
  obtain ⟨-, -, hES⟩ := D₀.finitePresentationModule_isColimit_baseChange sys cT hZ
    (fun e => D₀.isAffineHom_stageSpaceSystem_map E g e)
    (D₀.isQuasiCompactSpace_stageSpaceSystem E g)
    (D₀.isAbsolutelyQuasiSeparated_stageSpaceSystem E g hZ)
    (D₀.isLimit_stageSpaceCone E c g hc) (D₀.siteContainsBaseChangeLimits_stageSpaceSystem E c g hc)
  obtain ⟨kF, QF, hQF, ⟨αF⟩⟩ := hES F' hF'
  obtain ⟨kG, QG, hQG, ⟨αG⟩⟩ := hES G' hG'
  let A₀ : CoherentObject D₀ :=
    { T := cT.pt
      F := G'
      quasicoherent := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B _ hZ ψ.inv
        u.G u.quasicoherent_G
      finitePresentation := hG'
      flat := hG'flat
      properSupport := hG'proper }
  obtain ⟨jG, eG, hjG⟩ := D₀.flatProperSupportDescends E c hc A₀ rfl g kG (cT.π.app kG) rfl QG
    hQG αG.symm
  let m : Over j := IsCofiltered.min kF jG
  let eF : m ⟶ kF := IsCofiltered.minToLeft kF jG
  let eGm : m ⟶ kG := IsCofiltered.minToRight kF jG ≫ eG
  let Tm := sys.obj m
  let Fm := (modulePullback B _ hZ (D₀.relativeMap (sys.map eF))).obj QF
  let Gm := (modulePullback B _ hZ (D₀.relativeMap (sys.map eGm))).obj QG
  have hFm : Fm.IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePullback B _ hZ _ _ hQF
  have hGm : Gm.IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_modulePullback B _ hZ _ _ hQG
  have hsqm := isPullback_baseChangeMap D₀.f (sys.map (IsCofiltered.minToRight kF jG))
  have hGmflat : IsFlatOver B _ hZ (D₀.space Tm).2 (D₀.projection Tm).hom Gm :=
    isFlatOver_of_isPullback_of_comp hsqm QG hQG (D₀.relativeMap (sys.map eG))
      (D₀.relativeMap (sys.map eGm)) (D₀.relativeMap_map_comp sys _ eG) hjG.1
  have hGmproper : HasProperSupportOver (D₀.projection Tm) Gm :=
    HasProperSupportOver.of_isPullback_of_comp hsqm QG hQG (D₀.relativeMap (sys.map eG))
      (D₀.relativeMap (sys.map eGm)) (D₀.relativeMap_map_comp sys _ eG) hjG.2
  let um : HomSituation B (⊤_ Scheme.{u}) hZ :=
    { X := D₀.space Tm
      base := (schemeSpaceFunctor B _ hZ).obj Tm.left
      f := D₀.projection Tm
      F := Fm
      G := Gm
      quasicoherent_F := inferInstance
      quasicoherent_G := inferInstance }
  have hum : um.IsAffineFinitePresentationAlgebraicSpaceOverBase
      (modulePushforwardCoherence B _ hZ) :=
    hstage (E.obj m.left) (locallyOfFiniteType_terminalFrom_specAdjoinFinsetDiagram_obj _ m.left)
      um rfl (D₀.isFinitePresentation_projection Tm) hFm hGm hGmflat hGmproper
  let gm : u.base ⟶ um.base := eY.hom ≫ (schemeSpaceFunctor B _ hZ).map (cT.π.app m).left
  have sq₁ : IsPullback ψ.hom u.f (D₀.projection cT.pt) eY.hom :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ (Iso.isIso_hom ψ) (Iso.isIso_hom eY) ⟨hψ⟩
  have sqm : IsPullback (ψ.hom ≫ D₀.relativeMap (cT.π.app m)) u.f um.f gm :=
    sq₁.paste_horiz (isPullback_baseChangeMap D₀.f (cT.π.app m))
  let e : u.X ≅ (um.baseChangedSituation gm).X :=
    sqm.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B _ hZ um.f gm)
  have he₁ : e.hom ≫ (um.baseChangedSituation gm).f = u.f := sqm.isoIsPullback_hom_snd _ _ _
  have he₂ : e.hom ≫ um.baseChangedSourceProjection gm = ψ.hom ≫ D₀.relativeMap (cT.π.app m) :=
    sqm.isoIsPullback_hom_fst _ _ _
  let ιψ : ∀ M : Modules.{u, u} B _ hZ u.X.1 u.X.2,
      M ≅ (modulePullback B _ hZ ψ.hom).obj ((modulePullback B _ hZ ψ.inv).obj M) := fun M =>
    ((modulePullbackIdIso B _ hZ u.X).app M).symm ≪≫
      pullbackComparison B _ hZ ψ.hom ψ.inv (𝟙 _) ψ.hom_inv_id M
  let τ : ∀ {k' : Over j} (ek : m ⟶ k') (Q : Modules.{u, u} B _ hZ (D₀.space (sys.obj k')).1
      (D₀.space (sys.obj k')).2) (M : Modules.{u, u} B _ hZ u.X.1 u.X.2),
      ((modulePullback B _ hZ ψ.inv).obj M ≅
        (modulePullback B _ hZ (D₀.relativeMap (cT.π.app k'))).obj Q) →
      (M ≅ (modulePullback B _ hZ e.hom).obj ((modulePullback B _ hZ
        (um.baseChangedSourceProjection gm)).obj
          ((modulePullback B _ hZ (D₀.relativeMap (sys.map ek))).obj Q))) :=
    fun {k'} ek Q M α => ιψ M ≪≫ (modulePullback B _ hZ ψ.hom).mapIso (α ≪≫
      pullbackComparison B _ hZ (D₀.relativeMap (cT.π.app m)) (D₀.relativeMap (sys.map ek))
        (D₀.relativeMap (cT.π.app k')) (D₀.relativeMap_cone_comp sys cT ek) Q) ≪≫
      (pullbackComparison B _ hZ ψ.hom (D₀.relativeMap (cT.π.app m)) _ rfl _).symm ≪≫
      pullbackComparison B _ hZ e.hom (um.baseChangedSourceProjection gm) _ he₂ _
  have hiso := homFunctorIsoOfIso u (modulePushforwardCoherence B _ hZ) e
    (um.baseChangedSituation gm).f he₁ (um.baseChangedSituation gm).F
    (um.baseChangedSituation gm).G (τ eF QF u.F αF) (τ eGm QG u.G αG)
  exact (hum.baseChangedSituation gm).of_iso hiso.symm

end HomSituation

end AlgebraicGeometry.Space

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeFinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation

/-!
# The direct image along a quasi-finite morphism on stacks of coherent sheaves

Let `B` be an algebraic space and let `π : X ⟶ Y` be a quasi-finite morphism of algebraic spaces
which are separated and of finite presentation over `B`. Then `π_*` induces a morphism
`Coh_{X/B} ⟶ Coh_{Y/B}`: for an object `(T, ℱ)` of `Coh_{X/B}` the pair `(T, π_{T,*}ℱ)` is an
object of `Coh_{Y/B}`, and for `h : T' ⟶ T` the base change map
`Y_h^* π_{T,*}ℱ ⟶ π_{T',*} X_h^* ℱ` is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.exists_fittingReduction`: the module `ℱ` of an object
  `(T, ℱ)` of `Coh_{X/Y}` is the direct image, along a closed immersion `i : Z ⟶ X_T` of finite
  presentation with `Z` proper over `T`, of a quasi-coherent `𝒪_Z`-module of finite presentation
  which is flat over `T`.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.exists_finiteReduction`: the composite
  `Z ⟶ X_T ⟶ Y_T` is finite and of finite presentation.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.isCoherentModule_pushforward`:
  `(T, π_{T,*}ℱ)` is an object of `Coh_{Y/B}`.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.isIso_baseChange_app`: the base change
  maps of `π_*` are isomorphisms at the modules of objects of `Coh_{X/B}`.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.cohPushforward`: the 1-morphism
  `Coh_{X/B} ⟶ Coh_{Y/B}` of categories over the big fppf site induced by `π_*`.

## References

* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 0CZ6](https://stacks.math.columbia.edu/tag/0CZ6)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0610](https://stacks.math.columbia.edu/tag/0610)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_coherentStackPushforwardQuasiFinite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_coherentStackPushforwardQuasiFinite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_coherentStackPushforwardQuasiFinite B S hS).has_limit _

/-- If a composite of four morphisms and its first, third and fourth factors are isomorphisms, so
is its second factor. -/
theorem isIso_of_isIso_comp₄ {C : Type*} [Category* C] {W X Y Z V : C} {a : W ⟶ X} {b : X ⟶ Y}
    {c : Y ⟶ Z} {d : Z ⟶ V} (ha : IsIso a) (hc : IsIso c) (hd : IsIso d)
    (h : IsIso (a ≫ b ≫ c ≫ d)) : IsIso b := by
  rw [show b = inv a ≫ (a ≫ b ≫ c ≫ d) ≫ inv d ≫ inv c by simp]
  infer_instance

/-- A natural transformation invertible at an object is invertible at every isomorphic object. -/
theorem NatTrans.isIso_app_of_iso_of_isIso_app {C : Type*} {D : Type*} [Category* C]
    [Category* D] {F G : C ⥤ D} (σ : F ⟶ G) {X Y : C} (e : X ≅ Y) (h : IsIso (σ.app X)) :
    IsIso (σ.app Y) := by
  rw [show σ.app Y = inv (F.map e.hom) ≫ σ.app X ≫ G.map e.hom by
    rw [← σ.naturality e.hom, IsIso.inv_hom_id_assoc]]
  infer_instance

/-! ### The reduction along the zeroth Fitting ideal -/

/-- For an object `(T, ℱ)` of `Coh_{X/Y}` there is a closed immersion `i : Z ⟶ X_T` of finite
presentation with `Z ⟶ T` proper, and a quasi-coherent `𝒪_Z`-module `𝒢` of finite presentation,
flat over `T`, with `i_*𝒢 ≅ ℱ`. -/
theorem CoherentObject.exists_fittingReduction {D : CoherentSituation B S hS}
    (A : CoherentObject D) :
    ∃ (Z : AlgebraicSpaces B S hS) (i : Z ⟶ D.space A.T) (G : Modules.{u, u} B S hS Z.1 Z.2),
      IsClosedImmersion B S hS i.hom ∧ IsFinitePresentation B S hS i.hom ∧
        IsProper B S hS (i ≫ D.projection A.T).hom ∧ G.IsQuasicoherentOnSite ∧
        G.IsFinitePresentationOnSite ∧ IsFlatOver B S hS Z.2 (i ≫ D.projection A.T).hom G ∧
        Nonempty ((modulePushforward B S hS i).obj G ≅ A.F) := by
  obtain ⟨hp, hU, hproper⟩ := A.properSupport
  have := A.quasicoherent
  have := A.finitePresentation
  have hqcFit : ∀ r : ℕ, (fittingIdeal B S hS (D.space A.T).1 (D.space A.T).2 A.F
      r).toSheafOfModules.IsQuasicoherentOnSite := fun r ↦
    (isFiniteTypeQuasicoherentIdeal_fittingIdeal_of_isFinitePresentationOnSite (D.space A.T) A.F
      A.quasicoherent A.finitePresentation r).1
  obtain ⟨Zs, hZs, -⟩ := exists_fittingClosedSubspaces B S hS (D.space A.T) A.F hqcFit
  obtain ⟨H, hHqc, -, ⟨e⟩⟩ :=
    exists_module_on_fittingClosedSubspace B S hS (D.space A.T) A.F (Zs 0) (hZs 0)
  let i := closedSubspaceInclusion B S hS (D.space A.T) (Zs 0)
  have hi : IsClosedImmersion B S hS i.hom := (Zs 0).2.2
  have hrange : Set.range (pointsMap B S hS (Zs 0).1.toFunctor (Zs 0).1.ι) ⊆
      supportOfSheaf B S hS (D.space A.T).1 ((SheafOfModules.toSheaf _).obj A.F) :=
    (range_pointsMap_schemeTheoreticSupport_eq_supportOfSheaf B S hS (D.space A.T) A.F (Zs 0)
      (hZs 0)).2.1.subset
  have hZT : IsProper B S hS (i.hom ≫ (D.projection A.T).hom) :=
    isProper_comp_of_hasProperSupport_of_range_subset B S hS (D.space A.T).2
      ((schemeSpaceFunctor B S hS).obj A.T.left).2 (D.projection A.T).hom hp ⟨hU, hproper⟩
      (closedSubspaceToSpace B S hS (D.space A.T) (Zs 0)).2 i.hom hi hrange
  have hHfp : SheafOfModules.IsFinitePresentationOnSite H :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso
      (((modulePullback B S hS i).mapIso e).symm ≪≫
        (modulePullbackCounitIso B S hS i hi).app H)
      (isFinitePresentationOnSite_modulePullback B S hS i A.F A.finitePresentation)
  have hflat : IsFlatOver B S hS (closedSubspaceToSpace B S hS (D.space A.T) (Zs 0)).2
      (i ≫ D.projection A.T).hom H :=
    have := hHqc
    isFlatOver_of_isFlatOver_modulePushforward B S hS i hi (D.projection A.T) H
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm A.quasicoherent)
      (IsFlatOver.of_iso B S hS (D.space A.T).2 e.symm A.flat)
  exact ⟨closedSubspaceToSpace B S hS (D.space A.T) (Zs 0), i, H, hi,
    isFinitePresentation_ι_of_definingIdealSheaf_eq_fittingIdeal_zero B S hS (D.space A.T) A.F
      A.quasicoherent A.finitePresentation (Zs 0) (hZs 0),
    hZT, hHqc, hHfp, hflat, ⟨e⟩⟩

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The projection `X_T ⟶ T` of the base change of a morphism of finite presentation is of
finite presentation (Stacks 03XR). -/
theorem isFinitePresentation_projection (T : SchemesOver D.Y) :
    IsFinitePresentation B S hS (D.projection T).hom :=
  IsFinitePresentation.of_isPullback B S hS (D.space T).2 D.X.2
    ((schemeSpaceFunctor B S hS).obj T.left).2 D.Y.2
    (IsPullback.of_hasPullback D.f.hom T.hom.hom) D.finitePresentation

end CoherentSituation

namespace CoherentPushforwardSituation

variable (D : CoherentPushforwardSituation B S hS)

/-- `π_T ≫ (Y_T ⟶ T) = (X_T ⟶ T)` on the underlying morphisms of presheaves. -/
theorem mapAt_hom_comp_projection_hom (T : SchemesOver D.base) :
    (D.mapAt T).hom ≫ (D.target.projection T).hom = (D.source.projection T).hom :=
  congrArg (fun m ↦ m.hom) (D.mapAt_comp_projection T)

/-- For an object `(T, ℱ)` of `Coh_{X/B}` there is a closed immersion `i : Z ⟶ X_T` and a
quasi-coherent `𝒪_Z`-module `𝒢` of finite presentation, flat over `T`, with `i_*𝒢 ≅ ℱ`, such that
the composite `Z ⟶ X_T ⟶ Y_T` of `i` and `π_T` is finite and of finite presentation. -/
theorem exists_finiteReduction (A : CoherentObject D.source) :
    ∃ (Z : AlgebraicSpaces B S hS) (i : Z ⟶ D.source.space A.T)
      (G : Modules.{u, u} B S hS Z.1 Z.2),
      IsClosedImmersion B S hS i.hom ∧ IsFinite B S hS (i ≫ D.mapAt A.T).hom ∧
        IsFinitePresentation B S hS (i ≫ D.mapAt A.T).hom ∧ G.IsQuasicoherentOnSite ∧
        G.IsFinitePresentationOnSite ∧
        IsFlatOver B S hS Z.2 ((i ≫ D.mapAt A.T) ≫ D.target.projection A.T).hom G ∧
        Nonempty ((modulePushforward B S hS i).obj G ≅ A.F) := by
  obtain ⟨Z, i, G, hi, hifp, hZT, hGqc, hGfp, hGflat, he⟩ := A.exists_fittingReduction
  have hcomm := D.mapAt_hom_comp_projection_hom A.T
  have hWZ : IsProper B S hS (i.hom ≫ (D.mapAt A.T).hom ≫ (D.target.projection A.T).hom) := by
    rwa [hcomm]
  have hfin : IsFinite B S hS (i ≫ D.mapAt A.T).hom :=
    isFinite_comp_of_isLocallyQuasiFinite_of_comp_isProper_of_isSeparated B S hS Z.2
      (D.source.space A.T).2 (D.target.space A.T).2
      ((schemeSpaceFunctor B S hS).obj A.T.left).2 i.hom (D.mapAt A.T).hom
      (D.target.projection A.T).hom
      (isLocallyQuasiFinite_of_isImmersion B S hS i.hom
        (isImmersion_of_isClosedImmersion B S hS hi))
      (D.isLocallyQuasiFinite_mapAt A.T) hWZ (D.isSeparated_targetProjection A.T)
  have hfp : IsFinitePresentation B S hS (i ≫ D.mapAt A.T).hom := by
    refine isFinitePresentation_of_comp_isProper_of_isSeparated B S hS Z.2
      (D.target.space A.T).2 ((schemeSpaceFunctor B S hS).obj A.T.left).2
      (i ≫ D.mapAt A.T).hom (D.target.projection A.T).hom ?_ hWZ
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (D.target.isFinitePresentation_projection A.T).1) (D.isSeparated_targetProjection A.T)
    show IsLocallyOfFinitePresentation B S hS
      (i.hom ≫ (D.mapAt A.T).hom ≫ (D.target.projection A.T).hom)
    rw [hcomm]
    exact isLocallyOfFinitePresentation_comp B S hS Z.2 (D.source.space A.T).2
      ((schemeSpaceFunctor B S hS).obj A.T.left).2 _ _ hifp.1
      (D.source.isFinitePresentation_projection A.T).1
  have hflat : IsFlatOver B S hS Z.2 ((i ≫ D.mapAt A.T) ≫ D.target.projection A.T).hom G := by
    have : ((i ≫ D.mapAt A.T) ≫ D.target.projection A.T).hom =
        (i ≫ D.source.projection A.T).hom := by
      show i.hom ≫ (D.mapAt A.T).hom ≫ (D.target.projection A.T).hom = _
      rw [hcomm]; rfl
    rwa [this]
  exact ⟨Z, i, G, hi, hfin, hfp, hGqc, hGfp, hflat, he⟩

/-- For an object `(T, ℱ)` of `Coh_{X/B}` the direct image `π_{T,*}ℱ` is quasi-coherent, of finite
presentation, flat over `T` and has support proper over `T`, so `(T, π_{T,*}ℱ)` is an object of
`Coh_{Y/B}`. -/
theorem isCoherentModule_pushforward (A : CoherentObject D.source) :
    D.target.IsCoherentModule A.T ((modulePushforward B S hS (D.mapAt A.T)).obj A.F) := by
  obtain ⟨Z, i, G, hi, hfin, hfp, hGqc, hGfp, hGflat, ⟨e⟩⟩ := D.exists_finiteReduction A
  let φ := i ≫ D.mapAt A.T
  let e' : (modulePushforward B S hS φ).obj G ≅
      (modulePushforward B S hS (D.mapAt A.T)).obj A.F :=
    ((modulePushforwardCompIso B S hS i (D.mapAt A.T)).app G).symm ≪≫
      (modulePushforward B S hS (D.mapAt A.T)).mapIso e
  have hqc : ((modulePushforward B S hS φ).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS φ (IsFinite.isAffineHom hfin) G
      hGqc
  let hrep := relativelyRepresentable_hom_of_isFinite B S hS φ hfin
  have hfpG : G.IsFinitePresentation :=
    SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' G hGfp
  have hfpφ : ((modulePushforward B S hS φ).obj G).IsFinitePresentation :=
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((modulePushforwardChartIso B S hS φ hrep).app G).symm
      ((isFinitePresentation_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite B S hS φ
        hfin hfp G hGqc).1 hfpG)
  have hfpOn : ((modulePushforward B S hS φ).obj G).IsFinitePresentationOnSite :=
    have := hfpφ
    SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation _
  have hfpF : ((modulePushforward B S hS (D.mapAt A.T)).obj A.F).IsFinitePresentationOnSite :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso e' hfpOn
  have := hfpF
  refine ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e' hqc, hfpF,
    IsFlatOver.of_iso B S hS (D.target.space A.T).2 e'
      (isFlatOver_modulePushforward_of_isFinite B S hS φ hfin (D.target.projection A.T) G hGqc
        hGflat), ?_⟩
  obtain ⟨hp, hU, hproper⟩ := A.properSupport
  have hcomm := D.mapAt_hom_comp_projection_hom A.T
  have hpY := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (D.target.isFinitePresentation_projection A.T).1
  have hK := isClosed_image_of_isProperOver B S hS (D.source.space A.T).2
    (D.target.space A.T).2 ((schemeSpaceFunctor B S hS).obj A.T.left).2 (D.mapAt A.T).hom
    (D.source.projection A.T).hom (D.target.projection A.T).hom hcomm hp hpY
    (D.isSeparated_targetProjection A.T) _ hU hproper
  have hKproper := isProperOver_image_of_isSeparated B S hS (D.source.space A.T).2
    (D.target.space A.T).2 ((schemeSpaceFunctor B S hS).obj A.T.left).2 (D.mapAt A.T).hom
    (D.source.projection A.T).hom (D.target.projection A.T).hom hcomm hp hpY
    (D.isSeparated_targetProjection A.T) _ hU hproper hK
  have hsub : D.target.support A.T ((modulePushforward B S hS (D.mapAt A.T)).obj A.F) ⊆
      pointsMap B S hS (D.source.space A.T).1 (D.mapAt A.T).hom '' D.source.support A.T A.F :=
    (supportOfSheaf_modulePushforward_subset_closure B S hS (D.mapAt A.T) A.F).trans
      (closure_minimal subset_rfl hK)
  have hcl : IsClosed (D.target.support A.T ((modulePushforward B S hS (D.mapAt A.T)).obj A.F)) :=
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS _ (D.target.space A.T).2 _
  exact ⟨hpY, hcl, isProperOver_of_subset B S hS (D.target.space A.T).2
    ((schemeSpaceFunctor B S hS).obj A.T.left).2 _ hpY _ _ hcl hK hsub hKproper⟩

/-- For an object `(T, ℱ)` of `Coh_{X/B}` and a morphism `h : T' ⟶ T` of test schemes the base
change map `Y_h^* π_{T,*}ℱ ⟶ π_{T',*} X_h^*ℱ` is an isomorphism. -/
theorem isIso_baseChange_app (A : CoherentObject D.source) {T : SchemesOver D.base}
    (h : T ⟶ A.T) : IsIso ((D.baseChange h).app A.F) := by
  obtain ⟨Z, i, G, hi, hfin, -, hGqc, -, -, ⟨e⟩⟩ := D.exists_finiteReduction A
  let fst : AlgebraicSpaces.fiberProduct B S hS i (D.source.relativeMap h) ⟶ Z :=
    ObjectProperty.homMk (pullback.fst i.hom (D.source.relativeMap h).hom)
  let snd : AlgebraicSpaces.fiberProduct B S hS i (D.source.relativeMap h) ⟶ D.source.space T :=
    ObjectProperty.homMk (pullback.snd i.hom (D.source.relativeMap h).hom)
  have sq₁ : IsPullback fst snd i (D.source.relativeMap h) :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS i (D.source.relativeMap h)
  have sq : IsPullback fst (snd ≫ D.mapAt T) (i ≫ D.mapAt A.T) (D.target.relativeMap h) :=
    sq₁.paste_vert (D.isPullback_relativeMap h)
  have hout := isIso_moduleBaseChangeMap_app_of_isAffineHom sq (IsFinite.isAffineHom hfin) G hGqc
  have hi' : IsIso ((moduleBaseChangeMap i (D.source.relativeMap h) snd fst sq₁.w).app G) :=
    isIso_moduleBaseChangeMap_app_of_isAffineHom sq₁
      (isAffineHom_of_isClosedImmersion B S hS i.hom hi) G hGqc
  rw [moduleBaseChangeMap_comp i (D.source.relativeMap h) snd fst (D.mapAt A.T)
    (D.target.relativeMap h) (D.mapAt T) sq₁.w (D.relativeMap_comp_mapAt h) sq.w G] at hout
  have h4 := isIso_of_isIso_comp₄
    (Functor.map_isIso (modulePullback B S hS (D.target.relativeMap h))
      (((modulePushforwardCompIso B S hS i (D.mapAt A.T)).app G).inv))
    (Functor.map_isIso (modulePushforward B S hS (D.mapAt T))
      ((moduleBaseChangeMap i (D.source.relativeMap h) snd fst sq₁.w).app G))
    (Iso.isIso_hom ((modulePushforwardCompIso B S hS snd (D.mapAt T)).app
      ((modulePullback B S hS fst).obj G))) hout
  exact NatTrans.isIso_app_of_iso_of_isIso_app (D.baseChange h) e h4

/-- For a quasi-finite morphism of algebraic spaces separated and of finite presentation over the
base, the direct image of the module of an object of `Coh_{X/B}` is the module of an object of
`Coh_{Y/B}`, and the base change maps are isomorphisms at the modules of objects of
`Coh_{X/B}`. -/
theorem preservesCoherence : D.PreservesCoherence :=
  ⟨D.isCoherentModule_pushforward, fun A _ h ↦ D.isIso_baseChange_app A h⟩

/-! ### The direct image on stacks of coherent sheaves -/

/-- Let `B` be an algebraic space and let `π : X ⟶ Y` be a quasi-finite
morphism of algebraic spaces which are separated and of finite presentation over `B`.  Then `π_*`
induces a morphism `Coh_{X/B} ⟶ Coh_{Y/B}`: the 1-morphism of categories over the big fppf site
sending an object `(T, ℱ)` to `(T, π_{T,*}ℱ)` and a morphism `(h, φ)`, with `φ : X_h^*ℱ' ⟶ ℱ`, to
`(h, θ_h ≫ π_{T,*}φ)`, where `θ_h : Y_h^*π_{T',*}ℱ' ⟶ π_{T,*}X_h^*ℱ'` is the base change map. -/
@[stacks 0DN9]
def cohPushforward :
    coherentBasedCategory D.source.categoryData ⥤ᵇ coherentBasedCategory D.target.categoryData :=
  pushforwardBased D.preservesCoherence

/-- The direct image keeps the test scheme of an object. -/
@[simp]
theorem cohPushforward_obj_T (A : CoherentObject D.source) :
    (D.cohPushforward.obj A).T = A.T :=
  rfl

/-- The module of the image of an object `(T, ℱ)` is `π_{T,*}ℱ`. -/
@[simp]
theorem cohPushforward_obj_F (A : CoherentObject D.source) :
    (D.cohPushforward.obj A).F = (modulePushforward B S hS (D.mapAt A.T)).obj A.F :=
  rfl

/-- The direct image keeps the morphism of test schemes of a morphism. -/
theorem cohPushforward_map_base {A A' : CoherentObject D.source} (m : CoherentHom A A') :
    (D.cohPushforward.map (X := A) (Y := A') m : CoherentHom _ _).base = m.base :=
  rfl

/-- The comparison of modules of the image of a morphism `(h, φ)` is `θ_h ≫ π_{T,*}φ`. -/
theorem cohPushforward_map_fibre {A A' : CoherentObject D.source} (m : CoherentHom A A') :
    (D.cohPushforward.map (X := A) (Y := A') m : CoherentHom _ _).fibre =
      (D.baseChange m.base).app A'.F ≫ (modulePushforward B S hS (D.mapAt A.T)).map m.fibre :=
  rfl

/-- The 1-morphism `Coh_{X/B} ⟶ Coh_{Y/B}` induced by `π_*` commutes with the projections of
`Coh_{X/B}` and `Coh_{Y/B}` to the test schemes over `B` which forget the module. -/
theorem cohPushforward_comp_coherentToBase :
    D.cohPushforward.toFunctor ⋙ (coherentToBase D.target.categoryData).toFunctor =
      (coherentToBase D.source.categoryData).toFunctor :=
  rfl

end CoherentPushforwardSituation

end AlgebraicGeometry.Space

end

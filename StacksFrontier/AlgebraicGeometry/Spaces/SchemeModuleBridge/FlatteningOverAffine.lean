module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.BlowupOfRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.RepresentableOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ModuleFlatteningBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFinitePresentationBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestrictionOver
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange

/-!
# Flattening by blowing up over an affine base

Let `A` be an affine algebraic space over a scheme `S`, let `f : X ⟶ A` be locally of finite
presentation with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite type and
let `U ⊆ A` be a quasi-compact open subspace such that `F|_{X ×_A U}` is of finite presentation
and flat over `U`.  Then there is a closed subspace `Z ⊆ A` of finite presentation, disjoint from
`U`, and a blowup `b : A' ⟶ A` in `Z`, such that the strict transform of `F` with respect to `b`
is of finite presentation and flat over `A'`.

This is the step of the proof of Stacks 087C that applies the theorem for schemes, Stacks 0815,
over an affine scheme étale over the base.  Its conclusion is stated entirely in the vocabulary
of algebraic spaces: the centre is a closed subspace of `A`, the blowup is one in the sense of
the universal property of Stacks 085U, and the strict transform is the one of Stacks 0862.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatOverOpenOnCharts`: flatness of a module over an open subspace of
  the target, read on charts, the companion of
  `AlgebraicGeometry.Space.IsFinitePresentationOverOpenOnCharts`.
* `AlgebraicGeometry.Space.restrictOverChartDiagram`: the square of charts of `X ×_A U ⟶ U` cut
  out by `U` in a square of charts of `f`.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentationOverOpenOnCharts_of_isFinitePresentationOnSite`,
  `AlgebraicGeometry.Space.isFlatOverOpenOnCharts_of_isFlatOver`: finite presentation and
  flatness of `F|_{X ×_A U}` over `U` are read on every commuting square of charts of `f`.
* `AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_isAffineSpace`: the statement above.

## Implementation notes

Write `A` as the algebraic space of an affine scheme `T`.  The source applies Stacks 0815 to
`X ⟶ T`; here it is applied to an affine scheme `V` with a surjective étale morphism `V ⟶ X`,
which exists because `X` is quasi-compact.  With `T` it forms a commuting square of charts of
`f`, on which the hypotheses on `F` are the hypotheses of Stacks 0815.  The ideal `I ⊆ 𝒪_T` it
produces cuts out the closed subspace `AlgebraicGeometry.Space.closedSubspaceOfIdeal`, transported
to `A`.  Every blowup of `A` in it, pulled back to `T`, is the space of the scheme blowup,
`AlgebraicGeometry.Space.exists_iso_yoneda_blowUpObj_of_isBlowupAlong`.  The scheme `V ×_T T'`
is then an étale chart of `X ×_A A'` covering it, on which the strict transform of `F` is the
scheme strict transform of Stacks 0815,
`AlgebraicGeometry.Space.nonempty_strictTransformSheaf_iso_restrictToChart`.  Flatness and finite
presentation are read off that one chart: flatness at every point is flatness at a point of one
chart through it, `AlgebraicGeometry.Space.isFlatOver_of_forall_isFlatOverAtPoint`, and finite
presentation is local on a covering.

## References

* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

variable (B S hS) in
/-- A module on the source of a morphism of algebraic spaces is *flat over an open subspace `V`
of the target, on charts* when, on every commuting square of étale scheme charts, the
restriction of the module to the inverse image of the chart-level `V` is flat over the
chart-level `V`.  This is the chartwise reading of flatness of `F|_{f⁻¹V}` over `V`, the
companion of `AlgebraicGeometry.Space.IsFinitePresentationOverOpenOnCharts`. -/
abbrev IsFlatOverOpenOnCharts {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (F : Modules.{u, u} B S hS X hX)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V) : Prop :=
  ∀ d : ChartDiagram B S hS X Y f,
    AlgebraicGeometry.IsFlatOver
      (((BigFppfOver.toScheme B S hS).map d.g) ∣_
        chartOpenOfOpenSubspace B S hS V hV d.V).toLRSHom.toShHom
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ
        chartOpenOfOpenSubspace B S hS V hV d.V).ι).obj (chartModule B S hS hX F d.U))

/-! ### Hypotheses over an open subspace, read on charts -/

section OpenOnCharts

/-- A morphism into a presheaf through a monomorphism is étale as soon as its composite with the
monomorphism is: it is the base change of that composite along the monomorphism. -/
theorem presheaf_etale_of_comp_mono {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : P ⟶ Q)
    [Mono m] {Y : BigFppfOver B S hS} (g : yoneda.obj Y ⟶ P)
    (h : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf (g ≫ m)) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf g :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 _) (snd := g) (f := g ≫ m) (g := m)
      ⟨Category.id_comp _⟩) h

/-- A scheme property containing isomorphisms holds, on the presheaf level, for any isomorphism
out of a representable presheaf. -/
private theorem presheaf_inverseImage_of_isIso (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), IsIso g → P g) {T : BigFppfOver B S hS}
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : yoneda.obj T ⟶ Q) [IsIso g] :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf g := by
  have hid := presheaf_id_of_iso B S hS (MorphismProperty.inverseImage P
    (BigFppfOver.toScheme B S hS)) (fun _ _ g _ => hP _ inferInstance) T
  simpa using MorphismProperty.RespectsIso.postcomp _ g _ hid

variable {X A : AlgebraicSpaces B S hS} (f : X ⟶ A) (U : OpenSubspaces B S hS A.1)
  (d : ChartDiagram B S hS X.1 A.1 f.hom)

/-- The open of the source chart of a commuting square of étale scheme charts of `f` lying over
the open subspace `U` of the target. -/
abbrev chartPreimageOpen : (chartScheme d.U).Opens :=
  (BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ chartOpenOfOpenSubspace B S hS U.1 U.2 d.V

/-- The points of the chart of `X` cut out by the open over `U` map into `U`. -/
theorem range_pointsMap_chartOpens_chartPreimageOpen_subset :
    Set.range (pointsMap B S hS _
      (((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)).obj.hom ≫ f.hom)) ⊆
      Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) := by
  rintro _ ⟨y, rfl⟩
  rw [pointsMap_comp, Function.comp_apply,
    pointsMap_hom_eq_pointOfEtaleChart_chartSchemeMap (chartOpensHom B S hS X d.U _) y,
    ← pointOfEtaleChart_map_g]
  have hmem : ∀ x : ((chartPreimageOpen f U d : (chartScheme d.U).Opens) : Scheme.{u}),
      (chartPreimageOpen f U d).ι x ∈ chartPreimageOpen f U d := fun x => x.2
  exact hmem _

/-- The points of the chart of `A` cut out by the open `U` map into `U`. -/
theorem range_pointsMap_chartOpens_chartOpenOfOpenSubspace_subset :
    Set.range (pointsMap B S hS _
      ((chartOpens B S hS d.V).obj (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V)).obj.hom) ⊆
      Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) := by
  rintro _ ⟨y, rfl⟩
  rw [pointsMap_hom_eq_pointOfEtaleChart_chartSchemeMap (chartOpensHom B S hS A d.V _) y]
  have hmem : ∀ x : ((chartOpenOfOpenSubspace B S hS U.1 U.2 d.V : (chartScheme d.V).Opens) :
      Scheme.{u}), (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V).ι x ∈
        chartOpenOfOpenSubspace B S hS U.1 U.2 d.V := fun x => x.2
  exact hmem _

/-- The chart of `A` cut out by `U`, as a morphism into `U`. -/
noncomputable def chartOpenToOpenSubspace :
    yoneda.obj ((chartOpens B S hS d.V).obj (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V)).obj.left ⟶
      U.1.toFunctor :=
  ((factorsThrough_openSubspace_iff_points B S hS A.2 (isAlgebraicSpace_yoneda B S hS _) U.1 U.2
    _).2 (range_pointsMap_chartOpens_chartOpenOfOpenSubspace_subset f U d)).choose

/-- `chartOpenToOpenSubspace` followed by the inclusion of `U` is the structure morphism to `A`
of the chart of `A` cut out by `U`. -/
theorem chartOpenToOpenSubspace_ι : chartOpenToOpenSubspace f U d ≫ U.1.ι =
    ((chartOpens B S hS d.V).obj (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V)).obj.hom :=
  ((factorsThrough_openSubspace_iff_points B S hS A.2 (isAlgebraicSpace_yoneda B S hS _) U.1 U.2
    _).2 (range_pointsMap_chartOpens_chartOpenOfOpenSubspace_subset f U d)).choose_spec

/-- The chart of `X` cut out by the open over `U`, as a morphism into `U`. -/
noncomputable def chartPreimageOpenToOpenSubspace :
    yoneda.obj ((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)).obj.left ⟶
      U.1.toFunctor :=
  ((factorsThrough_openSubspace_iff_points B S hS A.2 (isAlgebraicSpace_yoneda B S hS _) U.1 U.2
    _).2 (range_pointsMap_chartOpens_chartPreimageOpen_subset f U d)).choose

/-- `chartPreimageOpenToOpenSubspace` followed by the inclusion of `U` is the structure morphism
to `X` of the chart of `X` cut out by the open over `U`, followed by `f`. -/
theorem chartPreimageOpenToOpenSubspace_ι : chartPreimageOpenToOpenSubspace f U d ≫ U.1.ι =
    ((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)).obj.hom ≫ f.hom :=
  ((factorsThrough_openSubspace_iff_points B S hS A.2 (isAlgebraicSpace_yoneda B S hS _) U.1 U.2
    _).2 (range_pointsMap_chartOpens_chartPreimageOpen_subset f U d)).choose_spec

/-- The étale chart of `X ×_A U` given by the open of a chart of `X` lying over `U`. -/
noncomputable def restrictOverChart : SmallEtale B S hS (restrictOver f U).1 :=
  ⟨CostructuredArrow.mk (pullback.lift
      ((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)).obj.hom
      (chartPreimageOpenToOpenSubspace f U d) (chartPreimageOpenToOpenSubspace_ι f U d).symm),
    by
      have : Mono U.toSpaceι.hom := (inferInstance : Mono U.1.ι)
      refine presheaf_etale_of_comp_mono (pullback.fst f.hom U.toSpaceι.hom)
        (pullback.lift ((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)).obj.hom
          (chartPreimageOpenToOpenSubspace f U d)
          (chartPreimageOpenToOpenSubspace_ι f U d).symm) ?_
      rw [pullback.lift_fst]
      exact ((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)).property⟩

/-- The étale chart of `U` given by the open of a chart of `A` cut out by `U`. -/
noncomputable def openSubspaceChart : SmallEtale B S hS U.toSpace.1 :=
  ⟨CostructuredArrow.mk (chartOpenToOpenSubspace f U d),
    by
      refine presheaf_etale_of_comp_mono U.1.ι (chartOpenToOpenSubspace f U d) ?_
      rw [chartOpenToOpenSubspace_ι]
      exact ((chartOpens B S hS d.V).obj (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V)).property⟩

/-- The morphism of schemes of a commuting square of charts, restricted to the opens over `U`,
as a morphism of the site. -/
noncomputable def chartPreimageOpenHom : chartOpenOver B S hS d.U (chartPreimageOpen f U d) ⟶
    chartOpenOver B S hS d.V (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V) :=
  Over.homMk (ObjectProperty.homMk ((BigFppfOver.toScheme B S hS).map d.g ∣_
    chartOpenOfOpenSubspace B S hS U.1 U.2 d.V)) (by
      apply B.inclusion.map_injective
      change (_ ∣_ _) ≫ (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V).ι ≫
          B.inclusion.map d.V.obj.left.hom =
        (chartPreimageOpen f U d).ι ≫ B.inclusion.map d.U.obj.left.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      exact congrArg ((chartPreimageOpen f U d).ι ≫ ·)
        (congrArg B.inclusion.map (Over.w d.g)))

/-- The morphism of charts restricted to the opens over `U` commutes with the inclusions of those
opens and the morphism of charts `d.g`. -/
theorem chartPreimageOpenHom_comp_chartOpenOverι :
    chartPreimageOpenHom f U d ≫
        chartOpenOverι B S hS d.V (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V) =
      chartOpenOverι B S hS d.U (chartPreimageOpen f U d) ≫ d.g :=
  (BigFppfOver.toScheme B S hS).map_injective (morphismRestrict_ι _ _)

/-- **The square of charts of `X ×_A U ⟶ U` cut out by `U` in a square of charts of `f`.** -/
noncomputable def restrictOverChartDiagram :
    ChartDiagram B S hS (restrictOver f U).1 U.toSpace.1 (restrictOverHom f U).hom where
  U := restrictOverChart f U d
  V := openSubspaceChart f U d
  g := chartPreimageOpenHom f U d
  comm := by
    refine (cancel_mono U.1.ι).mp ?_
    have h1 : ((restrictOverChart f U d).obj.hom ≫ (restrictOverHom f U).hom) ≫ U.1.ι =
        ((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)).obj.hom ≫ f.hom :=
      (Category.assoc _ _ _).trans ((congrArg ((restrictOverChart f U d).obj.hom ≫ ·)
        (pullback.condition (f := f.hom) (g := U.toSpaceι.hom)).symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f.hom) (pullback.lift_fst _ _ _))))
    have hc : yoneda.map (chartPreimageOpenHom f U d) ≫
        yoneda.map (chartOpenOverι B S hS d.V (chartOpenOfOpenSubspace B S hS U.1 U.2 d.V)) =
        yoneda.map (chartOpenOverι B S hS d.U (chartPreimageOpen f U d)) ≫ yoneda.map d.g := by
      rw [← Functor.map_comp, ← Functor.map_comp, chartPreimageOpenHom_comp_chartOpenOverι]
    have h2 : (yoneda.map (chartPreimageOpenHom f U d) ≫ (openSubspaceChart f U d).obj.hom) ≫
        U.1.ι = ((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)).obj.hom ≫ f.hom :=
      (Category.assoc _ _ _).trans ((congrArg (yoneda.map (chartPreimageOpenHom f U d) ≫ ·)
        (chartOpenToOpenSubspace_ι f U d)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ d.V.obj.hom) hc).trans ((Category.assoc _ _ _).trans
        ((congrArg (yoneda.map (chartOpenOverι B S hS d.U (chartPreimageOpen f U d)) ≫ ·)
          d.comm.symm).trans (Category.assoc _ _ _).symm)))))
    exact h1.trans h2.symm

variable (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)

include hFqc in
/-- The restriction of `F` to the open of a chart of `X` over `U` is the restriction of
`F|_{X ×_A U}` to the corresponding chart of `X ×_A U`. -/
theorem nonempty_pullback_chartPreimageOpen_iso_restrictToChart :
    Nonempty ((Scheme.Modules.pullback (chartPreimageOpen f U d).ι).obj
        (chartModule B S hS X.2 F d.U) ≅
      restrictToChart B S hS (restrictOver f U).2
        ((modulePullback B S hS (restrictOverι f U)).obj F) (restrictOverChart f U d)) := by
  obtain ⟨e1⟩ := nonempty_pullback_opens_restrictToChart B S hS X F hFqc d.U
    (chartPreimageOpen f U d)
  exact ⟨e1 ≪≫ ((Scheme.Modules.pullbackCongr ((BigFppfOver.toScheme B S hS).map_id _) ≪≫
      Scheme.Modules.pullbackId _).app _).symm ≪≫
    chartRestrictionBaseChangeIso B S hS (restrictOverι f U) F hFqc
      ((chartOpens B S hS d.U).obj (chartPreimageOpen f U d)) (restrictOverChart f U d) (𝟙 _)
      (by simp only [restrictOverChart]; exact (pullback.lift_fst _ _ _).symm)⟩

include hFqc in
/-- **Finite presentation of `F|_{X ×_A U}` gives finite presentation over `U` on charts.** -/
theorem isFinitePresentationOverOpenOnCharts_of_isFinitePresentationOnSite
    (hFU : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite) :
    IsFinitePresentationOverOpenOnCharts B S hS X.2 f.hom F U.1 U.2 := fun d => by
  obtain ⟨e⟩ := nonempty_pullback_chartPreimageOpen_iso_restrictToChart f U d F hFqc
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso e.symm
    (isFinitePresentation_restrictToChart B S hS (restrictOver f U) _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F hFqc) hFU
      (restrictOverChart f U d))

include hFqc in
/-- **Flatness of `F|_{X ×_A U}` over `U` gives flatness over `U` on charts.** -/
theorem isFlatOverOpenOnCharts_of_isFlatOver
    (hFU : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    IsFlatOverOpenOnCharts B S hS X.2 f.hom F U.1 U.2 := fun d => by
  obtain ⟨e⟩ := nonempty_pullback_chartPreimageOpen_iso_restrictToChart f U d F hFqc
  exact (AlgebraicGeometry.isFlatOver_iff_of_iso _ e).mpr (hFU (restrictOverChartDiagram f U d))

end OpenOnCharts

/-- **Flattening by blowing up over an affine base** (the step of Stacks 087C that applies
Stacks 0815).  Let `A` be an affine algebraic space, let `f : X ⟶ A` be locally of finite
presentation with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite type and
let `U ⊆ A` be a quasi-compact open subspace such that `F|_{X ×_A U}` is of finite presentation
and flat over `U`.  Then there is a closed subspace `Z ⊆ A` of finite presentation, disjoint from
`U`, and a blowup `b : A' ⟶ A` in `Z`, such that the strict transform of `F` with respect to `b`
is of finite presentation and flat over `A'`. -/
theorem exists_isFlatteningBlowup_of_isAffineSpace {A X : AlgebraicSpaces B S hS}
    (hA : IsAffineSpace B S hS A.1) (f : X ⟶ A) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (U : OpenSubspaces B S hS A.1) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1 :=
    isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hA
  obtain ⟨T, hTaff, ⟨eA⟩⟩ := hA
  have := hTaff
  let e : yoneda.obj T ≅ A.1 := eA.symm
  -- an affine surjective étale chart `V` of `X`, and `T` as a chart of `A`
  obtain ⟨V₀, v, hv, hvsurj⟩ := exists_affine_isSurjective_etaleChart B S hS _ X.2 hXqc
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj V₀)) := V₀.2
  let cV : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk v, hv⟩
  have hTet : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf e.hom :=
    presheaf_inverseImage_of_isIso (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (fun g _ => inferInstanceAs (AlgebraicGeometry.Etale g)) _
  have hTsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf e.hom :=
    presheaf_inverseImage_of_isIso (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (fun g _ => inferInstanceAs (AlgebraicGeometry.Surjective g)) _
  let cWA : SmallEtale B S hS A.1 := ⟨CostructuredArrow.mk e.hom, hTet⟩
  let p : (BigAffineFppf.inclusion B S hS).obj V₀ ⟶ T :=
    Yoneda.fullyFaithful.preimage (v ≫ f.hom ≫ e.inv)
  have hpv : yoneda.map p = v ≫ f.hom ≫ e.inv := Yoneda.fullyFaithful.map_preimage _
  have hp : cV.obj.hom ≫ f.hom = yoneda.map p ≫ e.hom := by
    show v ≫ f.hom = _
    rw [hpv]
    simp
  let d₀ : ChartDiagram B S hS X.1 A.1 f.hom :=
    { U := cV
      V := cWA
      g := p
      comm := hp }
  -- the hypotheses of Stacks 0815 on the square of charts `V ⟶ T`
  have hGqc : (chartModule B S hS X.2 F cV).IsQuasicoherent :=
    isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS _ _ hFqc cV
  have hGft : (chartModule B S hS X.2 F cV).IsFiniteType :=
    isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS X F hFqc hFft cV
  have hUι : IsQuasiCompact B S hS U.1.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ A.2 hAqs hUqc U.1.ι
  have hUWc : IsCompact (chartOpenOfOpenSubspace B S hS U.1 U.2 cWA :
      Set (etaleChartScheme B S hS cWA)) := by
    have : CompactSpace (etaleChartScheme B S hS cWA) :=
      (inferInstance : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    have h := isRetrocompactOnCharts_of_isQuasiCompact B S hS U.1 U.2 hUι cWA isCompact_univ
      isOpen_univ
    rwa [Set.inter_univ] at h
  have hGfp := isFinitePresentationOverOpenOnCharts_of_isFinitePresentationOnSite f U F hFqc
    hFUfp d₀
  have hGflat := isFlatOverOpenOnCharts_of_isFlatOver f U F hFqc hFUflat d₀
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p) :=
    locallyOfFinitePresentation_chartDiagram B S hS hf d₀
  have := hGqc
  have := hGft
  -- Stacks 0815 on the chart
  obtain ⟨I, hIfp, hIdisj, -, hSTfp, hSTflat⟩ :=
    exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts
      ((BigFppfOver.toScheme B S hS).map p) (chartModule B S hS X.2 F cV)
      (chartOpenOfOpenSubspace B S hS U.1 U.2 cWA) hUWc hGfp hGflat
  -- the centre, transported to `A`
  let Z : ClosedSubspaces B S hS A.1 :=
    preimageClosedSubspace (ObjectProperty.homMk e.inv : A ⟶ schemeSpace T)
      (closedSubspaceOfIdeal T I)
  have hZT : Z.1.preimage e.hom = (closedSubspaceOfIdeal T I).1 :=
    (Subfunctor.preimage_comp _ e.hom e.inv).symm.trans
      ((congrArg (Subfunctor.preimage _) e.hom_inv_id).trans (Subfunctor.preimage_id _))
  have hZfp : IsFinitePresentation B S hS Z.1.ι := by
    have hft := (finitePresentation_subschemeι_iff_isFiniteType I).mp hIfp
    refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
      (Z := ⟨Z.1.toFunctor, Z.2.1⟩) (X := A) (ObjectProperty.homMk Z.1.ι) Z.2.2 (b := e.hom)
      hTet hTsurj).mpr ?_
    intro A₀
    rw [ker_rep_snd_of_preimage_eq_closedSubspaceOfIdeal T I Z e.hom hZT]
    exact hft A₀
  have hinv : ∀ y : points B S hS A.1,
      pointsMap B S hS _ e.hom (pointsMap B S hS _ e.inv y) = y := fun y => by
    rw [← Function.comp_apply (f := pointsMap B S hS _ e.hom), ← pointsMap_comp, e.inv_hom_id,
      pointsMap_id]
    rfl
  have hmemZ : ∀ y : points B S hS A.1, y ∈ subspacePointSet B S hS A.1 Z.1 ↔
      pointsEquivScheme B S hS T (pointsMap B S hS _ e.inv y) ∈ I.support := fun y => by
    have h := range_pointsMap_preimage_ι B S hS (G := A.1) (F := yoneda.obj T) e.inv
      (closedSubspaceOfIdeal T I).1
    exact (Set.ext_iff.mp h y).trans (Set.ext_iff.mp (subspacePointSet_closedSubspaceOfIdeal T I) _)
  have hdisj : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) := by
    refine Set.disjoint_left.mpr fun y hyU hyZ => ?_
    rw [hmemZ] at hyZ
    have hyU' : pointsEquivScheme B S hS T (pointsMap B S hS _ e.inv y) ∈
        chartOpenOfOpenSubspace B S hS U.1 U.2 cWA := by
      rw [mem_chartOpenOfOpenSubspace_iff]
      show pointsMap B S hS _ e.hom ((pointsEquivScheme B S hS T).symm
        (pointsEquivScheme B S hS T (pointsMap B S hS _ e.inv y))) ∈ _
      rw [Equiv.symm_apply_apply, hinv]
      exact hyU
    exact Set.disjoint_left.mp hIdisj hyU' hyZ
  -- a blowup of `A` in `Z`, and its base change to `T`, the space of the scheme blowup
  obtain ⟨A', b, hb⟩ := exists_isBlowupAlong_of_isFinitePresentation Z hZfp
  refine ⟨Z, A', b, hZfp, hdisj, hb, ?_⟩
  have hgflat : IsFlat B S hS (ObjectProperty.homMk e.hom : schemeSpace T ⟶ A).hom :=
    isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS e.hom)
  have hq := isBlowupAlong_preimage_of_isPullback_of_isFlat hgflat hb
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk e.hom : schemeSpace T ⟶ A) b)
  rw [show preimageClosedSubspace (ObjectProperty.homMk e.hom : schemeSpace T ⟶ A) Z =
    closedSubspaceOfIdeal T I from Subtype.ext hZT] at hq
  obtain ⟨e', he'⟩ := exists_iso_yoneda_blowUpObj_of_isBlowupAlong T I hIfp hq
  let b₀ : blowUpObj T I ⟶ T := blowUpObjHom T I
  let cW' : yoneda.obj (blowUpObj T I) ⟶ A'.1 := e'.hom ≫ pullback.snd e.hom b.hom
  have he'' : e'.hom ≫ pullback.fst e.hom b.hom = yoneda.map b₀ := he'
  have hbW : yoneda.map b₀ ≫ e.hom = cW' ≫ b.hom :=
    (congrArg (· ≫ e.hom) he''.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (e'.hom ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm))
  have hsq : IsPullback (yoneda.map b₀) cW' e.hom b.hom := by
    have hsq1 : IsPullback (yoneda.map b₀) e'.hom (𝟙 _) (pullback.fst e.hom b.hom) :=
      IsPullback.of_vert_isIso ⟨by rw [Category.comp_id]; exact he''.symm⟩
    have h := hsq1.paste_vert (IsPullback.of_hasPullback e.hom b.hom)
    rwa [Category.id_comp] at h
  have hT : B.Contains (pullback ((BigFppfOver.toScheme B S hS).map p)
      ((BigFppfOver.toScheme B S hS).map b₀)) :=
    Scheme.size_pullback_lt _ _ ((BigAffineFppf.inclusion B S hS).obj V₀).left.property
      (blowUpObj T I).left.property
  -- the inverse image of the centre is closed, with quasi-compact complement
  have hEcl : IsClosedSubspace B S hS (Z.1.preimage b.hom) := (preimageClosedSubspace b Z).2
  have hcl := exceptionalPreimage_isClosedSubspace B S hS f b _ hEcl
  have hclosed : IsClosed (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom)) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS (strictTransformPullback B S hS f b).2 _
      hcl.2
  have hOE : IsQuasiCompact B S hS (openComplement B S hS (Z.1.preimage b.hom)).ι :=
    isQuasiCompact_of_isAffineHom' B S hS _
      (isOpenSubspace_openComplement B S hS A'.2 _ hEcl).1 A'.2
      (isAffineHom_ι_openComplement_of_isEffectiveCartierDivisor B S hS A'
        (preimageClosedSubspace b Z) hb.isPullbackDefined)
  have hOqc : IsQuasiCompact B S hS
      (openComplement B S hS (exceptionalPreimage B S hS f b (Z.1.preimage b.hom))).ι := by
    rw [← openComplement_preimage]
    exact isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage _ _) hOE
  have hK := (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS _
    (strictTransformPullback B S hS f b).2 _).mp
    (isQuasicoherentOnSite_supportedSectionsSubmodule B S hS
      (strictTransformPullback B S hS f b).2 _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (strictTransformPullbackToSource B S hS f b) _ hFqc)
      hclosed (isOpenSubspace_openComplement B S hS (strictTransformPullback B S hS f b).2 _ hcl)
      (range_pointsMap_ι_openComplement B S hS _) hOqc)
  -- the chart `V ×_T T'` of `X ×_A A'`, on which the strict transform is computed
  let cT := strictTransformBaseChangeChart (f := f) (b := b) (cV := cV) (cW := e.hom)
    (cW' := cW') (p := p) (b₀ := b₀) hT hp hbW hsq
  let := isContinuous_chartOpens B S hS _ (strictTransformPullback B S hS f b).2 cT
  have hE₀ : ∀ t : chartScheme cT,
      t ∈ Stacks.StrictTransform.exceptionalPreimage ((BigFppfOver.toScheme B S hS).map p)
        ((BigFppfOver.toScheme B S hS).map b₀) (exceptionalIdeal I) ↔
      pointOfEtaleChart B S hS cT t ∈ exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom) :=
      fun t => by
    have h1 : cT.obj.hom ≫ (strictTransformPullbackToBlowUp B S hS f b).hom =
        yoneda.map (chartPullbackSnd cV p b₀ hT) ≫ cW' :=
      pullback.lift_snd _ _ _
    have h2 : cT.obj.hom ≫ (strictTransformPullbackToBlowUp B S hS f b).hom ≫ b.hom ≫ e.inv =
        yoneda.map (chartPullbackSnd cV p b₀ hT ≫ b₀) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b.hom ≫ e.inv) h1).trans
        ((Category.assoc _ _ _).trans ((congrArg (yoneda.map _ ≫ ·)
          (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e.inv) hbW.symm)).trans
            ((Category.assoc _ _ _).trans ((congrArg (yoneda.map b₀ ≫ ·) e.hom_inv_id).trans
              (Category.comp_id _))))).trans (yoneda.map_comp _ _).symm)))
    have hpt : pointsMap B S hS _ e.inv (pointsMap B S hS _ b.hom (pointsMap B S hS _
        (strictTransformPullbackToBlowUp B S hS f b).hom (pointOfEtaleChart B S hS cT t))) =
        (pointsEquivScheme B S hS T).symm ((BigFppfOver.toScheme B S hS).map
          (chartPullbackSnd cV p b₀ hT ≫ b₀) t) := by
      unfold pointOfEtaleChart
      rw [← Function.comp_apply (f := pointsMap B S hS _ (strictTransformPullbackToBlowUp
          B S hS f b).hom), ← pointsMap_comp, ← Function.comp_apply (f := pointsMap B S hS _
          b.hom), ← pointsMap_comp, ← Function.comp_apply (f := pointsMap B S hS _ e.inv),
        ← pointsMap_comp]
      simp only [Category.assoc]
      rw [h2]
      rw [Equiv.eq_symm_apply]
      exact (pointsToScheme_pointsMap_yoneda B S hS _ _).trans
        (congrArg _ ((pointsEquivScheme B S hS cT.obj.left).apply_symm_apply t))
    rw [exceptionalPreimageSet_eq_preimage, Set.mem_preimage, range_pointsMap_preimage_ι]
    show _ ↔ pointsMap B S hS _ b.hom (pointsMap B S hS _ (strictTransformPullbackToBlowUp
        B S hS f b).hom (pointOfEtaleChart B S hS cT t)) ∈ subspacePointSet B S hS A.1 Z.1
    rw [hmemZ, hpt, Equiv.apply_symm_apply]
    have hsupp : ((exceptionalIdeal I).support : Set (AlgebraicGeometry.blowUp I)) =
        AlgebraicGeometry.blowUpToBase I ⁻¹' I.support := by
      show ((I.comap (AlgebraicGeometry.blowUpToBase I)).support :
        Set (AlgebraicGeometry.blowUp I)) = _
      rw [Scheme.IdealSheafData.support_comap]
      rfl
    refine (Set.ext_iff.mp hsupp _).trans (Iff.of_eq (congrArg (· ∈ I.support) ?_))
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    rfl
  obtain ⟨ι⟩ := nonempty_strictTransformSheaf_iso_restrictToChart (f := f) (b := b) (cV := cV)
    (cW := e.hom) (cW' := cW') (p := p) (b₀ := b₀) hT hp hbW hsq (Z.1.preimage b.hom) F
    (exceptionalIdeal I) hFqc hE₀ hclosed hK
  -- the strict transform is quasi-coherent
  have hGcart := (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS _
    (strictTransformPullback B S hS f b).2 _).mp
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (strictTransformPullbackToSource B S hS f b) _ hFqc)
  have hHqc : (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_cokernel_of_cartesian _ hK hGcart
  -- the conclusions of Stacks 0815, along the structure morphism of the blowup object
  have hb₀ : (BigFppfOver.toScheme B S hS).map b₀ = AlgebraicGeometry.blowUpToBase I := rfl
  rw [← hb₀] at hSTfp hSTflat
  have hflatT := (AlgebraicGeometry.isFlatOver_iff_of_iso _ ι).mp hSTflat
  have hfpT := Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso ι hSTfp
  -- the chart `V ×_T T'` covers `X ×_A A'`
  have hTcov : Function.Surjective (pointsMap B S hS _ cT.obj.hom) :=
    surjective_pointsMap_of_isPullback B S hS
      (isPullback_chartPullbackMap (f := f) (b := b) (cV := cV) (cW := e.hom) (cW' := cW')
        (p := p) (b₀ := b₀) hT hp hbW hsq).flip hvsurj
  -- finite presentation, read on that chart
  have hover := (isFinitePresentation_restrictToChart_iff B S hS _ _ hHqc cT).mp hfpT
  have hfp : (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F).IsFinitePresentation := by
    refine (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation
      _).2 ⟨PUnit, fun _ => cT, fun Y => ?_, fun _ => hover⟩
    refine (SmallEtale.topology B S hS _).superset_covering ?_
      (SmallEtale.coversTop_of_isSurjective B S hS _ (strictTransformPullback B S hS f b).2
        cT hTcov Y)
    rintro Y' g ⟨i, hi⟩
    exact ⟨PUnit.unit, hi⟩
  refine ⟨SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation _ (h := hfp), ?_⟩
  -- flatness, read on the chart diagram `V ×_T T' ⟶ T'`
  have : IsIso cW' :=
    IsIso.comp_isIso' (Iso.isIso_hom e') (pullback_snd_iso_of_left_iso e.hom b.hom)
  have hEt : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf cW' :=
    presheaf_inverseImage_of_isIso (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (fun g _ => inferInstanceAs (AlgebraicGeometry.Etale g)) _
  let d₁ : ChartDiagram B S hS _ A'.1 (strictTransformPullbackToBlowUp B S hS f b).hom :=
    { U := cT
      V := ⟨CostructuredArrow.mk cW', hEt⟩
      g := chartPullbackSnd cV p b₀ hT
      comm := pullback.lift_snd _ _ _ }
  refine isFlatOver_of_forall_isFlatOverAtPoint B S hS _ _ hHqc fun x => ?_
  obtain ⟨y, rfl⟩ := hTcov x
  refine ⟨d₁, pointsEquivScheme B S hS _ y, by simp [d₁], ?_⟩
  exact hflatT _

end AlgebraicGeometry.Space

end

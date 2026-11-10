module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonTilde
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingHomSquareComparisonModel
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineZariskiBaseChangeUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquare
public import StacksFrontier.CategoryTheory.ObjectProperty.TransportSquare

/-!
# The Zariski chart of an affine square of the big fppf site

For a cartesian square `U' → V'`, `U' → U`, `U → V`, `V' → V` of objects of the big fppf site with
affine underlying schemes, the four schemes are covered by the single chart given by their rings
of global functions, through the canonical isomorphisms `X ≅ Spec Γ(X, ⊤)`. The base change map of
Stacks 08IB on this chart is compared with the étale base change map of the algebraic spaces;
this file records the chart and the transport, along Stacks 08GH, of a morphism
`L f^* K ⟶ K'` of `D_QCoh` of the represented algebraic spaces to the underlying schemes, and
proves that the chart comparison for the transport is invertible exactly when the étale base
change map is.

## Main definitions

* `AlgebraicGeometry.Space.affineQuadrupleChart`: the whole chart of an affine cartesian square.
* `AlgebraicGeometry.Space.representedQuasicoherentTransport`: the transport of
  `φ : L f^* K ⟶ K'` to `L g_0^* K_0 ⟶ K_0'` on the underlying schemes.

## Main results

* `AlgebraicGeometry.Space.isIso_affineQuadrupleChart_comparison_iff`: the comparison of
  Stacks 0DJ8 (2) on `affineQuadrupleChart` for the transport of `φ` is invertible if and only if
  the étale base change map of `φ` is.

## Implementation notes

The proof passes through the ring-level comparison of Stacks 065Z: on the étale side by
`AlgebraicGeometry.Space.exists_isUnit_representedAffineZariskiBaseChange` (the two paths
around 08GH agree up to a central unit), on the Zariski side by
`AlgebraicGeometry.BaseChangeChart.isIso_comparison_tilde_iff`, with the model change of
`RingTheory.TorIndependence.isIso_ringHomSquareComparisonLS_comp_iff` in between.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- `isIso_comparison_tilde_iff` with the inverses of the chart's open immersions replaced by
morphisms equal to them. -/
theorem isIso_comparison_tilde_iff_of_eq (ch : BaseChangeChart f g f' g') [IsIso ch.incU]
    [IsIso ch.incU'] {j : X ⟶ Spec ch.A} {j' : X' ⟶ Spec ch.A'} (hj : inv ch.incU = j)
    (hj' : inv ch.incU' = j') (w : g' ≫ j = j' ≫ Spec.map ch.c)
    (N : DerivedCategory (ModuleCat.{u} ch.A)) (N' : DerivedCategory (ModuleCat.{u} ch.A'))
    (ψ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      ch.c.hom).functor.obj N ⟶ N') :
    IsIso (ch.comparison
        ((Stacks.Duality.derivedPullback j).obj ((tilde.functor ch.A).mapDerivedCategory.obj N))
        ((Stacks.Duality.derivedPullback j').obj ((tilde.functor ch.A').mapDerivedCategory.obj N'))
        ((Stacks.Duality.derivedPullbackCompIso g' j).hom.app
            ((tilde.functor ch.A).mapDerivedCategory.obj N) ≫
          eqToHom (congrArg (fun t : X' ⟶ Spec ch.A => (Stacks.Duality.derivedPullback t).obj
            ((tilde.functor ch.A).mapDerivedCategory.obj N)) w) ≫
          (Stacks.Duality.derivedPullbackCompIso j' (Spec.map ch.c)).inv.app
            ((tilde.functor ch.A).mapDerivedCategory.obj N) ≫
          (Stacks.Duality.derivedPullback j').map
            ((affinePullbackComparison ch.A ch.A' ch.c).hom.app N ≫
              (tilde.functor ch.A').mapDerivedCategory.map ψ))) ↔
      IsIso ((RingTheory.TorIndependence.ringHomSquareComparisonLS ch.a.hom ch.b.hom ch.c.hom
          ch.d.hom ch.isPushout_hom).app N ≫
        (ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.map ψ) := by
  subst hj hj'
  exact isIso_comparison_tilde_iff ch N N' ψ

end AlgebraicGeometry.BaseChangeChart

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Chart

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U)

/-- The whole chart of a cartesian square of affine objects of the site. -/
def affineQuadrupleChart (hpb : IsPullback g₀' f₀' f₀ g₀) :
    BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀) ((BigFppfOver.toScheme B S hS).map g₀)
      ((BigFppfOver.toScheme B S hS).map f₀') ((BigFppfOver.toScheme B S hS).map g₀') where
  R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
  A := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  R' := Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
  A' := Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
  incV := ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv
  incU := ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv
  incV' := ((BigFppfOver.toScheme B S hS).obj V').isoSpec.inv
  incU' := ((BigFppfOver.toScheme B S hS).obj U').isoSpec.inv
  isOpenImmersion_incV := inferInstance
  isOpenImmersion_incU := inferInstance
  isOpenImmersion_incV' := inferInstance
  a := representedAffineCommRingCatHom B S hS f₀
  b := representedAffineCommRingCatHom B S hS g₀
  c := representedAffineCommRingCatHom B S hS g₀'
  d := representedAffineCommRingCatHom B S hS f₀'
  wU := by simp [Iso.inv_comp_eq, Scheme.isoSpec_hom_naturality_assoc]
  wV' := by simp [Iso.inv_comp_eq, Scheme.isoSpec_hom_naturality_assoc]
  wU'U := by simp [Iso.inv_comp_eq, Scheme.isoSpec_hom_naturality_assoc]
  wU'V' := by simp [Iso.inv_comp_eq, Scheme.isoSpec_hom_naturality_assoc]
  isPushout := by
    have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
    exact isPushout_appTop_of_isPullback (hpb.map (BigFppfOver.toScheme B S hS))

end Chart


section Transport

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The 08GH transport of a morphism `L f^* K ⟶ K'` of `D_QCoh` of algebraic spaces to the
underlying schemes. -/
def representedQuasicoherentTransport
    (K : QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T).1
      (representedSpace T).2)
    (K' : QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace T').1
      (representedSpace T').2)
    (φ : (quasicoherentDerivedModulePullback (representedSpaceMap B S hS g)).obj K ⟶ K') :
    (Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map g.left)).obj
        ((representedDualityQuasicoherentDerivedEquivalence B S hS T).inverse.obj K) ⟶
      (representedDualityQuasicoherentDerivedEquivalence B S hS T').inverse.obj K' :=
  (representedDualityQuasicoherentDerivedEquivalence B S hS T').toAdjunction.homEquiv _ _
    ((representedQuasicoherentDerivedPullbackIso g).hom.app _ ≫
      (quasicoherentDerivedModulePullback (representedSpaceMap B S hS g)).map
        ((representedDualityQuasicoherentDerivedEquivalence B S hS T).counitIso.hom.app K) ≫ φ)

end Transport

section Plain

/-- Stacks 08GH on `D_QCoh`, read in the unbounded derived categories. -/
theorem representedQuasicoherentDerivedPullbackIso_hom_app_hom {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T)
    (X : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) :
    ((representedQuasicoherentDerivedPullbackIso g).hom.app X).hom =
      (representedQuasicoherentDerivedEquivalenceFunctorCompιIso T').hom.app
          ((Stacks.Duality.quasiCoherentDerivedPullback' (B.inclusion.map g.left)).obj X) ≫
        (representedDerivedPullbackSquareIso g).inv.app X.obj ≫
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedQuasicoherentDerivedEquivalenceFunctorCompιIso T).inv.app X) :=
  ObjectProperty.preimageIso_square_hom_app_hom
    (L₀ := Stacks.Duality.derivedPullback (B.inclusion.map g.left))
    (hP := Stacks.Duality.isQuasicoherent_homology_derivedPullback' (B.inclusion.map g.left))
    (L := smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g))
    (hQ := fun K => derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K.obj K.property)
    (E := (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor)
    (E' := (representedDualityQuasicoherentDerivedEquivalence B S hS T').functor)
    (F := (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).inverse ⋙
        representedZariskiDerivedPullback B S hS T)
    (F' := (StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T')).inverse ⋙
        representedZariskiDerivedPullback B S hS T')
    (e := representedQuasicoherentDerivedEquivalenceFunctorCompιIso T)
    (e' := representedQuasicoherentDerivedEquivalenceFunctorCompιIso T')
    (sq := representedDerivedPullbackSquareIso g)
    (σ := representedQuasicoherentDerivedPullbackIso g) (hσ := rfl) X

/-- The chase behind the comparison of transports of the whole affine chart: the 08GH square,
the comparison of Stacks 08DW and of the étale base change map, up to a central unit. -/
theorem affineQuadrupleChart_transport_chase {𝒟 𝒟' 𝒵' 𝒮' 𝒜ₗ 𝒜 : Type*} {_ : Category 𝒟}
    {_ : Category 𝒟'} {_ : Category 𝒵'} {_ : Category 𝒮'} {_ : Category 𝒜ₗ} {_ : Category 𝒜}
    (Lf : 𝒟 ⥤ 𝒟') (F' : 𝒵' ⥤ 𝒟') (Lj' : 𝒮' ⥤ 𝒵') (Z' : 𝒜ₗ ⥤ 𝒮') (G' : 𝒜 ⥤ 𝒜ₗ) (Φ' : 𝒜 ⥤ 𝒟')
    {FX ΦM K : 𝒟} {K' : 𝒟'} {B₀ B₁ B₂ : 𝒵'} {S₀ : 𝒮'} {Y : 𝒜ₗ} {E M' : 𝒜}
    (sqh : Lf.obj FX ⟶ F'.obj B₀) (sqi : F'.obj B₀ ⟶ Lf.obj FX) (hsq : sqi ≫ sqh = 𝟙 _)
    (τM : FX ⟶ ΦM) (κ : ΦM ⟶ K) (φ : Lf.obj K ⟶ K') (a : B₀ ⟶ B₁) (b : B₁ ⟶ B₂)
    (c : B₂ ⟶ Lj'.obj S₀) (d : S₀ ⟶ Z'.obj Y) (μ : Y ⟶ G'.obj E)
    (pd : B₀ ⟶ Lj'.obj (Z'.obj (G'.obj E))) (hpd : a ≫ b ≫ c ≫ Lj'.map (d ≫ Z'.map μ) = pd)
    (t : F'.obj (Lj'.obj (Z'.obj (G'.obj E))) ⟶ Φ'.obj E)
    (t' : F'.obj (Lj'.obj (Z'.obj (G'.obj M'))) ⟶ Φ'.obj M') (β : Lf.obj ΦM ⟶ Φ'.obj E)
    (u : E ⟶ E) (ψ : E ⟶ M') (u' uinv : M' ⟶ M') (κ' : Φ'.obj M' ⟶ K')
    (hC : sqh ≫ F'.map pd ≫ t = Lf.map τM ≫ β ≫ Φ'.map u)
    (hτ' : F'.map (Lj'.map (Z'.map (G'.map (ψ ≫ uinv)))) ≫ t' = t ≫ Φ'.map (ψ ≫ uinv))
    (hu : u ≫ ψ = ψ ≫ u') (hinv : u' ≫ uinv = 𝟙 M')
    (hspec : Lf.map κ ≫ φ = β ≫ Φ'.map ψ ≫ κ') :
    sqi ≫ Lf.map τM ≫ Lf.map κ ≫ φ =
      F'.map (a ≫ b ≫ c ≫ Lj'.map d ≫ Lj'.map (Z'.map (μ ≫ G'.map (ψ ≫ uinv)))) ≫ t' ≫ κ' := by
  have e : F'.map pd ≫ t = sqi ≫ Lf.map τM ≫ β ≫ Φ'.map u := by
    rw [← hC, reassoc_of% hsq]
  have hp : a ≫ b ≫ c ≫ Lj'.map d ≫ Lj'.map (Z'.map (μ ≫ G'.map (ψ ≫ uinv))) =
      pd ≫ Lj'.map (Z'.map (G'.map (ψ ≫ uinv))) := by
    rw [← hpd]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hp, CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% hτ', reassoc_of% e, hspec]
  simp only [← Φ'.map_comp_assoc, reassoc_of% hu, hinv, Category.comp_id]

end Plain

section Statement

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
/-- The étale base change map of an affine square is invertible if and only if the ring-level
comparison of Stacks 065Z, followed by the étale base change map and an automorphism of the
identity, is. -/
theorem isIso_representedAffineSectionsBaseChangeComp_iff_unit (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K')
    (t : 𝟭 (DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) ≅ 𝟭 _) :
    IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K K' φ) ↔
      IsIso ((RingTheory.TorIndependence.ringHomSquareComparison
          (representedAffineCommRingCatHom B S hS f₀).hom
          (representedAffineCommRingCatHom B S hS g₀).hom
          (representedAffineCommRingCatHom B S hS g₀').hom
          (representedAffineCommRingCatHom B S hS f₀').hom
          ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
            (representedAffineRingHom_comp B S hS f₀' g₀))).app
          ((representedAffineDerivedSections B S hS U).obj K) ≫
        (ModuleCat.restrictScalars
            (representedAffineCommRingCatHom B S hS f₀').hom).mapDerivedCategory.map
          (representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ ≫
            t.inv.app ((representedAffineDerivedSections B S hS U').obj K'))) := by
  rw [Functor.map_comp, ← Category.assoc, isIso_comp_right_iff]
  rfl

/-- The object of `D_QCoh` of the scheme of an affine object obtained from the derived sections
of `K` by `tilde` and the chart isomorphism. -/
private abbrev affineChartQuasicoherentObject (X : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X)]
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩))) :
    @Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS X)
      (Scheme.Modules.hasDerivedCategory _) :=
  ⟨_, Stacks.Duality.isQuasicoherent_homology_derivedPullback'
    ((BigFppfOver.toScheme B S hS).obj X).isoSpec.hom
    ⟨_, @isQuasicoherent_homology_mapDerivedCategory_obj.{u, u}
      Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u}
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)))
      (Scheme.Modules.hasDerivedCategory _)
      ((Stacks.Injectives.grothendieckModelEquiv.{u}
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj X, ⊤))).functor.obj
        ((representedAffineDerivedSections B S hS X).obj K))⟩⟩

/-- The isomorphism comparing the chart object with `K`, for `K` quasicoherent. -/
private abbrev affineChartQuasicoherentIso (X : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X)]
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩)))
    (hK : QcohDerived B S hS ⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ K) :
    ((StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS X)).inverse ⋙
      representedZariskiDerivedPullback B S hS X).obj
        (affineChartQuasicoherentObject X K).obj ≅ K :=
  (representedAffineZariskiAssociatedIso X).app _ ≪≫
    @asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS X).counit.app K)
      (isIso_representedAffineDerivedAdjunction_counit_app B S hS X K hK)

/-- **The whole chart of an affine cartesian square computes the étale base change map.** For a
morphism `φ : L f^* K ⟶ K'` of `D_QCoh` of the represented algebraic spaces of an affine cartesian
square, the comparison of Stacks 0DJ8 (2) on the chart `affineQuadrupleChart`, for the transport
of `φ` along Stacks 08GH, is invertible if and only if the étale base change map is. -/
theorem isIso_affineQuadrupleChart_comparison_iff (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (hpb : IsPullback g₀' f₀' f₀ g₀)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hK : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (hK' : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ K')
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K') :
    IsIso ((affineQuadrupleChart f₀ g₀ f₀' g₀' hpb).comparison
        ((representedDualityQuasicoherentDerivedEquivalence B S hS U).inverse.obj ⟨K, hK⟩).obj
        ((representedDualityQuasicoherentDerivedEquivalence B S hS U').inverse.obj ⟨K', hK'⟩).obj
        (representedQuasicoherentTransport g₀' ⟨K, hK⟩ ⟨K', hK'⟩ (ObjectProperty.homMk φ)).hom) ↔
      IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K K' φ) := by
  refine (exists_isUnit_representedAffineZariskiBaseChange g₀').elim fun c hc => ?_
  refine Iff.trans ?_ (isIso_representedAffineSectionsBaseChangeComp_iff_unit f₀ g₀ f₀' g₀' w₀ K
    K' φ (unitCentralIso (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) c.isUnit)).symm
  refine Iff.trans ?_ (RingTheory.TorIndependence.isIso_ringHomSquareComparisonLS_comp_iff _ _ _ _
    _ ((representedAffineDerivedSections B S hS U).obj K)
    ((representedAffineDerivedSections B S hS U').obj K')
    (representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ ≫
      (unitCentralIso (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) c.isUnit).inv.app
        ((representedAffineDerivedSections B S hS U').obj K')))
  have : IsIso (affineQuadrupleChart f₀ g₀ f₀' g₀' hpb).incU :=
    (inferInstance : IsIso ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv)
  have : IsIso (affineQuadrupleChart f₀ g₀ f₀' g₀' hpb).incU' :=
    (inferInstance : IsIso ((BigFppfOver.toScheme B S hS).obj U').isoSpec.inv)
  refine Iff.trans ?_ (BaseChangeChart.isIso_comparison_tilde_iff_of_eq
    (affineQuadrupleChart f₀ g₀ f₀' g₀' hpb) (IsIso.Iso.inv_inv _) (IsIso.Iso.inv_inv _)
    (isoSpec_hom_square g₀') _ _ _)
  refine Exists.elim (ObjectProperty.map_comp_eq_homEquiv_comp_hom
      (Stacks.Duality.derivedPullback (B.inclusion.map g₀'.left))
      (Stacks.Duality.isQuasicoherent_homology_derivedPullback' (B.inclusion.map g₀'.left))
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀'))
      (fun K => derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K.obj K.property)
      (representedDualityQuasicoherentDerivedEquivalence B S hS U)
      (representedDualityQuasicoherentDerivedEquivalence B S hS U')
      ((StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U)).inverse ⋙
        representedZariskiDerivedPullback B S hS U)
      ((StacksDraft.DerivedModel.schemeModulesComparison
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse ⋙
        representedZariskiDerivedPullback B S hS U')
      (representedQuasicoherentDerivedEquivalenceFunctorCompιIso U)
      (representedQuasicoherentDerivedEquivalenceFunctorCompιIso U')
      (representedDerivedPullbackSquareIso g₀')
      (representedQuasicoherentDerivedPullbackIso g₀') rfl
      (K := ⟨K, hK⟩) (K' := ⟨K', hK'⟩) (ObjectProperty.homMk φ)
      (affineChartQuasicoherentObject U K) (affineChartQuasicoherentObject U' K')
      (affineChartQuasicoherentIso U K hK) (affineChartQuasicoherentIso U' K' hK')
      _ ?_) fun ε h => h.elim fun ε' hε => BaseChangeChart.isIso_comparison_iff_of_iso _
        ((ObjectProperty.ι _).mapIso ε) ((ObjectProperty.ι _).mapIso ε') _ _ hε
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.trans_hom, Iso.app_hom,
    Functor.comp_map]
  refine affineQuadrupleChart_transport_chase
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀'))
    ((StacksDraft.DerivedModel.schemeModulesComparison
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U')).inverse ⋙
      representedZariskiDerivedPullback B S hS U')
    (Stacks.Duality.derivedPullback ((BigFppfOver.toScheme B S hS).obj U').isoSpec.hom) _ _
    (representedAffineToposDerivedAssociated B S hS U') ?sqh _ ?hsq _ _ _ _ _ _ _ _ ?pd ?hpd ?t _
    ?β ?u _ ?u' _ _ ?hC ?hτ ?hu ?hinv ?hspec
  case sqh => exact (representedDerivedPullbackSquareIso g₀').hom.app _
  case hsq => exact Iso.inv_hom_id_app _ _
  case pd =>
    exact representedAffineZariskiPathDerived g₀'
      ((representedAffineDerivedSections B S hS U).obj K)
  case t => exact (representedAffineZariskiAssociatedIso U').hom.app _
  case β => exact (representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app _
  case u =>
    exact (unitCentralIso (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) c.isUnit).hom.app _
  case u' =>
    exact (unitCentralIso (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) c.isUnit).hom.app _
  case hpd => rfl
  case hC => exact hc _
  case hτ => exact (representedAffineZariskiAssociatedIso U').hom.naturality _
  case hu =>
    exact ((unitCentralIso (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
      c.isUnit).hom.naturality _).symm
  case hinv =>
    exact (unitCentralIso (c : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
      c.isUnit).hom_inv_id_app _
  case hspec => exact representedAffineSectionsBaseChangeMap_spec B S hS g₀' K K' φ

end Statement

end AlgebraicGeometry.Space

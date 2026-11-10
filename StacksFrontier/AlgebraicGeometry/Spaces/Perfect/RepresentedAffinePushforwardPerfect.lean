module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.ChartRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Perfect
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineTargetHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional

/-!
# The derived direct image of a perfect object along a morphism of affine representables

Let `g : U' ⟶ U` be a morphism of the big fppf site over `S` whose source and target have affine
underlying schemes, with rings of global functions `R = Γ(U)` and `R' = Γ(U')`, and let `F` be a
perfect object of `D(𝒪_{yoneda.obj U'})`.  Then `RΓ(U, Rg_*F)` is a bounded complex of finite
projective `R'`-modules with scalars restricted to `R`.  If moreover the represented morphism is
perfect (Stacks 06BZ), `R'` has finite Tor dimension over `R` and `RΓ(U, Rg_*F)` has finite Tor
dimension over `R` (Stacks 066K).

## Main results

All in the namespace `AlgebraicGeometry.Space`.

* `nonempty_rightDerived_obj_iso_of_rightAcyclic`: a bounded below complex of modules acyclic for
  the direct image computes the derived direct image (Stacks 015E).
* `modulePushforwardCompRepresentedAffineSectionsIso`: `Γ(U, g_*F)` is `Γ(U', F)` read over `R`.
* `representedAffineAssociatedModulePushforwardIso`: `g_*(M^~) ≅ (M|_R)^~`.
* `exists_iso_representedAffineDerivedSections_derivedPushforward`: the first statement above.
* `exists_hasTorAmplitudeCanonical_representedAffineDerivedSections_derivedPushforward`: the
  Tor-dimension statement.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 066K](https://stacks.math.columbia.edu/tag/066K)
* [Stacks Project, Tag 06BZ](https://stacks.math.columbia.edu/tag/06BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image of modules along a morphism of algebraic spaces is additive, at the instance
spelling of this file. -/
local instance additive_modulePushforward' {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (modulePushforward B S hS f).Additive :=
  additive_modulePushforward B S hS f

section RightDerived

variable {W Y : AlgebraicSpaces B S hS} (g : W ⟶ Y)
  (RF : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]

include α in
/-- **A bounded below complex of acyclic modules computes the derived direct image**: if every
term of a complex `K` in degrees `≥ n` is right acyclic for the direct image `g_*`, then
`Rg_*(K) ≅ g_*K`, for every right derived functor `Rg_*` of the direct image (Stacks 015E). -/
theorem nonempty_rightDerived_obj_iso_of_rightAcyclic
    (K : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) (n : ℤ) [K.IsStrictlyGE n]
    (hK : ∀ i, (modulePushforward B S hS g).rightAcyclic (K.X i)) :
    Nonempty (RF.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((modulePushforward B S hS g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) := by
  obtain ⟨L, i, hi, hL, hLn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  obtain ⟨e⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS g RF α L
    (CochainComplex.isKInjective_of_injective L n)
  have hq : QuasiIso (((modulePushforward B S hS g).mapHomologicalComplex
      (ComplexShape.up ℤ)).map i) :=
    Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic (modulePushforward B S hS g) i
      ⟨n, inferInstance⟩ ⟨n, hLn⟩ hK
      (fun j => Functor.rightAcyclic_of_injective (modulePushforward B S hS g) (L.X j))
  exact ⟨RF.mapIso (asIso (DerivedCategory.Q.map i)) ≪≫ e ≪≫
    (asIso (DerivedCategory.Q.map (((modulePushforward B S hS g).mapHomologicalComplex
      (ComplexShape.up ℤ)).map i))).symm⟩

end RightDerived

section Affine

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)

/-- The ring map `Γ(U) ⟶ Γ(U')` of a morphism of affine representables. -/
abbrev representedAffineRingHom :
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →+* Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
  (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map g)).hom

/-- **Sections of a direct image along a morphism of affine representables**: `Γ(U, g_* F)` is
`Γ(U', F)` with scalars restricted to `Γ(U)`, naturally in `F`.  It is the conjugate of the
isomorphism `g^*(M^~) ≅ (Γ(U') ⊗_{Γ(U)} M)^~` of left adjoints. -/
def modulePushforwardCompRepresentedAffineSectionsIso :
    modulePushforward B S hS (representedSpaceMap B S hS g) ⋙ representedAffineSections B S hS U ≅
      representedAffineSections B S hS U' ⋙
        ModuleCat.restrictScalars.{u, u, u} (representedAffineRingHom B S hS g) :=
  conjugateIsoEquiv
    ((representedAffineAssociatedAdjunction B S hS U).comp
      (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)))
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (representedAffineRingHom B S hS g)).comp
      (representedAffineAssociatedAdjunction B S hS U'))
    (representedAffineAssociatedModulePullbackIso B S hS g).symm

/-- The counit of the associated module and sections is invertible at a quasi-coherent module. -/
theorem isIso_representedAffineAssociatedAdjunction_counit_app
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    IsIso ((representedAffineAssociatedAdjunction B S hS U).counit.app N) := by
  have := (representedAffineAssociatedFullyFaithful B S hS U).full
  have := (representedAffineAssociatedFullyFaithful B S hS U).faithful
  exact Adjunction.isIso_counit_app_of_iso _
    ((ObjectProperty.ι _).mapIso ((representedAffineAssoc B S hS U).counitIso.app ⟨N, hN⟩).symm ≪≫
      (representedAffineAssociatedIso B S hS U).app _)

/-- **The direct image of an associated module along a morphism of affine representables** is
the associated module of the restriction of scalars: `g_*(M^~) ≅ (M|_{Γ(U)})^~`, naturally in the
`Γ(U')`-module `M`. -/
def representedAffineAssociatedModulePushforwardIso :
    representedAffineAssociated B S hS U' ⋙
        modulePushforward B S hS (representedSpaceMap B S hS g) ≅
      ModuleCat.restrictScalars.{u, u, u} (representedAffineRingHom B S hS g) ⋙
        representedAffineAssociated B S hS U :=
  have : _root_.AlgebraicGeometry.IsAffineHom (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) g.left) := by
    rw [schemeHom_associatedBigEtaleSite]
    exact @AlgebraicGeometry.isAffineHom_of_isAffine _ _ _
      ‹IsAffine ((BigFppfOver.toScheme B S hS).obj U')›
      ‹IsAffine ((BigFppfOver.toScheme B S hS).obj U)›
  have hc' := fun M => isIso_representedAffineAssociatedAdjunction_counit_app B S hS
    ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj
      ((representedAffineAssociated B S hS U').obj M))
    (isQuasicoherentOnSite_modulePushforward_representedSpaceMap B S hS g _
      (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U' M))
  have : IsIso (representedAffineAssociatedAdjunction B S hS U').unit := by
    have := (representedAffineAssociatedFullyFaithful B S hS U').full
    have := (representedAffineAssociatedFullyFaithful B S hS U').faithful
    exact (representedAffineAssociatedAdjunction B S hS U').unit_isIso_of_L_fully_faithful
  have hc : IsIso (Functor.whiskerLeft (representedAffineAssociated B S hS U' ⋙
      modulePushforward B S hS (representedSpaceMap B S hS g))
        (representedAffineAssociatedAdjunction B S hS U).counit) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hc'
  (Functor.rightUnitor _).symm ≪≫
    (asIso (Functor.whiskerLeft (representedAffineAssociated B S hS U' ⋙
      modulePushforward B S hS (representedSpaceMap B S hS g))
        (representedAffineAssociatedAdjunction B S hS U).counit)).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (representedAffineAssociated B S hS U')
      (Functor.isoWhiskerRight (modulePushforwardCompRepresentedAffineSectionsIso B S hS g)
        (representedAffineAssociated B S hS U)) ≪≫
    Functor.isoWhiskerRight
      ((asIso (representedAffineAssociatedAdjunction B S hS U').unit).symm)
      (ModuleCat.restrictScalars.{u, u, u} (representedAffineRingHom B S hS g) ⋙
        representedAffineAssociated B S hS U)

end Affine

section Base

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)

/-- **The derived sections of the derived direct image of a perfect object along a morphism of
affine representables.**  If `F` is perfect on `yoneda.obj U'`, then `RΓ(U, Rg_*F)` is
represented by a bounded complex of finite projective `Γ(U')`-modules with scalars restricted to
`Γ(U)`.

`RΓ(U', F)` is perfect (`AlgebraicGeometry.Space.isPerfect_representedAffineDerivedSections_obj`),
so `F = Φ(P)` for a bounded complex `P` of finite projective modules; the associated modules are
quasi-coherent, hence acyclic for the direct image along the affine morphism `g`, so
`Rg_*Φ(P) = g_*(P^~) = (P|_{Γ(U)})^~`, whose derived sections are `P|_{Γ(U)}`. -/
theorem exists_iso_representedAffineDerivedSections_derivedPushforward
    (F : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U')
      (isAlgebraicSpace_yoneda B S hS U')))
    (hF : (smallEtaleRingedSite B S hS (yoneda.obj U')
      (isAlgebraicSpace_yoneda B S hS U')).IsPerfect F) :
    ∃ (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) (P.X i)) ∧
      (∀ i, Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) (P.X i)) ∧
      letI := additive_modulePushforward B S hS (representedSpaceMap B S hS g)
      Nonempty ((representedAffineDerivedSections B S hS U).obj
          ((Stacks.DerivedFunctor.totalRightDerived
            (modulePushforward B S hS (representedSpaceMap B S hS g))).obj F) ≅
        DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{u, u, u}
          (representedAffineRingHom B S hS g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) := by
  let t := representedSpaceMap B S hS g
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨eP⟩⟩ :=
    isPerfect_representedAffineDerivedSections_obj B S hS U' F hF
  refine ⟨P, a, b, ha, hb, hfin, hproj, ?_⟩
  let := additive_modulePushforward B S hS t
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U' F
    (qcohDerived_of_isPerfect B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ F hF)
  let Φ' := representedAffineAssociated B S hS U'
  let Φ := representedAffineAssociated B S hS U
  let res := ModuleCat.restrictScalars.{u, u, u} (representedAffineRingHom B S hS g)
  let tp := modulePushforward B S hS t
  let C := (Φ'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  -- `F ≅ Q(P^~)`
  let e₁ : F ≅ DerivedCategory.Q.obj C :=
    (asIso ((representedAffineDerivedAdjunction B S hS U').counit.app F)).symm ≪≫
      (representedAffineDerivedAssociated B S hS U').mapIso eP ≪≫
      (Φ'.mapDerivedCategoryFactors.app P)
  -- the terms of `P^~` are acyclic for the direct image along the affine `t`
  have : PreservesFiniteLimits tp :=
    have := (modulePullbackAdjunction B S hS t).rightAdjoint_preservesLimits
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} tp
  have hac : ∀ i, tp.rightAcyclic (C.X i) := fun i => by
    rw [rightAcyclic_iff_isZero_rightDerived]
    intro n hn
    exact isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite B S hS t
      (isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U' inferInstance)
        (isAffineSpace_yoneda B S hS U inferInstance))
      _ (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U' (P.X i)) n hn
  have : CochainComplex.IsStrictlyGE C a :=
    Stacks.DerivedFunctor.isStrictlyGE_mapHomologicalComplex Φ' P a
  have := hasRightDerivedFunctor_modulePushforward B S hS t
  obtain ⟨e₂⟩ := nonempty_rightDerived_obj_iso_of_rightAcyclic B S hS t
    (Stacks.DerivedFunctor.totalRightDerived tp)
    ((Stacks.DerivedFunctor.homotopyMap tp).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))) C a hac
  -- `t_*(P^~) ≅ (P|_R)^~`
  let e₃ : (tp.mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((res.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (Φ' ⋙ tp))
        (ComplexShape.up ℤ)).app P).symm ≪≫
      (NatIso.mapHomologicalComplex (representedAffineAssociatedModulePushforwardIso B S hS g)
        (ComplexShape.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (res ⋙ Φ)) (ComplexShape.up ℤ)).app P)
  have := isIso_representedAffineDerivedAdjunction_unit B S hS U
  exact ⟨(representedAffineDerivedSections B S hS U).mapIso
      ((Stacks.DerivedFunctor.totalRightDerived tp).mapIso e₁ ≪≫ e₂ ≪≫
        DerivedCategory.Q.mapIso e₃ ≪≫ (Φ.mapDerivedCategoryFactors.app _).symm) ≪≫
    (asIso ((representedAffineDerivedAdjunction B S hS U).unit.app _)).symm⟩

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- A perfect morphism of representable algebraic spaces has perfect underlying morphism of
schemes: the identity charts of the two representables form a commuting square of étale charts. -/
theorem perfect_toScheme_map_of_isPerfect
    (hg : IsPerfect B S hS (representedSpaceMap B S hS g).hom) :
    _root_.AlgebraicGeometry.Perfect ((BigFppfOver.toScheme B S hS).map g) := by
  have : MorphismProperty.ContainsIdentities
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have := MorphismProperty.ContainsIdentities.inverseImage
    (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}))
    (BigFppfOver.toScheme B S hS)
  have := MorphismProperty.RespectsIso.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  exact hg U' U (𝟙 _) (𝟙 _) g (MorphismProperty.presheaf_of_isIso _ _)
    (MorphismProperty.presheaf_of_isIso _ _)
    (by simp [schemeSpaceMap_hom])

/-- **The affine case of the Tor-dimension estimate.**  If `g : U' ⟶ U` is a morphism of affine
representables whose represented morphism is perfect, then for every perfect object `F` of
`D(𝒪_{yoneda.obj U'})` the derived sections `RΓ(U, Rg_*F)` have finite Tor dimension over
`Γ(U)`: they are a bounded complex of finite projective `Γ(U')`-modules read over `Γ(U)`
(`AlgebraicGeometry.Space.exists_iso_representedAffineDerivedSections_derivedPushforward`), and
`Γ(U')` has finite Tor dimension over `Γ(U)` because `g` is perfect (Stacks 066K, 067H). -/
theorem exists_hasTorAmplitudeCanonical_representedAffineDerivedSections_derivedPushforward
    (hg : IsPerfect B S hS (representedSpaceMap B S hS g).hom)
    (F : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U')
      (isAlgebraicSpace_yoneda B S hS U')))
    (hF : (smallEtaleRingedSite B S hS (yoneda.obj U')
      (isAlgebraicSpace_yoneda B S hS U')).IsPerfect F) :
    letI := additive_modulePushforward B S hS (representedSpaceMap B S hS g)
    ∃ a b : ℤ, StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((representedAffineDerivedSections B S hS U).obj
          ((Stacks.DerivedFunctor.totalRightDerived
            (modulePushforward B S hS (representedSpaceMap B S hS g))).obj F)) a b := by
  let := additive_modulePushforward B S hS (representedSpaceMap B S hS g)
  obtain ⟨P, a, b, ha, hb, hfin, hproj, ⟨e⟩⟩ :=
    exists_iso_representedAffineDerivedSections_derivedPushforward B S hS g F hF
  have hP : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) (DerivedCategory.Q.obj P) a b :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ _ a b).2
      ⟨P, fun i => inferInstance, ha, hb, ⟨Iso.refl _⟩⟩
  have := perfect_toScheme_map_of_isPerfect B S hS g hg
  let f := (BigFppfOver.toScheme B S hS).map g
  obtain ⟨c, d, hcd⟩ := hasFiniteTorDimensionCanonical_restrictScalars_appLE f ⊤
    (isAffineOpen_top _) ⊤ (isAffineOpen_top _) le_top P ⟨a, b, hP⟩
  have hφ : (f.appLE ⊤ ⊤ le_top).hom = representedAffineRingHom B S hS g :=
    congrArg CommRingCat.Hom.hom (Stacks.Descent.appLE_top_top f le_top)
  refine ⟨c, d, BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ c d hcd⟩
  refine ?_ ≪≫ e.symm
  change (ModuleCat.restrictScalars (f.appLE ⊤ ⊤ le_top).hom).mapDerivedCategory.obj
    (DerivedCategory.Q.obj P) ≅ _
  rw [hφ]
  exact (ModuleCat.restrictScalars
    (representedAffineRingHom B S hS g)).mapDerivedCategoryFactors.app P

end Base

end AlgebraicGeometry.Space

end

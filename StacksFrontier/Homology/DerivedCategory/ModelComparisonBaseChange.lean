module

public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.CategoryTheory.Localization.ModelComparisonCounit
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeComparisonFactorization
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMapAsMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional

/-!
# The derived base change map at the standard and at the locally small model

For a morphism of ringed spaces, the comparisons `StacksDraft.DerivedModel.derivedPullbackModelIso`
and `StacksDraft.DerivedModel.derivedPushforwardModelIso` of derived pullback and derived direct
image at the two models are compatible with the comparisons of derived and underived functors.

## Main results

* `StacksDraft.DerivedModel.derivedPullbackModelIso_hom_app_comp` and
  `StacksDraft.DerivedModel.map_derivedPushforwardModelIso_hom_app` — the compatibilities.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u w₁ w₂

namespace StacksDraft.DerivedModel

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `derivedPullbackModelIso` is compatible with the comparisons of derived and underived
pullback at the two models. -/
theorem derivedPullbackModelIso_hom_app_comp
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (derivedPullbackModelIso f).hom.app
        ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).obj M) ≫
      (@derivedPullback X Y f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).map
        ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv.app M) ≫
      (@derivedPullbackComparison X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          inferInstance).app M =
    (Stacks.Injectives.grothendieckModelEquiv
        (SheafOfModules.{u} (structureSheafRing X))).functor.map
        ((@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) inferInstance).app M) ≫
      (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).inv.app
        (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) := by
  have := isLeftDerivedFunctor_comp_isEquivalence
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (@derivedPullbackComparison X Y f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).symm
  have h := Functor.leftDerivedNatTrans_app _ _
    ((Functor.associator _ _ _).inv ≫ whiskerRight
      (@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) inferInstance)
      (Stacks.Injectives.grothendieckModelEquiv
        (SheafOfModules.{u} (structureSheafRing X))).functor)
    (transportLeftDerivedCounit
      (@derivedPullbackComparison X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
      (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).symm)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).symm).hom M
  simp only [transportLeftDerivedCounit, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Iso.symm_hom, Category.id_comp, Iso.trans_hom,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at h
  exact h

/-- `derivedPushforwardModelIso` is compatible with the comparisons of underived and derived
direct image at the two models. -/
theorem map_derivedPushforwardUnit_comp_derivedPushforwardModelIso_hom_app
    (N : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (Stacks.Injectives.grothendieckModelEquiv
        (SheafOfModules.{u} (structureSheafRing Y))).functor.map
        ((@derivedPushforwardUnit X Y f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _)).app N) ≫
      (derivedPushforwardModelIso f).hom.app
        ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).obj N) =
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv.app
        (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) ≫
      (@derivedPushforwardUnit X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).app N ≫
      (@derivedPushforward X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).map
        ((shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app N) := by
  have := isRightDerivedFunctor_comp_isEquivalence
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (@derivedPushforwardUnit X Y f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).symm
  have h := Functor.rightDerivedNatTrans_app _ _
    (whiskerRight
      (@derivedPushforwardUnit X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _))
      (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing Y))).functor
      ≫ (Functor.associator _ _ _).hom)
    (transportRightDerivedUnit
      (@derivedPushforwardUnit X Y f
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
      (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).symm)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).symm).hom N
  simp only [transportRightDerivedUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_hom, Iso.symm_inv, Category.comp_id, Iso.trans_hom,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp] at h
  exact h

/-- The class of a quasi-isomorphism of complexes is invertible in the standard derived category. -/
private theorem isIso_Qh_map_quotient_map_of_quasiIso
    {A B : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (s : A ⟶ B)
    (hs : QuasiIso s) :
    IsIso ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).map
      ((HomotopyCategory.quotient _ _).map s)) :=
  Localization.inverts _ (HomotopyCategory.quasiIso _ _) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs)

/-- Every object of the standard derived category is, up to isomorphism, the class of a complex at
which the comparison of underived and derived direct image is invertible. -/
theorem exists_iso_Qh_isIso_derivedPushforwardUnit
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing X)))) :
    ∃ (N : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
      (_ : K ≅ (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).obj N),
      IsIso ((@derivedPushforwardUnit X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _)).app N) := by
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective X
    ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).objPreimage K).as
  have := isIso_Qh_map_quotient_map_of_quasiIso s hs
  exact ⟨(HomotopyCategory.quotient _ _).obj I,
    ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).objObjPreimageIso K).symm ≪≫
      @asIso _ _ _ _ ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).map
        ((HomotopyCategory.quotient _ _).map s)) this,
    @isIso_derivedPushforwardUnit_app_of_isKInjective X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) I hI⟩

/-- Every object of the standard derived category is, up to isomorphism, the class of a complex at
which the comparison of derived and underived pullback is invertible. -/
theorem exists_iso_Qh_isIso_derivedPullbackComparison
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Y)))) :
    ∃ (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      (_ : K ≅ (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).obj M),
      IsIso ((@derivedPullbackComparison X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) inferInstance).app M) := by
  obtain ⟨P, s, hP, -, hs, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y
    ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).objPreimage K).as
  have := isIso_Qh_map_quotient_map_of_quasiIso s hs
  exact ⟨(HomotopyCategory.quotient _ _).obj P,
    ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).objObjPreimageIso K).symm ≪≫
      (@asIso _ _ _ _ ((@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)).map
        ((HomotopyCategory.quotient _ _).map s)) this).symm,
    @Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat X Y f
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) P hP⟩

/-- Derived pullback along equal morphisms, componentwise the identity. -/
def derivedPullbackCongr {X Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Z))]
    {h₁ h₂ : X ⟶ Z} (e : h₁ = h₂) : derivedPullback h₁ ≅ derivedPullback h₂ :=
  NatIso.ofComponents (fun K => eqToIso (congrArg (fun h : X ⟶ Z => (derivedPullback h).obj K) e))
    (by subst e; intros; simp)

/-- The components of `derivedPullbackCongr`. -/
theorem derivedPullbackCongr_hom_app {X Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Z))]
    {h₁ h₂ : X ⟶ Z} (e : h₁ = h₂)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    (derivedPullbackCongr e).hom.app K =
      eqToHom (congrArg (fun h : X ⟶ Z => (derivedPullback h).obj K) e) := rfl

/-- The functor-level transport is `derivedPullbackCongr`. -/
theorem eqToIso_derivedPullback_eq_derivedPullbackCongr {X Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Z))]
    {h₁ h₂ : X ⟶ Z} (e : h₁ = h₂) :
    eqToIso (congrArg (fun h : X ⟶ Z => derivedPullback h) e) = derivedPullbackCongr e := by
  subst e
  ext K
  simp [derivedPullbackCongr_hom_app]

/-- `derivedPullbackModelIso` commutes with transport along an equality of morphisms. -/
theorem derivedPullbackCongr_hom_app_comp_derivedPullbackModelIso_inv_app {X Z : RingedSpace.{u, u}}
    {h₁ h₂ : X ⟶ Z} (e : h₁ = h₂)
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z)))) :
    (@derivedPullbackCongr X Z (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) _ _ e).hom.app
        ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K) ≫
      (derivedPullbackModelIso h₂).inv.app K =
    (derivedPullbackModelIso h₁).inv.app K ≫
      (Stacks.Injectives.grothendieckModelEquiv _).functor.map
        ((@derivedPullbackCongr X Z (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          _ _ e).hom.app K) := by
  subst e
  simp only [derivedPullbackCongr_hom_app, eqToHom_refl, Category.id_comp]
  exact (Category.comp_id _).symm.trans (congrArg _
    ((Stacks.Injectives.grothendieckModelEquiv
      (SheafOfModules.{u} (structureSheafRing X))).functor.map_id _).symm)

/-- **The canonical comparison of Tag 0D5S at an arbitrary model of the derived categories.**
The comparison for `L(f ≫ g)^*` factors through the degreewise pullback-composition isomorphism.
-/
theorem derivedPullbackCompIsoCanonical_hom_app_comp_comparison_of_models
    {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing Y))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing Z))]
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
      (DerivedCategory.Qh.obj W) ≫
        (derivedPullbackComparison (f ≫ g)).app W =
      (derivedPullback f).map ((derivedPullbackComparison g).app W) ≫
        (derivedPullbackComparison f).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
          DerivedCategory.Qh.map ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f
            g).hom.app W) :=
  (Functor.leftDerived_fac_app (derivedPullback (f ≫ g)) (derivedPullbackComparison (f ≫ g))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
      (derivedPullback g ⋙ derivedPullback f)
      (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit f g (derivedPullback f)
        (derivedPullback g)
        (derivedPullbackComparison f) (derivedPullbackComparison g)) W).trans
    (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app f g (derivedPullback f)
      (derivedPullback g)
      (derivedPullbackComparison f) (derivedPullbackComparison g) W)

open Stacks.DerivedPullback.Composition
  (derivedPullbackCompIsoCanonical pullbackOnHomotopyCompIso) in
/-- The comparison of the two models of derived pullback is compatible with the composition
isomorphisms. -/
theorem derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso {X Y Z : RingedSpace.{u, u}}
    (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z)
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing Z)))) :
    (@derivedPullbackCompIsoCanonical _ _ _ f₁ f₂
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).hom.app
        ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K) ≫
      (derivedPullbackModelIso (f₁ ≫ f₂)).inv.app K =
    (@derivedPullback _ _ f₁ (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).map
        ((derivedPullbackModelIso f₂).inv.app K) ≫
      (derivedPullbackModelIso f₁).inv.app
        ((@derivedPullback _ _ f₂ (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          inferInstance).obj K) ≫
      (Stacks.Injectives.grothendieckModelEquiv _).functor.map
        ((@derivedPullbackCompIsoCanonical _ _ _ f₁ f₂ (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)).hom.app K) :=
  Stacks.CategoryTheory.ModelComparison.comp_comm
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).symm
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).symm
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Z))).symm
    (pullbackOnHomotopyCompIso f₁ f₂)
    (@derivedPullbackCompIsoCanonical _ _ _ f₁ f₂ (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
    (@derivedPullbackCompIsoCanonical _ _ _ f₁ f₂
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (@derivedPullbackComparison _ _ f₁ (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) inferInstance)
    (@derivedPullbackComparison _ _ f₂ (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) inferInstance)
    (@derivedPullbackComparison _ _ (f₁ ≫ f₂) (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) inferInstance)
    (@derivedPullbackComparison _ _ f₁
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (@derivedPullbackComparison _ _ f₂
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (@derivedPullbackComparison _ _ (f₁ ≫ f₂)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (derivedPullbackModelIso f₁) (derivedPullbackModelIso f₂) (derivedPullbackModelIso (f₁ ≫ f₂))
    (@derivedPullbackCompIsoCanonical_hom_app_comp_comparison_of_models
      _ _ _ f₁ f₂ (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _))
    (@derivedPullbackCompIsoCanonical_hom_app_comp_comparison_of_models
      _ _ _ f₁ f₂ (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (derivedPullbackModelIso_hom_app_comp f₁) (derivedPullbackModelIso_hom_app_comp f₂)
    (derivedPullbackModelIso_hom_app_comp (f₁ ≫ f₂))
    (exists_iso_Qh_isIso_derivedPullbackComparison (f₁ ≫ f₂)) K

/-- The comparison of the two models of derived pullback and direct image is compatible with the
counits of the derived adjunctions. -/
theorem map_derivedPushforwardModelIso_comp_counit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing X)))) :
    (@derivedPullback _ _ f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance).map
        ((derivedPushforwardModelIso f).hom.app K) ≫
      (@derivedAdjunction _ _ f
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)).counit.app
        ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K) =
    (derivedPullbackModelIso f).inv.app
        ((@derivedPushforward _ _ f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _)).obj K) ≫
      (Stacks.Injectives.grothendieckModelEquiv _).functor.map
        ((@derivedAdjunction _ _ f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _)).counit.app K) :=
  Stacks.CategoryTheory.ModelComparison.counit_comm
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing X))).symm
    (shrinkComparisonQhIso (SheafOfModules.{u} (structureSheafRing Y))).symm
    (homotopyPullbackPushforwardAdjunction f)
    (@derivedAdjunction _ _ f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
    (@derivedAdjunction _ _ f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (@derivedPullbackComparison _ _ f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) inferInstance)
    (@derivedPullbackComparison _ _ f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) inferInstance)
    (@derivedPushforwardUnit _ _ f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
    (@derivedPushforwardUnit _ _ f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (derivedPullbackModelIso f) (derivedPushforwardModelIso f)
    (@derivedAdjunction_counit_fac _ _ f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _))
    (@derivedAdjunction_counit_fac _ _ f
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (derivedPullbackModelIso_hom_app_comp f)
    (map_derivedPushforwardUnit_comp_derivedPushforwardModelIso_hom_app f)
    (exists_iso_Qh_isIso_derivedPushforwardUnit f) K

section Standard

open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

/-- `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`, with the transport along
the square taken componentwise. -/
theorem derivedPullbackCompIsoLeft_eq {X' X S' S : RingedSpace.{u, u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g) :
    Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq =
      @derivedPullbackCompIsoCanonical _ _ _ f' g (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ≪≫
        @derivedPullbackCongr X' S (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          _ _ sq.symm := by
  rw [← @eqToIso_derivedPullback_eq_derivedPullbackCongr.{u, u + 1, u + 1} X' S
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _ _ sq.symm]
  rfl

end Standard


open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical) in
/-- **The derived base change map at the locally small model is invertible where it is at the
standard model.** For a commutative square of ringed spaces and `K ∈ D(𝒪_X)`, if the derived base
change map `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K` of [Stacks, Tag 08HY] is invertible at the standard model,
then so is the base change map of the derived adjunctions at the locally small model. -/
theorem isIso_baseChangeMap_of_isIso_derivedBaseChangeMap {X' X S' S : RingedSpace.{u, u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing X))))
    (hK : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq K)) :
    IsIso (Stacks.CategoryTheory.BaseChange.map
      (@derivedAdjunction _ _ f
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
      (@derivedAdjunction _ _ f'
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
      (@derivedPullbackCompIsoCanonical _ _ _ f' g
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) ≪≫
        @derivedPullbackCongr X' S
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _) _ _ sq.symm)
      (@derivedPullbackCompIsoCanonical _ _ _ g' f
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
      ((Stacks.Injectives.grothendieckModelEquiv _).functor.obj K)) := by
  have : IsIso (Stacks.CategoryTheory.BaseChange.map
      (@derivedAdjunction _ _ f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
      (@derivedAdjunction _ _ f' (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
      (@derivedPullbackCompIsoCanonical _ _ _ f' g (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ≪≫
        @derivedPullbackCongr X' S (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          _ _ sq.symm)
      (@derivedPullbackCompIsoCanonical _ _ _ g' f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)) K) := by
    rw [Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq_map,
      derivedPullbackCompIsoLeft_eq] at hK
    exact hK
  exact Stacks.CategoryTheory.BaseChange.isIso_map_of_factorization_of_comparison
    (@derivedAdjunction _ _ f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
    (@derivedAdjunction _ _ f' (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))
    (@derivedAdjunction _ _ f (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (@derivedAdjunction _ _ f'
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _))
    (@derivedPullbackCompIsoCanonical _ _ _ f' g (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ≪≫
      @derivedPullbackCongr X' S (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        _ _ sq.symm)
    (@derivedPullbackCompIsoCanonical _ _ _ g' f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)) _ _
    (derivedPullbackModelIso g).inv (derivedPullbackModelIso g').inv
    (derivedPullbackModelIso f).inv (derivedPullbackModelIso f').inv
    (derivedPushforwardModelIso f).hom (derivedPushforwardModelIso f').hom K
    (map_derivedPushforwardModelIso_comp_counit f) (map_derivedPushforwardModelIso_comp_counit f')
    (derivedPullbackModelIso (g' ≫ f)).inv
    (fun K => Stacks.CategoryTheory.BaseChange.comparison_trans _ _ _ _ _ _ _ _ K
      (derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso f' g K)
      (derivedPullbackCongr_hom_app_comp_derivedPullbackModelIso_inv_app sq.symm K))
    (fun K => derivedPullbackCompIsoCanonical_comp_derivedPullbackModelIso g' f K)

end StacksDraft.DerivedModel

module

public import StacksFrontier.Deformation.RingedSpaceThickening.InverseImageNaiveCotangentComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactAdjunctionDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes
public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismExtClass
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
import StacksCore.Tactic.StacksAttribute

/-!
# The identification of Ext groups in Stacks 0GQ2, and the final deduction

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces, and
factor `g` as `ι : (Y, 𝒪_Y) ⟶ (Y, g⁻¹𝒪_X)` followed by `π : (Y, g⁻¹𝒪_X) ⟶ (X, 𝒪_X)`. For an
`𝒪_Y`-module `𝒢` the remark **Stacks 0GQ2** identifies
`Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢) = Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)` by the tensor–hom
adjunction, and deduces that a morphism `Y' ⟶ X'` compatible with `g` and `c` exists if and only
if `ξ` and `ζ` have the same image in `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)`. This file proves:

* `derivedPullbackLiftProj`: the comparison `Lι^* ∘ Lπ^* ⟶ Lg^*`, an isomorphism;
* `inverseImageExtEquiv`: the identification
  `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢) ≃ Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`, through
  `Lg^* = Lι^* ∘ π^*`, the adjunction `Lι^* ⊣ ι_*` and `g⁻¹𝖭𝖫_{X/S} = 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}`;
* `inverseImageExtEquiv_restrictDerivedExtClass`: it carries the image of `ζ` in
  `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)` (Stacks 0GQ1's `restrictDerivedExtClass`) to the image of `ζ` in
  `Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`, the class of `𝒪'₂`;
* `inverseImageExtEquiv_pullbackExtClass`: it carries the image of `ξ` in
  `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)` (Stacks 0GQ1's `pullbackExtClass`) to the image of `ξ` in
  `Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`, the class of `𝒪'₁`;
* `nonempty_compatibleMorphism_iff_isomorphismClassesEquivExt_eq` and
  `nonempty_compatibleMorphism_iff_images_eq`: the remark's final deduction.

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (f : X ⟶ S) (g : Y ⟶ X)

/-- `ι^* ∘ π^* ≅ g^*`: the left adjoints of `ι_* ⋙ π_* ≅ g_*`. -/
def pullbackLiftProjIso :
    modulePullback (inverseImageProj g) ⋙ modulePullback (inverseImageLift g) ≅ modulePullback g :=
  Adjunction.leftAdjointCompIso (modulePullbackPushforwardAdjunction (inverseImageProj g))
    (modulePullbackPushforwardAdjunction (inverseImageLift g))
    (modulePullbackPushforwardAdjunction g) (pushforwardLiftProjNatIso g)

/-- The unit of `g^* ⊣ g_*` is that of `π^* ⊣ π_*` followed by that of `ι^* ⊣ ι_*`, through
`ι^*π^* ≅ g^*` and `π_*ι_* ≅ g_*`. -/
theorem unit_pullbackLiftProjIso (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction (inverseImageProj g)).unit.app M ≫
        (modulePushforward (inverseImageProj g)).map
          ((modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
            ((modulePullback (inverseImageProj g)).obj M)) ≫
        (pushforwardLiftProjNatIso g).hom.app _ ≫
        (modulePushforward g).map ((pullbackLiftProjIso g).hom.app M) =
      (modulePullbackPushforwardAdjunction g).unit.app M := by
  have h := unit_conjugateEquiv ((modulePullbackPushforwardAdjunction (inverseImageProj g)).comp
    (modulePullbackPushforwardAdjunction (inverseImageLift g)))
    (modulePullbackPushforwardAdjunction g) (pullbackLiftProjIso g).inv M
  rw [pullbackLiftProjIso, Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    Adjunction.comp_unit_app] at h
  rw [← Category.assoc, ← Category.assoc]
  refine (congrArg (· ≫ (modulePushforward g).map ((pullbackLiftProjIso g).hom.app M)) h).trans ?_
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  change _ ≫ (modulePushforward g).map
    (((pullbackLiftProjIso g).inv ≫ (pullbackLiftProjIso g).hom).app M) = _
  rw [Iso.inv_hom_id, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The comparison `Lι^*Lπ^*(K) ⟶ ι^*π^*K ≅ g^*K` of the composite of the two derived pullbacks
with degreewise pullback along `g`. -/
def derivedPullbackLiftProjCounit :
    DerivedCategory.Qh ⋙ (derivedPullback (inverseImageProj g) ⋙
      derivedPullback (inverseImageLift g)) ⟶ pullbackOnHomotopy g :=
  Functor.whiskerRight (derivedPullbackComparison (inverseImageProj g))
      (derivedPullback (inverseImageLift g)) ≫
    Functor.whiskerLeft ((modulePullback (inverseImageProj g)).mapHomotopyCategory
      (ComplexShape.up ℤ)) (derivedPullbackComparison (inverseImageLift g)) ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (pullbackLiftProjIso g)
      (ComplexShape.up ℤ)).hom DerivedCategory.Qh

/-- `derivedPullbackLiftProjCounit` on an object. -/
theorem derivedPullbackLiftProjCounit_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullbackLiftProjCounit g).app K =
      (derivedPullback (inverseImageLift g)).map
          ((derivedPullbackComparison (inverseImageProj g)).app K) ≫
        (derivedPullbackComparison (inverseImageLift g)).app
          (((modulePullback (inverseImageProj g)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (pullbackLiftProjIso g)
          (ComplexShape.up ℤ)).hom.app K) :=
  rfl

/-- **`Lι^* ∘ Lπ^* ⟶ Lg^*`**, the comparison of derived pullbacks along `g = π ∘ ι` given by the
universal property of `Lg^*`. -/
def derivedPullbackLiftProj :
    derivedPullback (inverseImageProj g) ⋙ derivedPullback (inverseImageLift g) ⟶
      derivedPullback g :=
  (derivedPullback g).leftDerivedLift (derivedPullbackComparison g)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    _ (derivedPullbackLiftProjCounit g)

/-- `Lι^*Lπ^* ⟶ Lg^*` followed by the comparison of `Lg^*` with `g^*` is the comparison of
`Lι^*Lπ^*` with `ι^*π^* ≅ g^*`. -/
theorem derivedPullbackLiftProj_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullbackLiftProj g).app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison g).app K = (derivedPullbackLiftProjCounit g).app K :=
  Functor.leftDerived_fac_app _ _ _ _ _ K

/-- The comparison `Lι^* ∘ Lπ^* ⟶ Lg^*` is an isomorphism. -/
instance : IsIso (derivedPullbackLiftProj g) := by
  refine ((derivedPullback g).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    (derivedPullbackComparison g)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    _ (derivedPullbackLiftProjCounit g)).1 ?_
  refine LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat X)
    (fun N => by
      obtain ⟨K, hK, s, hs⟩ := Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat X N
      exact ⟨K, hK, s, hs⟩)
    (pullbackOnHomotopy g) (fun s hs hK hM => pullbackInvertsQuasiIso_isKFlat g s hs hK hM)
    DerivedCategory.Qh _ _ (fun K hK => ?_)
  rw [derivedPullbackLiftProjCounit_app]
  have h₁ := Stacks.DerivedPullback.Composition.isIso_derivedPullbackComparison_app_of_isKFlat
    (inverseImageProj g) K hK
  have h₂ := Stacks.DerivedPullback.Composition.isIso_derivedPullbackComparison_app_of_isKFlat
    (inverseImageLift g) _ (Stacks.DerivedPullback.Composition.isKFlat_pullback
      (inverseImageProj g) K hK)
  infer_instance

/-- `ι^*π^* ≅ g^*` on homotopy categories, read in the derived category. -/
theorem Qh_map_mapHomotopyCategoryCompIso_pullbackLiftProjIso
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (pullbackLiftProjIso g)
          (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) =
      DerivedCategory.Qh.map
          (((modulePullback (inverseImageLift g)).mapHomotopyCategory (ComplexShape.up ℤ)).map
            (((modulePullback (inverseImageProj g)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app P)) ≫
        DerivedCategory.Qh.map
            (((modulePullback (inverseImageLift g)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app
              (((modulePullback (inverseImageProj g)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              ((Functor.mapHomologicalComplexCompIso (pullbackLiftProjIso g)
                (ComplexShape.up ℤ)).hom.app P)) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Qh.map
    (StacksDraft.MapHomotopyCategory.mapHomotopyCategoryCompIso_hom_app_comp_factors
      (pullbackLiftProjIso g) (ComplexShape.up ℤ) P)

/-- **The comparison `Lι^*Lπ^* ⟶ Lg^*` on a complex.** -/
theorem derivedPullbackLiftProj_app_comp_onComplex
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedPullbackLiftProj g).app (DerivedCategory.Q.obj P) ≫
        derivedPullbackComparisonOnComplex g P =
      (derivedPullback (inverseImageLift g)).map
          (derivedPullbackComparisonOnComplex (inverseImageProj g) P) ≫
        derivedPullbackComparisonOnComplex (inverseImageLift g)
            (((modulePullback (inverseImageProj g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (pullbackLiftProjIso g)
            (ComplexShape.up ℤ)).hom.app P) := by
  have hfac := (derivedPullbackLiftProj_app_comp g
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)).trans
    (derivedPullbackLiftProjCounit_app g _)
  have hnatf : (derivedPullback (inverseImageLift g)).map (DerivedCategory.Qh.map
          (((modulePullback (inverseImageProj g)).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app P)) ≫
        (derivedPullbackComparison (inverseImageLift g)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((modulePullback (inverseImageProj g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) =
      (derivedPullbackComparison (inverseImageLift g)).app
          (((modulePullback (inverseImageProj g)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          (((modulePullback (inverseImageLift g)).mapHomotopyCategory (ComplexShape.up ℤ)).map
            (((modulePullback (inverseImageProj g)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app P)) :=
    (derivedPullbackComparison (inverseImageLift g)).naturality _
  have hnatA : (derivedPullback (inverseImageLift g)).map
        ((derivedPullback (inverseImageProj g)).map
          ((DerivedCategory.quotientCompQhIso _).inv.app P)) ≫
        (derivedPullbackLiftProj g).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
      (derivedPullbackLiftProj g).app (DerivedCategory.Q.obj P) ≫
        (derivedPullback g).map ((DerivedCategory.quotientCompQhIso _).inv.app P) :=
    (derivedPullbackLiftProj g).naturality _
  have hnatQ : DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso (pullbackLiftProjIso g)
              (ComplexShape.up ℤ)).hom.app P)) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (DerivedCategory.quotientCompQhIso _).hom.app
          (((modulePullback (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((modulePullback (inverseImageProj g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (pullbackLiftProjIso g)
          (ComplexShape.up ℤ)).hom.app P) :=
    (DerivedCategory.quotientCompQhIso _).hom.naturality _
  unfold derivedPullbackComparisonOnComplex
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  conv_rhs =>
    rw [Stacks.DerivedPullback.Composition.derivedPullback_map_quotientCompQhIso_hom_inv_assoc
      (inverseImageLift g) (inverseImageProj g) P, reassoc_of% hnatf, ← hnatQ]
  conv_lhs => rw [← reassoc_of% hnatA, reassoc_of% hfac,
    reassoc_of% (Qh_map_mapHomotopyCategoryCompIso_pullbackLiftProjIso g P)]

/-- The degreewise unit of `ι^* ⊣ ι_*` on a complex, read in the derived category. -/
theorem inverseImageLift_derivedUnit_tail
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageRingedSpace g))) ℤ) :
    (DerivedCategory.quotientCompQhIso _).inv.app M ≫
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction (inverseImageLift g)).unit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ≫
      DerivedCategory.Qh.map (((modulePushforward (inverseImageLift g)).mapHomotopyCategory
          (ComplexShape.up ℤ)).map
        (((modulePullback (inverseImageLift g)).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app M)) ≫
      DerivedCategory.Qh.map (((modulePushforward (inverseImageLift g)).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app
        (((modulePullback (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((modulePushforward (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((modulePullback (inverseImageLift g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) =
      DerivedCategory.Q.map
        (((modulePullbackPushforwardAdjunction (inverseImageLift g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app M) := by
  let ι := inverseImageLift g
  let Mq := (HomotopyCategory.quotient
    (SheafOfModules.{u} (structureSheafRing (inverseImageRingedSpace g)))
    (ComplexShape.up ℤ)).obj M
  let N := ((modulePullback ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  have hH : (homotopyPullbackPushforwardAdjunction ι).unit.app Mq ≫
      ((modulePushforward ι).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((modulePullback ι).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M) ≫
      ((modulePushforward ι).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app N =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((modulePullbackPushforwardAdjunction ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app M) := by
    change (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((CategoryTheory.Adjunction.mapHomologicalComplexAdjunction
          (modulePullbackPushforwardAdjunction ι) (ComplexShape.up ℤ)).unit.app M) ≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((modulePushforward ι).mapHomologicalComplex (ComplexShape.up ℤ)).map (𝟙 _)) ≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (𝟙 _) = _
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    congr 1
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality
    (((modulePullbackPushforwardAdjunction ι).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M)
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Category.assoc, hH]
  exact (congrArg (_ ≫ ·) hq).trans (Iso.inv_hom_id_app_assoc _ _ _)

/-- **The derived unit of `ι` on a complex.** The unit of `Lι^* ⊣ Rι_*` at `Q M`, followed by
`Rι_*` of the comparison `Lι^*QM ⟶ Q(ι^*M)`, is `Q` of the degreewise unit followed by the
identification `Q(ι_*ι^*M) = Rι_*Q(ι^*M)` of the exact functor `ι_*`. -/
theorem inverseImageLift_derivedAdjunction_unit_app_Q
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageRingedSpace g))) ℤ) :
    (derivedAdjunction (inverseImageLift g)).unit.app (DerivedCategory.Q.obj M) ≫
        (derivedPushforward (inverseImageLift g)).map
          (derivedPullbackComparisonOnComplex (inverseImageLift g) M) =
      DerivedCategory.Q.map
        (((modulePullbackPushforwardAdjunction (inverseImageLift g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app M) ≫
        (modulePushforward (inverseImageLift g)).mapDerivedCategoryFactors.inv.app
          (((modulePullback (inverseImageLift g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        (derivedPushforwardComparisonIso (inverseImageLift g)).hom.app
          (DerivedCategory.Q.obj (((modulePullback (inverseImageLift g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) := by
  have hu := derivedAdjunction_unit_fac (inverseImageLift g)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)
  have hn := (derivedAdjunction (inverseImageLift g)).unit.naturality
    ((DerivedCategory.quotientCompQhIso _).inv.app M)
  -- notation
  let ι := inverseImageLift g
  let Mq := (HomotopyCategory.quotient
    (SheafOfModules.{u} (structureSheafRing (inverseImageRingedSpace g)))
    (ComplexShape.up ℤ)).obj M
  let N := ((modulePullback ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  have hdpu := (derivedPushforwardUnit ι).naturality
    (((modulePullback ι).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M)
  have hfac := Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app
    (modulePushforward ι) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)
  have hci := (derivedPushforwardComparisonIso ι).hom.naturality
    ((DerivedCategory.quotientCompQhIso _).hom.app N)
  have hfh := (modulePushforward ι).mapDerivedCategoryFactorsh_hom_app N
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality
    (((modulePullbackPushforwardAdjunction ι).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M)
  have hG : (modulePushforward ι).mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) ≫
      (modulePushforward ι).mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso _).hom.app N) =
      DerivedCategory.Qh.map (((modulePushforward ι).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom.app N) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (((modulePushforward ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        (modulePushforward ι).mapDerivedCategoryFactors.inv.app N := by
    rw [← cancel_epi ((modulePushforward ι).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)), Iso.hom_inv_id_app_assoc, hfh]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc DerivedCategory.Qh, Iso.inv_hom_id_app]
    simp
  have hn' : (derivedAdjunction ι).unit.app (DerivedCategory.Q.obj M) ≫
      (derivedPushforward ι).map ((derivedPullback ι).map
        ((DerivedCategory.quotientCompQhIso _).inv.app M)) =
      (DerivedCategory.quotientCompQhIso _).inv.app M ≫
        (derivedAdjunction ι).unit.app (DerivedCategory.Qh.obj Mq) := hn.symm
  unfold derivedPullbackComparisonOnComplex
  simp only [CategoryTheory.Functor.map_comp]
  rw [reassoc_of% hn', reassoc_of% hu]
  have hdpu' : (derivedPushforwardUnit ι).app
        (((modulePullback ι).mapHomotopyCategory (ComplexShape.up ℤ)).obj Mq) ≫
      (derivedPushforward ι).map (DerivedCategory.Qh.map
        (((modulePullback ι).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M)) =
      DerivedCategory.Qh.map (((modulePushforward ι).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((modulePullback ι).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M)) ≫
        (derivedPushforwardUnit ι).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) :=
    hdpu.symm
  rw [reassoc_of% hdpu', ← hfac]
  simp only [Category.assoc]
  have hci' : (derivedPushforwardComparisonIso ι).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
      (derivedPushforward ι).map ((DerivedCategory.quotientCompQhIso _).hom.app N) =
      (modulePushforward ι).mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso _).hom.app N) ≫
        (derivedPushforwardComparisonIso ι).hom.app (DerivedCategory.Q.obj N) := hci.symm
  rw [hci', reassoc_of% hG, reassoc_of% (inverseImageLift_derivedUnit_tail g M)]

/-- `π^*` is exact, so the comparison `Lπ^*QK ⟶ Q(π^*K)` is invertible. -/
instance isIso_derivedPullbackComparisonOnComplex_proj
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    IsIso (derivedPullbackComparisonOnComplex (inverseImageProj g) K) := by
  have h : ∀ M, IsIso ((derivedPullbackComparison (inverseImageProj g)).app M) := fun M => by
    rw [← Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app
      (modulePullback (inverseImageProj g)) (derivedPullback (inverseImageProj g))
      (derivedPullbackComparison (inverseImageProj g)) M]
    infer_instance
  unfold derivedPullbackComparisonOnComplex
  infer_instance

/-- `Lι^*Q(π^*K) ≅ Lg^*QK`. -/
def liftProjComparison (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedPullback (inverseImageLift g)).obj
        (DerivedCategory.Q.obj (((modulePullback (inverseImageProj g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) ≅
      (derivedPullback g).obj (DerivedCategory.Q.obj K) :=
  (derivedPullback (inverseImageLift g)).mapIso
      (asIso (derivedPullbackComparisonOnComplex (inverseImageProj g) K)).symm ≪≫
    (asIso (derivedPullbackLiftProj g)).app (DerivedCategory.Q.obj K)

/-- `Lι^*Q(π^*K) ≅ Lg^*QK` followed by the comparison `Lg^*QK ⟶ Q(g^*K)` is the comparison
`Lι^*Q(π^*K) ⟶ Q(ι^*π^*K)` followed by `ι^*π^* ≅ g^*`. -/
theorem liftProjComparison_hom_comp
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (liftProjComparison g K).hom ≫ derivedPullbackComparisonOnComplex g K =
      derivedPullbackComparisonOnComplex (inverseImageLift g)
          (((modulePullback (inverseImageProj g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (pullbackLiftProjIso g)
          (ComplexShape.up ℤ)).hom.app K) := by
  change ((derivedPullback (inverseImageLift g)).map
      (CategoryTheory.inv (derivedPullbackComparisonOnComplex (inverseImageProj g) K)) ≫
    (derivedPullbackLiftProj g).app (DerivedCategory.Q.obj K)) ≫ _ = _
  rw [Category.assoc, derivedPullbackLiftProj_app_comp_onComplex, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The transposition `Hom(Lg^*QK, B) ⟶ Hom(Q(π^*K), ι_*B)` along `g = π ∘ ι`: through
`Lι^*Q(π^*K) ≅ Lg^*QK`, the adjunction `Lι^* ⊣ Rι_*`, and `Rι_* ≅ ι_*` for the exact `ι_*`. -/
def liftProjTransport (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    {B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (z : (derivedPullback g).obj (DerivedCategory.Q.obj K) ⟶ B) :
    DerivedCategory.Q.obj (((modulePullback (inverseImageProj g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
      (modulePushforward (inverseImageLift g)).mapDerivedCategory.obj B :=
  (derivedAdjunction (inverseImageLift g)).homEquiv _ _ ((liftProjComparison g K).hom ≫ z) ≫
    (derivedPushforwardComparisonIso (inverseImageLift g)).inv.app B

/-- The degreewise unit `π^*K ⟶ ι_*ι^*π^*K ≅ ι_*g^*K`. -/
abbrev liftProjUnit (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :=
  ((modulePullbackPushforwardAdjunction (inverseImageLift g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).unit.app (((modulePullback (inverseImageProj g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≫
    ((modulePushforward (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso (pullbackLiftProjIso g) (ComplexShape.up ℤ)).hom.app K)

/-- Naturality of `mapDerivedCategoryFactors.inv` for the exact functor `ι_*`. -/
private theorem mapDerivedCategoryFactors_inv_comp_map_Q_map
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (a : K ⟶ L) :
    (modulePushforward (inverseImageLift g)).mapDerivedCategoryFactors.inv.app K ≫
      (modulePushforward (inverseImageLift g)).mapDerivedCategory.map (DerivedCategory.Q.map a) =
    DerivedCategory.Q.map (((modulePushforward (inverseImageLift g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map a) ≫
      (modulePushforward (inverseImageLift g)).mapDerivedCategoryFactors.inv.app L := by
  rw [← cancel_epi ((modulePushforward (inverseImageLift g)).mapDerivedCategoryFactors.hom.app _),
    Iso.hom_inv_id_app_assoc]
  exact ((Iso.eq_comp_inv ((modulePushforward (inverseImageLift g)).mapDerivedCategoryFactors.app
    _)).2 ((modulePushforward (inverseImageLift g)).mapDerivedCategoryFactors_hom_naturality
      a)).trans (Category.assoc _ _ _)

/-- **The transposition on maps factoring through the comparison `Lg^*QK ⟶ Q(g^*K)`.** -/
theorem liftProjTransport_comparison
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    {B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (w : DerivedCategory.Q.obj
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶ B) :
    liftProjTransport g K (derivedPullbackComparisonOnComplex g K ≫ w) =
      DerivedCategory.Q.map (liftProjUnit g K) ≫
        (modulePushforward (inverseImageLift g)).mapDerivedCategoryFactors.inv.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (modulePushforward (inverseImageLift g)).mapDerivedCategory.map w := by
  unfold liftProjTransport
  rw [Adjunction.homEquiv_unit, reassoc_of% (liftProjComparison_hom_comp g K),
    CategoryTheory.Functor.map_comp,
    reassoc_of% (inverseImageLift_derivedAdjunction_unit_app_Q g _)]
  have hn := (derivedPushforwardComparisonIso (inverseImageLift g)).hom.naturality
    (DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (pullbackLiftProjIso g)
      (ComplexShape.up ℤ)).hom.app K) ≫ w)
  simp only [Category.assoc]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app, Category.comp_id, CategoryTheory.Functor.map_comp]
  rw [reassoc_of% (mapDerivedCategoryFactors_inv_comp_map_Q_map g _),
    ← Category.assoc (DerivedCategory.Q.map _),
    ← CategoryTheory.Functor.map_comp]

/-- The unit of `g^* ⊣ g_*` on complexes, through `g = π ∘ ι`. -/
theorem unit_liftProjUnit (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app K ≫
      ((modulePushforward (inverseImageProj g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (liftProjUnit g K) =
      ((modulePullbackPushforwardAdjunction g).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app K ≫
        (NatTrans.mapHomologicalComplex (pushforwardLiftProjNatIso g).inv
          (ComplexShape.up ℤ)).app _ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h := unit_pullbackLiftProjIso g (K.X n)
  have hn := (pushforwardLiftProjNatIso g).hom.naturality ((pullbackLiftProjIso g).hom.app (K.X n))
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  change (modulePullbackPushforwardAdjunction (inverseImageProj g)).unit.app (K.X n) ≫
      (modulePushforward (inverseImageProj g)).map
        ((modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
          ((modulePullback (inverseImageProj g)).obj (K.X n)) ≫
        (modulePushforward (inverseImageLift g)).map ((pullbackLiftProjIso g).hom.app (K.X n))) =
    (modulePullbackPushforwardAdjunction g).unit.app (K.X n) ≫
      (pushforwardLiftProjNatIso g).inv.app ((modulePullback g).obj (K.X n))
  rw [← h, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  congr 2

/-- **The canonical maps of naive cotangent complexes along `g = π ∘ ι`, on pullbacks**:
`π^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S} ⟶ ι_*𝖭𝖫_{Y/S}` is the unit followed by `ι_*` of
`g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`. -/
theorem liftProjUnit_comp_pullbackNaiveCotangentMap :
    liftProjUnit g (PresentedSquareZeroExtension.relativeComplex f) ≫
        ((modulePushforward (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (pullbackNaiveCotangentMap g f) =
      pullbackNaiveCotangentMap (inverseImageProj g) f ≫ inverseImageNaiveCotangentMap f g := by
  apply (((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv _ _).injective
  have hκ : ((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).homEquiv _ _ (pullbackNaiveCotangentMap (inverseImageProj g) f) =
      naiveCotangentPushMap (inverseImageProj g) f := Equiv.apply_symm_apply _ _
  have hr := ((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
    (ComplexShape.up ℤ)).homEquiv_naturality_right
      (pullbackNaiveCotangentMap (inverseImageProj g) f) (inverseImageNaiveCotangentMap f g)
  have hφ := (NatTrans.mapHomologicalComplex (pushforwardLiftProjNatIso g).inv
    (ComplexShape.up ℤ)).naturality (pullbackNaiveCotangentMap g f)
  have hg : ((modulePullbackPushforwardAdjunction g).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app _ ≫
      ((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (pullbackNaiveCotangentMap g f) = naiveCotangentPushMap g f :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  refine (congrArg
      (((modulePullbackPushforwardAdjunction (inverseImageProj g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app (PresentedSquareZeroExtension.relativeComplex f) ≫ ·)
    (CategoryTheory.Functor.map_comp
      ((modulePushforward (inverseImageProj g)).mapHomologicalComplex (ComplexShape.up ℤ))
      (liftProjUnit g (PresentedSquareZeroExtension.relativeComplex f))
      (((modulePushforward (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (pullbackNaiveCotangentMap g f)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ((modulePushforward (inverseImageProj g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (((modulePushforward (inverseImageLift g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (pullbackNaiveCotangentMap g f)))
    (unit_liftProjUnit g (PresentedSquareZeroExtension.relativeComplex f))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hφ.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hg).trans ?_
  refine (naiveCotangentPushMap_comp f g).trans ?_
  exact (hr.trans (congrArg (· ≫ _) hκ)).symm

/-- `Lι^*Q(π^*K) ≅ Lg^*QK` is natural in the complex `K`. -/
theorem liftProjComparison_naturality
    {K K' : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (a : K ⟶ K') :
    (liftProjComparison g K).hom ≫ (derivedPullback g).map (DerivedCategory.Q.map a) =
      (derivedPullback (inverseImageLift g)).map (DerivedCategory.Q.map
        (((modulePullback (inverseImageProj g)).mapHomologicalComplex (ComplexShape.up ℤ)).map a)) ≫
        (liftProjComparison g K').hom := by
  have h₁ := derivedPullbackComparisonOnComplex_naturality' (inverseImageProj g) a
  have h₂ : CategoryTheory.inv (derivedPullbackComparisonOnComplex (inverseImageProj g) K) ≫
      (derivedPullback (inverseImageProj g)).map (DerivedCategory.Q.map a) =
      DerivedCategory.Q.map (((modulePullback (inverseImageProj g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map a) ≫
        CategoryTheory.inv (derivedPullbackComparisonOnComplex (inverseImageProj g) K') := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, h₁]
  have h₃ := (derivedPullbackLiftProj g).naturality (DerivedCategory.Q.map a)
  change ((derivedPullback (inverseImageLift g)).map
      (CategoryTheory.inv (derivedPullbackComparisonOnComplex (inverseImageProj g) K)) ≫
      (derivedPullbackLiftProj g).app (DerivedCategory.Q.obj K)) ≫ _ =
    _ ≫ ((derivedPullback (inverseImageLift g)).map
      (CategoryTheory.inv (derivedPullbackComparisonOnComplex (inverseImageProj g) K')) ≫
      (derivedPullbackLiftProj g).app (DerivedCategory.Q.obj K'))
  rw [Category.assoc, ← h₃]
  change _ ≫ (derivedPullback (inverseImageLift g)).map ((derivedPullback (inverseImageProj g)).map
    (DerivedCategory.Q.map a)) ≫ _ = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h₂]
  exact (congrArg (· ≫ (derivedPullbackLiftProj g).app (DerivedCategory.Q.obj K'))
    (CategoryTheory.Functor.map_comp (derivedPullback (inverseImageLift g)) _ _)).trans
    (Category.assoc _ _ _)

/-- The transposition is natural in the complex. -/
theorem liftProjTransport_naturality
    {K K' : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (a : K ⟶ K')
    {B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (z : (derivedPullback g).obj (DerivedCategory.Q.obj K') ⟶ B) :
    liftProjTransport g K ((derivedPullback g).map (DerivedCategory.Q.map a) ≫ z) =
      DerivedCategory.Q.map (((modulePullback (inverseImageProj g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a) ≫ liftProjTransport g K' z := by
  unfold liftProjTransport
  rw [← Category.assoc ((liftProjComparison g K).hom), liftProjComparison_naturality,
    Category.assoc, Adjunction.homEquiv_naturality_left, Category.assoc]

/-- The unit of `π^* ⊣ π_*` followed by `π_*` of the unit of `ι^* ⊣ ι_*` is the unit of
`g^* ⊣ g_*` read through `ι^*π^* ≅ g^*`. -/
theorem unit_proj_comp_lift (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction (inverseImageProj g)).unit.app M ≫
      (modulePushforward (inverseImageProj g)).map
        ((modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
          ((modulePullback (inverseImageProj g)).obj M) ≫
        (modulePushforward (inverseImageLift g)).map ((pullbackLiftProjIso g).hom.app M)) =
    (modulePullbackPushforwardAdjunction g).unit.app M ≫
      (pushforwardLiftProjNatIso g).inv.app ((modulePullback g).obj M) := by
  have h := unit_pullbackLiftProjIso g M
  rw [← h, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  congr 2

/-- **`c^♭` along `π` is `c^♭` along `g` read through `ι`.** -/
theorem unit_lift_comp_cAdj {F : SheafOfModules.{u} (structureSheafRing X)}
    {G : SheafOfModules.{u} (structureSheafRing Y)} (c : F ⟶ (modulePushforward g).obj G) :
    (modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
        ((modulePullback (inverseImageProj g)).obj F) ≫
      (modulePushforward (inverseImageLift g)).map
        ((pullbackLiftProjIso g).hom.app F ≫ LiftGluing.cAdj g c) =
      inverseImageIdealMap c := by
  apply ((modulePullbackPushforwardAdjunction (inverseImageProj g)).homEquiv _ _).injective
  refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
  have hn := (pushforwardLiftProjNatIso g).inv.naturality (LiftGluing.cAdj g c)
  have hc : (modulePullbackPushforwardAdjunction g).unit.app F ≫
      (modulePushforward g).map (LiftGluing.cAdj g c) = c :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hlhs : (modulePullbackPushforwardAdjunction (inverseImageProj g)).unit.app F ≫
      (modulePushforward (inverseImageProj g)).map
        ((modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
            ((modulePullback (inverseImageProj g)).obj F) ≫
          (modulePushforward (inverseImageLift g)).map
            ((pullbackLiftProjIso g).hom.app F ≫ LiftGluing.cAdj g c)) =
      c ≫ (pushforwardLiftProjNatIso g).inv.app G := by
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, ← Category.assoc]
    rw [Category.assoc ((modulePullbackPushforwardAdjunction (inverseImageProj g)).unit.app F),
      ← CategoryTheory.Functor.map_comp, unit_proj_comp_lift, Category.assoc]
    change _ ≫ _ ≫ (modulePushforward (inverseImageLift g) ⋙
      modulePushforward (inverseImageProj g)).map (LiftGluing.cAdj g c) = _
    rw [← hn, ← Category.assoc, hc]
  refine ((Adjunction.homEquiv_unit _ _ _ _).trans hlhs).trans ?_
  ext
  rfl

section Identification

variable {f g} {G : SheafOfModules.{u} (structureSheafRing Y)}

/-- The tail `ι_*(𝒢[0][1]) ≅ (ι_*𝒢)[0][1]` of `mapExtOne` for the exact `ι_*`. -/
def liftShiftSingleIso :
    (modulePushforward (inverseImageLift g)).mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        ((modulePushforward (inverseImageLift g)).obj G))⟦(1 : ℤ)⟧ :=
  ((modulePushforward (inverseImageLift g)).mapDerivedCategory.commShiftIso (1 : ℤ)).app _ ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso
      (((modulePushforward (inverseImageLift g)).mapDerivedCategorySingleFunctor 0).app G)

variable (f g G) in
/-- **The identification `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢) = Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)` of
Stacks 0GQ2.** Through `Lg^* = Lι^* ∘ π^*` along `g = π ∘ ι`, the tensor–hom adjunction
`Lι^* ⊣ Rι_* = ι_*` (restriction of scalars along `g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`), and the identification
`g⁻¹𝖭𝖫_{X/S} = 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` (`inverseImageNaiveCotangentIso`). -/
@[stacks 0GQ2]
def inverseImageExtEquiv :
    extOnePulledNaiveCotangent g f G ≃
      extOneNaiveCotangent (inverseImageSpaceHom f g) (restrictedModule g G) :=
  ((Iso.homCongr (liftProjComparison g (PresentedSquareZeroExtension.relativeComplex f)).symm
      (Iso.refl _)).trans ((derivedAdjunction (inverseImageLift g)).homEquiv _ _)).trans
    (Iso.homCongr (DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIso f g))
      (((derivedPushforwardComparisonIso (inverseImageLift g)).app _).symm ≪≫ liftShiftSingleIso))

/-- **The identification `inverseImageExtEquiv` is the explicit composite**: the transposition
`liftProjTransport` along the adjunction `Lι^* ⊣ ι_*`, preceded by
`g⁻¹𝖭𝖫_{X/S} = 𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}` and followed by `ι_*(𝒢[1]) = (ι_*𝒢)[1]`. -/
@[stacks 0GQ2]
theorem inverseImageExtEquiv_apply (z : extOnePulledNaiveCotangent g f G) :
    inverseImageExtEquiv f g G z =
      (DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIso f g)).inv ≫
        liftProjTransport g (PresentedSquareZeroExtension.relativeComplex f) z ≫
        liftShiftSingleIso.hom :=
  (congrArg (fun t => (DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIso f g)).inv ≫
      (derivedAdjunction (inverseImageLift g)).homEquiv _ _
        ((liftProjComparison g (PresentedSquareZeroExtension.relativeComplex f)).hom ≫ t) ≫
      ((derivedPushforwardComparisonIso (inverseImageLift g)).inv.app _ ≫ liftShiftSingleIso.hom))
    (Category.comp_id z)).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)

/-- Algebra for `inverseImageExtEquiv_restrictDerivedExtClass`. -/
private theorem assemble_aux {C : Type*} [Category* C] {A A' U V DU DV W T : C} (k : A ≅ A')
    (u : A ⟶ U) (p : U ⟶ V) (fi₁ : U ⟶ DU) (fi₂ : V ⟶ DV) (Dp : DU ⟶ DV) (Dz : DV ⟶ W)
    (t : W ⟶ T) (n : A' ⟶ V) (h₁ : fi₁ ≫ Dp = p ≫ fi₂) (h₂ : u ≫ p = k.hom ≫ n) :
    k.inv ≫ (u ≫ fi₁ ≫ Dp ≫ Dz) ≫ t = n ≫ fi₂ ≫ Dz ≫ t := by
  simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₂, Iso.inv_hom_id_assoc]

/-- **The image of `ζ` through `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)` is its image in
`Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`.** -/
@[stacks 0GQ2]
theorem inverseImageExtEquiv_restrictDerivedExtClass (ζ : extOneNaiveCotangent (g ≫ f) G) :
    inverseImageExtEquiv f g G
        (restrictDerivedExtClass (derivedPullbackNaiveCotangentMap g f) ζ) =
      inverseImageExtMap ζ := by
  refine (inverseImageExtEquiv_apply (G := G)
    (restrictDerivedExtClass (derivedPullbackNaiveCotangentMap g f) ζ)).trans ?_
  have hq : restrictDerivedExtClass (derivedPullbackNaiveCotangentMap g f) ζ =
      derivedPullbackComparisonOnComplex g (PresentedSquareZeroExtension.relativeComplex f) ≫
        (DerivedCategory.Q.map (pullbackNaiveCotangentMap g f) ≫ ζ) :=
    (congrArg (· ≫ ζ) (derivedPullbackNaiveCotangentMap_eq (f := f) g)).trans (Category.assoc _ _ _)
  refine (congrArg (fun t => (DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIso f g)).inv ≫
      liftProjTransport g (PresentedSquareZeroExtension.relativeComplex f) t ≫
        liftShiftSingleIso.hom) hq).trans ?_
  refine (congrArg (fun t => (DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIso f g)).inv ≫
      t ≫ liftShiftSingleIso.hom) ((liftProjTransport_comparison g _ _).trans
        (congrArg (fun t => _ ≫ _ ≫ t) (CategoryTheory.Functor.map_comp _ _ _)))).trans ?_
  have hf' := mapDerivedCategoryFactors_inv_comp_map_Q_map g (pullbackNaiveCotangentMap g f)
  have h₂ : DerivedCategory.Q.map
        (liftProjUnit g (PresentedSquareZeroExtension.relativeComplex f)) ≫
      DerivedCategory.Q.map (((modulePushforward (inverseImageLift g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (pullbackNaiveCotangentMap g f)) =
      (DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIso f g)).hom ≫
        DerivedCategory.Q.map (inverseImageNaiveCotangentMap f g) :=
    (CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (liftProjUnit_comp_pullbackNaiveCotangentMap f g)).trans
        (CategoryTheory.Functor.map_comp _ _ _))
  exact assemble_aux _ _ _ _ _ _ _ _ _ hf' h₂

end Identification

section Xi

/-- Algebra for `xiComparison_f_negOne`. -/
private theorem assemble_xi {C : Type*} [Category* C] {A πK ιgK ιgK' ιD ιG πC πF : C} (πi : A ⟶ πK)
    (u : πK ⟶ ιgK) (ig : ιgK ⟶ ιD) (x : ιD ⟶ ιG) (e₂ : A ⟶ πC) (pδ : πC ⟶ πF) (cb : πF ⟶ ιG)
    (pe : πC ⟶ πK) (y : ιgK ⟶ ιgK') (z : ιgK' ⟶ ιG) (pa : πK ⟶ πF) (uF : πF ⟶ ιgK')
    (F1 : πi = e₂ ≫ pe) (F2 : ig ≫ x = y ≫ z) (F3 : pa ≫ uF = u ≫ y) (F4 : pe ≫ pa = pδ)
    (F5 : uF ≫ z = cb) : ((πi ≫ u) ≫ ig) ≫ x = e₂ ≫ pδ ≫ cb := by
  rw [Category.assoc, Category.assoc, F2, F1, ← F4, ← F5]
  simp only [Category.assoc]
  rw [← reassoc_of% F3]

/-- Algebra for `key_xi`. -/
private theorem assemble_L {C : Type*} [Category* C] {A₀ A₁ A₂ R T B₁ B₂ C₁ C₂ : C} (u : A₀ ⟶ A₁)
    (v : A₁ ⟶ A₂) (TT : A₂ ⟶ R) (t : R ⟶ T) (TT' : A₁ ⟶ R) (U : A₁ ⟶ B₁) (fi : B₁ ⟶ C₁)
    (Dw : C₁ ⟶ R) (p : B₁ ⟶ B₂) (fi' : B₂ ⟶ C₂) (DcY : C₂ ⟶ R) (cl : A₀ ⟶ T)
    (h₁ : v ≫ TT = TT') (h₂ : TT' = U ≫ fi ≫ Dw) (h₃ : fi ≫ Dw = p ≫ fi' ≫ DcY)
    (h₄ : (u ≫ U ≫ p) ≫ fi' ≫ DcY ≫ t = cl) : (u ≫ v) ≫ TT ≫ t = cl := by
  subst h₂
  rw [← h₄]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₃]

/-- Algebra for `key_xi`. -/
private theorem assemble_R {C : Type*} [Category* C] {A₀ A₁ A₂ E T : C} (u : A₀ ⟶ A₁) (v : A₁ ⟶ A₂)
    (X : A₂ ⟶ E) (S : E ⟶ T) (Y : A₁ ⟶ E) (w : A₁ ⟶ A₀) (cl : A₀ ⟶ T)
    (h₁ : v ≫ X = Y) (h₂ : w ≫ cl = Y ≫ S) (h₃ : u ≫ w = 𝟙 _) : (u ≫ v) ≫ X ≫ S = cl := by
  rw [Category.assoc, reassoc_of% h₁, ← h₂, reassoc_of% h₃]

open HomologicalComplex in
/-- `mapDoubleIso` in degree `-1`. -/
theorem mapDoubleIso_hom_f_negOne {X' Y' : RingedSpace.{u, u}} (h : Y' ⟶ X')
    {C B : SheafOfModules.{u} (structureSheafRing X')} (d : C ⟶ B)
    (h₁ : (double d ComplexShape.upIntRelNegOneZero).X (-1) = C)
    (h₂ : (double ((modulePullback h).map d) ComplexShape.upIntRelNegOneZero).X (-1) =
      (modulePullback h).obj C) :
    (mapDoubleIso h d).hom.f (-1) ≫ eqToHom h₂ = (modulePullback h).map (eqToHom h₁) := by
  have hinv : (mapDoubleIso h d).inv.f (-1) =
      eqToHom h₂ ≫ (modulePullback h).map (eqToHom h₁.symm) := by
    change (doubleMapFunctorHom (modulePullback h) d ComplexShape.upIntRelNegOneZero (by decide)).f
      (-1) = _
    rw [doubleMapFunctorHom, mkHomFromDouble_f₀]
    rfl
  rw [← cancel_epi ((mapDoubleIso h d).inv.f (-1)), ← Category.assoc,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f, Category.id_comp, hinv,
    Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.comp_id]

open HomologicalComplex in
/-- The inverse of `mapDoubleIso` in degree `-1`. -/
theorem mapDoubleIso_inv_f_negOne {X' Y' : RingedSpace.{u, u}} (h : Y' ⟶ X')
    {C B : SheafOfModules.{u} (structureSheafRing X')} (d : C ⟶ B)
    (h₁ : (double d ComplexShape.upIntRelNegOneZero).X (-1) = C)
    (h₂ : (double ((modulePullback h).map d) ComplexShape.upIntRelNegOneZero).X (-1) =
      (modulePullback h).obj C) :
    (mapDoubleIso h d).inv.f (-1) = eqToHom h₂ ≫ (modulePullback h).map (eqToHom h₁.symm) := by
  change (doubleMapFunctorHom (modulePullback h) d ComplexShape.upIntRelNegOneZero (by decide)).f
    (-1) = _
  rw [doubleMapFunctorHom, mkHomFromDouble_f₀]
  rfl

/-- The unit `π^* ⟶ ι_*ι^*π^* ≅ ι_*g^*` is natural. -/
theorem liftProjUnit_naturality {M N : SheafOfModules.{u} (structureSheafRing X)} (a : M ⟶ N) :
    (modulePullback (inverseImageProj g)).map a ≫
        (modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
          ((modulePullback (inverseImageProj g)).obj N) ≫
        (modulePushforward (inverseImageLift g)).map ((pullbackLiftProjIso g).hom.app N) =
      (modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
          ((modulePullback (inverseImageProj g)).obj M) ≫
        (modulePushforward (inverseImageLift g)).map ((pullbackLiftProjIso g).hom.app M) ≫
        (modulePushforward (inverseImageLift g)).map ((modulePullback g).map a) := by
  have h₁ := (modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.naturality
    ((modulePullback (inverseImageProj g)).map a)
  have h₂ := (pullbackLiftProjIso g).hom.naturality a
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h₁).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (_ ≫ ·) ?_
  refine ((CategoryTheory.Functor.map_comp (modulePushforward (inverseImageLift g)) _ _).symm.trans
    ?_).trans (CategoryTheory.Functor.map_comp (modulePushforward (inverseImageLift g)) _ _)
  exact congrArg (modulePushforward (inverseImageLift g)).map h₂

variable {f g} {G : SheafOfModules.{u} (structureSheafRing Y)}
  {F : SheafOfModules.{u} (structureSheafRing X)}
  (P : SquareZeroAlgebraExtension f F) (c : F ⟶ (modulePushforward g).obj G)

/-- The chain map `double(π^*d) ⟶ ι_*(double(g^*d))` comparing the two pulled presentations. -/
abbrev xiComparison :=
  (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).inv ≫
    liftProjUnit g (LiftGluing.KX P) ≫
    ((modulePushforward (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (mapDoubleIso g (LiftGluing.dX P)).hom

/-- `xiComparison` in degree `-1`. -/
theorem xiComparison_f_negOne
    (h₁ : (HomologicalComplex.double ((modulePullback g).map (LiftGluing.dX P))
      ComplexShape.upIntRelNegOneZero).X (-1) = (modulePullback g).obj (LiftGluing.cX P))
    (h₂ : (HomologicalComplex.double ((modulePullback (inverseImageProj g)).map (LiftGluing.dX P))
      ComplexShape.upIntRelNegOneZero).X (-1) =
        (modulePullback (inverseImageProj g)).obj (LiftGluing.cX P)) :
    (xiComparison P).f (-1) ≫ (modulePushforward (inverseImageLift g)).map
        (eqToHom h₁ ≫ (modulePullback g).map (LiftGluing.δX P) ≫ LiftGluing.cAdj g c) =
      eqToHom h₂ ≫ (modulePullback (inverseImageProj g)).map (LiftGluing.δX P) ≫
        inverseImageIdealMap c := by
  have e₁ : (LiftGluing.KX P).X (-1) = LiftGluing.cX P := by
    simp [LiftGluing.KX, HomologicalComplex.double]
  have hg := mapDoubleIso_hom_f_negOne g (LiftGluing.dX P) e₁ h₁
  have hπ := mapDoubleIso_inv_f_negOne (inverseImageProj g) (LiftGluing.dX P) e₁ h₂
  have hn := liftProjUnit_naturality g (eqToHom e₁ ≫ LiftGluing.δX P)
  have hA := unit_lift_comp_cAdj g c
  change ((mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).inv.f (-1) ≫
      ((modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
          ((modulePullback (inverseImageProj g)).obj ((LiftGluing.KX P).X (-1))) ≫
        (modulePushforward (inverseImageLift g)).map
          ((pullbackLiftProjIso g).hom.app ((LiftGluing.KX P).X (-1)))) ≫
      (modulePushforward (inverseImageLift g)).map
        ((mapDoubleIso g (LiftGluing.dX P)).hom.f (-1))) ≫
      _ = _
  have hn' := hn.trans (Category.assoc _ _ _).symm
  refine assemble_xi ((mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).inv.f (-1))
    ((modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
          ((modulePullback (inverseImageProj g)).obj ((LiftGluing.KX P).X (-1))) ≫
        (modulePushforward (inverseImageLift g)).map
          ((pullbackLiftProjIso g).hom.app ((LiftGluing.KX P).X (-1))))
    ((modulePushforward (inverseImageLift g)).map ((mapDoubleIso g (LiftGluing.dX P)).hom.f (-1)))
    ((modulePushforward (inverseImageLift g)).map
      (eqToHom h₁ ≫ (modulePullback g).map (LiftGluing.δX P) ≫ LiftGluing.cAdj g c))
    (eqToHom h₂) ((modulePullback (inverseImageProj g)).map (LiftGluing.δX P))
    (inverseImageIdealMap c) ((modulePullback (inverseImageProj g)).map (eqToHom e₁.symm))
    ((modulePushforward (inverseImageLift g)).map
      ((modulePullback g).map (eqToHom e₁ ≫ LiftGluing.δX P)))
    ((modulePushforward (inverseImageLift g)).map (LiftGluing.cAdj g c))
    ((modulePullback (inverseImageProj g)).map (eqToHom e₁ ≫ LiftGluing.δX P))
    ((modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
          ((modulePullback (inverseImageProj g)).obj F) ≫
        (modulePushforward (inverseImageLift g)).map ((pullbackLiftProjIso g).hom.app F))
    hπ ?_ hn' ?_ ?_
  · refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
    refine Eq.trans ?_ (CategoryTheory.Functor.map_comp _ _ _)
    refine congrArg (modulePushforward (inverseImageLift g)).map ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) hg).trans ?_
    refine Eq.trans ?_
      (congrArg (· ≫ LiftGluing.cAdj g c) (CategoryTheory.Functor.map_comp _ _ _)).symm
    exact (Category.assoc _ _ _).symm
  · refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
    exact congrArg (modulePullback (inverseImageProj g)).map
      ((Category.assoc _ _ _).symm.trans (by rw [eqToHom_trans, eqToHom_refl, Category.id_comp]))
  · exact (Category.assoc _ _ _).trans ((congrArg
      ((modulePullbackPushforwardAdjunction (inverseImageLift g)).unit.app
        ((modulePullback (inverseImageProj g)).obj F) ≫ ·)
      (CategoryTheory.Functor.map_comp (modulePushforward (inverseImageLift g))
        ((pullbackLiftProjIso g).hom.app F) (LiftGluing.cAdj g c)).symm).trans hA)

/-- The transposition of the image of `ξ` in `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)` is the image of
`ξ` along `π^*` and `c`, read on `g⁻¹𝖭𝖫_{X/S}`. -/
theorem key_xi :
    liftProjTransport g (PresentedSquareZeroExtension.relativeComplex f)
        (pullbackExtClass g f (LiftGluing.cAdj g c) P.extClass) ≫ liftShiftSingleIso.hom =
      inverseImagePushoutExtMap c P.extClass := by
  have hX : IsIso (DerivedCategory.Q.map (LiftGluing.compX P)) :=
    PresentedSquareZeroExtension.isIso_Q_map_comparison f P.generators P.generatorsMap
  have hπ := (modulePullback (inverseImageProj g)).isIso_Q_map_mapHomologicalComplex_map
    (LiftGluing.compX P)
  have hid₁ : IsIso (DerivedCategory.Q.map (𝟙 (HomologicalComplex.double
      ((modulePullback g).map (LiftGluing.dX P)) ComplexShape.upIntRelNegOneZero))) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  have hid₂ : IsIso (DerivedCategory.Q.map (𝟙 (HomologicalComplex.double
      ((modulePullback (inverseImageProj g)).map (LiftGluing.dX P))
        ComplexShape.upIntRelNegOneZero))) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  have hid₀ : IsIso (DerivedCategory.Q.map (𝟙 (LiftGluing.KX P))) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  have hfwd := Functor.Q_map_comp_mapExtOne_conormalExtClass
    (modulePushforward (inverseImageLift g)) ((modulePullback g).map (LiftGluing.dX P))
    ((modulePullback (inverseImageProj g)).map (LiftGluing.dX P)) (𝟙 _) (𝟙 _) hid₁ hid₂
    (xiComparison P) (xiComparison P) (by simp)
    ((modulePullback g).map (LiftGluing.δX P) ≫ LiftGluing.cAdj g c)
    ((modulePullback (inverseImageProj g)).map (LiftGluing.δX P) ≫ inverseImageIdealMap c)
    (by simp [HomologicalComplex.double]) (by simp [HomologicalComplex.double])
    (xiComparison_f_negOne P c _ _)
  have hrev := Functor.Q_map_comp_conormalExtClass_eq_mapExtOne_comp
    (modulePullback (inverseImageProj g)) (LiftGluing.dX P)
    ((modulePullback (inverseImageProj g)).map (LiftGluing.dX P)) (𝟙 _) (𝟙 _) hid₀ hid₂
    (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).hom
    (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).hom (by simp) (inverseImageIdealMap c)
    (LiftGluing.δX P)
    ((modulePullback (inverseImageProj g)).map (LiftGluing.δX P) ≫ inverseImageIdealMap c)
    (by simp [HomologicalComplex.double]) (by simp [HomologicalComplex.double])
    (((congrArg (· ≫ inverseImageIdealMap c) (CategoryTheory.Functor.map_comp _ _ _)).trans
      (Category.assoc _ _ _)).trans ((congrArg (· ≫ (modulePullback (inverseImageProj g)).map
        (LiftGluing.δX P) ≫ inverseImageIdealMap c)
          (mapDoubleIso_hom_f_negOne (inverseImageProj g) (LiftGluing.dX P) _ _).symm).trans
        (Category.assoc _ _ _)))
  simp only [CategoryTheory.Functor.map_id, IsIso.inv_id] at hfwd hrev
  -- the comparison
  let φ := (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).inv ≫
    ((modulePullback (inverseImageProj g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (LiftGluing.compX P)
  have hφ : IsIso (DerivedCategory.Q.map φ) := by
    rw [CategoryTheory.Functor.map_comp]; infer_instance
  refine (cancel_epi (DerivedCategory.Q.map φ)).1 ?_
  have e1 : DerivedCategory.Q.map φ =
      DerivedCategory.Q.map (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).inv ≫
        DerivedCategory.Q.map (((modulePullback (inverseImageProj g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (LiftGluing.compX P)) := CategoryTheory.Functor.map_comp _ _ _
  have e2 := (modulePullback (inverseImageProj g)).mapExtOne_Q_map_comp (LiftGluing.compX P)
    P.extClass
  have e3 := LiftGluing.Q_map_compX_comp_extClass P
  have hR : DerivedCategory.Q.map φ ≫ inverseImagePushoutExtMap c P.extClass =
      (NaiveCotangentTwoTerm.ofDoubleNegOne
            ((modulePullback (inverseImageProj g)).map (LiftGluing.dX P))).conormalExtClass
        (restrictedModule g G)
        ((modulePullback (inverseImageProj g)).map (LiftGluing.δX P) ≫ inverseImageIdealMap c) := by
    have h₁ := e2.symm.trans (congrArg (modulePullback (inverseImageProj g)).mapExtOne e3)
    have h₃ : DerivedCategory.Q.map (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).inv ≫
        DerivedCategory.Q.map (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).hom = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    have hrev' := (congrArg (DerivedCategory.Q.map
        (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).hom ≫ ·)
          (Category.id_comp _)).symm.trans
      (hrev.trans (congrArg (fun t => (modulePullback (inverseImageProj g)).mapExtOne t ≫
        ((DerivedCategory.singleFunctor _ 0).map (inverseImageIdealMap c))⟦(1 : ℤ)⟧')
          (Category.id_comp _)))
    exact (congrArg (· ≫ _) e1).trans (assemble_R _ _ _ _ _ _ _ h₁ hrev' h₃)
  refine Eq.trans ?_ hR.symm
  have hfwd' := hfwd.trans (Category.id_comp _)
  have hfwd'' : (DerivedCategory.Q.map (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).inv ≫
      DerivedCategory.Q.map (liftProjUnit g (LiftGluing.KX P)) ≫
      DerivedCategory.Q.map (((modulePushforward (inverseImageLift g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (mapDoubleIso g (LiftGluing.dX P)).hom)) ≫ _ = _ :=
    (congrArg (· ≫ _) ((CategoryTheory.Functor.map_comp DerivedCategory.Q
      (mapDoubleIso (inverseImageProj g) (LiftGluing.dX P)).inv
      (liftProjUnit g (LiftGluing.KX P) ≫
        ((modulePushforward (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (mapDoubleIso g (LiftGluing.dX P)).hom)).trans
      (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_comp DerivedCategory.Q
        (liftProjUnit g (LiftGluing.KX P))
        (((modulePushforward (inverseImageLift g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (mapDoubleIso g (LiftGluing.dX P)).hom))))).symm.trans
      ((congrArg (_ ≫ ·) (congrArg (modulePushforward (inverseImageLift g)).mapExtOne
        (Category.id_comp _))).symm.trans hfwd')
  have L2 := (liftProjTransport_naturality g (LiftGluing.compX P)
    (pullbackExtClass g f (LiftGluing.cAdj g c) P.extClass)).symm
  have L34 := (congrArg (liftProjTransport g (LiftGluing.KX P))
    (LiftGluing.map_Q_compX_comp_pullbackExtClass g P c)).trans
    (liftProjTransport_comparison g (LiftGluing.KX P) _)
  have hfX := mapDerivedCategoryFactors_inv_comp_map_Q_map g (mapDoubleIso g (LiftGluing.dX P)).hom
  have L5 := (congrArg
      ((modulePushforward (inverseImageLift g)).mapDerivedCategoryFactors.inv.app _ ≫ ·)
    (CategoryTheory.Functor.map_comp (modulePushforward (inverseImageLift g)).mapDerivedCategory
      (DerivedCategory.Q.map (mapDoubleIso g (LiftGluing.dX P)).hom)
      ((NaiveCotangentTwoTerm.ofDoubleNegOne ((modulePullback g).map
            (LiftGluing.dX P))).conormalExtClass G
            ((modulePullback g).map (LiftGluing.δX P) ≫ LiftGluing.cAdj g c)))).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hfX).trans (Category.assoc _ _ _)))
  exact (congrArg (· ≫ _) e1).trans (assemble_L _ _ _ _ _ _ _ _ _ _ _ _ L2 L34 L5 hfwd'')

end Xi

section Final

variable {f g} {G : SheafOfModules.{u} (structureSheafRing Y)}
  {F : SheafOfModules.{u} (structureSheafRing X)}

/-- **The image of `ξ` through `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)` is its image in
`Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`.** -/
@[stacks 0GQ2]
theorem inverseImageExtEquiv_pullbackExtClass (P : SquareZeroAlgebraExtension f F)
    (c : F ⟶ (modulePushforward g).obj G) :
    inverseImageExtEquiv f g G (pullbackExtClass g f (LiftGluing.cAdj g c) P.extClass) =
      inverseImageXiMap c P.extClass :=
  (inverseImageExtEquiv_apply (G := G)
    (pullbackExtClass g f (LiftGluing.cAdj g c) P.extClass)).trans
    (congrArg ((DerivedCategory.Q.mapIso (inverseImageNaiveCotangentIso f g)).inv ≫ ·) (key_xi P c))

/-- **Stacks 0GQ2, the classification.** By the diagram chase and the bijection of Stacks 0GPZ for
the ringed space `(Y, g⁻¹𝒪_X)` over `S`, an `S`-morphism `Y' ⟶ X'` compatible with `g` and `c`
exists if and only if the extensions `𝒪'₁` and `𝒪'₂` have the same class in
`Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢)`. -/
@[stacks 0GQ2]
theorem nonempty_compatibleMorphism_iff_isomorphismClassesEquivExt_eq
    (P : SquareZeroAlgebraExtension f F) (Q : SquareZeroAlgebraExtension (g ≫ f) G)
    (c : F ⟶ (modulePushforward g).obj G) :
    Nonempty (CompatibleMorphism P Q c) ↔
      SquareZeroAlgebraExtension.isomorphismClassesEquivExt (inverseImageSpaceHom f g)
          (restrictedModule g G) (Quotient.mk _ (inverseImagePushout G P c)) =
        SquareZeroAlgebraExtension.isomorphismClassesEquivExt (inverseImageSpaceHom f g)
          (restrictedModule g G) (Quotient.mk _ (inverseImagePullback Q)) :=
  (nonempty_compatibleMorphism_iff_nonempty_iso P c Q).trans
    ((Quotient.eq (r := isIsomorphicSetoid _)).symm.trans (Equiv.apply_eq_iff_eq _).symm)

/-- **Stacks 0GQ2, the final deduction.** An `S`-morphism `Y' ⟶ X'` compatible with `g` and `c`
exists if and only if `ξ` and `ζ` have the same image in `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)`: through the
identification `Ext¹_{g⁻¹𝒪_X}(𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}, 𝒢) = Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)`
(`inverseImageExtEquiv`), the class of `𝒪'₁` is the image of `ξ` and the class of `𝒪'₂` is the
image of `ζ`, so this is `nonempty_compatibleMorphism_iff_isomorphismClassesEquivExt_eq`. -/
@[stacks 0GQ2]
theorem nonempty_compatibleMorphism_iff_images_eq
    (P : SquareZeroAlgebraExtension f F) (Q : SquareZeroAlgebraExtension (g ≫ f) G)
    (c : F ⟶ (modulePushforward g).obj G) :
    Nonempty (CompatibleMorphism P Q c) ↔
      pullbackExtClass g f (LiftGluing.cAdj g c)
          (SquareZeroAlgebraExtension.isomorphismClassesEquivExt f F (Quotient.mk _ P)) =
        restrictDerivedExtClass (derivedPullbackNaiveCotangentMap g f)
          (SquareZeroAlgebraExtension.isomorphismClassesEquivExt (g ≫ f) G (Quotient.mk _ Q)) := by
  refine (nonempty_compatibleMorphism_iff_isomorphismClassesEquivExt_eq P Q c).trans ?_
  refine Iff.trans ?_ (Equiv.apply_eq_iff_eq (inverseImageExtEquiv f g G))
  refine Eq.congr ?_ ?_
  · exact (isomorphismClassesEquivExt_inverseImagePushout P c).trans
      (inverseImageExtEquiv_pullbackExtClass P c).symm
  · exact (isomorphismClassesEquivExt_inverseImagePullback Q).trans
      (inverseImageExtEquiv_restrictDerivedExtClass Q.extClass).symm

end Final

end AlgebraicGeometry.RingedSpaceThickening

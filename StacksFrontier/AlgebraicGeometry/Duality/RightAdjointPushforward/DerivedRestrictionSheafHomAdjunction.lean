module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# The derived adjunction between restriction of scalars and internal Hom

For a morphism of schemes `f : Y ⟶ X`, an adjunction between restriction of scalars from
`f₊ 𝒪_Y`-modules to `𝒪_X`-modules and an additive internal-Hom functor induces, on derived
categories, an adjunction between a left derived functor of restriction of scalars and a right
derived functor of the internal Hom.

## Main definitions

* `AlgebraicGeometry.derivedRestrictionSheafHomAdjunction`: the adjunction between the derived
  restriction of scalars and the derived internal-Hom functor.

## Main results

* `AlgebraicGeometry.derivedRestrictionSheafHom_comp_isDerivedFunctor`: the composites of the
  derived functors are derived functors of the underived composites.
* `AlgebraicGeometry.derivedRestrictionSheafHomAdjunction_counit_fac`: the derived counit,
  preceded by the comparison maps, is the class of the underived counit applied termwise.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Functor
open Stacks.DerivedFunctor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- The composites of the derived functors of `derivedRestrictionSheafHomAdjunction` are derived
functors of the underived composites. -/
public theorem derivedRestrictionSheafHom_comp_isDerivedFunctor
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (sheafHom : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (pushforwardRingCatSheaf f)) [sheafHom.Additive]
    (underivedAdjunction :
      SheafOfModules.restrictScalars f.toRingCatSheafHom ⊣ sheafHom)
    (derivedSheafHom : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)))
    (derivedSheafHomComparison :
      sheafHom.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ derivedSheafHom)
    [derivedSheafHom.IsRightDerivedFunctor derivedSheafHomComparison
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ))]
    (derivedRestriction :
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) ⥤
        DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (derivedRestrictionComparison :
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      DerivedCategory.Qh ⋙ derivedRestriction ⟶
        (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [derivedRestriction.IsLeftDerivedFunctor derivedRestrictionComparison
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (pushforwardRingCatSheaf f)) (ComplexShape.up ℤ))] :
    (derivedRestriction ⋙ derivedSheafHom).IsLeftDerivedFunctor
        ((Functor.associator DerivedCategory.Qh derivedRestriction derivedSheafHom).inv ≫
          whiskerRight derivedRestrictionComparison derivedSheafHom)
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
      (derivedSheafHom ⋙ derivedRestriction).IsRightDerivedFunctor
        (whiskerRight derivedSheafHomComparison derivedRestriction ≫
          (Functor.associator DerivedCategory.Qh derivedSheafHom derivedRestriction).hom)
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  let : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
    SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
  let G := SheafOfModules.restrictScalars f.toRingCatSheafHom
  let : G.IsLeftAdjoint := underivedAdjunction.isLeftAdjoint
  let : Limits.PreservesFiniteLimits G :=
    restrictionPreservesFiniteLimits f.toRingCatSheafHom
  let : Limits.PreservesFiniteColimits G := inferInstance
  let : G.PreservesHomology := inferInstance
  have hG : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).IsInvertedBy
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso _
      (G.mapDerivedCategoryFactorsh).symm]
    exact MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh
      (Localization.inverts _ _) _
  have : IsIso derivedRestrictionComparison :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _ hG
  have : (derivedRestriction ⋙ derivedSheafHom).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh derivedRestriction derivedSheafHom).inv ≫
        whiskerRight derivedRestrictionComparison derivedSheafHom)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
    apply (Functor.isLeftDerivedFunctor_iff_of_inverts _ _
      (MorphismProperty.IsInvertedBy.of_comp _ _ hG _)).2
    infer_instance
  have hK : ∀ K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
        (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q := by
    intro K
    let R := Stacks.Injectives.functorialKInjectiveResolution
      (SheafOfModules.{u} X.ringCatSheaf)
    exact ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩
  let F := sheafHom.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have : F.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    (F.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} hK).1
  have hterminal : ∀ Y : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf),
      Nonempty (Σ t : CostructuredArrow DerivedCategory.Qh Y, Limits.IsTerminal t) := by
    intro Y
    let K := (DerivedCategory.Qh.objPreimage Y).as
    obtain ⟨I, q, hI, hq⟩ := hK K
    have : I.IsKInjective := hI
    have hq' : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient _ _).map q) := by
      rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map q)) :=
      Localization.inverts _ _ _ hq'
    let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ Y :=
      (asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map q))).symm ≪≫
        DerivedCategory.Qh.objObjPreimageIso Y
    exact ⟨⟨CostructuredArrow.mk e.hom,
      terminalCostructuredArrowOfBijective DerivedCategory.Qh Y _ e
        (fun Z => CochainComplex.IsKInjective.Qh_map_bijective Z I)⟩⟩
  have : derivedRestriction.PreservesPointwiseLeftKanExtension
      F DerivedCategory.Qh := fun Y => by
    obtain ⟨t, ht⟩ := (hterminal Y).some
    let : Limits.PreservesColimit
        (CostructuredArrow.proj DerivedCategory.Qh Y ⋙ F) derivedRestriction :=
      preservesColimitOfTerminal ht _ _
    infer_instance
  let : HasPointwiseLeftKanExtension DerivedCategory.Qh F :=
    F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let : derivedRestriction.PreservesLeftKanExtension F DerivedCategory.Qh := inferInstance
  let : derivedSheafHom.IsLeftKanExtension derivedSheafHomComparison :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  exact ⟨inferInstance,
    ⟨Functor.PreservesLeftKanExtension.preserves derivedSheafHom derivedSheafHomComparison⟩⟩

/-- For a morphism `f : Y ⟶ X`, given an internal-Hom functor right adjoint to restriction of
scalars from `f₊ 𝒪_Y`-modules to `𝒪_X`-modules, a right derived functor of it and a left derived
functor of restriction of scalars, the derived restriction of scalars `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)` is left
adjoint to the derived internal-Hom functor `D(𝒪_X) ⥤ D(f₊ 𝒪_Y)`. -/
@[no_expose]
public noncomputable def derivedRestrictionSheafHomAdjunction
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (sheafHom : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (pushforwardRingCatSheaf f)) [sheafHom.Additive]
    (underivedAdjunction :
      SheafOfModules.restrictScalars f.toRingCatSheafHom ⊣ sheafHom)
    (derivedSheafHom : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)))
    (derivedSheafHomComparison :
      sheafHom.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ derivedSheafHom)
    [derivedSheafHom.IsRightDerivedFunctor derivedSheafHomComparison
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ))]
    (derivedRestriction :
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) ⥤
        DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (derivedRestrictionComparison :
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      DerivedCategory.Qh ⋙ derivedRestriction ⟶
        (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [derivedRestriction.IsLeftDerivedFunctor derivedRestrictionComparison
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (pushforwardRingCatSheaf f)) (ComplexShape.up ℤ))] :
    derivedRestriction ⊣ derivedSheafHom :=
  letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
    SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
  have h := derivedRestrictionSheafHom_comp_isDerivedFunctor f sheafHom underivedAdjunction
    derivedSheafHom derivedSheafHomComparison derivedRestriction derivedRestrictionComparison
  letI := h.1
  letI := h.2
  (underivedAdjunction.mapHomotopyCategory (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    derivedRestrictionComparison derivedSheafHomComparison

/-- **The derived counit is evaluation at `1`, termwise.** On a complex `M` of `𝒪_X`-modules, the
counit of `derivedRestrictionSheafHomAdjunction`, preceded by the comparison maps, is the class of
the counit of the underived adjunction applied termwise. -/
public theorem derivedRestrictionSheafHomAdjunction_counit_fac
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (sheafHom : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (pushforwardRingCatSheaf f)) [sheafHom.Additive]
    (underivedAdjunction :
      SheafOfModules.restrictScalars f.toRingCatSheafHom ⊣ sheafHom)
    (derivedSheafHom : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)))
    (derivedSheafHomComparison :
      sheafHom.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ derivedSheafHom)
    [derivedSheafHom.IsRightDerivedFunctor derivedSheafHomComparison
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ))]
    (derivedRestriction :
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) ⥤
        DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (derivedRestrictionComparison :
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      DerivedCategory.Qh ⋙ derivedRestriction ⟶
        (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [derivedRestriction.IsLeftDerivedFunctor derivedRestrictionComparison
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (pushforwardRingCatSheaf f)) (ComplexShape.up ℤ))]
    (M : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    derivedRestriction.map
        (derivedSheafHomComparison.app ((HomotopyCategory.quotient _ _).obj M)) ≫
      (derivedRestrictionSheafHomAdjunction f sheafHom underivedAdjunction derivedSheafHom
        derivedSheafHomComparison derivedRestriction derivedRestrictionComparison).counit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M)) =
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      derivedRestrictionComparison.app ((sheafHom.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj M)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((underivedAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app M)) := by
  let : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
    SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
  have h := derivedRestrictionSheafHom_comp_isDerivedFunctor f sheafHom underivedAdjunction
    derivedSheafHom derivedSheafHomComparison derivedRestriction derivedRestrictionComparison
  have := h.1
  have := h.2
  unfold derivedRestrictionSheafHomAdjunction
  exact (underivedAdjunction.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) derivedRestrictionComparison
    derivedSheafHomComparison ((HomotopyCategory.quotient _ _).obj M)

end AlgebraicGeometry

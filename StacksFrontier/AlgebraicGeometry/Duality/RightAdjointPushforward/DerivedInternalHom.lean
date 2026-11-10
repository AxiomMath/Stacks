module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.AffineSections
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.DerivedAdjunction

/-!
# The derived internal Hom as a composite

For a morphism of schemes `f : Y ⟶ X`, the derived sheaf-Hom with values in modules over
`f₊ 𝒪_Y` can be followed by restriction of scalars to `𝒪_X`. This file identifies that
composite, canonically, with the derived internal-Hom functor `Rℰom_{𝒪_X}(f₊ 𝒪_Y, -)`.

## Main definitions

* `AlgebraicGeometry.compositeDerivedSheafHomComparison` is the comparison map from the
  underived internal-Hom to the composite of the two derived functors.

## Main results

* `AlgebraicGeometry.derivedSheafHom_comp_derivedRestriction_iso_derivedInternalHom` identifies
  the composite with the derived internal-Hom, canonically with respect to their comparison
  maps.

## Implementation notes

The functors are specified by their derived-functor universal properties. The comparison for
the composite uses the inverse of the comparison for restriction of scalars; this map is an
isomorphism because restriction of scalars is exact. The conclusion includes the uniqueness
which makes the displayed isomorphism canonical.

**None of that data is hypothetical.** The underived internal Hom is
`RingedSpaceModuleAdjunction.homSheaf` (Tag 0BUZ), each derived extension of it exists by the
K-injective resolutions of Tag 079P, and the derived extension of restriction of scalars is
`CategoryTheory.Functor.mapDerivedCategory`, restriction of scalars being exact. Tag 0BV1 with
nothing assumed beyond the morphism `f` is therefore
`AlgebraicGeometry.derivedHomSheaf_comp_derivedRestriction_iso`, in the module
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ConstructedDerivedAdjunction`,
which carries the tag with no caveat. The theorem below is the reduction it is obtained from, and
it is kept in the general form because the conclusion then depends on no choice of model for any
of the three derived functors.

## References

* [Stacks Project, Tag 0BV1](https://stacks.math.columbia.edu/tag/0BV1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- The comparison map exhibiting the composite of derived sheaf-Hom and derived
restriction of scalars as a derived functor of the underlying internal-Hom. -/
public noncomputable def compositeDerivedSheafHomComparison
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (sheafHom : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (pushforwardRingCatSheaf f)) [sheafHom.Additive]
    (derivedSheafHom : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)))
    (derivedSheafHomComparison :
      sheafHom.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ derivedSheafHom)
    (derivedRestriction :
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) ⥤
        DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (derivedRestrictionComparison :
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      DerivedCategory.Qh ⋙ derivedRestriction ⟶
        (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [IsIso derivedRestrictionComparison] :
    letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
      SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
    (sheafHom ⋙ SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedSheafHom ⋙ derivedRestriction) :=
  letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
    SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
  whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (sheafHom.mapHomotopyCategory (ComplexShape.up ℤ))
      (inv derivedRestrictionComparison) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight derivedSheafHomComparison derivedRestriction ≫
    (Functor.associator _ _ _).hom

/-- Derived restriction of scalars is a left derived functor of restriction of scalars. -/
public theorem isLeftDerivedFunctor_derivedRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    (derivedRestriction :
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) ⥤
        DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (derivedRestrictionComparison :
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      DerivedCategory.Qh ⋙ derivedRestriction ⟶
        (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [IsIso derivedRestrictionComparison] :
    derivedRestriction.IsLeftDerivedFunctor derivedRestrictionComparison
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (pushforwardRingCatSheaf f)) (ComplexShape.up ℤ)) := by
  let R := SheafOfModules.restrictScalars f.toRingCatSheafHom
  let : R.IsLeftAdjoint :=
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction f.toRingCatSheafHom).isLeftAdjoint
  let : R.Additive := SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
  let : Limits.PreservesFiniteLimits R := by
    have h : Limits.PreservesFiniteLimits (R ⋙ SheafOfModules.toSheaf X.ringCatSheaf) := by
      change Limits.PreservesFiniteLimits (SheafOfModules.toSheaf
        (pushforwardRingCatSheaf f))
      infer_instance
    exact Limits.preservesFiniteLimits_of_reflects_of_preserves R
      (SheafOfModules.toSheaf X.ringCatSheaf)
  let : Limits.PreservesFiniteColimits R := inferInstance
  let : R.PreservesHomology := inferInstance
  have hR : (HomotopyCategory.quasiIso (SheafOfModules.{u} (pushforwardRingCatSheaf f))
      (ComplexShape.up ℤ)).IsInvertedBy
        (R.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso _ R.mapDerivedCategoryFactorsh.symm]
    exact MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh
      (Localization.inverts _ _) _
  apply (Functor.isLeftDerivedFunctor_iff_of_inverts
    derivedRestriction derivedRestrictionComparison hR).2
  infer_instance

/-- Derived restriction of scalars along `f` is a left adjoint. -/
public theorem isLeftAdjoint_derivedRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    (derivedRestriction :
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) ⥤
        DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (derivedRestrictionComparison :
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      DerivedCategory.Qh ⋙ derivedRestriction ⟶
        (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [IsIso derivedRestrictionComparison] :
    derivedRestriction.IsLeftAdjoint := by
  let RAdj := RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction f.toRingCatSheafHom
  let stdHom := RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom
  let : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
    SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
  let : stdHom.Additive := RAdj.right_adjoint_additive
  have := isLeftDerivedFunctor_derivedRestriction f derivedRestriction
    derivedRestrictionComparison
  let W₀ := HomotopyCategory.quasiIso
    (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)
  let stdHomComplex := stdHom.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have hK : ∀ K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
        (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q := by
    intro K
    let T := Stacks.Injectives.functorialKInjectiveResolution
      (SheafOfModules.{u} X.ringCatSheaf)
    exact ⟨T.functor.obj K, T.inclusion.app K, T.isKInjective K, T.quasiIso K⟩
  let : stdHomComplex.HasPointwiseRightDerivedFunctor W₀ :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} stdHomComplex hK).1
  exact (derivedRestriction_adj_derivedSheafHom f stdHom RAdj
    (stdHomComplex.totalRightDerived DerivedCategory.Qh W₀)
    (stdHomComplex.totalRightDerivedUnit DerivedCategory.Qh W₀) derivedRestriction
    derivedRestrictionComparison).some.isLeftAdjoint

/-- The composite of derived sheaf-Hom and derived restriction of scalars is a right derived
functor of the underlying internal-Hom, via `compositeDerivedSheafHomComparison`. -/
public theorem isRightDerivedFunctor_compositeDerivedSheafHomComparison
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (sheafHom : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (pushforwardRingCatSheaf f)) [sheafHom.Additive]
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
    [IsIso derivedRestrictionComparison] :
    (derivedSheafHom ⋙ derivedRestriction).IsRightDerivedFunctor
      (compositeDerivedSheafHomComparison f sheafHom derivedSheafHom
        derivedSheafHomComparison derivedRestriction derivedRestrictionComparison)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) := by
  let : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
    SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
  have := isLeftAdjoint_derivedRestriction f derivedRestriction derivedRestrictionComparison
  let α :=
    whiskerRight derivedSheafHomComparison derivedRestriction ≫
      (Functor.associator _ derivedSheafHom derivedRestriction).hom
  let eSource :=
    isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm
        DerivedCategory.Qh ≪≫
      (Functor.associator _ _ _) ≪≫
      isoWhiskerLeft (sheafHom.mapHomotopyCategory (ComplexShape.up ℤ))
        (asIso derivedRestrictionComparison).symm ≪≫
      (Functor.associator _ _ _).symm
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  apply (Functor.isLeftKanExtension_iff_of_iso₂
    (α₁ := compositeDerivedSheafHomComparison f sheafHom derivedSheafHom
      derivedSheafHomComparison derivedRestriction derivedRestrictionComparison)
    (α₂ := α) (e := eSource) (e' := Iso.refl _) ?_).2
  · exact Functor.IsRightDerivedFunctor.isLeftKanExtension _ α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))
  · simp [compositeDerivedSheafHomComparison, eSource, α]

/-- **Stacks 0BV1.** After forgetting the `f₊ 𝒪_Y`-module structure, the
derived sheaf-Hom functor is canonically the derived internal-Hom over `𝒪_X`.
The displayed compatibility with the comparison maps characterizes the
isomorphism uniquely.

This is the general form: the underived internal Hom and the three derived functors are taken as
data. All of that data is constructed, and the unconditional form of the tag is
`AlgebraicGeometry.derivedHomSheaf_comp_derivedRestriction_iso`.

This general form takes its functors as data, so it is not registered under [stacks 0BV1]; it is
superseded by `AlgebraicGeometry.derivedHomSheaf_comp_derivedRestriction_iso`. -/
public theorem derivedSheafHom_comp_derivedRestriction_iso_derivedInternalHom
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (sheafHom : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (pushforwardRingCatSheaf f)) [sheafHom.Additive]
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
    [IsIso derivedRestrictionComparison]
    (derivedInternalHom : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (derivedInternalHomComparison :
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      (sheafHom ⋙ SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ derivedInternalHom)
    [derivedInternalHom.IsRightDerivedFunctor derivedInternalHomComparison
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ))] :
    letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
      SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
    ∃! e : derivedSheafHom ⋙ derivedRestriction ≅ derivedInternalHom,
      compositeDerivedSheafHomComparison f sheafHom derivedSheafHom
          derivedSheafHomComparison derivedRestriction derivedRestrictionComparison ≫
        whiskerLeft DerivedCategory.Qh e.hom = derivedInternalHomComparison := by
  have := isRightDerivedFunctor_compositeDerivedSheafHomComparison f sheafHom derivedSheafHom
    derivedSheafHomComparison derivedRestriction derivedRestrictionComparison
  let W₀ := HomotopyCategory.quasiIso
    (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)
  let α := compositeDerivedSheafHomComparison f sheafHom derivedSheafHom
    derivedSheafHomComparison derivedRestriction derivedRestrictionComparison
  let e := Functor.rightDerivedUnique (derivedSheafHom ⋙ derivedRestriction)
    derivedInternalHom α derivedInternalHomComparison W₀
  have he : α ≫ whiskerLeft DerivedCategory.Qh e.hom = derivedInternalHomComparison := by
    simp [e, Functor.rightDerivedUnique]
  exact ⟨e, he, fun e' he' => Iso.ext <| Functor.rightDerived_ext
    (RF := derivedSheafHom ⋙ derivedRestriction) (α := α) (W := W₀) derivedInternalHom
    e'.hom e.hom (he'.trans he.symm)⟩

end AlgebraicGeometry

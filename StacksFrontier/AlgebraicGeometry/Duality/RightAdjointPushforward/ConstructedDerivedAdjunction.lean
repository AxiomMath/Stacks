module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.DerivedInternalHom

/-!
# The derived internal-Hom adjunction, with no assumed data

Let `f : Y ⟶ X` be a morphism of schemes. The underived internal-Hom functor
`ℰom_{𝒪_X}(f₊ 𝒪_Y, -) : Mod(𝒪_X) ⥤ Mod(f₊ 𝒪_Y)` and its adjunction with restriction of
scalars are the ones constructed for Stacks, Tag 0BUZ, namely
`RingedSpaceModuleAdjunction.homSheaf` and
`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction`. This file derives both sides:
restriction of scalars is exact, so `Functor.mapDerivedCategory` already is its derived
extension, and the internal-Hom functor acquires one from the K-injective resolutions of
Stacks, Tag 079P. With all the functors constructed, Tags 0BV0 and 0BV1 hold with no assumed
data.

## Main definitions

* `AlgebraicGeometry.derivedRestrictionOfScalars` is the functor `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)` induced
  by restriction of scalars.
* `AlgebraicGeometry.derivedHomSheaf` is `R ℰom(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(f₊ 𝒪_Y)`, the total
  right derived functor of `RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom`.
* `AlgebraicGeometry.derivedInternalHomPushforward` is
  `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(𝒪_X)`, the total right derived functor of the same
  internal Hom read as a functor to `𝒪_X`-modules.

## Main results

* `AlgebraicGeometry.derivedRestriction_adj_derivedHomSheaf` (Tag 0BV0): `R ℰom(f₊ 𝒪_Y, -)`
  is right adjoint to the functor `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)` induced by restriction of scalars.
* `AlgebraicGeometry.derivedHomSheaf_comp_derivedRestriction_iso` (Tag 0BV1): following
  `R ℰom(f₊ 𝒪_Y, -)` by that functor gives `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`, canonically.

## Implementation notes

The two results are the instances, at the constructed data, of the corresponding statements with
the data assumed: `AlgebraicGeometry.derivedRestriction_adj_derivedSheafHom` and
`AlgebraicGeometry.derivedSheafHom_comp_derivedRestriction_iso_derivedInternalHom`. Nothing here
is hypothetical: `homSheaf` and its adjunction are built in
`StacksFrontier/Topology/Sheaves/Functors/Module/HomSheaf.lean`, the derived extension of
`homSheaf` exists because every complex of `𝒪_X`-modules has a K-injective resolution
(`Stacks.Injectives.functorialKInjectiveResolution`), and the derived extension of restriction of
scalars is `Functor.mapDerivedCategory`, restriction of scalars being exact.

`R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` is taken in the sense of the source's "derived extension" of the left
exact functor `ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`, which is how the source introduces it, and not as a value
of the derived internal-Hom bifunctor `Stacks.SheafOfModules.derivedSheafHom`; no comparison
between the two is claimed here.

The additivity and exactness of the two underived functors are supplied by name rather than by
instance resolution: the `Preadditive` structure on `SheafOfModules.{u} X.ringCatSheaf` is
reachable along several paths, so the `Additive` instances are not found automatically. For the
same reason the functors below are packaged as definitions with those facts discharged inside,
which keeps the two statements free of local instance bindings.

The derived categories are the ones of `HasDerivedCategory.standard`, as in the two files whose
statements are instantiated.

## References

* [Stacks Project, Tag 0BV0](https://stacks.math.columbia.edu/tag/0BV0)
* [Stacks Project, Tag 0BV1](https://stacks.math.columbia.edu/tag/0BV1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- Every cochain complex of modules on a scheme admits a quasi-isomorphism into a K-injective
complex; this is the functorial K-injective resolution of Stacks, Tag 079P. -/
public theorem exists_isKInjective_quasiIso (Z : Scheme.{u})
    (K : CochainComplex (SheafOfModules.{u} Z.ringCatSheaf) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{u} Z.ringCatSheaf) ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q :=
  let R := Stacks.Injectives.functorialKInjectiveResolution (SheafOfModules.{u} Z.ringCatSheaf)
  ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩

/-- Any functor out of the homotopy category of complexes of modules on a scheme has a pointwise
right derived functor, K-injective resolutions being available. -/
public instance hasPointwiseRightDerivedFunctor_schemeModules {Z : Scheme.{u}}
    {H : Type (u + 1)} [Category.{u + 1} H]
    (F : HomotopyCategory (SheafOfModules.{u} Z.ringCatSheaf) (ComplexShape.up ℤ) ⥤ H) :
    F.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} Z.ringCatSheaf) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
    u + 1, u + 1, u + 1, u + 1, u + 1} F (exists_isKInjective_quasiIso Z)).1

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Restriction of scalars along `f₊` is additive. -/
public theorem restrictScalars_additive :
    (SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom).Additive :=
  SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom

/-- The internal-Hom functor `ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of Stacks, Tag 0BUZ is additive, being
right adjoint to the additive functor of restriction of scalars. -/
public theorem homSheaf_additive :
    (RingedSpaceModuleAdjunction.homSheaf.{u} f.toRingCatSheafHom).Additive :=
  have := restrictScalars_additive f
  (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction
    f.toRingCatSheafHom).right_adjoint_additive

/-- The internal-Hom functor of Stacks, Tag 0BUZ, read as a functor to `𝒪_X`-modules, is
additive. -/
public theorem homSheaf_comp_restrictScalars_additive :
    (RingedSpaceModuleAdjunction.homSheaf.{u} f.toRingCatSheafHom ⋙
      SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom).Additive :=
  have := restrictScalars_additive f
  have := homSheaf_additive f
  inferInstance

/-- Restriction of scalars along `f₊` preserves finite colimits, being a left adjoint by Stacks,
Tag 0BUZ. -/
public theorem restrictScalars_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom) :=
  have : (SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom).IsLeftAdjoint :=
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction
      f.toRingCatSheafHom).isLeftAdjoint
  inferInstance

/-- The functor `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)` induced by restriction of scalars. Restriction of scalars
is exact, so this is already its derived extension. -/
public noncomputable def derivedRestrictionOfScalars :
    DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) ⥤
      DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  letI := restrictScalars_additive f
  letI := restrictionPreservesFiniteLimits f.toRingCatSheafHom
  letI := restrictScalars_preservesFiniteColimits f
  (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategory

/-- The comparison identifying `AlgebraicGeometry.derivedRestrictionOfScalars` as the derived
extension of restriction of scalars. It is an isomorphism, restriction of scalars being exact. -/
public noncomputable def derivedRestrictionOfScalarsFactors :
    letI := restrictScalars_additive f
    DerivedCategory.Qh ⋙ derivedRestrictionOfScalars f ≅
      (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  letI := restrictScalars_additive f
  letI := restrictionPreservesFiniteLimits f.toRingCatSheafHom
  letI := restrictScalars_preservesFiniteColimits f
  (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh

/-- `R ℰom(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(f₊ 𝒪_Y)`, the derived extension of the internal-Hom functor
of Stacks, Tag 0BUZ. -/
public noncomputable def derivedHomSheaf :
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) :=
  letI := homSheaf_additive f
  ((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- The comparison map exhibiting `AlgebraicGeometry.derivedHomSheaf` as the derived extension of
`ℰom(f₊ 𝒪_Y, -)`. -/
public noncomputable def derivedHomSheafUnit :
    letI := homSheaf_additive f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedHomSheaf f :=
  letI := homSheaf_additive f
  ((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- `AlgebraicGeometry.derivedHomSheaf`, with the comparison map
`AlgebraicGeometry.derivedHomSheafUnit`, is the right derived functor of `ℰom(f₊ 𝒪_Y, -)` with
respect to the quasi-isomorphisms. -/
public instance derivedHomSheaf_isRightDerivedFunctor :
    (derivedHomSheaf f).IsRightDerivedFunctor (derivedHomSheafUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) := by
  let := homSheaf_additive f
  exact inferInstanceAs
    ((((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
          (ComplexShape.up ℤ))).IsRightDerivedFunctor
      (((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)))

/-- **Stacks 0BV0.** For a morphism of schemes `f : Y ⟶ X`, the derived internal-Hom functor
`R ℰom(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(f₊ 𝒪_Y)` is right adjoint to the functor `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)`
induced by restriction of scalars. -/
@[stacks 0BV0]
public theorem derivedRestriction_adj_derivedHomSheaf :
    Nonempty (derivedRestrictionOfScalars f ⊣ derivedHomSheaf f) := by
  let := restrictScalars_additive f
  let := homSheaf_additive f
  let := restrictionPreservesFiniteLimits f.toRingCatSheafHom
  let := restrictScalars_preservesFiniteColimits f
  have hR : (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (pushforwardRingCatSheaf f)) (ComplexShape.up ℤ)).IsInvertedBy
      ((SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso _
      (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh.symm]
    exact MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh
      (Localization.inverts _ _) _
  let : (SheafOfModules.restrictScalars
      f.toRingCatSheafHom).mapDerivedCategory.IsLeftDerivedFunctor
      (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (pushforwardRingCatSheaf f)) (ComplexShape.up ℤ)) := by
    apply (Functor.isLeftDerivedFunctor_iff_of_inverts _ _ hR).2
    infer_instance
  exact derivedRestriction_adj_derivedSheafHom f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom)
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction f.toRingCatSheafHom)
    (derivedHomSheaf f) (derivedHomSheafUnit f)
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategory
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh.hom

/-- `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(𝒪_X)`, the derived extension of the internal-Hom
functor of Stacks, Tag 0BUZ read as a functor to `𝒪_X`-modules. -/
public noncomputable def derivedInternalHomPushforward :
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  letI := homSheaf_comp_restrictScalars_additive f
  ((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
          SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- The comparison map exhibiting `AlgebraicGeometry.derivedInternalHomPushforward` as the
derived extension of `ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`. -/
public noncomputable def derivedInternalHomPushforwardUnit :
    letI := homSheaf_comp_restrictScalars_additive f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
          SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedInternalHomPushforward f :=
  letI := homSheaf_comp_restrictScalars_additive f
  ((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
          SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- `AlgebraicGeometry.derivedInternalHomPushforward`, with the comparison map
`AlgebraicGeometry.derivedInternalHomPushforwardUnit`, is the right derived functor of
`ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` with respect to the quasi-isomorphisms. -/
public instance derivedInternalHomPushforward_isRightDerivedFunctor :
    (derivedInternalHomPushforward f).IsRightDerivedFunctor
      (derivedInternalHomPushforwardUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) := by
  let := homSheaf_comp_restrictScalars_additive f
  exact inferInstanceAs
    ((((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
              SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
          (ComplexShape.up ℤ))).IsRightDerivedFunctor
      (((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
              SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)))

/-- The comparison map exhibiting the composite of `AlgebraicGeometry.derivedHomSheaf` and
`AlgebraicGeometry.derivedRestrictionOfScalars` as a derived extension of
`ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`. -/
public noncomputable def compositeDerivedHomSheafUnit :
    letI := homSheaf_comp_restrictScalars_additive f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
          SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedHomSheaf f ⋙ derivedRestrictionOfScalars f) :=
  letI := restrictScalars_additive f
  letI := homSheaf_additive f
  letI := restrictionPreservesFiniteLimits f.toRingCatSheafHom
  letI := restrictScalars_preservesFiniteColimits f
  compositeDerivedSheafHomComparison f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom)
    (derivedHomSheaf f) (derivedHomSheafUnit f)
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategory
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh.hom

/-- **Stacks 0BV1.** Following `R ℰom(f₊ 𝒪_Y, -)` by the functor `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)` induced
by restriction of scalars gives `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`. The displayed compatibility with the
comparison maps characterizes the isomorphism uniquely. -/
@[stacks 0BV1]
public theorem derivedHomSheaf_comp_derivedRestriction_iso :
    ∃! e : derivedHomSheaf f ⋙ derivedRestrictionOfScalars f ≅
        derivedInternalHomPushforward f,
      compositeDerivedHomSheafUnit f ≫ whiskerLeft DerivedCategory.Qh e.hom =
        derivedInternalHomPushforwardUnit f := by
  let := restrictScalars_additive f
  let := homSheaf_additive f
  let := homSheaf_comp_restrictScalars_additive f
  let := restrictionPreservesFiniteLimits f.toRingCatSheafHom
  let := restrictScalars_preservesFiniteColimits f
  exact derivedSheafHom_comp_derivedRestriction_iso_derivedInternalHom f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom)
    (derivedHomSheaf f) (derivedHomSheafUnit f)
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategory
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh.hom
    (derivedInternalHomPushforward f) (derivedInternalHomPushforwardUnit f)

end AlgebraicGeometry

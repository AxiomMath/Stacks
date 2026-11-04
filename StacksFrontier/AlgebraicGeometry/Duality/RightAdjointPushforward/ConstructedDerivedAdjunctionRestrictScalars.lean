module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ConstructedDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.DerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.DerivedRestrictionSheafHomAdjunction

/-!
# The derived adjunction between restriction of scalars and `R ℰom(f₊ 𝒪_Y, -)`

For a morphism of schemes `f : Y ⟶ X`, the functor `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)` induced by restriction
of scalars is left adjoint to `R ℰom(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(f₊ 𝒪_Y)`, and the counit of this
adjunction is induced by evaluation at `1`.

## Main definitions

* `AlgebraicGeometry.derivedRestrictScalarsHomAdjunction`: The adjunction
  `derivedRestrictionOfScalars f ⊣ derivedHomSheaf f`.

## Main results

* `RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction_counit_app_val_app_apply`: The counit
  of `restrictScalarsHomAdjunction` sends a section `ψ` to `ψ(1)`.
* `AlgebraicGeometry.restrictScalars_mapDerivedCategory_isLeftDerivedFunctor`: Restriction of
  scalars on derived categories is the left derived functor of restriction of scalars.
* `AlgebraicGeometry.derivedRestrictScalarsHomAdjunction_counit_fac`: The counit of
  `derivedRestrictScalarsHomAdjunction` on a complex is the class of the termwise counit.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction

/-- **The counit of `restrictScalarsHomAdjunction` is evaluation at `1`.** On sections over `U`,
it sends `ψ : 𝒪₂|_U ⟶ F|_U` to `ψ(1) ∈ F(U)`. -/
public theorem restrictScalarsHomAdjunction_counit_app_val_app_apply
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : CategoryTheory.Sheaf J RingCat.{u}}
    (α : 𝒪₁ ⟶ 𝒪₂) (F : SheafOfModules.{u} 𝒪₁) (U : Cᵒᵖ)
    (ψ : Stacks.PresheafOfModules.CoextendScalars.coextSec α.hom F.val U) :
    ((restrictScalarsHomAdjunction α).counit.app F).val.app U ψ =
      ψ.app (Opposite.op (Over.mk (𝟙 U.unop))) (1 : (𝒪₂.obj.obj (Opposite.op U.unop) : Type _)) :=
  rfl

end RingedSpaceModuleAdjunction

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The functor induced by restriction of scalars on derived categories is the left derived
functor of restriction of scalars, which is exact. -/
public theorem restrictScalars_mapDerivedCategory_isLeftDerivedFunctor :
    letI := restrictScalars_additive f
    letI := restrictionPreservesFiniteLimits f.toRingCatSheafHom
    letI := restrictScalars_preservesFiniteColimits f
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategory.IsLeftDerivedFunctor
      (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (pushforwardRingCatSheaf f)) (ComplexShape.up ℤ)) := by
  let := restrictScalars_additive f
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
  apply (Functor.isLeftDerivedFunctor_iff_of_inverts _ _ hR).2
  infer_instance

/-- The adjunction of Stacks 0BV0: for a morphism of schemes `f : Y ⟶ X`, the functor
`R ℰom(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(f₊ 𝒪_Y)` is right adjoint to the functor `D(f₊ 𝒪_Y) ⥤ D(𝒪_X)`
induced by restriction of scalars, by the adjunction derived from
`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction` termwise. -/
public noncomputable def derivedRestrictScalarsHomAdjunction :
    derivedRestrictionOfScalars f ⊣ derivedHomSheaf f :=
  letI := restrictScalars_additive f
  letI := homSheaf_additive f
  letI := restrictionPreservesFiniteLimits f.toRingCatSheafHom
  letI := restrictScalars_preservesFiniteColimits f
  letI := restrictScalars_mapDerivedCategory_isLeftDerivedFunctor f
  derivedRestrictionSheafHomAdjunction f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom)
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction f.toRingCatSheafHom)
    (derivedHomSheaf f) (derivedHomSheafUnit f)
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategory
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh.hom

/-- **The counit of `derivedRestrictScalarsHomAdjunction` is evaluation at `1`.** On a complex
`M` of `𝒪_X`-modules, the counit, preceded by the comparison maps, is the class of the counit of
`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction` applied termwise, which on sections
is `ψ ↦ ψ(1)`
(`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction_counit_app_val_app_apply`). -/
public theorem derivedRestrictScalarsHomAdjunction_counit_fac
    (M : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    letI := restrictScalars_additive f
    letI := homSheaf_additive f
    (derivedRestrictionOfScalars f).map
        ((derivedHomSheafUnit f).app ((HomotopyCategory.quotient _ _).obj M)) ≫
      (derivedRestrictScalarsHomAdjunction f).counit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M)) =
      (derivedRestrictionOfScalarsFactors f).hom.app
          (((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj M)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (((RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction
            f.toRingCatSheafHom).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app M)) :=
  let := restrictScalars_additive f
  let := homSheaf_additive f
  let := restrictionPreservesFiniteLimits f.toRingCatSheafHom
  let := restrictScalars_preservesFiniteColimits f
  let := restrictScalars_mapDerivedCategory_isLeftDerivedFunctor f
  derivedRestrictionSheafHomAdjunction_counit_fac f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom)
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction f.toRingCatSheafHom)
    (derivedHomSheaf f) (derivedHomSheafUnit f)
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategory
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryFactorsh.hom M

end AlgebraicGeometry

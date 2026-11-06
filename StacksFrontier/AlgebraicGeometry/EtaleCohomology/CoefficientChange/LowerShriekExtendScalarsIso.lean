module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ConstantProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.TotalProjectionAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.LowerShriekExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ExtensionByZeroExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.ModuleVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.CategoryTheory.Adjunction.MateRightAdjointImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DirectImageRestrictScalarsUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology with compact support commutes with derived extension of coefficients

Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings.  This file proves that the comparison
`Rg_*(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rg_*(E ⊗^L_{Λ₁} Λ₂)` is invertible for a quasi-compact quasi-separated
morphism `g` whose direct image has finite cohomological dimension, and deduces the second
diagram of [Stacks, Remark 0GL6] for `Rf_! = R(f̄)_* ∘ Rj_!`.

After restriction of coefficients, which is conservative, the comparison becomes the
projection formula `Rg_*E ⊗^L_{Λ₁} Λ̲₂ ⟶ Rg_*(E ⊗^L_{Λ₁} Λ̲₂)`
(`Stacks.EtaleCohomology.etaleModuleDerivedProjectionMap`), which is invertible by dévissage from
the case of `Λ₁` itself (`CategoryTheory.isIso_mateEquiv_symm_app`).  The identification uses
that the projection formula intertwines the actions of `Λ₂`
(`Stacks.EtaleCohomology.etaleModuleDerivedProjectionMap_coefficientAction`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex.KFlatBifunctor

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/- The instance proofs `F.Additive`, `(F.obj X).Additive` and `HasMapBifunctor` for the tensor
product over `Λ` are the named ones of `ModuleTensor.TensorBifunctorInstances`, stated as
`etaleModuleDerivedTensor` records them, so that every `derivedBifunctor (etaleModuleTensor Λ X)`
written here is the unfolding of `etaleModuleDerivedTensor Λ X` up to proofs of the same
propositions; with independently synthesized proofs the kernel compares the two by evaluating the
derived bifunctor, which is prohibitively slow. -/
attribute [local instance high] etaleModuleTensor_additive etaleModuleTensor_obj_additive
  etaleModuleTensor_hasTotal_mapBifunctor

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)


/-- Naturality of the derived action of `Λ₂`. -/
@[reassoc]
theorem etaleModuleDerivedCoefficientAction_naturality (Z : Scheme.{u})
    {d d' : DerivedCategory (EtaleModules.{u, r} Λ₂ Z)} (f : d ⟶ d') :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Z).map
        ((etaleModuleDerivedRestrictScalars.{u, r} φ Z).map f)).app
        (DerivedCategory.Q.obj (coefficientSheafComplex.{u, r} φ Z)) ≫
      etaleModuleDerivedCoefficientAction φ Z d' =
    etaleModuleDerivedCoefficientAction φ Z d ≫ (etaleModuleDerivedRestrictScalars.{u, r} φ Z).map
        f := by
  have h₁ := (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ Z).inv.naturality
    ((etaleModuleDerivedRestrictScalars.{u, r} φ Z).map f)
  have h₂ := (etaleModuleDerivedExtendRestrictAdj.{u, r} φ Z).counit.naturality f
  dsimp only [Functor.flip_obj_map, Functor.comp_map, Functor.id_map] at h₁ h₂
  simp only [etaleModuleDerivedCoefficientAction]
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, Category.assoc]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-! ### Factors with pinned types

The components of the natural isomorphisms used below, each with its source and target spelled
in one way, so that the morphisms compared by the kernel are syntactically equal. -/

/-- The component at `d` of `Rg_* ∘ res ≅ res ∘ Rg_*`, `Rg_*(res d) ⟶ res(Rg_* d)`. -/
def etaleModuleDerivedDirectImageUnboundedRestrictScalarsInvApp
    (d : DerivedCategory (EtaleModules.{u, r} Λ₂ X)) :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d) ⟶
        (etaleModuleDerivedRestrictScalars.{u, r} φ Y).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g).obj d) :=
  (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv.app d

/-- The component of the projection formula at `E` and `M`,
`Rg_*E ⊗^L c_Y M ⟶ Rg_*(E ⊗^L c_X M)`. -/
def etaleModuleDerivedProjectionMapApp (E : DerivedCategory (EtaleModules.{u, r} Λ₁ X))
    (M : DerivedCategory (ModuleCat.{max (u + 1) r} Λ₁)) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
        g).obj E)).obj ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ Y).obj M) ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj (((etaleModuleDerivedTensor.{u, r}
          Λ₁ X).obj E).obj ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).obj M)) :=
  ((etaleModuleDerivedProjectionMap Λ₁ g).app E).app M

private theorem alphaInvApp_naturality {d d' : DerivedCategory (EtaleModules.{u, r} Λ₂ X)}
    (f : d ⟶ d') :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).map f) ≫
        etaleModuleDerivedDirectImageUnboundedRestrictScalarsInvApp φ g d' =
        etaleModuleDerivedDirectImageUnboundedRestrictScalarsInvApp φ g d ≫
        (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g).map f) :=
  (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv.naturality f

@[reassoc]
private theorem projectionMapApp_naturality_right (E : DerivedCategory (EtaleModules.{u, r} Λ₁ X))
    {M M' : DerivedCategory (ModuleCat.{max (u + 1) r} Λ₁)} (m : M ⟶ M') :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
        g).obj E)).map ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ Y).map m) ≫
        etaleModuleDerivedProjectionMapApp g E M' =
      etaleModuleDerivedProjectionMapApp g E M ≫ (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
          g).map (((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj E).map
          ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).map m)) :=
  ((etaleModuleDerivedProjectionMap Λ₁ g).app E).naturality m

@[reassoc]
private theorem projectionMapApp_naturality_left {E E' : DerivedCategory (EtaleModules.{u, r} Λ₁ X)}
    (e : E ⟶ E') (M : DerivedCategory (ModuleCat.{max (u + 1) r} Λ₁)) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
        g).map e)).app ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ Y).obj M) ≫
        etaleModuleDerivedProjectionMapApp g E' M =
      etaleModuleDerivedProjectionMapApp g E M ≫ (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
          g).map (((etaleModuleDerivedTensor.{u, r} Λ₁ X).map e).app
          ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).obj M)) :=
  NatTrans.congr_app ((etaleModuleDerivedProjectionMap Λ₁ g).naturality e) M

@[reassoc]
private theorem projectionMapApp_fac (K : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (N : (constantSheafKFlatComplexes.{u, r} Λ₁).FullSubcategory) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map (etaleModuleDirectImageUnboundedUnitApp Λ₁ g K)).app
        ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ Y).obj (DerivedCategory.Q.obj N.obj)) ≫
            etaleModuleDerivedProjectionMapApp g (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj
            N.obj) =
      etaleModuleProjectionMapAux Λ₁ g K N :=
  etaleModuleDerivedProjectionMap_fac Λ₁ g K N

/-- The comparison of `N̲ ⟶ Λ̲₂[0]` with the derived constant sheaf of `N ⟶ Λ₂`. -/
theorem coefficientSheafComplexMap_comp_coefficientSheafComplexIso (Z : Scheme.{u})
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    DerivedCategory.Q.map (coefficientSheafComplexMap φ Z N q) ≫ (coefficientSheafComplexIso φ
        Z).hom =
      etaleModuleConstantSheafQInv Λ₁ Z N ≫
        (etaleModuleDerivedConstantSheaf.{u, r} Λ₁ Z).map (DerivedCategory.Q.map q) := by
  show DerivedCategory.Q.map
      (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (etaleModuleConstantSheafFunctor.{u, r} Λ₁ Z) (ComplexShape.up ℤ) 0).hom.app
          (coefficientModule.{u} φ)) ≫
      (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (etaleModuleConstantSheafFunctor.{u, r} Λ₁ Z) (ComplexShape.up ℤ) 0).inv.app
          (coefficientModule.{u} φ)) ≫
        (etaleModuleConstantSheafFunctor.{u, r} Λ₁ Z).mapDerivedCategoryFactors.inv.app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ))) = _
  rw [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc DerivedCategory.Q
    ((HomologicalComplex.singleMapHomologicalComplex (etaleModuleConstantSheafFunctor.{u, r} Λ₁ Z)
      (ComplexShape.up ℤ) 0).hom.app (coefficientModule.{u} φ)), Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (etaleModuleConstantSheafFunctor.{u, r} Λ₁ Z).mapDerivedCategoryFactors.inv.naturality q

private theorem coefficientSheafComplexMap_eq (Z : Scheme.{u})
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    (etaleModuleConstantSheafQInv Λ₁ Z N ≫
        (etaleModuleDerivedConstantSheaf.{u, r} Λ₁ Z).map (DerivedCategory.Q.map q)) ≫
      (coefficientSheafComplexIso φ Z).inv = DerivedCategory.Q.map (coefficientSheafComplexMap φ Z
          N q) := by
  rw [← coefficientSheafComplexMap_comp_coefficientSheafComplexIso, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The derived constant sheaf of `N ⟶ Λ₂[0]` is invertible when `N ⟶ Λ₂[0]` is a
quasi-isomorphism. -/
theorem isIso_Q_map_coefficientSheafComplexMap (Z : Scheme.{u})
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ))
    [QuasiIso q] : IsIso (DerivedCategory.Q.map (coefficientSheafComplexMap φ Z N q)) := by
  rw [← coefficientSheafComplexMap_eq]
  infer_instance

private theorem constantSheafQInv_hom (Z : Scheme.{u})
    (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ) :
    etaleModuleConstantSheafQInv Λ₁ Z N ≫ etaleModuleConstantSheafQHom Λ₁ Z N = 𝟙 _ :=
  Iso.inv_hom_id_app _ _

private theorem comparisonRightInv_hom (Z : Scheme.{u})
    (K L : CochainComplex (EtaleModules.{u, r} Λ₁ Z) ℤ)
    (hL : KFlat (etaleModuleTensor.{u, r} Λ₁ Z) L) :
    etaleModuleComparisonRightInv Λ₁ Z K L hL ≫ etaleModuleComparisonRight Z K L hL = 𝟙 _ :=
  Iso.inv_hom_id _

/-- The action of `Λ₂` on `res(Rg_*d)`, transported to `Rg_*(res d) ⊗^L Λ̲₂`. -/
def directImageCoefficientActionLeft (d : DerivedCategory (EtaleModules.{u, r} Λ₂ X)) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
        g).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d))).obj (DerivedCategory.Q.obj
        (coefficientSheafComplex.{u, r} φ Y)) ⟶
      (etaleModuleDerivedRestrictScalars.{u, r} φ Y).obj
          ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g).obj d) :=
  ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map
      (etaleModuleDerivedDirectImageUnboundedRestrictScalarsInvApp φ g d)).app
      (DerivedCategory.Q.obj (coefficientSheafComplex.{u, r} φ Y)) ≫
    etaleModuleDerivedCoefficientAction φ Y ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂
        g).obj d)

/-- The projection formula followed by `Rg_*` of the action of `Λ₂` on `res d`. -/
def directImageCoefficientActionRight (d : DerivedCategory (EtaleModules.{u, r} Λ₂ X)) :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
        g).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d))).obj (DerivedCategory.Q.obj
        (coefficientSheafComplex.{u, r} φ Y)) ⟶
      (etaleModuleDerivedRestrictScalars.{u, r} φ Y).obj
          ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g).obj d) :=
  ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
      g).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d))).map
      (coefficientSheafComplexIso φ Y).hom ≫
    etaleModuleDerivedProjectionMapApp g ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d)
        (coefficientModuleComplex.{u} φ) ≫
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (((etaleModuleDerivedTensor.{u, r} Λ₁
        X).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d)).map
        (coefficientSheafComplexIso φ X).inv ≫
      etaleModuleDerivedCoefficientAction φ X d) ≫
    etaleModuleDerivedDirectImageUnboundedRestrictScalarsInvApp φ g d

section OnComplexes

variable (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)

private def facrInvX : DerivedCategory.Q.obj (((etaleModuleRestrictScalarsUniv.{u, r} φ
    X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ⟶
    (etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj J) :=
  (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app J

private def facrHomX : (etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj J)
    ⟶ DerivedCategory.Q.obj (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj J) :=
  (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.hom.app J

private def facrInvY : DerivedCategory.Q.obj (((etaleModuleDirectImage.{u, r} Λ₁
    g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((etaleModuleRestrictScalarsUniv.{u, r} φ
    X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ⟶
    (etaleModuleDerivedRestrictScalars.{u, r} φ Y).obj (DerivedCategory.Q.obj
    (((etaleModuleDirectImage.{u, r} Λ₂ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :=
  (etaleModuleRestrictScalarsUniv.{u, r} φ Y).mapDerivedCategoryFactors.inv.app
      (((etaleModuleDirectImage.{u, r} Λ₂ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)

private def facrHomY : (etaleModuleDerivedRestrictScalars.{u, r} φ Y).obj (DerivedCategory.Q.obj
    (((etaleModuleDirectImage.{u, r} Λ₂ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ⟶
    DerivedCategory.Q.obj (((etaleModuleDirectImage.{u, r} Λ₁ g).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj J)) :=
  (etaleModuleRestrictScalarsUniv.{u, r} φ Y).mapDerivedCategoryFactors.hom.app
      (((etaleModuleDirectImage.{u, r} Λ₂ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)

private def totalCoefficientActionY (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    totalComplex (etaleModuleTensor.{u, r} Λ₁ Y) (((etaleModuleDirectImage.{u, r} Λ₁
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((etaleModuleRestrictScalarsUniv.{u, r} φ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
        Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ⟶ (((etaleModuleDirectImage.{u, r} Λ₁
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((etaleModuleRestrictScalarsUniv.{u, r} φ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :=
  etaleModuleTotalCoefficientAction φ Y (((etaleModuleDirectImage.{u, r} Λ₂
      g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) N q

private theorem facrInvX_hom : facrInvX φ J ≫ facrHomX φ J = 𝟙 _ := Iso.inv_hom_id_app _ _

private theorem facrInvY_hom : facrInvY φ g J ≫ facrHomY φ g J = 𝟙 _ := Iso.inv_hom_id_app _ _

private theorem totalCoefficientActionY_eq (N : CochainComplex (ModuleCat.{max (u + 1) r} Λ₁) ℤ)
    (q : N ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ)) :
    totalCoefficientActionY φ g J N q =
      etaleModuleTotalProjectionMap Λ₁ g (((etaleModuleRestrictScalarsUniv.{u, r} φ
          X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) N ≫
        ((etaleModuleDirectImage.{u, r} Λ₁ g).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (etaleModuleTotalCoefficientAction φ X J N q) :=
  etaleModuleTotalProjectionMap_coefficientAction φ g J N q

private theorem alphaRed :
    etaleModuleDirectImageUnboundedUnitApp Λ₁ g (((etaleModuleRestrictScalarsUniv.{u, r} φ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (facrInvX φ J) ≫
      etaleModuleDerivedDirectImageUnboundedRestrictScalarsInvApp φ g (DerivedCategory.Q.obj J) =
          facrInvY φ g J ≫ (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map
          (etaleModuleDirectImageUnboundedUnitApp Λ₂ g J) :=
  etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso_inv_fac φ g J

variable (N : (constantSheafKFlatComplexes.{u, r} Λ₁).FullSubcategory)
  (q : N.obj ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ))

private theorem actionY_fac :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ Y).obj
        (DerivedCategory.Q.obj (((etaleModuleDirectImage.{u, r} Λ₂ g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)))).map (DerivedCategory.Q.map (coefficientSheafComplexMap φ Y
        N.obj q)) ≫
      etaleModuleDerivedCoefficientAction φ Y (DerivedCategory.Q.obj
          (((etaleModuleDirectImage.{u, r} Λ₂ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
          =
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map (facrHomY φ g J)).app (DerivedCategory.Q.obj
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ Y).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        N.obj)) ≫ etaleModuleComparisonRight (Λ₁ := Λ₁) Y (((etaleModuleDirectImage.{u, r} Λ₁
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((etaleModuleRestrictScalarsUniv.{u, r} φ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
        Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj) (N.property Y).1 ≫
      DerivedCategory.Q.map (totalCoefficientActionY φ g J N.obj q) ≫ facrInvY φ g J :=
  etaleModuleDerivedCoefficientAction_fac φ Y (((etaleModuleDirectImage.{u, r} Λ₂
      g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
    ⟨(HomotopyCategory.quotient _ _).obj N.obj, N.property⟩ q

private theorem actionX_fac :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj
        (DerivedCategory.Q.obj J))).map (DerivedCategory.Q.map (coefficientSheafComplexMap φ X
        N.obj q)) ≫
      etaleModuleDerivedCoefficientAction φ X (DerivedCategory.Q.obj J) =
    ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map (facrHomX φ J)).app (DerivedCategory.Q.obj
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        N.obj)) ≫ etaleModuleComparisonRight (Λ₁ := Λ₁) X (((etaleModuleRestrictScalarsUniv.{u, r} φ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj) (N.property X).1 ≫
      DerivedCategory.Q.map (etaleModuleTotalCoefficientAction φ X J N.obj q) ≫ facrInvX φ J :=
  etaleModuleDerivedCoefficientAction_fac φ X J
    ⟨(HomotopyCategory.quotient _ _).obj N.obj, N.property⟩ q

/-- The left side of `etaleModuleDerivedProjectionMap_coefficientAction` at a complex, against
a resolution `N ⟶ Λ₂`. -/
private theorem coefficientActionLeft_reduction :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map (etaleModuleDirectImageUnboundedUnitApp Λ₁ g
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (facrInvX φ J))).app
            (DerivedCategory.Q.obj (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
            Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj)) ≫
      ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj ((etaleModuleDerivedDirectImageUnbounded.{u, r}
          Λ₁ g).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj
          J)))).map (DerivedCategory.Q.map (coefficientSheafComplexMap φ Y N.obj q)) ≫
      directImageCoefficientActionLeft φ g (DerivedCategory.Q.obj J) =
    etaleModuleComparisonRight (Λ₁ := Λ₁) Y (((etaleModuleDirectImage.{u, r} Λ₁
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((etaleModuleRestrictScalarsUniv.{u, r} φ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
        Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj) (N.property Y).1 ≫
        DerivedCategory.Q.map (totalCoefficientActionY φ g J N.obj q) ≫ facrInvY φ g J ≫
      (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map (etaleModuleDirectImageUnboundedUnitApp Λ₂
          g J) := by
  rw [directImageCoefficientActionLeft, ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map
      (etaleModuleDerivedDirectImageUnboundedRestrictScalarsInvApp φ g (DerivedCategory.Q.obj
      J))).naturality_assoc,
    ← NatTrans.comp_app_assoc, ← Functor.map_comp, Category.assoc, alphaRed,
    Functor.map_comp, NatTrans.comp_app, Category.assoc,
    ← ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map ((etaleModuleDerivedRestrictScalars.{u, r} φ
        Y).map (etaleModuleDirectImageUnboundedUnitApp Λ₂ g J))).naturality_assoc,
    etaleModuleDerivedCoefficientAction_naturality, reassoc_of% (actionY_fac φ g J N q),
    ← NatTrans.comp_app_assoc, ← Functor.map_comp, facrInvY_hom, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp]

private theorem coefficientActionRight_inner :
    etaleModuleComparisonRightInv Λ₁ X (((etaleModuleRestrictScalarsUniv.{u, r} φ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj) (N.property X).1 ≫
      ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj (DerivedCategory.Q.obj
          (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J))).map (etaleModuleConstantSheafQInv Λ₁ X N.obj) ≫
      ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map (facrInvX φ J)).app
          ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).obj (DerivedCategory.Q.obj N.obj)) ≫
      ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ
          X).obj (DerivedCategory.Q.obj J))).map ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).map
          (DerivedCategory.Q.map q)) ≫
      ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ
          X).obj (DerivedCategory.Q.obj J))).map (coefficientSheafComplexIso φ X).inv ≫
      etaleModuleDerivedCoefficientAction φ X (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map (etaleModuleTotalCoefficientAction φ X J N.obj q) ≫ facrInvX φ J := by
  rw [((etaleModuleDerivedTensor.{u, r} Λ₁ X).map (facrInvX φ J)).naturality_assoc,
    ← Functor.map_comp_assoc ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj J))),
    ← Functor.map_comp_assoc ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj J))),
    coefficientSheafComplexMap_eq, actionX_fac φ J N q, ← NatTrans.comp_app_assoc,
    ← Functor.map_comp, facrInvX_hom, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, ← Category.assoc (etaleModuleComparisonRightInv Λ₁ X
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N.obj)
      (N.property X).1), comparisonRightInv_hom, Category.id_comp]

/-- The right side of `etaleModuleDerivedProjectionMap_coefficientAction` at a complex, against
a resolution `N ⟶ Λ₂`. -/
private theorem coefficientActionRight_reduction :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map (etaleModuleDirectImageUnboundedUnitApp Λ₁ g
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (facrInvX φ J))).app
            (DerivedCategory.Q.obj (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
            Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj)) ≫
      ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj ((etaleModuleDerivedDirectImageUnbounded.{u, r}
          Λ₁ g).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj
          J)))).map (DerivedCategory.Q.map (coefficientSheafComplexMap φ Y N.obj q)) ≫
      directImageCoefficientActionRight φ g (DerivedCategory.Q.obj J) =
    etaleModuleComparisonRight (Λ₁ := Λ₁) Y (((etaleModuleDirectImage.{u, r} Λ₁
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((etaleModuleRestrictScalarsUniv.{u, r} φ
        X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
        (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
        Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj) (N.property Y).1 ≫
        DerivedCategory.Q.map (totalCoefficientActionY φ g J N.obj q) ≫ facrInvY φ g J ≫
      (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map (etaleModuleDirectImageUnboundedUnitApp Λ₂
          g J) := by
  have hF : (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (etaleModuleComparisonRightInv
      Λ₁ X (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J) (((etaleModuleConstantSheafFunctor.{u, r} Λ₁
      X).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.obj) (N.property X).1 ≫
        ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj (DerivedCategory.Q.obj
            (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J))).map (etaleModuleConstantSheafQInv Λ₁ X N.obj)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (((etaleModuleDerivedTensor.{u, r}
          Λ₁ X).map (facrInvX φ J)).app ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).obj
          (DerivedCategory.Q.obj N.obj))) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (((etaleModuleDerivedTensor.{u, r}
          Λ₁ X).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj
          J))).map ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).map (DerivedCategory.Q.map q))) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (((etaleModuleDerivedTensor.{u, r}
          Λ₁ X).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj
          J))).map (coefficientSheafComplexIso φ X).inv ≫
        etaleModuleDerivedCoefficientAction φ X (DerivedCategory.Q.obj J)) =
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (DerivedCategory.Q.map
          (etaleModuleTotalCoefficientAction φ X J N.obj q)) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (facrInvX φ J) := by
    rw [← Functor.map_comp (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g), ← Functor.map_comp
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g),
      ← Functor.map_comp (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g), ← Functor.map_comp
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g), Category.assoc,
      coefficientActionRight_inner]
  rw [directImageCoefficientActionRight,
    ← Functor.map_comp_assoc ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj J)))),
    coefficientSheafComplexMap_comp_coefficientSheafComplexIso,
    Functor.map_comp_assoc ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj (DerivedCategory.Q.obj J)))),
    projectionMapApp_naturality_right_assoc,
    ← ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map (etaleModuleDirectImageUnboundedUnitApp Λ₁ g
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map (facrInvX φ J))).naturality_assoc,
          Functor.map_comp (etaleModuleDerivedTensor.{u, r} Λ₁ Y),
    NatTrans.comp_app, Category.assoc,
    projectionMapApp_naturality_left_assoc, projectionMapApp_fac_assoc,
    etaleModuleProjectionMapAux]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj (DerivedCategory.Q.obj
      (((etaleModuleDirectImage.{u, r} Λ₁ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      J)))), constantSheafQInv_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hF, ← etaleModuleDirectImageUnboundedUnitApp_naturality_assoc, alphaRed,
    totalCoefficientActionY_eq, Functor.map_comp, Category.assoc]

end OnComplexes

/-- Naturality of `directImageCoefficientActionLeft`. -/
theorem directImageCoefficientActionLeft_naturality
    {d d' : DerivedCategory (EtaleModules.{u, r} Λ₂ X)} (f : d ⟶ d') :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
        g).map ((etaleModuleDerivedRestrictScalars.{u, r} φ X).map f))).app (DerivedCategory.Q.obj
        (coefficientSheafComplex.{u, r} φ Y)) ≫
      directImageCoefficientActionLeft φ g d' =
    directImageCoefficientActionLeft φ g d ≫ (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g).map f) := by
  rw [directImageCoefficientActionLeft, directImageCoefficientActionLeft,
    ← NatTrans.comp_app_assoc, ← Functor.map_comp, alphaInvApp_naturality, Functor.map_comp,
    NatTrans.comp_app, Category.assoc, etaleModuleDerivedCoefficientAction_naturality,
    Category.assoc]

/-- Naturality of `directImageCoefficientActionRight`. -/
theorem directImageCoefficientActionRight_naturality
    {d d' : DerivedCategory (EtaleModules.{u, r} Λ₂ X)} (f : d ⟶ d') :
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁
        g).map ((etaleModuleDerivedRestrictScalars.{u, r} φ X).map f))).app (DerivedCategory.Q.obj
        (coefficientSheafComplex.{u, r} φ Y)) ≫
      directImageCoefficientActionRight φ g d' =
    directImageCoefficientActionRight φ g d ≫ (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g).map f) := by
  have h : ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map ((etaleModuleDerivedRestrictScalars.{u, r} φ
      X).map f)).app ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).obj
      (coefficientModuleComplex.{u} φ)) ≫
        ((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ
            X).obj d')).map (coefficientSheafComplexIso φ X).inv ≫
        etaleModuleDerivedCoefficientAction φ X d' =
      (((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj ((etaleModuleDerivedRestrictScalars.{u, r} φ
          X).obj d)).map (coefficientSheafComplexIso φ X).inv ≫
        etaleModuleDerivedCoefficientAction φ X d) ≫ (etaleModuleDerivedRestrictScalars.{u, r} φ
            X).map f := by
    rw [← ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map ((etaleModuleDerivedRestrictScalars.{u, r} φ
        X).map f)).naturality_assoc,
      etaleModuleDerivedCoefficientAction_naturality, Category.assoc]
  rw [directImageCoefficientActionRight, directImageCoefficientActionRight,
    ← ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map ((etaleModuleDerivedDirectImageUnbounded.{u, r}
        Λ₁ g).map ((etaleModuleDerivedRestrictScalars.{u, r} φ X).map f))).naturality_assoc,
    projectionMapApp_naturality_left_assoc, ← Functor.map_comp_assoc
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g), h,
    Functor.map_comp_assoc (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g),
        alphaInvApp_naturality]
  simp only [Category.assoc]

/-- **The projection formula intertwines the actions of `Λ₂`.** For `d ∈ D(X_étale, Λ₂)`, the
action of `Λ₂` on `res(Rg_*d) ≅ Rg_*(res d)` is the projection formula
`Rg_*(res d) ⊗^L Λ̲₂ ⟶ Rg_*(res d ⊗^L Λ̲₂)` followed by `Rg_*` of the action on `res d`. -/
theorem etaleModuleDerivedProjectionMap_coefficientAction
    (d : DerivedCategory (EtaleModules.{u, r} Λ₂ X)) :
    directImageCoefficientActionLeft φ g d = directImageCoefficientActionRight φ g d := by
  have key : ∀ (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ), J.IsKInjective →
      directImageCoefficientActionLeft φ g (DerivedCategory.Q.obj J) =
        directImageCoefficientActionRight φ g (DerivedCategory.Q.obj J) := by
    intro J hJ
    obtain ⟨P, p, hp, hP⟩ := exists_quasiIso_kFlat_etaleModuleConstantSheafFunctor.{u, r} Λ₁
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (coefficientModule.{u} φ))
    let N : (constantSheafKFlatComplexes.{u, r} Λ₁).FullSubcategory := ⟨P, hP⟩
    have : IsIso (etaleModuleDirectImageUnboundedUnitApp Λ₁ g
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)) :=
      isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_restrictScalars.{u, r} φ g J hJ
    have : IsIso (facrInvX φ J) :=
      inferInstanceAs (IsIso ((etaleModuleRestrictScalarsUniv.{u, r} φ
          X).mapDerivedCategoryFactors.inv.app J))
    have := hp
    have : IsIso (DerivedCategory.Q.map (coefficientSheafComplexMap φ Y N.obj p)) :=
      isIso_Q_map_coefficientSheafComplexMap φ Y P p
    have hL := coefficientActionLeft_reduction φ g J N p
    rw [← coefficientActionRight_reduction φ g J N p] at hL
    exact (cancel_epi _).1 ((cancel_epi _).1 hL)
  obtain ⟨K, ⟨e⟩⟩ : ∃ K, Nonempty (d ≅ DerivedCategory.Q.obj K) :=
    ⟨_, ⟨(DerivedCategory.Q.objObjPreimageIso d).symm⟩⟩
  obtain ⟨J, s, hJ, hs⟩ := Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
    (EtaleModules.{u, r} Λ₂ X) K
  have : IsIso (DerivedCategory.Q.map s) := Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso _ _) s ((HomologicalComplex.mem_quasiIso_iff _).2 hs)
  let i : d ≅ DerivedCategory.Q.obj J := e ≪≫ asIso (DerivedCategory.Q.map s)
  have hl := directImageCoefficientActionLeft_naturality φ g i.hom
  rw [key J hJ, directImageCoefficientActionRight_naturality φ g i.hom] at hl
  exact ((cancel_mono _).1 hl).symm

/-- The comparison `res(Rg_*E ⊗^L Λ₂) ⟶ Rg_*(res(E ⊗^L Λ₂))` through which the comparison of
derived direct images with extension of coefficients is computed: the projection formula against
`Λ̲₂`, read through `res(- ⊗^L Λ₂) ≅ - ⊗^L Λ̲₂`. -/
def directImageExtendScalarsProjection (E : DerivedCategory (EtaleModules.{u, r} Λ₁ X)) :
    (etaleModuleDerivedRestrictScalars.{u, r} φ Y).obj ((etaleModuleDerivedExtendScalars.{u, r} φ
        Y).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj E)) ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj
          ((etaleModuleDerivedExtendScalars.{u, r} φ X).obj E)) :=
  (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ Y).hom.app
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj E) ≫
    ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).obj
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj E)).map
        (coefficientSheafComplexIso φ Y).hom ≫
    ((etaleModuleDerivedProjectionMap Λ₁ g).app E).app (coefficientModuleComplex.{u} φ) ≫
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
      (((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj E).map (coefficientSheafComplexIso φ X).inv ≫
        (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X).inv.app E)

/-- Naturality of `directImageExtendScalarsProjection`. -/
theorem directImageExtendScalarsProjection_naturality
    {E E' : DerivedCategory (EtaleModules.{u, r} Λ₁ X)} (f : E ⟶ E') :
    (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map ((etaleModuleDerivedExtendScalars.{u, r} φ
        Y).map
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map f)) ≫
      directImageExtendScalarsProjection φ g E' =
    directImageExtendScalarsProjection φ g E ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).map
          ((etaleModuleDerivedExtendScalars.{u, r} φ X).map f)) := by
  have h1 := (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ Y).hom.naturality
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map f)
  have h2 := ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map f)).naturality
      (coefficientSheafComplexIso φ Y).hom
  have h3 : ((etaleModuleDerivedTensor.{u, r} Λ₁ Y).map
      ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        f)).app ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ Y).obj (coefficientModuleComplex.{u}
            φ)) ≫
      ((etaleModuleDerivedProjectionMap Λ₁ g).app E').app (coefficientModuleComplex.{u} φ) =
      ((etaleModuleDerivedProjectionMap Λ₁ g).app E).app (coefficientModuleComplex.{u} φ) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        (((etaleModuleDerivedTensor.{u, r} Λ₁ X).map f).app
          ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).obj (coefficientModuleComplex.{u} φ))) :=
    NatTrans.congr_app ((etaleModuleDerivedProjectionMap Λ₁ g).naturality f)
      (coefficientModuleComplex.{u} φ)
  have h4 := ((etaleModuleDerivedTensor.{u, r} Λ₁ X).map f).naturality
    (coefficientSheafComplexIso φ X).inv
  have h5 := (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X).inv.naturality f
  dsimp only [Functor.comp_map, Functor.flip_obj_map] at h1 h5
  have h45 : (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        (((etaleModuleDerivedTensor.{u, r} Λ₁ X).map f).app
          ((etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).obj (coefficientModuleComplex.{u} φ))) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        (((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj E').map (coefficientSheafComplexIso φ X).inv ≫
          (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X).inv.app E') =
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        (((etaleModuleDerivedTensor.{u, r} Λ₁ X).obj E).map (coefficientSheafComplexIso φ X).inv ≫
          (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X).inv.app E) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).map
          ((etaleModuleDerivedExtendScalars.{u, r} φ X).map f)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← reassoc_of% h4, h5, Category.assoc]
  simp only [directImageExtendScalarsProjection, Category.assoc]
  rw [reassoc_of% h1, ← reassoc_of% h2, reassoc_of% h3, h45]

/-- `directImageExtendScalarsProjection` carries the action of `Λ₂` on `res(Rg_* d)` to the action
on `Rg_*(res d)`: the hypothesis of `CategoryTheory.map_mateEquiv_symm_app_eq`. -/
theorem directImageExtendScalarsProjection_counit (d : DerivedCategory (EtaleModules.{u, r} Λ₂ X)) :
    (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map ((etaleModuleDerivedExtendScalars.{u, r} φ
        Y).map
        ((etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv.app d)) ≫
      (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map
        ((etaleModuleDerivedExtendRestrictAdj.{u, r} φ Y).counit.app
          ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g).obj d)) =
    directImageExtendScalarsProjection φ g ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).map
          ((etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit.app d)) ≫
      (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv.app d := by
  have h := etaleModuleDerivedProjectionMap_coefficientAction φ g d
  simp only [directImageCoefficientActionLeft, directImageCoefficientActionRight,
    etaleModuleDerivedDirectImageUnboundedRestrictScalarsInvApp, etaleModuleDerivedProjectionMapApp,
    etaleModuleDerivedCoefficientAction, Functor.map_comp, Category.assoc] at h
  have he := (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ Y).inv.naturality
    ((etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv.app d)
  dsimp only [Functor.comp_map, Functor.flip_obj_map] at he
  rw [← cancel_epi ((etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ Y).inv.app
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).obj
      ((etaleModuleDerivedRestrictScalars.{u, r} φ X).obj d))), ← reassoc_of% he]
  simp only [directImageExtendScalarsProjection, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  exact h

/-- Restriction of coefficients reflects isomorphisms. -/
instance etaleModuleDerivedRestrictScalars_reflectsIsomorphisms (Z : Scheme.{u}) :
    (etaleModuleDerivedRestrictScalars.{u, r} φ Z).ReflectsIsomorphisms :=
  ⟨fun f hf => isIso_of_isIso_etaleModuleDerivedRestrictScalars_map φ Z f hf⟩

/- `Stacks.EtaleCohomology.hasSheafifyEtale` is stated at the coefficient universe `u + 1`;
instance search would try to unify the coefficient universe `max (u + 1) r` with it and fail on
the universe constraint, so it is switched off for the next declaration. -/
attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale in
/-- **The derived direct image commutes with derived extension of coefficients** along a
quasi-compact quasi-separated morphism whose direct image on sheaves of `Λ₁`-modules has finite
cohomological dimension: the comparison `Rg_*(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rg_*(E ⊗^L_{Λ₁} Λ₂)` is an
isomorphism. -/
@[sga "4½ Rapport 4.12" "Proper case of (*)"]
theorem isIso_derivedDirectImageUnboundedExtendScalarsMap [QuasiCompact g] [QuasiSeparated g]
    (hcd : ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, r} Λ₁ X,
      IsZero (((etaleModuleDirectImage.{u, r} Λ₁ g).rightDerived q).obj F)) :
    IsIso (derivedDirectImageUnboundedExtendScalarsMap.{u, r} φ g) := by
  have := isIso_etaleModuleDerivedProjectionMap Λ₁ g hcd
  have h : ∀ E, IsIso ((derivedDirectImageUnboundedExtendScalarsMap.{u, r} φ g).app E) := by
    intro E
    have : IsIso (directImageExtendScalarsProjection φ g E) := by
      dsimp only [directImageExtendScalarsProjection]
      infer_instance
    exact isIso_mateEquiv_symm_app (adj₁ := etaleModuleDerivedExtendRestrictAdj.{u, r} φ X)
      (adj₂ := etaleModuleDerivedExtendRestrictAdj.{u, r} φ Y)
      (α := (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv)
      (π := directImageExtendScalarsProjection φ g)
      (hπ := fun f => directImageExtendScalarsProjection_naturality φ g f)
      (hα := directImageExtendScalarsProjection_counit φ g) E
  exact NatIso.isIso_of_isIso_app _

/-- **The second diagram of [Stacks, Remark 0GL6], modulo the inputs of the finite cohomological
dimension of proper direct images.**  Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings
with `Λ₁` torsion, `f : X ⟶ Y` a morphism of schemes with `Y` quasi-compact and `j` a
compactification of `X` over `Y`.  Then the comparison
`Rf_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rf_!(E ⊗^L_{Λ₁} Λ₂)` is an isomorphism, given proper base change for
torsion abelian sheaves (`h095T`) and the vanishing of the cohomology of curves (`h03SC`), the two
inputs of `exists_isZero_rightDerived_etaleModuleDirectImage_of_isProper_of_fiberDim`. -/
theorem isIso_derivedLowerShriekUnboundedExtendScalarsMap
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (h03SC : CurveTorsionCohomologyStatement.{u, r})
    (hΛ₁ : ∀ x : Λ₁, ∃ n : ℕ, 0 < n ∧ (n : Λ₁) * x = 0)
    {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) :
    IsIso (derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j) := by
  -- given by its term: in this module's import closure instance search for
  -- `QuasiSeparated j.toBase` runs out of heartbeats
  have : QuasiSeparated j.toBase := IsSeparated.instQuasiSeparated j.toBase
  have hP : IsProper j.toBase := j.property.2
  obtain ⟨N, hN⟩ := @AlgebraicGeometry.exists_topologicalKrullDim_fiber_le _ _ j.toBase
    hP.toLocallyOfFiniteType
    (@AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _ _ _ hP.toUniversallyClosed) ‹_›
  have := isIso_derivedDirectImageUnboundedExtendScalarsMap φ j.toBase
    (exists_isZero_rightDerived_etaleModuleDirectImage_of_isProper_of_fiberDim h095T h03SC Λ₁ hΛ₁
      j.toBase N hN)
  have : ∀ E, IsIso ((derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j).app E) :=
    fun E => isIso_derivedLowerShriekUnboundedExtendScalarsMap_app_of_isIso φ f j E
      inferInstance inferInstance
  exact NatIso.isIso_of_isIso_app _

/-- The second diagram of [Stacks, Remark 0GL6] as the existence of a natural isomorphism
`Rf_!(-) ⊗^L_{Λ₁} Λ₂ ≅ Rf_!(- ⊗^L_{Λ₁} Λ₂)`, under the hypotheses of
`isIso_derivedLowerShriekUnboundedExtendScalarsMap`. -/
theorem nonempty_derivedLowerShriekUnboundedExtendScalarsIso
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, r} p)
    (h03SC : CurveTorsionCohomologyStatement.{u, r})
    (hΛ₁ : ∀ x : Λ₁, ∃ n : ℕ, 0 < n ∧ (n : Λ₁) * x = 0)
    {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) (j : CompactificationOf (Over.mk f)) :
    Nonempty (derivedLowerShriekUnbounded.{u, r} f j Λ₁ ⋙ etaleModuleDerivedExtendScalars.{u, r} φ
        Y ≅
      etaleModuleDerivedExtendScalars.{u, r} φ X ⋙ derivedLowerShriekUnbounded.{u, r} f j Λ₂) :=
  have := isIso_derivedLowerShriekUnboundedExtendScalarsMap φ h095T h03SC hΛ₁ f j
  ⟨asIso (derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j)⟩

end Stacks.EtaleCohomology

end

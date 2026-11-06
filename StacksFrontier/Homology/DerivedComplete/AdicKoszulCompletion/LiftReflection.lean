module

public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion.Construction
import all Mathlib.CategoryTheory.Discrete.Basic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Functorial Koszul power completion: reflection along universe enlargement

Universe enlargement of the derived category of modules reflects vanishing of cohomology,
isomorphisms, and vanishing of scalar-tower derived limits. This proves
`KoszulCompletion.UniverseLiftComparisonLaws`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace KoszulLiftReflectionAudit

attribute [local instance] KoszulCompletion.derivedCountableProducts

/-- An exact additive functor commutes with the cohomology objects of the derived category:
`Hⁿ(D(F)(X)) ≅ F(Hⁿ(X))`. The isomorphism is obtained by choosing a cochain complex
representing `X` and transporting the degreewise identification along the localization `Q`. -/
public noncomputable def homologyMapDerivedCategoryObjIso
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (degree : ℤ) :
    (DerivedCategory.homologyFunctor D degree).obj (F.mapDerivedCategory.obj X) ≅
      F.obj ((DerivedCategory.homologyFunctor C degree).obj X) := by
  let representative := DerivedCategory.Q.objPreimage X
  let comparison : DerivedCategory.Q.obj representative ≅ X :=
    DerivedCategory.Q.objObjPreimageIso X
  exact (DerivedCategory.homologyFunctor D degree).mapIso
      (F.mapDerivedCategory.mapIso comparison.symm) ≪≫
    (DerivedCategory.homologyFunctor D degree).mapIso
      (F.mapDerivedCategoryFactors.app representative) ≪≫
    (DerivedCategory.homologyFunctorFactors D degree).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj representative) ≪≫
    (representative.sc degree).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C degree).app representative).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor C degree).mapIso comparison)

/-- A faithful exact functor reflects vanishing of cohomology. -/
theorem isZero_homology_mapDerivedCategory_iff
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (X : DerivedCategory C) (degree : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor D degree).obj (F.mapDerivedCategory.obj X)) ↔
      IsZero ((DerivedCategory.homologyFunctor C degree).obj X) := by
  rw [(homologyMapDerivedCategoryObjIso F X degree).isZero_iff]
  refine ⟨fun vanishing ↦ (IsZero.iff_id_eq_zero _).mpr <| F.map_injective ?_, F.map_isZero⟩
  rw [F.map_id, F.map_zero]
  exact vanishing.eq_zero_of_src (𝟙 _)

private theorem isZero_iff_isIso_zero
    {C : Type*} [Category* C] [HasZeroMorphisms C] (X : C) :
    IsZero X ↔ IsIso (0 : X ⟶ X) :=
  ⟨fun vanishing => (isIsoZeroSelfEquiv X).symm ((IsZero.iff_id_eq_zero X).1 vanishing),
    fun invertible => (IsZero.iff_id_eq_zero X).2 (isIsoZeroSelfEquiv X invertible)⟩

private theorem isZero_iff_homology_zero
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (X : DerivedCategory C) :
    IsZero X ↔ ∀ degree : ℤ, IsZero ((DerivedCategory.homologyFunctor C degree).obj X) := by
  rw [isZero_iff_isIso_zero, DerivedCategory.isIso_iff]
  refine forall_congr' fun degree => ?_
  rw [(DerivedCategory.homologyFunctor C degree).map_zero, ← isZero_iff_isIso_zero]

private theorem isZero_mapDerivedCategory_iff
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (X : DerivedCategory C) :
    IsZero (F.mapDerivedCategory.obj X) ↔ IsZero X := by
  rw [isZero_iff_homology_zero, isZero_iff_homology_zero]
  exact forall_congr' fun degree => isZero_homology_mapDerivedCategory_iff F X degree

private theorem isIso_mapDerivedCategory_iff
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] {X Y : DerivedCategory C} (morphism : X ⟶ Y) :
    IsIso (F.mapDerivedCategory.map morphism) ↔ IsIso morphism := by
  refine ⟨fun invertible ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨cone, next, boundary, distinguished⟩ := distinguished_cocone_triangle morphism
  have mappedZero : IsZero (F.mapDerivedCategory.obj cone) :=
    (Triangle.isZero₃_iff_isIso₁ _
      (F.mapDerivedCategory.map_distinguished _ distinguished)).2 invertible
  exact (Triangle.isZero₃_iff_isIso₁ _ distinguished).1
    ((isZero_mapDerivedCategory_iff F cone).1 mappedZero)


private theorem derivedUniverseLift_isZero_iff
    (A : Type u) [CommRing A] (X : DerivedCategory (ModuleCat.{v} A)) :
    IsZero ((AdicKoszul.derivedUniverseLift.{u, v} A).obj X) ↔ IsZero X :=
  isZero_mapDerivedCategory_iff (AdicKoszul.moduleUniverseLift.{u, v} A) X

private theorem derivedUniverseLift_isIso_map_iff
    (A : Type u) [CommRing A] {X Y : DerivedCategory (ModuleCat.{v} A)}
    (morphism : X ⟶ Y) :
    IsIso ((AdicKoszul.derivedUniverseLift.{u, v} A).map morphism) ↔ IsIso morphism :=
  isIso_mapDerivedCategory_iff (AdicKoszul.moduleUniverseLift.{u, v} A) morphism

private abbrev sequenceDifference
    {C : Type*} [Category* C] [Preadditive C]
    (objects : ℕ → C) [HasProduct objects]
    (transition : ∀ index, objects (index + 1) ⟶ objects index) :
    (∏ᶜ objects) ⟶ ∏ᶜ objects :=
  Pi.lift fun index => Pi.π objects index - Pi.π objects (index + 1) ≫ transition index

private theorem exists_zero_limit_iff_difference
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ degree : ℤ, (shiftFunctor C degree).Additive] [Pretriangulated C]
    (objects : ℕ → C) [HasProductsOfShape ℕ C]
    (transition : ∀ index, objects (index + 1) ⟶ objects index) :
    (∃ limitObject, IsDerivedLimit (Functor.ofOpSequence transition) limitObject ∧
      IsZero limitObject) ↔ IsIso (sequenceDifference objects transition) := by
  constructor
  · rintro ⟨limitObject, ⟨projection, boundary, distinguished⟩, vanishing⟩
    have invertible := (Triangle.isZero₁_iff_isIso₂ _ distinguished).1 vanishing
    simpa only [Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂, Functor.ofOpSequence_obj,
      Functor.ofOpSequence_map_homOfLE_succ] using! invertible
  · intro invertible
    obtain ⟨limitObject, projection, boundary, distinguished⟩ :=
      exists_isDerivedLimit (Functor.ofOpSequence transition)
    refine ⟨limitObject, ⟨projection, boundary, distinguished⟩, ?_⟩
    apply (Triangle.isZero₁_iff_isIso₂ _ distinguished).2
    simpa only [Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂, Functor.ofOpSequence_obj,
      Functor.ofOpSequence_map_homOfLE_succ] using! invertible

private theorem map_difference_comparison
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (objects : ℕ → C)
    [HasProduct objects] [HasProduct fun index => F.obj (objects index)]
    (transition : ∀ index, objects (index + 1) ⟶ objects index) :
    F.map (sequenceDifference objects transition) ≫ piComparison F objects =
      piComparison F objects ≫
        sequenceDifference (fun index => F.obj (objects index))
          (fun index => F.map (transition index)) := by
  apply Pi.hom_ext
  intro index
  dsimp only [sequenceDifference]
  rw [Category.assoc, piComparison_comp_π, ← F.map_comp, Pi.lift_comp_π,
    Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, piComparison_comp_π,
    F.map_sub, F.map_comp, ← Category.assoc, piComparison_comp_π]

private theorem isIso_difference_map_iff
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (objects : ℕ → C)
    [HasProduct objects] [HasProduct fun index => F.obj (objects index)]
    [PreservesLimit (Discrete.functor objects) F]
    (transition : ∀ index, objects (index + 1) ⟶ objects index)
    (reflect : IsIso (F.map (sequenceDifference objects transition)) →
      IsIso (sequenceDifference objects transition)) :
    IsIso (sequenceDifference (fun index => F.obj (objects index))
      (fun index => F.map (transition index))) ↔
      IsIso (sequenceDifference objects transition) := by
  have conjugation := map_difference_comparison F objects transition
  constructor
  · intro invertible
    apply reflect
    have equality : F.map (sequenceDifference objects transition) =
        piComparison F objects ≫
          sequenceDifference (fun index => F.obj (objects index))
            (fun index => F.map (transition index)) ≫ inv (piComparison F objects) := by
      rw [← Category.assoc, ← conjugation, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [equality]
    infer_instance
  · intro invertible
    have equality : sequenceDifference (fun index => F.obj (objects index))
        (fun index => F.map (transition index)) =
        inv (piComparison F objects) ≫ F.map (sequenceDifference objects transition) ≫
          piComparison F objects := by
      rw [conjugation, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rw [equality]
    infer_instance

private theorem derivedUniverseLift_zero_mapped_tower_iff
    (A : Type u) [CommRing A]
    (objects : ℕ → DerivedCategory (ModuleCat.{v} A))
    (transition : ∀ index, objects (index + 1) ⟶ objects index) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    letI : HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v} (ULift.{v} A))) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    (∃ limitObject, IsDerivedLimit
        (Functor.ofOpSequence
          (X := fun index => (AdicKoszul.derivedUniverseLift.{u, v} A).obj (objects index))
          (fun index => (AdicKoszul.derivedUniverseLift.{u, v} A).map (transition index)))
        limitObject ∧ IsZero limitObject) ↔
      (∃ limitObject, IsDerivedLimit (Functor.ofOpSequence transition) limitObject ∧
        IsZero limitObject) := by
  rw [exists_zero_limit_iff_difference, exists_zero_limit_iff_difference]
  exact isIso_difference_map_iff (AdicKoszul.derivedUniverseLift.{u, v} A) objects transition
    (derivedUniverseLift_isIso_map_iff A _).1

private theorem complexUniverseLift_map_scalar_identity
    (ring : Type u) [CommRing ring] (scalar : ring)
    (complex : CochainComplex (ModuleCat.{v} ring) ℤ) :
    ((AdicKoszul.moduleUniverseLift.{u, v} ring).mapHomologicalComplex (.up ℤ)).map
        (scalar • 𝟙 complex) =
      (ULift.up scalar : ULift.{v} ring) •
        𝟙 (((AdicKoszul.moduleUniverseLift.{u, v} ring).mapHomologicalComplex (.up ℤ)).obj
          complex) := by
  apply HomologicalComplex.hom_ext
  intro degree
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro element
  rfl

private theorem derivedUniverseLift_map_scalar_identity_Q
    (ring : Type u) [CommRing ring] (scalar : ring)
    (complex : CochainComplex (ModuleCat.{v} ring) ℤ) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map
        (scalar • 𝟙 (DerivedCategory.Q.obj complex)) =
      (ULift.up scalar : ULift.{v} ring) •
        𝟙 ((AdicKoszul.derivedUniverseLift.{u, v} ring).obj
          (DerivedCategory.Q.obj complex)) := by
  let comparison := (AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors
  have naturality := comparison.hom.naturality (scalar • 𝟙 complex)
  change (AdicKoszul.derivedUniverseLift.{u, v} ring).map
      (DerivedCategory.Q.map (scalar • 𝟙 complex)) ≫ comparison.hom.app complex =
    comparison.hom.app complex ≫ DerivedCategory.Q.map
      (((AdicKoszul.moduleUniverseLift.{u, v} ring).mapHomologicalComplex (.up ℤ)).map
        (scalar • 𝟙 complex)) at naturality
  rw [complexUniverseLift_map_scalar_identity] at naturality
  have sourceIdentity :=
    (DerivedCategory.Q (C := ModuleCat.{v} ring)).map_id complex
  have targetIdentity :=
    (DerivedCategory.Q (C := ModuleCat.{max u v} (ULift.{v} ring))).map_id
      (((AdicKoszul.moduleUniverseLift.{u, v} ring).mapHomologicalComplex (.up ℤ)).obj complex)
  simp only [Functor.map_smul] at naturality
  rw [sourceIdentity, targetIdentity] at naturality
  simp only [Linear.comp_smul] at naturality
  replace naturality := naturality.trans
    (congrArg (ULift.up scalar • ·) (Category.comp_id (comparison.hom.app complex)))
  apply (cancel_mono (comparison.hom.app complex)).1
  simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
    using! naturality

private theorem derivedUniverseLift_map_scalar_identity
    (ring : Type u) [CommRing ring] (scalar : ring)
    (object : DerivedCategory (ModuleCat.{v} ring)) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map (scalar • 𝟙 object) =
      (ULift.up scalar : ULift.{v} ring) •
        𝟙 ((AdicKoszul.derivedUniverseLift.{u, v} ring).obj object) := by
  let representative := DerivedCategory.Q.objPreimage object
  let comparison : DerivedCategory.Q.obj representative ≅ object :=
    DerivedCategory.Q.objObjPreimageIso object
  let lift := AdicKoszul.derivedUniverseLift.{u, v} ring
  apply (cancel_epi (lift.map comparison.hom)).1
  calc
    lift.map comparison.hom ≫ lift.map (scalar • 𝟙 object) =
        lift.map ((scalar • 𝟙 (DerivedCategory.Q.obj representative)) ≫ comparison.hom) := by
          rw [← lift.map_comp]
          simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
    _ = lift.map (scalar • 𝟙 (DerivedCategory.Q.obj representative)) ≫
        lift.map comparison.hom := lift.map_comp _ _
    _ = ((ULift.up scalar : ULift.{v} ring) •
          𝟙 (lift.obj (DerivedCategory.Q.obj representative))) ≫
        lift.map comparison.hom := by rw [derivedUniverseLift_map_scalar_identity_Q]
    _ = lift.map comparison.hom ≫ ((ULift.up scalar : ULift.{v} ring) •
        𝟙 (lift.obj object)) := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

theorem universeLiftComparisonLaws
    (ring : Type u) [CommRing ring] :
    KoszulCompletion.UniverseLiftComparisonLaws.{u, v} ring := by
  constructor
  intro scalar object
  have transport := derivedUniverseLift_zero_mapped_tower_iff ring
    (fun _ : ℕ => object) (fun _ => scalar • 𝟙 object)
  simpa only [derivedUniverseLift_map_scalar_identity] using transport


end KoszulLiftReflectionAudit

end

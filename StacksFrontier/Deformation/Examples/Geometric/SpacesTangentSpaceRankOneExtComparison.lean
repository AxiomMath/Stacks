module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleScalar
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentExtModelLinearEquiv
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLinearExtZero
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceClass
public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensionalResidueFieldAction
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceLinear

/-!
# The receptacle at `k` is `Ext¹(NL_{X/k}, 𝒪_X)`

The value at the rank-one module of the receptacle `V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)` of the classes
of deformations of an algebraic space `X` over `k` (`Deformation.Examples.spaceTangentExtFunctor`,
computed on the `Type u` model of the small étale site, `k` acting through the coefficients) is,
`k`-linearly, `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` with `NL_{X/k}` the naive cotangent complex of
Stacks 0D0V (`AlgebraicGeometry.Space.naiveCotangentComplex`, sections in `Type (u + 1)`), the
coefficient `𝒪_X` raised to that universe, in any model of the derived category, and `k` acting
through `Deformation.Examples.spaceResidueFieldRingHom`: the terms of [Stacks Project, Tag 0E41]
and of [Stacks Project, Tag 0E42].

## Main definitions

* `Deformation.Examples.spaceTangentExtRankOneModelLinearEquiv`: the receptacle at `k` is
  `Hom(NL_model, 𝒪_model[1])`.
* `Deformation.Examples.spaceTangentExtRankOneLinearEquiv`: the receptacle at `k` is
  `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Deformation.AlgebraExtension Stacks.Cohomology.SiteModules

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- The rings of sections of the structure sheaf of the model, read as a sheaf of rings, are
commutative. -/
local instance isMulCommutative_ringSheafOfSite_smallEtaleModelStructureSheaf_obj
    (V : (SmallEtaleModel B (Spec (.of Λ)) hΛ X)ᵒᵖ) :
    IsMulCommutative ((ringSheafOfSite
      (smallEtaleModelStructureSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))).obj.obj V) :=
  ⟨⟨fun a b => mul_comm (G := (structureSheaf B (Spec (.of Λ)) hΛ X hX).obj.obj
    (op ((smallEtaleModelEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).inverse.obj V.unop))) a b⟩⟩

/-- The action of `k` on the model of the small étale site of `X` through the structure
morphism. -/
abbrev spaceModelResidueRingHom :
    k →+* GlobalSectionRing (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) :=
  (modelRestrictGlobalSections B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).comp
    (spaceResidueFieldRingHom B hΛ hSpec X hX toK)

/-- `V ↦ (𝒪_X ⊗_k V)[1]` in the derived category of the model of the small étale site of `X`. -/
abbrev spaceTangentModelCoefficientFunctor :
    FGModuleCat.{u} k ⥤
      DerivedCategory
        (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) :=
  forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k) ⋙
    (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK) ⋙
      (modelModulesEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).functor ⋙
      DerivedCategory.singleFunctor
        (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) 0 ⋙
      shiftFunctor (DerivedCategory
        (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)))) (1 : ℤ))

/-- The naive cotangent complex of the model, in the derived category of
`Deformation.Examples.spaceTangentModelCoefficientFunctor`. -/
abbrev spaceModelNaiveCotangent :
    DerivedCategory (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) :=
  DerivedCategory.Q.obj (modelNaiveCotangentComplex B (Spec (.of Λ)) hΛ
    (spaceStructureMap B hΛ hSpec X hX toK))

/-- The receptacle at `V` read in the spelling of
`Deformation.Examples.spaceTangentModelCoefficientFunctor` (the identity). -/
def spaceTangentExtObjEquiv (V : FGModuleCat.{u} k) :
    (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj V ≃
      (spaceModelNaiveCotangent B hΛ hSpec X hX toK ⟶
        (spaceTangentModelCoefficientFunctor B hΛ hSpec X hX toK).obj V) :=
  Equiv.refl _

/-- The identification of spellings is compatible with postcomposition. -/
theorem spaceTangentExtObjEquiv_comp_map {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    (ξ : (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj V) :
    spaceTangentExtObjEquiv B hΛ hSpec X hX toK W
        ((spaceTangentExtFunctor B hΛ hSpec X hX toK).map g ξ) =
      spaceTangentExtObjEquiv B hΛ hSpec X hX toK V ξ ≫
        (spaceTangentModelCoefficientFunctor B hΛ hSpec X hX toK).map g :=
  rfl

/-- The identification of spellings carries the action of `k` on the receptacle to
postcomposition with the coefficients of `c • 𝟙`. -/
theorem spaceTangentExtObjEquiv_smul (V : FGModuleCat.{u} k) (c : k)
    (ξ : (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj V) :
    spaceTangentExtObjEquiv B hΛ hSpec X hX toK V (c • ξ) =
      spaceTangentExtObjEquiv B hΛ hSpec X hX toK V ξ ≫
        (spaceTangentModelCoefficientFunctor B hΛ hSpec X hX toK).map (c • 𝟙 V) :=
  rfl

/-- **`𝒪_X ⊗_k k ≅ 𝒪_X` on the model.** -/
def spaceTangentCoefficientRankOneIso :
    (modelModulesEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).functor.obj
        ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj (ModuleCat.of k k)) ≅
      SheafOfModules.unit (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) :=
  (modelModulesEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).functor.mapIso
      (baseRingTensorModuleSelfIso B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX) _) ≪≫
    modelModulesEquivUnitIso B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)

/-- **`𝒪_X ⊗_k -` carries multiplication by `c` on `k` to multiplication by the function `c`**,
on the model. -/
theorem spaceTangentCoefficient_map_smul (c : k) :
    (modelModulesEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).functor.map
        ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (spaceDefoFieldHom B hΛ hSpec X hX toK)).map
          (ModuleCat.ofHom (c • LinearMap.id : k →ₗ[k] k))) =
      globalSmul (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
        (spaceModelResidueRingHom B hΛ hSpec X hX toK c) _ :=
  (baseRingTensorModule_comp_scalarMap B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK) c).trans
    (Stacks.SheafOfModules.linearOver_smul_id _ (spaceDefoFieldHom B hΛ hSpec X hX toK) _ c)

/-- The scalar compatibility, read through `𝒪_X ⊗_k k ≅ 𝒪_X`. -/
theorem spaceTangentCoefficient_map_smul_comp (c : k) :
    (modelModulesEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).functor.map
        ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (spaceDefoFieldHom B hΛ hSpec X hX toK)).map
          (ModuleCat.ofHom (c • LinearMap.id : k →ₗ[k] k))) ≫
        (spaceTangentCoefficientRankOneIso B hΛ hSpec X hX toK).hom =
      (spaceTangentCoefficientRankOneIso B hΛ hSpec X hX toK).hom ≫
        globalSmul (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
          (spaceModelResidueRingHom B hΛ hSpec X hX toK c) _ := by
  rw [spaceTangentCoefficient_map_smul, comp_globalSmul]

/-- The coefficients `(𝒪_X ⊗_k k)[1] ≅ 𝒪_X[1]` in the derived category of the model. -/
def spaceTangentCoefficientRankOneShiftIso :
    (spaceTangentModelCoefficientFunctor B hΛ hSpec X hX toK).obj (FGModuleCat.of k k) ≅
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) 0).obj
        (SheafOfModules.unit (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))))⟦(1 : ℤ)⟧ :=
  (shiftFunctor (DerivedCategory
      (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)))) (1 : ℤ)).mapIso
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) 0).mapIso
      (spaceTangentCoefficientRankOneIso B hΛ hSpec X hX toK))

/-- The coefficient functor carries `c • 𝟙_k` to multiplication by the function `c`. -/
theorem spaceTangentModelCoefficientFunctor_map_smul_comp (c : k) :
    (spaceTangentModelCoefficientFunctor B hΛ hSpec X hX toK).map (c • 𝟙 (FGModuleCat.of k k)) ≫
        (spaceTangentCoefficientRankOneShiftIso B hΛ hSpec X hX toK).hom =
      (spaceTangentCoefficientRankOneShiftIso B hΛ hSpec X hX toK).hom ≫
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) 0).map
          (globalSmul (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
            (spaceModelResidueRingHom B hΛ hSpec X hX toK c) _))⟦(1 : ℤ)⟧' := by
  have e : (spaceTangentModelCoefficientFunctor B hΛ hSpec X hX toK).map
      (c • 𝟙 (FGModuleCat.of k k)) =
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) 0).map
        ((modelModulesEquiv B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).functor.map
          ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
            (spaceDefoFieldHom B hΛ hSpec X hX toK)).map
            (ModuleCat.ofHom (c • LinearMap.id : k →ₗ[k] k)))))⟦(1 : ℤ)⟧' :=
    rfl
  rw [e]
  simp only [spaceTangentCoefficientRankOneShiftIso, Functor.mapIso_hom, ← Functor.map_comp]
  rw [spaceTangentCoefficient_map_smul_comp]

/-- **The receptacle at `k` is `Hom(NL_model, 𝒪_model[1])`, `k`-linearly**, `k` acting on the
model through the structure morphism. -/
def spaceTangentExtRankOneModelLinearEquiv :
    letI : Linear k (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) :=
      Stacks.SheafOfModules.linearOver _ ((modelRestrictGlobalSections B (Spec (.of Λ)) hΛ
        (spaceOf B hΛ X hX)).comp (spaceResidueFieldRingHom B hΛ hSpec X hX toK))
    (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj (FGModuleCat.of k k) ≃ₗ[k]
      (spaceModelNaiveCotangent B hΛ hSpec X hX toK ⟶
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) 0).obj
          (SheafOfModules.unit
            (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))))⟦(1 : ℤ)⟧) :=
  letI : Linear k (SheafOfModules.{u} (modelRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) :=
    Stacks.SheafOfModules.linearOver _ ((modelRestrictGlobalSections B (Spec (.of Λ)) hΛ
      (spaceOf B hΛ X hX)).comp (spaceResidueFieldRingHom B hΛ hSpec X hX toK))
  { toFun := fun ξ => spaceTangentExtObjEquiv B hΛ hSpec X hX toK _ ξ ≫
      (spaceTangentCoefficientRankOneShiftIso B hΛ hSpec X hX toK).hom
    invFun := fun η => (spaceTangentExtObjEquiv B hΛ hSpec X hX toK _).symm
      (η ≫ (spaceTangentCoefficientRankOneShiftIso B hΛ hSpec X hX toK).inv)
    left_inv := fun ξ => by
      change (spaceTangentExtObjEquiv B hΛ hSpec X hX toK _).symm (_ ≫ _) = ξ
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Equiv.symm_apply_apply]
    right_inv := fun η => by
      change spaceTangentExtObjEquiv B hΛ hSpec X hX toK _
        ((spaceTangentExtObjEquiv B hΛ hSpec X hX toK _).symm _) ≫ _ = η
      rw [Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    map_add' := fun ξ η => Preadditive.add_comp _ _ _ _ _ _
    map_smul' := fun c ξ => by
      change spaceTangentExtObjEquiv B hΛ hSpec X hX toK _ (c • ξ) ≫ _ =
        c • (spaceTangentExtObjEquiv B hΛ hSpec X hX toK _ ξ ≫ _)
      rw [spaceTangentExtObjEquiv_smul, smul_eq_comp_singleFunctor_map,
        Stacks.SheafOfModules.linearOver_smul_id, Category.assoc, Category.assoc,
        spaceTangentModelCoefficientFunctor_map_smul_comp] }

/-- **The receptacle at `k` is `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`, `k`-linearly**, in the spelling of
`AlgebraicGeometry.Space.modelHomLinearEquivNaiveCotangentExt`: `𝒪_X` is the unit module raised to
the universe of `NL_{X/k}` and `k` acts through `Stacks.SheafOfModules.linearOver`. -/
def spaceTangentExtRankOneLinearEquivUliftUnit
    [HasDerivedCategory.{w} (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX)))] :
    letI : Linear k (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX))) :=
      Stacks.SheafOfModules.linearOver _ (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj (FGModuleCat.of k k) ≃ₗ[k]
      DerivedCategory.Ext
        (DerivedCategory.Q.obj (Space.naiveCotangentComplex B (Spec (.of Λ)) hΛ
          (spaceStructureMap B hΛ hSpec X hX toK)))
        ((DerivedCategory.singleFunctor _ 0).obj (Stacks.SheafOfModules.uliftUnit.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX))))
        1 :=
  (spaceTangentExtRankOneModelLinearEquiv B hΛ hSpec X hX toK).trans
    (modelHomLinearEquivNaiveCotangentExt B (Spec (.of Λ)) hΛ
      (spaceStructureMap B hΛ hSpec X hX toK) (spaceResidueFieldRingHom B hΛ hSpec X hX toK) 1)

/-- **The receptacle at `k` is `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`, `k`-linearly.** `NL_{X/k}` is the naive
cotangent complex of Stacks 0D0V at the structure morphism, the coefficient is `𝒪_X` with its
sections raised to the universe of `NL_{X/k}`
(`AlgebraicGeometry.Space.naiveCotangentCoefficient`), the derived category is any model, and `k`
acts through `Deformation.Examples.spaceResidueFieldRingHom`: the terms of the first display of
Stacks 0E41 and of `Deformation.Examples.moduleFinite_spaceNaiveCotangentExt`. -/
def spaceTangentExtRankOneLinearEquiv
    [HasDerivedCategory.{w} (Space.NaiveCotangentModules B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))] :
    letI := Space.naiveCotangentModulesLinear B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj (FGModuleCat.of k k) ≃ₗ[k]
      DerivedCategory.Ext
        (DerivedCategory.Q.obj (Space.naiveCotangentComplex B (Spec (.of Λ)) hΛ
          (spaceStructureMap B hΛ hSpec X hX toK)))
        ((DerivedCategory.singleFunctor _ 0).obj
          (Space.naiveCotangentCoefficient B (Spec (.of Λ)) hΛ
            (spaceStructureModule B hΛ (spaceOf B hΛ X hX)))) 1 :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.structureSheaf B (Spec (.of Λ)) hΛ X hX))) :=
    inferInstanceAs (HasDerivedCategory.{w} (Space.NaiveCotangentModules B (Spec (.of Λ)) hΛ
      (spaceOf B hΛ X hX)))
  letI := Space.naiveCotangentModulesLinear B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
    (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
  (spaceTangentExtRankOneLinearEquivUliftUnit B hΛ hSpec X hX toK).trans
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

end Deformation.Examples

end

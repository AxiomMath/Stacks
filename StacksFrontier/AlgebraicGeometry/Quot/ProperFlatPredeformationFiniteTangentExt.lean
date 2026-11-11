module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatPredeformationFiniteTangentClass
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceRankOneExtComparison
public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensionalExt

/-!
# The receptacle `Ext¹(NL_{X₀/k}, 𝒪_{X₀})` of a point of `Spaces'_{fp, flat, proper}` is finite

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `Spaces'_{fp, flat, proper}` over the big fppf site of an
arbitrary scheme `S`, over the spectrum of a field `k`. The value at `k` of the receptacle
`V ↦ Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)` of the classes of deformations of `x₀`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtFunctor`, computed on the `Type u` model
of the small étale site and with `k` acting through the coefficients) is a finite-dimensional
`k`-vector space.

The proof is the source's (the argument of Stacks 0D1K, through Stacks 0E42): the value at `k`
is, `k`-linearly, `Ext¹_{𝒪_{X₀}}(NL_{X₀/k}, 𝒪_{X₀})`; `NL_{X₀/k}` has coherent cohomology
sheaves, zero outside degrees `-1` and `0` (Stacks 0D0Y, 0D0Z for `X₀` of finite type over
`k`), and on the proper `X₀` the `Ext` groups from `D⁻_Coh` into `D⁺_Coh` are finite over the
affine `Spec k` (Stacks 0D0T). This is the argument of
`Deformation.Examples.moduleFinite_spaceNaiveCotangentExt` and
`Deformation.Examples.spaceTangentExtRankOneLinearEquiv`, carried out for the space of `x₀`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.finiteDimensional_tangentExtFunctor_obj`

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Deformation Deformation.Artin Deformation.AlgebraExtension AlgebraicGeometry.Space
open Stacks.Cohomology.SiteModules

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace CategoryTheory.Functor

variable {k : Type u} [Field k] {C : Type*} [Category.{u} C] [Preadditive C]
  [CategoryTheory.Linear k C]
  (F : FGModuleCat.{u} k ⥤ C) [F.Additive] (X : C) {Y : C} (e : F.obj (FGModuleCat.of k k) ≅ Y)
  (he : ∀ c : k, F.map (c • 𝟙 (FGModuleCat.of k k)) ≫ e.hom = e.hom ≫ (c • 𝟙 Y))

/-- **`Hom(X, F(k)) ≃ Hom(X, Y)`, `k`-linearly**, for an identification `F(k) ≅ Y` carrying the
scalar endomorphisms `F(c • 𝟙_k)` to the scalars of the `k`-linear category. -/
def homFunctorOfAdditiveObjLinearEquiv :
    (F.homFunctorOfAdditive X).obj (FGModuleCat.of k k) ≃ₗ[k] (X ⟶ Y) :=
  have key₁ : ∀ ξ : X ⟶ F.obj (FGModuleCat.of k k), (ξ ≫ e.hom) ≫ e.inv = ξ := fun ξ => by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key₂ : ∀ η : X ⟶ Y, (η ≫ e.inv) ≫ e.hom = η := fun η => by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have key₃ : ∀ (c : k) (ξ : X ⟶ F.obj (FGModuleCat.of k k)),
      (ξ ≫ F.map (c • 𝟙 (FGModuleCat.of k k))) ≫ e.hom = c • (ξ ≫ e.hom) := fun c ξ => by
    rw [Category.assoc, he, ← Category.assoc, CategoryTheory.Linear.comp_smul, Category.comp_id]
  { toFun := fun ξ => (ξ : X ⟶ F.obj (FGModuleCat.of k k)) ≫ e.hom
    invFun := fun η => (η ≫ e.inv : X ⟶ F.obj (FGModuleCat.of k k))
    left_inv := fun ξ => key₁ ξ
    right_inv := fun η => key₂ η
    map_add' := fun ξ η => Preadditive.add_comp _ _ _ _ _ _
    map_smul' := fun c ξ => key₃ c ξ }

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

/-! ### The receptacle of a morphism to an affine object, in general -/

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {k : Type u} [Field k]
  {X : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS} (g : X ⟶ schemeSpace V)
  (γ : k →+* baseRing B S hS V)

/-- The rings of sections of the structure sheaf of the model, read as a sheaf of rings, are
commutative. -/
local instance isMulCommutative_ringSheafOfSite_smallEtaleModelStructureSheaf_obj'
    (W : (SmallEtaleModel B S hS X.1)ᵒᵖ) :
    IsMulCommutative ((ringSheafOfSite
      (smallEtaleModelStructureSheaf B S hS X)).obj.obj W) :=
  ⟨⟨fun a b => mul_comm (G := (structureSheaf B S hS X.1 X.2).obj.obj
    (op ((smallEtaleModelEquiv B S hS X).inverse.obj W.unop))) a b⟩⟩

/-- The action of `k` on the global functions of the model of `X` through `g` and
`γ : k ⟶ Γ(V)`. -/
abbrev fieldHomOfMap : k →+* modelGlobalFunctions B S hS X :=
  (baseRingHomOfMap g).comp γ

/-- The action of `k` on the global functions of `X` through `g` and `γ : k ⟶ Γ(V)`. -/
abbrev residueRingHomOfMap :
    k →+* GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheaf B S hS X.1 X.2)) :=
  (pullbackToGlobalFunctions B S hS X V g).comp γ

/-- The action of `k` on the model of the small étale site of `X` through `g`. -/
abbrev modelResidueRingHomOfMap : k →+* GlobalSectionRing (modelRingSheaf B S hS X) :=
  (modelRestrictGlobalSections B S hS X).comp (residueRingHomOfMap B S hS g γ)

/-- **`M ↦ (𝒪_X ⊗_k M)[1]`** from `k`-modules to the derived category of modules on the model of
the small étale site of `X`, `k` acting through `g` and `γ`. -/
abbrev classDefoFunctor :=
  baseRingTensorModule B S hS X (fieldHomOfMap B S hS g γ) ⋙
    moduleRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse
      (structureSheaf B S hS X.1 X.2) ⋙
    DerivedCategory.singleFunctor (SheafOfModules.{u}
      ((sheafCompose (smallEtaleModelTopology B S hS X.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((ringRes (smallEtaleModelTopology B S hS X.1)
          (modelEquiv B S hS X).inverse).obj
          (structureSheaf B S hS X.1 X.2)))) 0 ⋙
    shiftFunctor _ (1 : ℤ)

/-- The functor `M ↦ (𝒪_X ⊗_k M)[1]` is additive. -/
instance : (classDefoFunctor B S hS g γ).Additive := by
  have := baseRingTensorModule_additive B S hS X (fieldHomOfMap B S hS g γ)
  have : (moduleRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse
      (structureSheaf B S hS X.1 X.2)).Additive := ⟨rfl⟩
  exact ⟨fun {M N f g'} => (congrArg (moduleRes (smallEtaleModelTopology B S hS X.1)
      (modelEquiv B S hS X).inverse (structureSheaf B S hS X.1 X.2) ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).map
      ((baseRingTensorModule B S hS X (fieldHomOfMap B S hS g γ)).map_add
        (f := f) (g := g'))).trans (Functor.map_add _)⟩

/-- **`V ↦ (𝒪_X ⊗_k V)[1]`** on finite-dimensional `k`-vector spaces. -/
abbrev classCoefficientFunctor :=
  forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k) ⋙ classDefoFunctor B S hS g γ

/-- The functor `V ↦ (𝒪_X ⊗_k V)[1]` is additive. -/
instance : (classCoefficientFunctor B S hS g γ).Additive :=
  inferInstance

/-- **The receptacle `V ↦ Ext¹(NL_{X/V}, 𝒪_X ⊗_k V)`** of a morphism `g : X ⟶ V` to an object of
the site, `k` acting on `𝒪_X` through `g` and `γ : k ⟶ Γ(V)`. -/
abbrev classExtFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{u} k :=
  (classCoefficientFunctor B S hS g γ).homFunctorOfAdditive
    (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS g))

/-- `V ↦ (𝒪_X ⊗_k V)[1]` in the spelling of the model modules. -/
abbrev classModelCoefficientFunctor :
    FGModuleCat.{u} k ⥤ DerivedCategory (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
  forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k) ⋙
    (baseRingTensorModule B S hS X (fieldHomOfMap B S hS g γ) ⋙
      (modelModulesEquiv B S hS X).functor ⋙
      DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0 ⋙
      shiftFunctor (DerivedCategory (SheafOfModules.{u} (modelRingSheaf B S hS X))) (1 : ℤ))

/-- The functor `V ↦ (𝒪_X ⊗_k V)[1]`, in the spelling of the model modules, is additive. -/
instance : (classModelCoefficientFunctor B S hS g γ).Additive := by
  have := baseRingTensorModule_additive B S hS X (fieldHomOfMap B S hS g γ)
  infer_instance

/-- **`𝒪_X ⊗_k k ≅ 𝒪_X` on the model.** -/
def classCoefficientRankOneIso :
    (modelModulesEquiv B S hS X).functor.obj
        ((baseRingTensorModule B S hS X (fieldHomOfMap B S hS g γ)).obj (ModuleCat.of k k)) ≅
      SheafOfModules.unit (modelRingSheaf B S hS X) :=
  (modelModulesEquiv B S hS X).functor.mapIso (baseRingTensorModuleSelfIso B S hS X _) ≪≫
    modelModulesEquivUnitIso B S hS X

/-- **`𝒪_X ⊗_k -` carries multiplication by `c` on `k` to multiplication by the function `c`**,
on the model. -/
theorem classCoefficient_map_smul (c : k) :
    (modelModulesEquiv B S hS X).functor.map
        ((baseRingTensorModule B S hS X (fieldHomOfMap B S hS g γ)).map
          (ModuleCat.ofHom (c • LinearMap.id : k →ₗ[k] k))) =
      globalSmul (modelRingSheaf B S hS X) (modelResidueRingHomOfMap B S hS g γ c) _ :=
  (baseRingTensorModule_comp_scalarMap B S hS X (fieldHomOfMap B S hS g γ) c).trans
    (Stacks.SheafOfModules.linearOver_smul_id _ (fieldHomOfMap B S hS g γ) _ c)

/-- The scalar compatibility, read through `𝒪_X ⊗_k k ≅ 𝒪_X`. -/
theorem classCoefficient_map_smul_comp (c : k) :
    (modelModulesEquiv B S hS X).functor.map
        ((baseRingTensorModule B S hS X (fieldHomOfMap B S hS g γ)).map
          (ModuleCat.ofHom (c • LinearMap.id : k →ₗ[k] k))) ≫
        (classCoefficientRankOneIso B S hS g γ).hom =
      (classCoefficientRankOneIso B S hS g γ).hom ≫
        globalSmul (modelRingSheaf B S hS X) (modelResidueRingHomOfMap B S hS g γ c) _ := by
  rw [classCoefficient_map_smul, comp_globalSmul]

/-- The coefficients `(𝒪_X ⊗_k k)[1] ≅ 𝒪_X[1]` in the derived category of the model. -/
def classCoefficientRankOneShiftIso :
    (classModelCoefficientFunctor B S hS g γ).obj (FGModuleCat.of k k) ≅
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0).obj
        (SheafOfModules.unit (modelRingSheaf B S hS X)))⟦(1 : ℤ)⟧ :=
  (shiftFunctor (DerivedCategory (SheafOfModules.{u} (modelRingSheaf B S hS X))) (1 : ℤ)).mapIso
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0).mapIso
      (classCoefficientRankOneIso B S hS g γ))

/-- The coefficient functor carries `c • 𝟙_k` to multiplication by the function `c`. -/
theorem classModelCoefficientFunctor_map_smul_comp (c : k) :
    (classModelCoefficientFunctor B S hS g γ).map (c • 𝟙 (FGModuleCat.of k k)) ≫
        (classCoefficientRankOneShiftIso B S hS g γ).hom =
      (classCoefficientRankOneShiftIso B S hS g γ).hom ≫
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0).map
          (globalSmul (modelRingSheaf B S hS X)
            (modelResidueRingHomOfMap B S hS g γ c) _))⟦(1 : ℤ)⟧' := by
  have e : (classModelCoefficientFunctor B S hS g γ).map (c • 𝟙 (FGModuleCat.of k k)) =
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0).map
        ((modelModulesEquiv B S hS X).functor.map
          ((baseRingTensorModule B S hS X (fieldHomOfMap B S hS g γ)).map
            (ModuleCat.ofHom (c • LinearMap.id : k →ₗ[k] k)))))⟦(1 : ℤ)⟧' :=
    rfl
  rw [e]
  simp only [classCoefficientRankOneShiftIso, Functor.mapIso_hom, ← Functor.map_comp]
  rw [classCoefficient_map_smul_comp]

/-- Multiplication by the function `c` on `𝒪_model[1]` is the scalar `c`, for the action of `k`
through `g`. -/
theorem shift_singleFunctor_map_globalSmul_eq_smul (c : k) :
    letI : Linear k (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
      Stacks.SheafOfModules.linearOver _ (modelResidueRingHomOfMap B S hS g γ)
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0).map
        (globalSmul (modelRingSheaf B S hS X) (modelResidueRingHomOfMap B S hS g γ c)
          _))⟦(1 : ℤ)⟧' =
      c • 𝟙 (((DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0).obj
        (SheafOfModules.unit (modelRingSheaf B S hS X)))⟦(1 : ℤ)⟧) := by
  let : Linear k (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
    Stacks.SheafOfModules.linearOver _ (modelResidueRingHomOfMap B S hS g γ)
  rw [← Stacks.SheafOfModules.linearOver_smul_id]
  exact (Category.id_comp _).symm.trans
    (Deformation.Examples.smul_eq_comp_singleFunctor_map (𝟙 _) c).symm

/-- **The receptacle at `k` is `Hom(NL_model, 𝒪_model[1])`, `k`-linearly**, `k` acting on the
model through `g`. -/
def classExtRankOneModelLinearEquiv :
    letI : Linear k (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
      Stacks.SheafOfModules.linearOver _ (modelResidueRingHomOfMap B S hS g γ)
    ((classModelCoefficientFunctor B S hS g γ).homFunctorOfAdditive
        (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS g))).obj
          (FGModuleCat.of k k) ≃ₗ[k]
      (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS g) ⟶
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0).obj
          (SheafOfModules.unit (modelRingSheaf B S hS X)))⟦(1 : ℤ)⟧) :=
  letI : Linear k (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
    Stacks.SheafOfModules.linearOver _ (modelResidueRingHomOfMap B S hS g γ)
  Functor.homFunctorOfAdditiveObjLinearEquiv (classModelCoefficientFunctor B S hS g γ)
    (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS g))
    (classCoefficientRankOneShiftIso B S hS g γ)
    (fun c => (classModelCoefficientFunctor_map_smul_comp B S hS g γ c).trans
      (congrArg ((classCoefficientRankOneShiftIso B S hS g γ).hom ≫ ·)
        (shift_singleFunctor_map_globalSmul_eq_smul B S hS g γ c)))

variable {g} (hγ : Function.Surjective γ) (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] (hg : IsProper B S hS g.hom)

include hγ hVaff hg in
/-- **`Ext^i(NL_{X/V}, 𝒪_X)` is finite over `k` for `g : X ⟶ V` proper over an affine noetherian
`V` and `k ⟶ Γ(V)` surjective**, `NL_{X/V}` the naive cotangent complex of Stacks 0D0V, the
coefficient the unit module at the universe of its sections: `NL_{X/V}` has coherent cohomology
sheaves, zero outside degrees `-1` and `0` (Stacks 0D0Z), and the `Ext` groups from `D⁻_Coh` into
`D⁺_Coh` are finite (Stacks 0D0T). -/
theorem moduleFinite_naiveCotangentExt_of_isProper
    [HasDerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))] (i : ℤ) :
    letI : Linear k (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (structureSheaf B S hS X.1 X.2))) :=
      Stacks.SheafOfModules.linearOver _ (residueRingHomOfMap B S hS g γ)
    Module.Finite k (DerivedCategory.Ext
      (DerivedCategory.Q.obj (naiveCotangentComplex B S hS g))
      ((DerivedCategory.singleFunctor _ 0).obj (Stacks.SheafOfModules.uliftUnit.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))) i) := by
  refine moduleFinite_naiveCotangentExt_of_moduleFinite_modelHom B S hS g
    (residueRingHomOfMap B S hS g γ) i ?_
  let φ := residueRingHomOfMap B S hS g γ
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (RestrictedModelModules B S hS X)
  let : Linear k (Modules.{u, u} B S hS X.1 X.2) := Stacks.SheafOfModules.linearOver _ φ
  have hXN := isNoetherian_of_isProper_toAffine B S hS V hVaff g hg
  have hfin : HasFiniteCoherentCohomologyOver B S hS X.1 X.2 φ := fun F hF n =>
    moduleFinite_restrictScalars_comp_of_surjective γ hγ (objectRingHom V g) _
      (moduleFinite_cohomology_of_isProper_toAffineObject V hVaff g hg F hF n)
  have hXln : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := hXN.2.2
  have hYln : HasEtaleLocalProperty B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).2 inferInstance
  have hlft : IsLocallyOfFiniteType B S hS g.hom := hg.2.1.1
  let E := modelModulesEquiv B S hS X
  have : E.functor.Additive := modelModulesEquiv_functor_additive (X := X) B S hS
  have : E.inverse.IsEquivalence := E.isEquivalence_inverse
  let NLm := modelNaiveCotangentComplex B S hS g
  let K := E.inverse.mapDerivedCategory.obj (DerivedCategory.Q.obj NLm)
  have eH : ∀ n : ℤ, (DerivedCategory.homologyFunctor _ n).obj K ≅
      modelNaiveCotangentHomology B S hS g n := fun n =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso E.inverse n).app _ ≪≫
      E.inverse.mapIso ((DerivedCategory.homologyFunctorFactors _ n).app NLm)
  have hzero : ∀ n : ℤ, n ≠ -1 → n ≠ 0 →
      IsZero (modelNaiveCotangentHomology B S hS g n) := fun n h₁ h₀ =>
    isZero_of_faithful_of_isZero_obj (spaceULift B S hS X)
      ((isZero_homology_naiveCotangentComplex B S hS g n h₁ h₀).of_iso
        (spaceULiftModelNaiveCotangentHomologyIso B S hS g n))
  have hcoh : ∀ n : ℤ, IsCoherent B S hS X.1 X.2 (modelNaiveCotangentHomology B S hS g n) := by
    intro n
    by_cases h₁ : n = -1
    · subst h₁
      exact isCoherent_modelNaiveCotangentHomology_negOne B S hS g hlft hXln hYln
    by_cases h₀ : n = 0
    · subst h₀
      exact isCoherent_modelNaiveCotangentHomology_zero B S hS g hlft hXln
    exact ObjectProperty.prop_of_isZero (isCoherent.{u, u} B S hS X.1 X.2) (hzero n h₁ h₀)
  have hK : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B S hS X.1 X.2) K :=
    ⟨⟨0, fun n hn => (hzero n (by omega) (by omega)).of_iso (eH n)⟩,
      fun n => isCoherent_of_iso B S hS X.2 (eH n).symm (hcoh n)⟩
  have : Fact (HasEtaleLocalProperty B S hS X.1
    (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hXln⟩
  let O := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  have hL := (derivedCategoryBMinus_and_plus_singleFunctor_of_isCoherent B S hS
    X.1 X.2 O (isCoherent_structureSheaf B S hS X.1 X.2)).2
  exact moduleFinite_hom_shift_of_hasFiniteCoherentCohomologyOver B S hS X.1 X.2
    φ hXN hfin K _ hK hL i

include hγ hVaff hg in
/-- **The receptacle at `k` is finite dimensional** for `g : X ⟶ V` proper over an affine
noetherian `V` and `k ⟶ Γ(V)` surjective. -/
theorem finiteDimensional_classExtFunctor_obj :
    FiniteDimensional k ((classExtFunctor B S hS g γ).obj (FGModuleCat.of k k)) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))
  let : Linear k (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheaf B S hS X.1 X.2))) :=
    Stacks.SheafOfModules.linearOver _ (residueRingHomOfMap B S hS g γ)
  let : Linear k (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
    Stacks.SheafOfModules.linearOver _ (modelResidueRingHomOfMap B S hS g γ)
  have h := moduleFinite_naiveCotangentExt_of_isProper B S hS γ hγ hVaff hg 1
  exact Module.Finite.equiv ((classExtRankOneModelLinearEquiv B S hS g γ).trans
    (modelHomLinearEquivNaiveCotangentExt B S hS g (residueRingHomOfMap B S hS g γ) 1)).symm

end General

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CartesianProperFlatSpaces B S hS)
  (hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- **The receptacle `Ext¹(NL_{X₀/k}, 𝒪_{X₀})` of a point of `Spaces'_{fp, flat, proper}` over a
field is finite dimensional**: `X₀` is proper over the affine noetherian `Spec k`. -/
theorem finiteDimensional_tangentExtFunctor_obj :
    FiniteDimensional k ((tangentExtFunctor B S hS iΛ x₀ hx₀).obj (FGModuleCat.of k k)) := by
  have e : (BigFppfOver.toScheme B S hS).obj ((cartesianProperFlatProjection B S hS).obj x₀) =
      Spec (.of k) := congrArg Over.left hx₀
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((cartesianProperFlatProjection B S hS).obj x₀)) := by
    rw [e]; infer_instance
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      ((cartesianProperFlatProjection B S hS).obj x₀)) := by
    rw [e]; infer_instance
  exact Space.finiteDimensional_classExtFunctor_obj B S hS
    (baseResidueFieldEquiv B S hS hx₀).toRingHom (baseResidueFieldEquiv B S hS hx₀).surjective
    hVaff (g := baseStructureMap B S hS (y₀ := x₀)) x₀.obj.property.2.2

end AlgebraicGeometry.ProperFlatSpaceDeformation

end

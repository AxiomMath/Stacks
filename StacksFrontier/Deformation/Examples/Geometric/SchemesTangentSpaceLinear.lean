module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionNatural
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceExt

/-!
# The tangent space of the deformation category of a scheme, `k`-linearly (Stacks 0DY9)

The receptacle of the `k`-linear form of the second display of [Stacks Project, Tag 0DY9]: the
groups `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)` as an additive `k`-linear functor of the
finite-dimensional `k`-vector space `V`, acting by postcomposition with `(𝒪_X ⊗_k g)[1]`.

## Main definitions

* `Deformation.Examples.schemeTangentExtModule`: the `k`-vector space structure on
  `Ext¹_{𝒪_X}(NL_{X/k}, 𝒢)`, induced by the `k`-linear structure of `𝒪_X`-modules.
* `Deformation.Examples.schemeTangentExtFunctor`: `V ↦ Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)`.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 06IJ](https://stacks.math.columbia.edu/tag/06IJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))



/-- The `k`-linear structure on `𝒪_X`-modules, in the spelling of the coefficients of
`AlgebraicGeometry.Scheme.naiveCotangentExt`. -/
abbrev schemeModulesLinear : Linear k (RingedSpace.siteModules X.left.toRingedSpace) :=
  modulesLinear k (Over.mk X.hom)

/-- **The `k`-vector space structure on `Ext¹_{𝒪_X}(NL_{X/k}, 𝒢)`**: `Ext¹` is a group of
morphisms of the derived category of `𝒪_X`-modules, which is `k`-linear because `𝒪_X`-modules
are. -/
@[instance_reducible]
def schemeTangentExtModule (G : X.left.Modules) :
    Module k (Scheme.naiveCotangentExt X.hom G 1) :=
  letI := schemeModulesLinear X
  (inferInstance : Linear k
    (DerivedCategory (RingedSpace.siteModules X.left.toRingedSpace))).homModule _ _

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- The `k`-vector space structure on `Ext¹_{𝒪_X}(NL_{X/k}, 𝒢)` at the standard model of the
derived category, the model of the acting group of [Stacks Project, Tag 08UC]. -/
@[instance_reducible]
def schemeTangentExtStdModule (G : SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :
    Module k (RingedSpaceThickening.extOneNaiveCotangent X.hom.toLRSHom.toShHom G) :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :=
    modulesLinear k (Over.mk X.hom)
  (inferInstance : Linear k
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)))).homModule _ _

/-- The shifted single complex `(𝒪_X ⊗_k V)[1]` as a functor of `V`. -/
abbrev schemeTangentCoefficientShiftFunctor :
    FGModuleCat.{u} k ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :=
  coefficientSheafFunctor X.hom ⋙
    DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) 0 ⋙
      shiftFunctor _ (1 : ℤ)

/-- The functor `V ↦ (𝒪_X ⊗_k V)[1]` is `k`-linear. -/
theorem schemeTangentCoefficientShiftFunctor_linear :
    letI : Linear k (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :=
      modulesLinear k (Over.mk X.hom)
    (schemeTangentCoefficientShiftFunctor X).Linear k := by
  let : Linear k (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :=
    modulesLinear k (Over.mk X.hom)
  have := coefficientSheafFunctor_linear (k := k) X.hom
  infer_instance

/-- `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)` at the standard model. -/
abbrev schemeTangentExtAt (V : FGModuleCat.{u} k) : Type (u + 1) :=
  RingedSpaceThickening.extOneNaiveCotangent X.hom.toLRSHom.toShHom
    ((coefficientSheafFunctor X.hom).obj V)

/-- The map of `Ext¹` groups induced by a map of coefficient modules. -/
def schemeTangentExtMap {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    letI := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj V)
    letI := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj W)
    schemeTangentExtAt X V →ₗ[k] schemeTangentExtAt X W :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :=
    modulesLinear k (Over.mk X.hom)
  Linear.rightComp k _ ((schemeTangentCoefficientShiftFunctor X).map g)

/-- **`V ↦ Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)` as a functor of the coefficient module.** -/
def schemeTangentExtFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{u + 1} k where
  obj V := @ModuleCat.of k _ (schemeTangentExtAt X V) _
    (schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj V))
  map {V W} g :=
    letI := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj V)
    letI := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj W)
    ModuleCat.ofHom (schemeTangentExtMap X g)
  map_id V := by
    let := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj V)
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : _ ⟶ _) ≫ (schemeTangentCoefficientShiftFunctor X).map (𝟙 V) = e
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  map_comp {V W Z} g h := by
    let := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj V)
    let := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj Z)
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : _ ⟶ _) ≫ (schemeTangentCoefficientShiftFunctor X).map (g ≫ h) =
      ((e : _ ⟶ _) ≫ (schemeTangentCoefficientShiftFunctor X).map g) ≫
        (schemeTangentCoefficientShiftFunctor X).map h
    rw [CategoryTheory.Functor.map_comp]
    exact (Category.assoc _ _ _).symm

/-- The functor acts by postcomposition. -/
theorem schemeTangentExtFunctor_map_apply {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    (e : schemeTangentExtAt X V) :
    (schemeTangentExtFunctor X).map g e =
      (e : _ ⟶ _) ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((coefficientSheafFunctor X.hom).map g))⟦(1 : ℤ)⟧' :=
  rfl

/-- The functor `V ↦ Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)` is additive. -/
instance : (schemeTangentExtFunctor X).Additive where
  map_add {V W g h} := by
    let := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj V)
    let := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj W)
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : _ ⟶ _) ≫ (schemeTangentCoefficientShiftFunctor X).map (g + h) =
      (e : _ ⟶ _) ≫ (schemeTangentCoefficientShiftFunctor X).map g +
        (e : _ ⟶ _) ≫ (schemeTangentCoefficientShiftFunctor X).map h
    rw [CategoryTheory.Functor.map_add]
    exact Preadditive.comp_add _ _ _ _ _ _

/-- The functor `V ↦ Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)` is `k`-linear. -/
instance : (schemeTangentExtFunctor X).Linear k where
  map_smul {V W} g c := by
    let := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj V)
    let := schemeTangentExtStdModule X ((coefficientSheafFunctor X.hom).obj W)
    let : Linear k (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :=
      modulesLinear k (Over.mk X.hom)
    have := schemeTangentCoefficientShiftFunctor_linear X
    refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
    change (e : _ ⟶ _) ≫ (schemeTangentCoefficientShiftFunctor X).map (c • g) =
      c • ((e : _ ⟶ _) ≫ (schemeTangentCoefficientShiftFunctor X).map g)
    rw [CategoryTheory.Functor.map_smul]
    exact Linear.comp_smul _ _ _ _ _ _

end Standard

/-- In a `k`-linear abelian category, a scalar acts on a morphism into a shifted single complex by
postcomposition with the shifted single complex of the scalar multiple of the identity. -/
theorem smul_eq_comp_singleFunctor_map {C : Type*} [Category C] [Abelian C] [Linear k C]
    [HasDerivedCategory C] {A : DerivedCategory C} {G : C}
    (x : A ⟶ ((DerivedCategory.singleFunctor C 0).obj G)⟦(1 : ℤ)⟧) (c : k) :
    c • x = x ≫ ((DerivedCategory.singleFunctor C 0).map (c • 𝟙 G))⟦(1 : ℤ)⟧' := by
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id, Linear.comp_smul,
    Category.comp_id]

/-- **The comparison of the two models of `Ext¹_{𝒪_X}(NL_{X/k}, 𝒢)` is `k`-linear.** A scalar acts
on a class by postcomposition with the shifted single complex of the scalar multiple of the
identity of `𝒢`, and the comparison commutes with postcomposition with such maps
(`AlgebraicGeometry.RingedSpace.extOneNaiveCotangentAddEquiv_comp_singleFunctor_map`). -/
theorem extOneNaiveCotangentAddEquiv_smul (G : X.left.Modules)
    (c : k) (x : RingedSpaceThickening.extOneNaiveCotangent X.hom.toLRSHom.toShHom G) :
    letI := schemeTangentExtStdModule X G
    letI := schemeTangentExtModule X G
    Scheme.extOneNaiveCotangentAddEquiv X.hom G (c • x) =
      c • Scheme.extOneNaiveCotangentAddEquiv X.hom G x := by
  let : Linear k (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :=
    modulesLinear k (Over.mk X.hom)
  let := schemeModulesLinear X
  have h1 := @smul_eq_comp_singleFunctor_map k _ _ _ _ _
    (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)))
    _ G x c
  have h2 := smul_eq_comp_singleFunctor_map (C := RingedSpace.siteModules X.left.toRingedSpace)
    (Scheme.extOneNaiveCotangentAddEquiv X.hom G x) c
  refine (congrArg (Scheme.extOneNaiveCotangentAddEquiv X.hom G) h1).trans ?_
  refine Eq.trans ?_ h2.symm
  exact RingedSpace.extOneNaiveCotangentAddEquiv_comp_singleFunctor_map _ _ x

end Deformation.Examples

end

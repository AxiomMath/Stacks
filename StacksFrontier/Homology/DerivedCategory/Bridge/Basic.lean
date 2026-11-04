module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelShiftedHom
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonExactFunctor
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonQuotient

/-!
# The comparison between two models of the derived category

`HasDerivedCategory.{w} C` is the *choice* of a localization of `CochainComplex C ℤ` at the
quasi-isomorphisms, with morphisms in `Type w`. Two choices `h₁ h₂` give two categories
`@DerivedCategory C _ _ h₁` and `@DerivedCategory C _ _ h₂`, compared by the equivalence
`StacksDraft.DerivedModel.modelEquiv h₁ h₂` coming from the uniqueness of localizations. This
file shows that this comparison is a triangulated equivalence, that it reflects isomorphisms and
zero objects in both directions, and compares it with the shrinking comparison of a Grothendieck
abelian category. For sheaves of modules it specializes the comparison to the standard model
`HasDerivedCategory.standard` and the locally small models `SheafOfModules.hasDerivedCategory`
and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## Main definitions

* `StacksDraft.DerivedModel.grothendieckModelEquivFunctorIso`: the shrinking comparison
  `Stacks.Injectives.grothendieckModelEquiv` and `modelEquiv` are isomorphic functors.
* `SheafOfModules.derivedModelEquiv`, `AlgebraicGeometry.Scheme.Modules.derivedModelEquiv`: the
  comparisons of the standard model with the locally small one, and their
  `derivedModelEquivCompQIso` with the localization functors.
* `AlgebraicGeometry.Scheme.Modules.schemeModulesComparisonFunctorIso`: the shrinking comparison
  for `X.Modules` is isomorphic to `derivedModelEquiv X`.

## Main results

* Instances: `(modelEquiv h₁ h₂).functor.CommShift ℤ`, `modelEquivInverseCommShift`,
  `modelEquiv_commShift`, `modelEquiv_isTriangulated`, and `commShift_modelCompQIso_hom`,
  `commShift_compUniqFunctor_Qh_hom`: the identifications with `Q` and `Qh` commute with the shift.
* `modelHomologyFunctorIso_hom_app_Q_obj`: the comparison of cohomology at a complex.
* `isIso_modelEquiv_functor_map_iff`, `isIso_modelEquiv_inverse_map_iff`,
  `isZero_modelEquiv_functor_obj_iff`, `isZero_modelEquiv_inverse_obj_iff`: the comparison and
  its inverse reflect and preserve isomorphisms and zero objects.
* `isIso_Q_map_iff_isIso_Q_map`, `isIso_Qh_map_iff_isIso_Qh_map`: a morphism of complexes, or of
  the homotopy category, becomes invertible in one model if and only if it does in the other.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Category Functor Limits

universe u v w z

namespace StacksDraft.DerivedModel

section OneModel

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The shift functors of any chosen derived category are additive. -/
theorem shiftFunctor_additive (h : HasDerivedCategory.{w} C) (n : ℤ) :
    (shiftFunctor (@DerivedCategory C _ _ h) n).Additive := by
  let := h
  infer_instance

end OneModel

section TwoModels

variable {C : Type u} [Category.{v} C] [Abelian C]
  (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)

attribute [instance] StacksDraft.Perfect.derivedEquivalenceCommShift

/-- The comparison of the two localizations of the homotopy category commutes with the shift. -/
instance commShift_compUniqFunctor_Qh_hom :
    NatTrans.CommShift (Localization.compUniqFunctor (@DerivedCategory.Qh C _ _ h₁)
      (@DerivedCategory.Qh C _ _ h₂) (HomotopyCategory.subcategoryAcyclic C).trW).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (@DerivedCategory.Qh C _ _ h₁)
    (HomotopyCategory.subcategoryAcyclic C).trW ℤ (@DerivedCategory.Qh C _ _ h₂)
    (modelEquiv h₁ h₂).functor

/-- The comparison of the two localizations of cochain complexes commutes with the shift. -/
instance commShift_modelCompQIso_hom : NatTrans.CommShift (modelCompQIso h₁ h₂).hom ℤ := by
  dsimp only [modelCompQIso, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance

/-- The inverse of the comparison equivalence commutes with the shift. -/
instance modelEquivInverseCommShift : (modelEquiv h₁ h₂).inverse.CommShift ℤ :=
  (modelEquiv h₁ h₂).commShiftInverse ℤ

/-- The comparison equivalence is compatible with the shift: its unit and counit commute with
the shift. -/
instance modelEquiv_commShift : (modelEquiv h₁ h₂).CommShift ℤ :=
  (modelEquiv h₁ h₂).commShift_of_functor ℤ

/-- The comparison equivalence is a triangulated equivalence. -/
instance modelEquiv_isTriangulated :
    letI := shiftFunctor_additive h₁
    letI := shiftFunctor_additive h₂
    (modelEquiv h₁ h₂).IsTriangulated :=
  letI := shiftFunctor_additive h₁
  letI := shiftFunctor_additive h₂
  Equivalence.IsTriangulated.mk' _ (StacksDraft.Perfect.derivedEquivalence_isTriangulated h₁ h₂)

/-! ### Cohomology -/

/-- At the image of a cochain complex `K`, the comparison of the cohomology functors of the two
models is the identification of both with the cohomology of `K`. -/
theorem modelHomologyFunctorIso_hom_app_Q_obj (n : ℤ) (K : CochainComplex C ℤ) :
    (modelHomologyFunctorIso h₁ h₂ n).hom.app ((@DerivedCategory.Q C _ _ h₁).obj K) =
      (@DerivedCategory.homologyFunctor C _ _ h₂ n).map ((modelCompQIso h₁ h₂).hom.app K) ≫
        (@DerivedCategory.homologyFunctorFactors C _ _ h₂ n).hom.app K ≫
          (@DerivedCategory.homologyFunctorFactors C _ _ h₁ n).inv.app K := by
  simp [modelHomologyFunctorIso, Localization.liftNatIso, Localization.liftNatTrans_app]

/-! ### Transfer along the comparison -/

/-- A morphism of the first model is invertible if and only if its comparison is. -/
theorem isIso_modelEquiv_functor_map_iff {X Y : @DerivedCategory C _ _ h₁} (f : X ⟶ Y) :
    IsIso ((modelEquiv h₁ h₂).functor.map f) ↔ IsIso f :=
  isIso_iff_of_reflects_iso f _

/-- A morphism of the second model is invertible if and only if its comparison back is. -/
theorem isIso_modelEquiv_inverse_map_iff {X Y : @DerivedCategory C _ _ h₂} (f : X ⟶ Y) :
    IsIso ((modelEquiv h₁ h₂).inverse.map f) ↔ IsIso f :=
  isIso_iff_of_reflects_iso f _

/-- An object of the first model is zero if and only if its comparison is. -/
theorem isZero_modelEquiv_functor_obj_iff (X : @DerivedCategory C _ _ h₁) :
    IsZero ((modelEquiv h₁ h₂).functor.obj X) ↔ IsZero X :=
  ⟨IsZero.of_full_of_faithful_of_isZero _ X, Functor.map_isZero _⟩

/-- An object of the second model is zero if and only if its comparison back is. -/
theorem isZero_modelEquiv_inverse_obj_iff (X : @DerivedCategory C _ _ h₂) :
    IsZero ((modelEquiv h₁ h₂).inverse.obj X) ↔ IsZero X :=
  ⟨IsZero.of_full_of_faithful_of_isZero _ X, Functor.map_isZero _⟩

/-- A morphism of cochain complexes becomes invertible in one model if and only if it does in the
other: both conditions say that it is a quasi-isomorphism. -/
theorem isIso_Q_map_iff_isIso_Q_map {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso ((@DerivedCategory.Q C _ _ h₁).map φ) ↔ IsIso ((@DerivedCategory.Q C _ _ h₂).map φ) := by
  rw [@DerivedCategory.isIso_Q_map_iff_quasiIso C _ _ h₁,
    @DerivedCategory.isIso_Q_map_iff_quasiIso C _ _ h₂]

/-- A morphism of the homotopy category becomes invertible in one model if and only if it does in
the other: both conditions say that it is a quasi-isomorphism. -/
theorem isIso_Qh_map_iff_isIso_Qh_map {K L : HomotopyCategory C (ComplexShape.up ℤ)}
    (φ : K ⟶ L) :
    IsIso ((@DerivedCategory.Qh C _ _ h₁).map φ) ↔
      IsIso ((@DerivedCategory.Qh C _ _ h₂).map φ) := by
  rw [@DerivedCategory.isIso_Qh_map_iff C _ _ h₁, @DerivedCategory.isIso_Qh_map_iff C _ _ h₂]

end TwoModels

/-! ### The standard model and the model of a Grothendieck abelian category -/

section Grothendieck

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The shift functors of the standard model are additive. -/
instance shiftFunctor_additive_standard (n : ℤ) :
    (shiftFunctor (@DerivedCategory C _ _ (HasDerivedCategory.standard C)) n).Additive :=
  shiftFunctor_additive _ n

variable (C) [IsGrothendieckAbelian.{w} C]

/-- The shift functors of the derived category model
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian` of a Grothendieck abelian category
are additive. -/
instance shiftFunctor_additive_grothendieck (n : ℤ) :
    (shiftFunctor (@DerivedCategory C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)) n).Additive :=
  shiftFunctor_additive _ n

/-- **The two comparisons of the standard model with the model of a Grothendieck abelian category
agree.** The shrinking equivalence `Stacks.Injectives.grothendieckModelEquiv` and the comparison
`modelEquiv` given by the uniqueness of localizations are isomorphic functors: both lift the
localization functor of `Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian` along the
standard one. -/
def grothendieckModelEquivFunctorIso :
    (Stacks.Injectives.grothendieckModelEquiv.{w} C).functor ≅
      (modelEquiv (HasDerivedCategory.standard C)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).functor :=
  letI : Localization.Lifting (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (@DerivedCategory.Q C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C))
      (modelEquiv (HasDerivedCategory.standard C)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).functor :=
    ⟨modelCompQIso _ _⟩
  Localization.liftNatIso (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (@DerivedCategory.Q C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C))
    (@DerivedCategory.Q C _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w} C)) _ _ (Iso.refl _)

end Grothendieck

end StacksDraft.DerivedModel

/-! ### Sheaves of modules -/

namespace SheafOfModules

open StacksDraft.DerivedModel

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- The shift functors of the locally small derived category of sheaves of `R`-modules are
additive. -/
instance shiftFunctor_additive_derivedCategory (n : ℤ) :
    (shiftFunctor (DerivedCategory (SheafOfModules.{u} R)) n).Additive :=
  shiftFunctor_additive _ n

/-- The comparison of the standard derived category of sheaves of `R`-modules with the locally
small one `SheafOfModules.hasDerivedCategory`. -/
abbrev derivedModelEquiv :
    @DerivedCategory (SheafOfModules.{u} R) _ _ (HasDerivedCategory.standard _) ≌
      DerivedCategory (SheafOfModules.{u} R) :=
  modelEquiv (HasDerivedCategory.standard _) (hasDerivedCategory R)

/-- The comparison of the two derived categories of sheaves of `R`-modules identifies their
localization functors. -/
abbrev derivedModelEquivCompQIso :
    @DerivedCategory.Q (SheafOfModules.{u} R) _ _ (HasDerivedCategory.standard _) ⋙
        (derivedModelEquiv R).functor ≅ DerivedCategory.Q :=
  modelCompQIso _ _

end SheafOfModules

/-! ### Sheaves of modules on a scheme -/

namespace AlgebraicGeometry.Scheme.Modules

open StacksDraft.DerivedModel

variable (X : Scheme.{u})

/-- The shift functors of the locally small derived category of `𝒪_X`-modules are additive. -/
instance shiftFunctor_additive_derivedCategory (n : ℤ) :
    (shiftFunctor (DerivedCategory X.Modules) n).Additive :=
  shiftFunctor_additive _ n

/-- The comparison of the standard derived category of `𝒪_X`-modules with the locally small one
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
abbrev derivedModelEquiv :
    @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _) ≌ DerivedCategory X.Modules :=
  modelEquiv (HasDerivedCategory.standard _) (hasDerivedCategory X)

/-- The comparison of the two derived categories of `𝒪_X`-modules identifies their localization
functors. -/
abbrev derivedModelEquivCompQIso :
    @DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _) ⋙
        (derivedModelEquiv X).functor ≅ DerivedCategory.Q :=
  modelCompQIso _ _

/-- The shrinking comparison `StacksDraft.DerivedModel.schemeModulesComparison` and
`derivedModelEquiv` are isomorphic functors. -/
def schemeModulesComparisonFunctorIso :
    (schemeModulesComparison X).functor ≅ (derivedModelEquiv X).functor :=
  grothendieckModelEquivFunctorIso X.Modules

end AlgebraicGeometry.Scheme.Modules

end

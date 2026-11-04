module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitFlatSingle
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorUnitMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DerivedRestrictionDictionaryCoherence

/-!
# Transporting the copower unit identification to the derived unit constraint

Let `S` be a simplicial-site situation.  The unit identification
`CategoryTheory.SimplicialSiteSituation.unitTensorIso`, `ℤ ⊗_ℤ - ≅ 𝟭` on abelian sheaves over
the total site, is built out of copower and sheafification identifications, and the unit
constraint `Stacks.DerivedTensor.AbelianSheaves.constantSheafLeftUnitIso` of the derived tensor
product of abelian sheaves out of the left unit constraint of the derived tensor product on
sheaves of modules over the constant sheaf of rings `ℤ`.  This file relates the two.

## Main results

* `CategoryTheory.mapDerivedCategoryIsoOfNatIso_hom_eq_derivedNatTrans`: the descent of an
  isomorphism of exact functors to derived categories is the descent of its underlying
  transformation.
* `CategoryTheory.derivedIdIso_eq_mapDerivedCategoryIdIso`: the two identifications of the descent
  of the identity functor agree.
* `Stacks.SheafOfModules.unitSheafTensorNatIso_hom_app_eq_leftUnitor`: the left unit law
  `Stacks.SheafOfModules.unitSheafTensorNatIso`, defined as the braiding followed by the right
  unit law, is the left unitor of `SheafOfModules.monoidalCategorySheafTensor`.
* `CategoryTheory.SimplicialSiteSituation.unitTensorIso_hom_app_eq_unitSheafTensorNatIso`: the
  copower unit identification is the sheaf-level left unit law, read across the equivalence of
  abelian sheaves with modules over `ℤ`.
* `CategoryTheory.SimplicialSiteSituation.inverseSingleTotalInteger_comp_inverseUnitObjectIso`:
  the three identifications carrying the coefficient of the derived tensor product from the
  constant integer sheaf to the structure sheaf of
  `Stacks.DerivedTensor.AbelianSheaves.intRingedSite` compose to
  `CategoryTheory.SimplicialSiteSituation.totalIntegerModuleIsoUnit` placed in degree zero.

## References

* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe u

attribute [local instance] CategoryTheory.SimplicialSiteSituation.hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

namespace CategoryTheory

section DerivedGlue

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F G : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The descent of an isomorphism of exact functors is the descent of its underlying
transformation.**  That is, `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`
applied to `e` has forward map `CategoryTheory.derivedNatTrans` of `e.hom`. -/
theorem mapDerivedCategoryIsoOfNatIso_hom_eq_derivedNatTrans (e : F ≅ G) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F G e).hom =
      derivedNatTrans F G e.hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun L => ?_
  rw [Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    derivedNatTrans_app]
  rfl

/-- **The two identifications of the descent of the identity functor agree.**
`CategoryTheory.derivedIdIso` and `Stacks.Homology.mapDerivedCategoryIdIso` are the same
isomorphism. -/
theorem derivedIdIso_eq_mapDerivedCategoryIdIso :
    (derivedIdIso (A := A)) = Stacks.Homology.mapDerivedCategoryIdIso := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun L => ?_)
  rw [derivedIdIso_hom_app_Q, Stacks.DerivedGlueing.mapDerivedCategoryIdIso_hom_app_Q]

end DerivedGlue

end CategoryTheory

namespace Stacks.SheafOfModules

variable (Y : RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (A : RingedSite.Modules Y)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The right unit law `- ⊗_𝒪 𝒪 ≅ id` at a sheaf of modules is the right unitor
`ℱ ⊗_𝒪 𝒪 ≅ ℱ` of the tensor product sheaf. -/
theorem sheafTensorUnitNatIso_hom_app :
    (sheafTensorUnitNatIso Y.O).hom.app A =
      (tensorSheafUnitRightIso Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom := by
  rw [← _root_.SheafOfModules.rightUnitor_sheafTensor_eq Y.O A]
  rfl

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The left unit law `𝒪 ⊗_𝒪 - ≅ id` at a sheaf of modules is the braiding followed by the
right unitor of the tensor product sheaf. -/
theorem unitSheafTensorNatIso_hom_app :
    (unitSheafTensorNatIso (Y := Y)).hom.app A =
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).hom.app
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app A ≫
        (tensorSheafUnitRightIso Y.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A).hom :=
  congrArg
    (fun g => ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).hom.app
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app A ≫ g)
    (sheafTensorUnitNatIso_hom_app Y A)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **The left unit law `𝒪 ⊗_𝒪 - ≅ id` is the left unitor of the re-seated monoidal structure
on sheaves of modules.** -/
theorem unitSheafTensorNatIso_hom_app_eq_leftUnitor :
    (unitSheafTensorNatIso (Y := Y)).hom.app A =
      (@MonoidalCategoryStruct.leftUnitor _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O).toMonoidalCategoryStruct A).hom :=
  (unitSheafTensorNatIso_hom_app Y A).trans
    ((_root_.SheafOfModules.sheafTensorBraiding_comp_tensorSheafUnitRightIso Y.O A).trans
      (_root_.SheafOfModules.leftUnitor_sheafTensor_eq Y.O A).symm)

end Stacks.SheafOfModules

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor

variable (S : SimplicialSiteSituation.{u})

/-- The forward map of `monoidalUnitLeftIsoAux`, written out as a composite. -/
theorem monoidalUnitLeftIsoAux_hom (F : Sheaf S.totalTopology Ab.{u}) :
    (monoidalUnitLeftIsoAux S F).hom =
      (moduleEquivalence S.totalTopology).functor.map
          ((((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).mapIso
                (totalIntegerModuleIsoUnit S)).app (barModule S F)).hom ≫
            (@MonoidalCategoryStruct.leftUnitor _ _
              (SheafOfModules.monoidalCategorySheafTensor
                (intRingSheaf S.totalTopology)).toMonoidalCategoryStruct
              (barModule S F)).hom) ≫
        (moduleEquivalence S.totalTopology).counitIso.hom.app F :=
  rfl

/-- **The copower unit identification is the sheaf-level left unit law**
`Stacks.SheafOfModules.unitSheafTensorNatIso`, read across the equivalence of abelian sheaves
with modules over `ℤ`. -/
theorem unitTensorIso_hom_app_eq_unitSheafTensorNatIso (F : Sheaf S.totalTopology Ab.{u}) :
    (unitTensorIso S).hom.app F =
      (moduleEquivalence S.totalTopology).functor.map
          ((((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).mapIso
                (totalIntegerModuleIsoUnit S)).app (barModule S F)).hom ≫
            (Stacks.SheafOfModules.unitSheafTensorNatIso
              (Y := intRingedSite S.totalTopology)).hom.app (barModule S F)) ≫
        (moduleEquivalence S.totalTopology).counitIso.hom.app F :=
  ((unitTensorIso_hom_app_eq S F).trans (monoidalUnitLeftIsoAux_hom S F)).trans
    (congrArg
      (fun g => (moduleEquivalence S.totalTopology).functor.map
          ((((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).mapIso
              (totalIntegerModuleIsoUnit S)).app (barModule S F)).hom ≫ g) ≫
        (moduleEquivalence S.totalTopology).counitIso.hom.app F)
      (Stacks.SheafOfModules.unitSheafTensorNatIso_hom_app_eq_leftUnitor
        (intRingedSite S.totalTopology) (barModule S F)).symm)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The forward map of `inverseUnitObjectIso`, written out as a composite. -/
theorem inverseUnitObjectIso_hom :
    (inverseUnitObjectIso S.totalTopology).hom =
      (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
          (intSheaf S.totalTopology)).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          (((moduleEquivalence S.totalTopology).unitIso.app
            (SheafOfModules.unit (intRings S.totalTopology))).symm).hom :=
  rfl

/-- The forward map of `totalIntegerModuleIsoUnit`, written out as a composite. -/
theorem totalIntegerModuleIsoUnit_hom :
    (totalIntegerModuleIsoUnit S).hom =
      (moduleEquivalence S.totalTopology).inverse.map
          (intSheafIsoConstantSheaf S.totalTopology).hom ≫
        (((moduleEquivalence S.totalTopology).unitIso.app
          (SheafOfModules.unit (intRings S.totalTopology))).symm).hom :=
  rfl

/-- **The coefficient transport.** The coefficient of the derived tensor product is
carried from the constant integer sheaf to the structure sheaf of `intRingedSite` by three
successive identifications — the single-functor compositor of the inverse equivalence, the
identification of the constant integer sheaf with the abelian sheaf underlying the structure
sheaf, and the unit of the equivalence spelled out by `inverseUnitObjectIso` — and their
composite is `totalIntegerModuleIsoUnit` placed in degree zero. -/
theorem inverseSingleTotalInteger_comp_inverseUnitObjectIso :
    (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
          (totalIntegerSheaf S)).inv ≫
        (moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (intSheafIsoConstantSheaf S.totalTopology).hom) ≫
          (inverseUnitObjectIso S.totalTopology).hom =
      (DerivedCategory.singleFunctor _ 0).map (totalIntegerModuleIsoUnit S).hom := by
  rw [inverseUnitObjectIso_hom, totalIntegerModuleIsoUnit_hom, Iso.inv_comp_eq,
    ← Category.assoc]
  erw [((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor
    (0 : ℤ)).hom.naturality (intSheafIsoConstantSheaf S.totalTopology).hom]
  exact Category.assoc _ _ _ |>.trans (_ ≫= ((DerivedCategory.singleFunctor _ 0).map_comp _ _).symm)

end Derived

end CategoryTheory.SimplicialSiteSituation

end

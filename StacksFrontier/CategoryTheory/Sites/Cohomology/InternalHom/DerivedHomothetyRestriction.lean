module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomothety

/-!
# The homothety map and restriction to a slice

Let `(C, 𝒪)` be a ringed site, `U` an object of `C` and `K` an object of `D(𝒪)`. Restricting the
homothety map `𝒪 ⟶ R𝓗om(K, K)` to the slice site `C/U` gives an isomorphism exactly when the
homothety map `𝒪_U ⟶ R𝓗om(K|_U, K|_U)` of the restriction is one.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_map_derivedHomothety_overFunctor_iff`: the statement.

## Implementation notes

Both sides are read on a K-flat representative `B` of `K` with a quasi-isomorphism `B ⟶ I` into a
K-injective complex: the homothety map of `Q B` is the class of the currying of
`Tot(𝒪[0] ⊗ B) ≅ B ⟶ I`, and currying commutes with restriction to a slice
(`AlgebraicGeometry.RingedSite.restrictComplexMap_curryMap`), the restrictions of `B` and `I`
staying K-flat (Stacks 0E8K) and K-injective (Stacks 08FI).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
  sliceSheafTensorAdditive sliceSheafTensorObjAdditive

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  CochainComplex.HomComplex
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.over U).J AddCommGrpCat.{u}]
  [(X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (X.O.over U))) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- The restriction of `𝒪[0]` to the slice is `𝒪_U[0]`. -/
def restrictComplexSingleUnitIso :
    (HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))
        (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ≅
      restrictComplex X ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) U :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
      (ComplexShape.up ℤ) 0).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm

/-- The slice statement on representatives. -/
theorem isIso_map_derivedHomothety_overFunctor_Q_iff
    (B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective] (q : B ⟶ I) [QuasiIso q] :
    IsIso ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.map (derivedHomothety X (DerivedCategory.Q.obj B))) ↔
      IsIso (derivedHomothety (X.over U)
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj (DerivedCategory.Q.obj B))) := by
  let F := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let g := (tensorComplexLeftUnitIso X B).hom ≫ q
  obtain ⟨a, b, hb⟩ := exists_derivedHomothety_Q_eq_curryMap X B I hB g
  have hB' : Stacks.SheafOfModules.IsKFlat (X.over U).O (restrictComplex X B U) :=
    Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex X U B hB
  have hI' : CochainComplex.IsKInjective
      (show CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
        restrictComplex X I U) :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  have : QuasiIso g := by dsimp only [g]; infer_instance
  have : QuasiIso (restrictComplexMap X U g) := by
    dsimp only [restrictComplexMap]
    infer_instance
  let g' : ((tensorComplex (X.over U).O).obj
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))
        (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)))).obj
          (restrictComplex X B U) ⟶
      restrictComplex X I U :=
    ((tensorComplex (X.over U).O).map (restrictComplexSingleUnitIso X U).hom).app
        (restrictComplex X B U) ≫
      (tensorComplexOverIso X U _ B).inv ≫ restrictComplexMap X U g
  have : QuasiIso g' :=
    (quasiIso_iff_comp_left _ _).2 ((quasiIso_iff_comp_left _ _).2 inferInstance)
  have hc : curryMap (X.over U) g' = (restrictComplexSingleUnitIso X U).hom ≫
      restrictComplexMap X U (curryMap X g) ≫ (sheafHomRestrictionComplexIso X U B I).hom :=
    (curryMap_comp_left (X.over U) (restrictComplexSingleUnitIso X U).hom _).trans
      (whisker_eq _ (restrictComplexMap_curryMap X U g).symm)
  refine Iff.trans ?_ ((isIso_derivedHomothety_iff_of_iso (X.over U)
    (restrictionComparison X U B)).trans (isIso_derivedHomothety_Q_iff (X.over U) _ _ hB' g')).symm
  rw [hc]
  refine Iff.trans ?_ (quasiIso_iff_comp_left (restrictComplexSingleUnitIso X U).hom _).symm
  refine Iff.trans ?_ (quasiIso_iff_comp_right _ (sheafHomRestrictionComplexIso X U B I).hom).symm
  rw [hb, Functor.map_comp, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff,
    ← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have hn := F.mapDerivedCategoryFactors_hom_naturality (curryMap X g)
  have key : IsIso (F.mapDerivedCategory.map (DerivedCategory.Q.map (curryMap X g))) ↔
      IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (curryMap X g))) := by
    rw [← isIso_comp_right_iff _ (F.mapDerivedCategoryFactors.hom.app _), hn, isIso_comp_left_iff]
  exact key

/-- **The homothety map commutes with restriction to a slice, as far as invertibility goes.**
For an object `U` of the site and `K` in `D(𝒪)`, the restriction to `C/U` of the homothety map
`𝒪 ⟶ R𝓗om(K, K)` is invertible exactly when the homothety map of `K|_U` is. -/
theorem isIso_map_derivedHomothety_overFunctor_iff
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.map (derivedHomothety X K)) ↔
      IsIso (derivedHomothety (X.over U)
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj K)) := by
  let e := kFlatModelIso X K
  rw [derivedHomothety_naturality X e, Functor.map_comp, isIso_comp_right_iff,
    ← isIso_derivedHomothety_iff_of_iso (X.over U)
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.mapIso e)]
  exact isIso_map_derivedHomothety_overFunctor_Q_iff X U _ _ (isKFlat_kFlatModel X K)
    (kFlatModelMap X K)

end AlgebraicGeometry.RingedSite

end

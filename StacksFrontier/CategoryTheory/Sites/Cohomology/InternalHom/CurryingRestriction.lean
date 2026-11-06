module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.UncurryingOfMorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionSections

/-!
# Currying commutes with restriction to a slice

Let `(C, O)` be a ringed site, `U` an object of `C` and `g : Tot(A ⊗_O B) ⟶ M` a morphism of
complexes of `O`-modules. Restricting the currying `A ⟶ SheafHom(B, M)` of `g` to the slice
site `C/U`, and reading the restricted internal Hom complex as the internal Hom complex of the
restrictions (Stacks 0E8H), gives the currying of the restriction of `g`, read through the
restriction comparison of total tensor complexes.

## Main results

* `AlgebraicGeometry.RingedSite.restrictComplexMap_curryMap`: the compatibility.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
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
  [sliceSheafify : HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [sliceLocallyBijective : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [sliceTensorAdditive : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [sliceTensorObjAdditive : ∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [sliceTensorHasMap : ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (X.O.over U))) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]

variable {A B M :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}


omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  sliceSheafify sliceLocallyBijective [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap in
/-- Evaluation on the restricted internal Hom complex is evaluation on the internal Hom complex
(Stacks 0E8H). -/
lemma applyHomSection_sheafHomRestrictionComplexIso (n p q : ℤ) (hpq : p + n = q)
    (W : (X.over U).C) (s : ((sheafHomComplex X B M).obj.X n).val.obj (op W.left))
    (l : ((restrictComplex X B U).X p).val.obj (op W)) :
    applyHomSection (X.over U) (sheafHomComplex (X.over U) (restrictComplex X B U)
        (restrictComplex X M U)) W n p q hpq
        (((sheafHomRestrictionComplexIso X U B M).hom.f n).val.app (op W) s) l =
      applyHomSection X (sheafHomComplex X B M) W.left n p q hpq s l := by
  have h := sheafHomRestrictionComplexIso_isRestriction X U B M (op W) n p q hpq s
  exact congrArg (fun φ => (φ.app (op (Over.mk (𝟙 W)))).hom l) h

/-- **Currying commutes with restriction to a slice.** -/
theorem restrictComplexMap_curryMap
    (g : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B ⟶ M) :
    restrictComplexMap X U (curryMap X g) ≫ (sheafHomRestrictionComplexIso X U B M).hom =
      @curryMap (X.over U) sliceSheafify sliceLocallyBijective sliceTensorAdditive
        sliceTensorObjAdditive sliceTensorHasMap _ _ _
        ((tensorComplexOverIso X U A B).inv ≫ restrictComplexMap X U g) := by
  ext t V : 3
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro k
  refine homSection_ext (X.over U) (sheafHomComplex (X.over U) (restrictComplex X B U)
    (restrictComplex X M U)) V.unop t fun r d hrd W i l => ?_
  refine Eq.trans (applyHomSectionOver_map_apply (Y := X.over U) _ V.unop W i t r d hrd k l) ?_
  refine Eq.trans ?_ (applyHomSectionOver_map_apply (Y := X.over U) _ V.unop W i t r d hrd k l).symm
  rw [curryMap_apply]
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  rw [applyHomSection_sheafHomRestrictionComplexIso, tensorComplexOverIso_inv_tensorComplexSection]
  exact curryMap_apply X g t r d hrd W.left _ l

end AlgebraicGeometry.RingedSite

end

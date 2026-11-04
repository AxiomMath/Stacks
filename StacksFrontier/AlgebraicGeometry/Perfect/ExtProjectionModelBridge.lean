module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatPullbackTensorTriangleIso
public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionFlatExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroUnconditional

/-!
# `Tot(f^*ℱ[0] ⊗ 𝒢) ≅ 𝒢 ⊗ f^*ℱ`

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `𝒢` a complex of `𝒪_X`-modules.
For an `𝒪_Y`-module `ℱ` placed in degree zero, the total complex `Tot(f^*ℱ[0] ⊗ 𝒢)` of
`Stacks.Cohomology.FlatPullbackTensor.complexFunctor` is the complex `𝒢 ⊗ f^*ℱ` with terms
`𝒢^p ⊗ f^*ℱ` of [Stacks, Tag 0A1F] (`Stacks.Cohomology.ExtProjectionFormula.tensorModuleComplex`),
naturally in `ℱ`: transpose the two factors of the total complex
(`HomologicalComplex.mapBifunctorFlipIso`), use that a second factor concentrated in degree zero
gives the termwise complex (`CochainComplex.KFlatBifunctor.totalSingleIso`), and swap the factors
of each term by the symmetry of the tensor product.

## Main definitions

* `Stacks.Cohomology.ExtProjectionModelBridge.rowBraidIso`: `f^*ℱ ⊗ 𝒢^• ≅ 𝒢^• ⊗ f^*ℱ`.
* `Stacks.Cohomology.ExtProjectionModelBridge.singleIso`: `Tot(f^*ℱ[0] ⊗ 𝒢) ≅ 𝒢 ⊗ f^*ℱ`, natural
  in `ℱ` (`singleIso_hom_naturality`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.ExtProjectionModelBridge

universe u

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf


open Stacks.Cohomology.FlatPullbackTensor (bifunctor complexFunctor)
open CochainComplex.KFlatBifunctor (rowComplex totalSingleIso)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (G : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)

/-- The termwise complex `p ↦ f^*ℱ ⊗ 𝒢^p` with the factors of each term swapped. -/
def rowBraidIso (F : SheafOfModules.{u} (structureSheafRing Y)) :
    rowComplex (bifunctor f).flip G F ≅
      CochainComplex.KFlatBifunctor.rowComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) G
        ((modulePullback f).obj F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.sheaf).app (G.X p)).symm.app
      ((modulePullback f).obj F))
    (fun p p' _ => by
      have h := NatTrans.congr_app
        ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.sheaf).inv.naturality (G.d p p'))
        ((modulePullback f).obj F)
      exact h.symm)

/-- **`Tot(f^*ℱ[0] ⊗ 𝒢) ≅ 𝒢 ⊗ f^*ℱ`.** -/
def singleIso (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (complexFunctor f G).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) ≅
      CochainComplex.KFlatBifunctor.rowComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) G
        ((modulePullback f).obj F) :=
  (HomologicalComplex.mapBifunctorFlipIso
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) G (bifunctor f)
      (ComplexShape.up ℤ)).symm ≪≫
    totalSingleIso (bifunctor f).flip G F ≪≫ rowBraidIso f G F

/-- The braided termwise identification is natural in `ℱ`. -/
theorem rowBraidIso_hom_naturality {F F' : SheafOfModules.{u} (structureSheafRing Y)} (φ : F ⟶ F') :
    CochainComplex.KFlatBifunctor.rowComplexMapSecond (bifunctor f).flip G φ ≫
      (rowBraidIso f G F').hom = (rowBraidIso f G F).hom ≫
        CochainComplex.KFlatBifunctor.rowComplexMapSecond
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) G
          ((modulePullback f).map φ) :=
  HomologicalComplex.hom_ext _ _ (fun p =>
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.sheaf).app (G.X p)).inv.naturality
      ((modulePullback f).map φ))

/-- **`Tot(f^*ℱ[0] ⊗ 𝒢) ≅ 𝒢 ⊗ f^*ℱ` is natural in `ℱ`.** The left-hand side is
`(complexFunctor f G).map (φ[0])`, written as the map of total complexes it is. -/
theorem singleIso_hom_naturality {F F' : SheafOfModules.{u} (structureSheafRing Y)} (φ : F ⟶ F') :
    HomologicalComplex.mapBifunctorMap ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ)
        (𝟙 G) (bifunctor f) (ComplexShape.up ℤ) ≫ (singleIso f G F').hom =
      (singleIso f G F).hom ≫ CochainComplex.KFlatBifunctor.rowComplexMapSecond
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) G
        ((modulePullback f).map φ) := by
  have h₁ := HomologicalComplex.mapBifunctorFlipIso_hom_naturality
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ) (𝟙 G) (bifunctor f)
      (ComplexShape.up ℤ)
  have h₁' : HomologicalComplex.mapBifunctorMap
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ) (𝟙 G) (bifunctor f)
        (ComplexShape.up ℤ) ≫
      (HomologicalComplex.mapBifunctorFlipIso
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F') G (bifunctor f)
        (ComplexShape.up ℤ)).inv =
      (HomologicalComplex.mapBifunctorFlipIso
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) G (bifunctor f)
        (ComplexShape.up ℤ)).inv ≫
      HomologicalComplex.mapBifunctorMap (𝟙 G)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ) (bifunctor f).flip
        (ComplexShape.up ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, h₁, Iso.inv_hom_id_assoc]
  have h₂ := CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_second
    (bifunctor f).flip G φ
  exact ((reassoc_of% h₁') _).trans ((congrArg (_ ≫ ·) ((reassoc_of% h₂) _)).trans
    ((congrArg (fun x => _ ≫ _ ≫ x) (rowBraidIso_hom_naturality f G φ)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm))

end Stacks.Cohomology.ExtProjectionModelBridge

end

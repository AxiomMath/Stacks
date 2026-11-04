module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TensorProduct
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherentSheaves.Basic
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.AffineTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Global sections of a tensor product on an affine scheme

For modules `M` and `N` over a commutative ring `R`, the global sections of the tensor product
of the associated sheaves on `Spec R` are `M ⊗_R N`, and more generally the global sections of
a tensor product of two quasi-coherent sheaves of modules on an affine scheme are the tensor
product of their global sections.

## Main definitions

* `AlgebraicGeometry.tensorSheafCongr`: the tensor product of sheaves of modules on `Spec R` is
  functorial in both arguments.
* `AlgebraicGeometry.tildeTensorSectionsIso`: `Γ(Spec R, M~ ⊗ N~) ≅ M ⊗_R N`.
* `AlgebraicGeometry.isQuasicoherentTensorSectionsIso`: for quasi-coherent `F`, `G` on
  `Spec R`, `Γ(Spec R, F ⊗ G) ≅ Γ(Spec R, F) ⊗_R Γ(Spec R, G)`.  This is the form the affine
  projection formula of [Stacks, Tag 0FZE] consumes.

## Implementation notes

The comparison `(M ⊗_R N)~ ≅ M~ ⊗_{𝒪_{Spec R}} N~` of [Stacks, Tag 01I8] is
`AlgebraicGeometry.tildeTensorIso`, and the global-sections statements below are that comparison
read through the adjunction `AlgebraicGeometry.tilde.adjunction` of [Stacks, Tag 01I7], whose
unit is invertible at every module.  Nothing about tensor sheafification is reproved here.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Tensoring sheaves of modules on `Spec R` is functorial in both arguments. -/
noncomputable def tensorSheafCongr (R : CommRingCat.{u})
    {F F' G G' : (Spec R).Modules} (e : F ≅ F') (d : G ≅ G') :
    specTensorSheaf R F G ≅ specTensorSheaf R F' G' := by
  let X := (Spec R).toRingedSpace
  letI : MonoidalCategory (PresheafOfModules (structureSheafRing X).obj) := by
    change MonoidalCategory (PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    infer_instance
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
      (structureSheafRing X).property).mapIso
    (MonoidalCategory.tensorIso ((SheafOfModules.forget (structureSheafRing X)).mapIso e)
      ((SheafOfModules.forget (structureSheafRing X)).mapIso d))

/-- **Global sections of a tensor product of associated sheaves.**
`Γ(Spec R, M~ ⊗ N~) ≅ M ⊗_R N`. -/
noncomputable def tildeTensorSectionsIso (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    moduleSpecΓFunctor.obj (specTensorSheaf R (tilde M) (tilde N)) ≅ M ⊗ N :=
  (moduleSpecΓFunctor.mapIso (tildeTensorIso R M N)).symm ≪≫
    (asIso ((tilde.adjunction (R := R)).unit.app (M ⊗ N))).symm

/-- **Global sections of a tensor product of quasi-coherent modules on an affine scheme.**
For quasi-coherent `F` and `G` on `Spec R`,
`Γ(Spec R, F ⊗ G) ≅ Γ(Spec R, F) ⊗_R Γ(Spec R, G)`.

This is the form in which the affine case of the projection formula of
[Stacks, Tag 0FZE] consumes Tag 01I8: there the two factors are quasi-coherent modules
rather than associated sheaves, and the two sides of the formula are compared by their
global sections over the affine target. -/
noncomputable def isQuasicoherentTensorSectionsIso (R : CommRingCat.{u})
    (F G : (Spec R).Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    moduleSpecΓFunctor.obj (specTensorSheaf R F G) ≅
      moduleSpecΓFunctor.obj F ⊗ moduleSpecΓFunctor.obj G := by
  letI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  letI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  exact moduleSpecΓFunctor.mapIso
      (tensorSheafCongr R (asIso F.fromTildeΓ).symm (asIso G.fromTildeΓ).symm ≪≫
        (tildeTensorIso R (moduleSpecΓFunctor.obj F) (moduleSpecΓFunctor.obj G)).symm) ≪≫
    (asIso ((tilde.adjunction (R := R)).unit.app
      (moduleSpecΓFunctor.obj F ⊗ moduleSpecΓFunctor.obj G))).symm

end AlgebraicGeometry

end

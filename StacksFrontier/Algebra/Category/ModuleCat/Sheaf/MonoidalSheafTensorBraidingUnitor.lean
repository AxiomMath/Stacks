module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraiding
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors

/-!
# The tensor braiding carries the right unitor of `⊗_𝒪` to the left unitor

On a ringed site `(C, J, 𝒪)` the two unitors `ℱ ⊗_𝒪 𝒪 ≅ ℱ` and `𝒪 ⊗_𝒪 ℱ ≅ ℱ` of the tensor
product sheaf are related by the tensor braiding
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`: braiding the two factors and then cancelling
the structure sheaf on the right is cancelling it on the left.

## Main results

* `SheafOfModules.sheafTensorBraiding_comp_tensorSheafUnitRightIso`: the tensor braiding
  followed by the right unitor is the left unitor.
* `SheafOfModules.tensorSheafUnitLeftIso_eq_trans`: the same as an equality of isomorphisms.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (A : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- The tensor braiding followed by the right unitor of `⊗_𝒪` is the left unitor: braiding
`𝒪 ⊗_𝒪 ℱ` to `ℱ ⊗_𝒪 𝒪` and then cancelling the structure sheaf on the right is cancelling it on
the left. -/
theorem sheafTensorBraiding_comp_tensorSheafUnitRightIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).hom.app
            (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).app A ≫
        (Stacks.SheafOfModules.tensorSheafUnitRightIso R.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf R).property A).hom =
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property A).hom := by
  rw [← braiding_eq_sheafTensorBraiding R (unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) A,
    ← rightUnitor_sheafTensor_eq R A, ← leftUnitor_sheafTensor_eq R A]
  exact @braiding_rightUnitor _ _ (monoidalCategorySheafTensor R)
    (@SymmetricCategory.toBraidedCategory _ _ (monoidalCategorySheafTensor R)
      (symmetricCategorySheafTensor R)) A

/-- `SheafOfModules.sheafTensorBraiding_comp_tensorSheafUnitRightIso` as an equality of
isomorphisms: the left unitor of `⊗_𝒪` is the tensor braiding followed by the right unitor. -/
theorem tensorSheafUnitLeftIso_eq_trans :
    Stacks.SheafOfModules.tensorSheafUnitLeftIso R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property A =
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app
            (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).app A ≪≫
        Stacks.SheafOfModules.tensorSheafUnitRightIso R.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf R).property A :=
  Iso.ext (sheafTensorBraiding_comp_tensorSheafUnitRightIso R A).symm

end SheafOfModules

end

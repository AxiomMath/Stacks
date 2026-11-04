module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits

/-!
# Tensoring in the right variable commutes with coproducts

On a ringed site `(C, 𝒪)` the tensor product sheaf of [Stacks, Tag 01CA] is the tensor product of
a monoidal structure on `Mod(𝒪)` in which it is the tensor product on the nose, so tensoring with
a fixed sheaf of modules in *either* variable commutes with arbitrary colimits. This file records
the right-variable statement and its consequence for a coproduct of copies of the structure sheaf:

`(⨁_{i ∈ ι} 𝒪) ⊗_𝒪 ℒ ≅ ⨁_{i ∈ ι} ℒ`.

## Main results

* `Stacks.SheafOfModules.Strict.preservesColimit_sheafTensorFlip`: tensoring in the right variable
  commutes with colimits.
* `Stacks.SheafOfModules.Strict.unitTensorIso`: the structure sheaf is a unit for the tensor
  product sheaf.
* `Stacks.SheafOfModules.Strict.coproductUnitTensorIso`: a coproduct of copies of the structure
  sheaf, tensored with `ℒ`, is a coproduct of copies of `ℒ`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

/-- **Tensoring in the right variable commutes with colimits.** The tensor product sheaf is the
tensor product of a monoidal structure on `Mod(𝒪)`, which is closed, so tensoring with a fixed
object on either side is a left adjoint. -/
theorem preservesColimit_sheafTensorFlip {K : Type*} [Category K] (F : K ⥤ Mod R) (L : Mod R) :
    PreservesColimit F ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj L) :=
  (preservesColimit_iff_of_natIso F (tensorRightIsoSheafTensor R L)).mp
    (preservesColimit_tensorRight R F L)

/-- **The structure sheaf is a unit for the tensor product sheaf**, `𝒪 ⊗_𝒪 ℒ ≅ ℒ`. -/
def unitTensorIso (L : Mod R) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj L).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≅ L :=
  MonoidalCategoryStruct.leftUnitor
    (self := (monoidalCategory R.obj (isSheaf_ringSheaf R)).toMonoidalCategoryStruct) L

/-- **A coproduct of copies of the structure sheaf, tensored with `ℒ`, is a coproduct of copies
of `ℒ`.** Tensoring in the right variable commutes with the coproduct, and each summand is
`𝒪 ⊗_𝒪 ℒ ≅ ℒ`. -/
def coproductUnitTensorIso (L : Mod R) (ι : Type w)
    [HasColimitsOfShape (Discrete ι) (Mod R)] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj L).obj
        (∐ fun _ : ι => _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≅
      ∐ fun _ : ι => L :=
  have := preservesColimit_sheafTensorFlip R
    (Discrete.functor fun _ : ι =>
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) L
  preservesColimitIso ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj L) _ ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => unitTensorIso R L)

end Stacks.SheafOfModules.Strict

end

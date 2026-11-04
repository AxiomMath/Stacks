module

public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkNaturality
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# The tensor product of modules on a scheme: quasi-coherence and an invertible factor

Two basic properties of the tensor product `L ⊗_{𝒪_X} N` of modules on a scheme. First, it is
quasi-coherent as soon as both factors are, which is [Stacks, Tag 01CE] for the tensor product
`AlgebraicGeometry.Scheme.Modules.tensorObj`. Second, tensoring on the right by an invertible
module `L` is an equivalence, so it is faithful and reflects vanishing of a morphism, and
`(F ⊗ L) ⊗ L^{⊗ -1}` is canonically `F`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tensorInverse`: the inverse tensor power `L^{⊗ -1}` of an
  invertible module, read as a module on the scheme.
* `AlgebraicGeometry.Scheme.Modules.tensorInverseCancelIso`: the cancellation isomorphism
  `(F ⊗ L) ⊗ L^{⊗ -1} ≅ F`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj`: [Stacks, Tag 01CE] for
  `tensorObj`.
* `AlgebraicGeometry.Scheme.Modules.isInvertible_tensorInverse`: the inverse tensor power is
  again invertible.
* `AlgebraicGeometry.Scheme.Modules.isEquivalence_invertibleTensorRightFunctor`: tensoring on
  the right by an invertible module is an equivalence.
* `AlgebraicGeometry.Scheme.Modules.eq_zero_of_tensorRightMap_eq_zero`: tensoring on the right
  by an invertible module reflects vanishing of a morphism.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Stacks Project, Tag 01CE** for modules on a scheme: the tensor product of two
quasi-coherent `𝒪_X`-modules is quasi-coherent. -/
theorem isQuasicoherent_tensorObj (A B : X.Modules) (hA : A.IsQuasicoherent)
    (hB : B.IsQuasicoherent) : (Scheme.Modules.tensorObj A B).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace A B hA hB

/-- The inverse tensor power `L^{⊗ -1}` of an invertible `𝒪_X`-module, read as a module on the
scheme. -/
abbrev tensorInverse (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    X.Modules :=
  Stacks.SheafOfModules.Invertible.tensorPower X.sheaf.obj X.ringCatSheaf.property L (-1)

/-- The inverse tensor power of an invertible module is invertible, by
[Stacks, Tag 01CU]. -/
theorem isInvertible_tensorInverse (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorInverse L) :=
  have _ : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower X.sheaf.obj
      X.ringCatSheaf.property L (-1))

/-- The cancellation isomorphism `(F ⊗ L) ⊗ L^{⊗ -1} ≅ F` for an invertible module `L`. -/
def tensorInverseCancelIso (F L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Scheme.Modules.tensorObj (Scheme.Modules.tensorObj F L) (tensorInverse L) ≅ F :=
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  have : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).flip.obj (L))).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor X.sheaf.obj
      X.ringCatSheaf.property L
  have eLW : Scheme.Modules.tensorObj L (tensorInverse L) ≅ SheafOfModules.unit X.ringCatSheaf :=
    Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property
        (Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.sheaf.obj
          X.ringCatSheaf.property L).symm (Iso.refl _) ≪≫
      Stacks.SheafOfModules.TensorPower.tensorPowerMulIso X.sheaf.obj X.ringCatSheaf.property
        L 1 (-1)
  Stacks.SheafOfModules.Invertible.tensorProductAssociator X.sheaf.obj
      X.ringCatSheaf.property F L _ ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property
      (Iso.refl F) eLW ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.sheaf.obj
      X.ringCatSheaf.property F

/-- Tensoring on the right by an invertible module is an equivalence, in the convention of
[Stacks, Tag 01CU]. -/
theorem isEquivalence_invertibleTensorRightFunctor (W : X.Modules)
    [hW : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).flip.obj (W))).IsEquivalence :=
  have : Stacks.SheafOfModules.IsInvertible _ X.ringCatSheaf.property W :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ W hW
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence _ _ W

/-- Tensoring on the right by an invertible module reflects vanishing of a morphism: if
`f ⊗ W = 0` then `f = 0`. -/
theorem eq_zero_of_tensorRightMap_eq_zero {A B : X.Modules} (W : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    (f : A ⟶ B) (h : Scheme.Modules.tensorRightMap f W = 0) : f = 0 := by
  have hfaith := (isEquivalence_invertibleTensorRightFunctor W).faithful
  have := (isEquivalence_invertibleTensorRightFunctor W).full
  exact hfaith.map_injective (X := A) (Y := B) (h.trans (Functor.map_zero
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).flip.obj (W))) A B).symm)

end AlgebraicGeometry.Scheme.Modules

end

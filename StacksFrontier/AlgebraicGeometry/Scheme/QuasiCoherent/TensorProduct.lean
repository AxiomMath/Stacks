module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# Functoriality of tensor products of associated sheaves on an affine scheme

For modules `M` and `N` over a commutative ring `R`, a pair of module maps `M ⟶ M'` and
`N ⟶ N'` induces a map of tensor-product sheaves
`M̃ ⊗ Ñ ⟶ M̃' ⊗ Ñ'` on `Spec R`, where the tensor product of sheaves of modules is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, the sheafification of the sectionwise
tensor-product presheaf.

## Main definitions

* `AlgebraicGeometry.tildeTensorSheafMap`: the morphism of tensor-product sheaves induced by two
  module maps.

## Implementation notes

The affine scheme is presented as `Spec R` and Mathlib's `AlgebraicGeometry.tilde` is
its associated-sheaf construction. The induced map is built by applying the sheafification
functor to the tensor product of the two underlying presheaf morphisms, so it is the
sheafification of the sectionwise map.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

universe u

/-- The map `M̃ ⊗ Ñ ⟶ M̃' ⊗ Ñ'` between tensor-product sheaves on `Spec R` induced by module
maps `f : M ⟶ M'` and `g : N ⟶ N'`. -/
public noncomputable def tildeTensorSheafMap (R : CommRingCat.{u})
    {M M' N N' : ModuleCat.{u} R} (f : M ⟶ M') (g : N ⟶ N') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Spec R).presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (Spec R).presheaf (forget₂ CommRingCat RingCat)
        (Spec R).ringCatSheaf.2⟩).obj (tilde M)).obj (tilde N) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Spec R).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (Spec R).presheaf (forget₂ CommRingCat RingCat)
          (Spec R).ringCatSheaf.2⟩).obj (tilde M')).obj (tilde N') :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify (Spec R).presheaf (Spec
    R).ringCatSheaf.2).map
    (PresheafOfModules.Monoidal.tensorHom (R := (Spec R).presheaf)
      (tilde.map f).val (tilde.map g).val)

end AlgebraicGeometry

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace

/-!
# External tensor products of modules

Given two schemes over a common base, the external tensor product of a module on each
scheme is the tensor product, on their fibre product, of the two pullback modules.

## Main definitions

* `AlgebraicGeometry.externalTensorProduct` is the external tensor product of two modules on
  schemes over a common base.

## Implementation notes

The fibre product and its projections are the categorical pullback and its canonical
projections. The tensor product of module sheaves is
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`. The
definition is an abbreviation so that clients can directly use the APIs of pullback and
tensor product sheaves.

## References

* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Limits

universe u

/-- The external tensor product of an `O_X`-module and an `O_Y`-module on the fibre
product of two schemes `X` and `Y` over `S`. -/
@[stacks 0G46 "external_tensor_product_of_modules"]
noncomputable abbrev externalTensorProduct {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (F : X.Modules) (G : Y.Modules) : (pullback f g).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(((pullback f g).toRingedSpace)).presheaf, (((pullback f g).toRingedSpace)).IsSheaf⟩).obj
      (((Scheme.Modules.pullback (pullback.fst f g)).obj F))).obj
        (((Scheme.Modules.pullback (pullback.snd f g)).obj G)))

end AlgebraicGeometry

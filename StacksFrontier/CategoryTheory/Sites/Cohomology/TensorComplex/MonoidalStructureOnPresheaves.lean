module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-! # The monoidal structure on presheaves of modules on a ringed site

Sheaves of modules on a ringed site `(C, O)` are indexed by the sheaf of (not necessarily
commutative) rings `AlgebraicGeometry.RingedSite.ringSheaf`, while the monoidal structure
`PresheafOfModulesOfCommRing.monoidalCategory` on presheaves of modules is only available over a
presheaf of *commutative* rings. This file records, once, the instances that bridge the two
and that every construction of a tensor product of complexes of modules on a ringed site
needs: the `CommRing` structure on the sections of `ringSheaf`, the monoidal structure on
presheaves of modules over it, and the preservation of zero morphisms and additivity of the
tensor bifunctor and of its partial applications, which is what makes the total complex of a
double complex of tensor products available and what lets it be compared with a shift.

All six are declared as **file-local** instances, exactly as they were when each consumer
declared its own copy: `CommRing (X.ringSheaf.obj.obj U)` would otherwise be a second route to
`Ring (X.ringSheaf.obj.obj U)` alongside the one `RingCat` already carries, and registering it
globally puts that diamond in front of every downstream file. A consumer switches them on with

```lean
attribute [local instance] AlgebraicGeometry.RingedSite.ringSheafSectionsCommRing
  AlgebraicGeometry.RingedSite.presheafOfModulesMonoidalCategory
  AlgebraicGeometry.RingedSite.curriedTensorPreservesZeroMorphisms
  AlgebraicGeometry.RingedSite.curriedTensorObjPreservesZeroMorphisms
  AlgebraicGeometry.RingedSite.curriedTensorAdditive
  AlgebraicGeometry.RingedSite.curriedTensorObjAdditive
```

which is the same idiom as
`AlgebraicGeometry.SheafOfModules.presheafOfModulesMonoidalCategory` and its consumer
`StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic`.

## Main definitions

* `AlgebraicGeometry.RingedSite.ringSheafSectionsCommRing`: the sections of the structure sheaf
  are a commutative ring, at the spelling `X.ringSheaf` at which sheaves of modules are indexed.
* `AlgebraicGeometry.RingedSite.presheafOfModulesMonoidalCategory`: presheaves of modules over
  the structure sheaf of a ringed site are monoidal, the tensor product being the pointwise one.

## Main results

* `AlgebraicGeometry.RingedSite.curriedTensorPreservesZeroMorphisms` and
  `AlgebraicGeometry.RingedSite.curriedTensorObjPreservesZeroMorphisms`: the tensor bifunctor
  and its partial applications preserve zero morphisms.
* `AlgebraicGeometry.RingedSite.curriedTensorAdditive` and
  `AlgebraicGeometry.RingedSite.curriedTensorObjAdditive`: they are additive. Both are needed by
  `Mathlib`'s comparison of the total complex of a bifunctor with a shift, and both hold for the
  same reason as the two above: the tensor product of presheaves of modules is pointwise, and
  the pointwise tensor product is bilinear.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

/-- The sections of the structure sheaf of a ringed site are a commutative ring, also at the
spelling `X.ringSheaf` at which sheaves of modules are indexed. -/
noncomputable local instance ringSheafSectionsCommRing (U : X.Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :=
  inferInstanceAs (CommRing (X.O.obj.obj U))

/-- Presheaves of modules over the structure sheaf of a ringed site are monoidal, the tensor
product being the pointwise one. -/
noncomputable local instance presheafOfModulesMonoidalCategory :
    MonoidalCategory (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.O.obj)

/-- The tensor bifunctor of presheaves of modules on a ringed site preserves zero morphisms. -/
local instance curriedTensorPreservesZeroMorphisms :
    (curriedTensor
      (PresheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).PreservesZeroMorphisms where
  map_zero {A B} := by
    apply NatTrans.ext
    funext C
    ext U : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun a c => ?_
    change (0 : B.obj U) ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] c = 0
    exact TensorProduct.zero_tmul _ _

/-- Tensoring with a fixed presheaf of modules on a ringed site preserves zero morphisms. -/
local instance curriedTensorObjPreservesZeroMorphisms
    (A : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    ((curriedTensor
      (PresheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj A).PreservesZeroMorphisms where
  map_zero {B C} := by
    ext U : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun a b => ?_
    change a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] (0 : C.obj U) = 0
    exact TensorProduct.tmul_zero _ _

/-- The tensor bifunctor of presheaves of modules on a ringed site is additive. -/
local instance curriedTensorAdditive :
    (curriedTensor
      (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).Additive where
  map_add {A B f g} := by
    apply NatTrans.ext
    funext C
    ext U : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun a c => ?_
    change (f.app U a + g.app U a) ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] c = _
    exact TensorProduct.add_tmul _ _ _

/-- Tensoring with a fixed presheaf of modules on a ringed site is additive. -/
local instance curriedTensorObjAdditive
    (A : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    ((curriedTensor
      (PresheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj A).Additive where
  map_add {B C f g} := by
    ext U : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun a b => ?_
    change a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] (f.app U b + g.app U b) = _
    exact TensorProduct.tmul_add _ _ _

end AlgebraicGeometry.RingedSite

end

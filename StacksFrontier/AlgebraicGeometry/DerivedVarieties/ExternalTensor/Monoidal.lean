module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorFunctorial

/-!
# The external tensor product is monoidal

Let `X` and `Y` be schemes over `S`. The external tensor product `E ⊠ G` of an `O_X`-module `E`
and an `O_Y`-module `G` is the tensor product of their pullbacks to `X ×_S Y`. It carries the
pair of structure sheaves to the structure sheaf and tensor products to tensor products, so that
`(E ⊠ G) ⊗ (E' ⊠ G') ≅ (E ⊗ E') ⊠ (G ⊗ G')` and, by induction, the `n`-th tensor power of
`E ⊠ G` is `E^{⊗ n} ⊠ G^{⊗ n}`.

## Main definitions

* `AlgebraicGeometry.tensorSheafUnitLeft`, `AlgebraicGeometry.tensorSheafUnitRight`,
  `AlgebraicGeometry.tensorSheafAssoc`, `AlgebraicGeometry.tensorSheafInterchange`: the unitors,
  the associator and the interchange isomorphism of the tensor product of modules on a ringed
  space.
* `AlgebraicGeometry.tensorSheafMapIso`: a pair of isomorphisms of modules induces an
  isomorphism of tensor products.
* `AlgebraicGeometry.tensorSheafNPow`: the `n`-th tensor power of a module on a ringed space.
* `AlgebraicGeometry.externalTensorProductUnitIso`: the external tensor product of the two
  structure sheaves is the structure sheaf of the fibre product.
* `AlgebraicGeometry.externalTensorProductTensorIso`: the external tensor product commutes with
  tensor products in each variable.
* `AlgebraicGeometry.externalTensorProductNPowIso`: the `n`-th tensor power of an external
  tensor product is the external tensor product of the `n`-th tensor powers.

## Implementation notes

The tensor product is the native bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`.
The native monoidal structure `SheafOfModules.monoidalCategorySheafTensor` has that tensor
product on objects, so the unitors, associator, and braiding apply directly, without a comparison
between tensor representations. The monoidal structures are activated only locally.

`AlgebraicGeometry.tensorSheafNPow` is not `Stacks.tensorPower`: the latter is defined by
iterating the autoequivalence given by tensoring with an *invertible* module, so it exists only
for invertible modules, while the external tensor product has to be raised to a power for
arbitrary ones. Its zeroth power is the structure sheaf, which is what lets the induction for
`externalTensorProductNPowIso` run with no separate base case at `n = 1`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

section RingedSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

attribute [local instance] presheafOfModulesMonoidal
  _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor

/-- A pair of isomorphisms of modules on a ringed space induces an isomorphism of their tensor
products, namely the induced map on tensor products. -/
noncomputable def tensorSheafMapIso {F F' G G' : SheafOfModules.{u} (structureSheafRing X)}
    (e : F ≅ F') (e' : G ≅ G') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (F)).obj (G)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (F')).obj (G')) :=
  (Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).mapIso
      (X := (F, G)) (Y := (F', G')) (Iso.prod e e')

/-- The monoidal structure on modules over a ringed space whose tensor product is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` and whose unit is the structure sheaf.
-/
noncomputable local instance ringedSpaceMonoidal :
    MonoidalCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  _root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf

/-- The monoidal structure `ringedSpaceMonoidal` on modules over a ringed space is braided. -/
noncomputable local instance ringedSpaceBraided :
    BraidedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (_root_.SheafOfModules.symmetricCategorySheafTensor X.sheaf).toBraidedCategory

/-- Tensoring with the structure sheaf on the left changes nothing. -/
noncomputable def tensorSheafUnitLeft (F : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
      ((SheafOfModules.unit (structureSheafRing X)))).obj (F)) ≅ F :=
  (_root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf).toMonoidalCategoryStruct.leftUnitor F

/-- Tensoring with the structure sheaf on the right changes nothing. -/
noncomputable def tensorSheafUnitRight (F : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (F)).obj
      ((SheafOfModules.unit (structureSheafRing X)))) ≅ F :=
  (_root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf).toMonoidalCategoryStruct.rightUnitor F

/-- The tensor product of modules on a ringed space is associative. -/
noncomputable def tensorSheafAssoc (F G H : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (F)).obj
          (G))))).obj (H)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (F)).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G)).obj
          (H))))) :=
  (_root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf).toMonoidalCategoryStruct.associator
    F G H

/-- The middle two factors of a fourfold tensor product of modules on a ringed space may be
exchanged. -/
noncomputable def tensorSheafInterchange
    (A B C D : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (A)).obj
          (B))))).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (C)).obj
          (D))))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (A)).obj
          (C))))).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (B)).obj
          (D))))) :=
  α_ A B (C ⊗ D) ≪≫
    whiskerLeftIso A ((α_ B C D).symm ≪≫ whiskerRightIso (β_ B C) D ≪≫ α_ C B D) ≪≫
    (α_ A C (B ⊗ D)).symm

/-- The `n`-th tensor power of a module on a ringed space, with the structure sheaf as the
zeroth power. -/
noncomputable def tensorSheafNPow (F : SheafOfModules.{u} (structureSheafRing X)) :
    ℕ → SheafOfModules.{u} (structureSheafRing X)
  | 0 => SheafOfModules.unit (structureSheafRing X)
  | n + 1 =>
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
      ((tensorSheafNPow F n))).obj (F))

/-- The zeroth tensor power of a module on a ringed space is the structure sheaf. -/
@[simp] theorem tensorSheafNPow_zero (F : SheafOfModules.{u} (structureSheafRing X)) :
    tensorSheafNPow X F 0 = SheafOfModules.unit (structureSheafRing X) := rfl

/-- The `(n + 1)`-st tensor power of `F` is the tensor product of the `n`-th power with `F`. -/
@[simp] theorem tensorSheafNPow_succ (F : SheafOfModules.{u} (structureSheafRing X)) (n : ℕ) :
    tensorSheafNPow X F (n + 1) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
        ((tensorSheafNPow X F n))).obj (F)) := rfl

end RingedSpace

section Scheme

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The external tensor product of the two structure sheaves is the structure sheaf of the
fibre product. -/
noncomputable def externalTensorProductUnitIso :
    externalTensorProduct f g (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit (pullback f g).ringCatSheaf :=
  tensorSheafMapIso (pullback f g).toRingedSpace
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (pullback.fst f g))
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (pullback.snd f g)) ≪≫
    tensorSheafUnitLeft (pullback f g).toRingedSpace _

/-- The external tensor product commutes with tensor products: the tensor product of
`E ⊠ G` and `E' ⊠ G'` on `X ×_S Y` is `(E ⊗ E') ⊠ (G ⊗ G')`. -/
noncomputable def externalTensorProductTensorIso
    (E E' : X.Modules) (G G' : Y.Modules) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((pullback f g).toRingedSpace)).presheaf, (((pullback f g).toRingedSpace)).IsSheaf⟩).obj
        ((externalTensorProduct f g E G))).obj ((externalTensorProduct f g E' G'))) ≅
      externalTensorProduct f g
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (E')))
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (G)).obj (G'))) :=
  tensorSheafInterchange (pullback f g).toRingedSpace _ _ _ _ ≪≫
    tensorSheafMapIso (pullback f g).toRingedSpace
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (pullback.fst f g) E E').symm
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (pullback.snd f g) G G').symm

/-- The `n`-th tensor power of an external tensor product is the external tensor product of the
`n`-th tensor powers. -/
noncomputable def externalTensorProductNPowIso (E : X.Modules) (G : Y.Modules) (n : ℕ) :
    tensorSheafNPow (pullback f g).toRingedSpace (externalTensorProduct f g E G) n ≅
      externalTensorProduct f g
        (tensorSheafNPow X.toRingedSpace E n) (tensorSheafNPow Y.toRingedSpace G n) := by
  induction n with
  | zero => exact (externalTensorProductUnitIso f g).symm
  | succ n ih =>
      exact tensorSheafMapIso (pullback f g).toRingedSpace ih (Iso.refl _) ≪≫
        externalTensorProductTensorIso f g _ E _ G

end Scheme

end AlgebraicGeometry

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf

/-!
# The ringed-space tensor product of sheaves of modules agrees with the monoidal one

For a ringed space `X`, the module
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace` describes the tensor
product
of two presheaves of `𝒪_X`-modules as the presheaf `U ↦ ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)`, and the tensor
product of two sheaves of modules as its sheafification. This file shows that these are
definitionally the tensor products coming from Mathlib's monoidal structure on presheaves of
modules, on objects and on morphisms, before and after sheafification, and deduces that the strict
monoidal structure on sheaves of `𝒪_X`-modules has this tensor product.

## Main results

* `Stacks.TensorSheafDedup.structureSheafRing_eq`: the sheaf of rings of a ringed space is the
  structure sheaf of its presheaf of commutative rings.
* `Stacks.TensorSheafDedup.sheafify_eq`: the two module-sheafification functors are the same
  functor, both being `PresheafOfModules.sheafification (𝟙 _)` over that sheaf of rings.
* `Stacks.TensorSheafDedup.presheafTensor_eq_tensorObj` and
  `Stacks.TensorSheafDedup.presheafTensor_eq_monoidalTensorObj`: the sectionwise presheaf tensor
  product is `Stacks.tensorObj`, and is Mathlib's monoidal product of presheaves of modules.
* `Stacks.TensorSheafDedup.tensorSheaf_eq` and
  `Stacks.TensorSheafDedup.tensorSheafMap_eq_sheafifyMap`: the same after sheafification, for the
  tensor product sheaf and for the induced morphism of tensor product sheaves.
* `Stacks.TensorSheafDedup.exists_monoidalCategory_tensorSheaf`: there is a monoidal structure on
  sheaves of `𝒪_X`-modules on a ringed space whose unit is `SheafOfModules.unit`, whose tensor
  product is given by `Stacks.SheafOfModules.Tensor.sheafTensor`, and whose tensor product of
  morphisms is the induced morphism of tensor product sheaves.

## Implementation notes

The object comparisons are `rfl`: the two presheaves of modules have the same modules of
sections, and their restriction maps are `TensorProduct.lift` of bilinear maps with the same
underlying function. Sheafification preserves the identification because on both sides it is
`PresheafOfModules.sheafification` at the identity of the same ring presheaf. The morphism
comparisons use `Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`.

The ringed space is taken at a single universe, `AlgebraicGeometry.RingedSpace.{u, u}`, which is
also the single module universe of Mathlib's monoidal structure on presheaves of modules.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [The Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/
@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace Stacks.TensorSheafDedup

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The sheaf of rings of a ringed space is the structure sheaf of its presheaf of commutative
rings. -/
theorem structureSheafRing_eq :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
      (structureSheafRing X).property =
      structureSheafRing X :=
  rfl

/-- The two module-sheafification functors agree: both are
`PresheafOfModules.sheafification (𝟙 _)` over the structure sheaf of rings. -/
theorem sheafify_eq :
    Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
      (structureSheafRing X).property
      = Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X :=
  rfl

section Presheaf

variable (F G : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorStalkRingedSpace.O X))

/-- The sectionwise tensor product of two presheaves of modules over a ringed space is
`Stacks.tensorObj`. -/
theorem presheafTensor_eq_tensorObj :
    (PresheafOfModules.tensorObj (O := (X).presheaf) (F) (G)) = Stacks.tensorObj F G :=
  rfl

/-- The sectionwise tensor product of two presheaves of modules over a ringed space is their
monoidal product in the category of presheaves of modules. -/
theorem presheafTensor_eq_monoidalTensorObj :
    (PresheafOfModules.tensorObj (O := (X).presheaf) (F) (G)) = F ⊗ G :=
  rfl

end Presheaf

section Sheaf

variable (A B : SheafOfModules.{u} (structureSheafRing
  X))

/-- The tensor product of two sheaves of modules over a ringed space, formed with the sheaf
property of the ringed space, is the one formed with the sheaf property of its sheaf of rings. -/
theorem tensorSheaf_eq :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (A)).obj (B)) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          ((structureSheafRing X).property)⟩).obj (A)).obj (B)) :=
  rfl

end Sheaf

/-- The morphism of tensor product sheaves induced by `f` and `g` is the sheafification of the
monoidal product of the underlying morphisms of presheaves of modules. -/
theorem tensorSheafMap_eq_sheafifyMap
    {A A' B B' : SheafOfModules.{u} (structureSheafRing
      X)}
    (f : A ⟶ A') (g : B ⟶ B') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((f, g) : (_, _) ⟶ (_, _))) =
      (Stacks.SheafOfModules.sheafifyFunctor X.presheaf
        (structureSheafRing X).property).map (f.val ⊗ₘ g.val) :=
  Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf f g

/-- There is a monoidal structure on sheaves of `𝒪_X`-modules on a ringed space whose unit is
`SheafOfModules.unit`, whose tensor product is given by `Stacks.SheafOfModules.Tensor.sheafTensor`,
and whose tensor product of morphisms is the induced morphism of tensor product sheaves. -/
theorem exists_monoidalCategory_tensorSheaf :
    ∃ M : MonoidalCategory (SheafOfModules.{u}
      (structureSheafRing X)),
      letI := M
      ∃ (_hunit : 𝟙_ (SheafOfModules.{u}
        (structureSheafRing X)) =
            SheafOfModules.unit (structureSheafRing X))
        (htensor : ∀ A B : SheafOfModules.{u}
          (structureSheafRing X),
            A ⊗ B = (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (A)).obj (B))),
        ∀ {A A' B B' : SheafOfModules.{u}
          (structureSheafRing X)}
          (f : A ⟶ A') (g : B ⟶ B'),
          eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((f, g) : (_, _) ⟶ (_, _))) :=
  ⟨Stacks.SheafOfModules.Strict.monoidalCategory X.presheaf
      (structureSheafRing X).property, rfl, fun _ _ ↦ rfl, fun f g ↦
    (Category.id_comp _).trans ((Category.comp_id _).trans
      ((Stacks.SheafOfModules.Strict.tensorHom_eq_sheafifyMap X.presheaf
        (structureSheafRing X).property f g).trans
          (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf f g).symm))⟩

end Stacks.TensorSheafDedup

end

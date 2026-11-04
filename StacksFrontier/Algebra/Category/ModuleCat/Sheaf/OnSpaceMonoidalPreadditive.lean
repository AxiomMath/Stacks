module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness

/-!
# The tensor product of modules on a ringed space is biadditive

`Stacks.SheafOfModules.OnSpace.monoidal` is the monoidal structure of [Stacks, Tag 01CA] on the
sheaves of modules over a ringed space: the tensor product is the sheafified tensor product and
the unit is the structure sheaf. This file proves that it is biadditive on morphisms, which is
`CategoryTheory.MonoidalPreadditive` for that structure, together with the one-variable
statements it rests on.

Biadditivity is what makes tensoring by a fixed module an additive functor, and so what lets an
additive statement — a kernel, a span, a surjectivity — be carried across a bijection of
hom-groups assembled from unitors, associators and whiskerings, in particular across the
hom-group form of the duality of a finite locally free module. Before this file the statements
available about the induced map `φ ⊗ ψ` were that it is the identity on a pair of identities,
zero on the pair `(0, 0)`, and compatible with composition; additivity in *one* variable, and so
already `φ ⊗ 0 = 0`, was not among them.

## Main results

* `Stacks.SheafOfModules.OnSpace.tensorSheafMap_add_left` and `_add_right`: the canonical
  induced morphism of sheafified tensor products is additive in each variable, with
  `tensorSheafMap_zero_right` the value at a zero map in the right variable (the left-hand
  companion `AlgebraicGeometry.SheafOfModules.tensorSheafMap_zero_left` is available already).
* `Stacks.SheafOfModules.OnSpace.tensorHom_eq_tensorSheafMap`: the monoidal product of two
  morphisms is the canonical induced morphism of the tensor product bifunctor
  `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `Stacks.SheafOfModules.OnSpace.monoidalPreadditive`: **the tensor product of modules on a
  ringed space is biadditive.**

## Implementation notes

The induced morphism of sheafified tensor products is the map of the uncurried bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, which by
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` is the sheafification of the
presheaf-level induced map `PresheafOfModules.tensorHom`. So each statement below is the
corresponding presheaf-level one — `PresheafOfModules.tensorHom_add_left`,
`tensorHom_add_right`, `tensorHom_zero_right`, each of which computes on local pure tensors —
carried through sheafification, which is additive because it is a left adjoint between
preadditive categories (`PresheafOfModules.sheafification_additive`). That is the same route as
the left-hand companion `AlgebraicGeometry.SheafOfModules.tensorSheafMap_zero_left`.

The four fields of `CategoryTheory.MonoidalPreadditive` are statements about the two
whiskerings. Each is turned into a statement about `φ ⊗ₘ ψ` by
`CategoryTheory.MonoidalCategory.id_tensorHom` and `tensorHom_id`, and then into one about the
bifunctor by `tensorHom_eq_tensorSheafMap`, which is
`Stacks.SheafOfModules.OnSpace.monoidal_tensorHom` with its two `eqToHom`s — both of them on a
`rfl`, since `monoidal_tensorObj` holds by `rfl` — discharged. Going through the bifunctor
rather than computing the whiskerings directly is what avoids the `ULift` spellings that the
transport defining `monoidal` leaves on the implicit arguments of
`Stacks.SheafOfModules.OnSpace.tensor_hom_ext`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TensorProduct

universe u

namespace Stacks.SheafOfModules.OnSpace

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace

-- The ring sheaf of a ringed space is written `⟨X.presheaf, X.IsSheaf⟩`, whose `property` field
-- is a proof of `X.presheaf.IsSheaf` where the sheaf structure wants
-- `Presheaf.IsSheaf (JX X) X.presheaf`.  The two are the same by definition, but not at
-- `implicit` transparency, so without this the statements below are not type-correct for `rw`.
-- `AlgebraicGeometry.SheafOfModules.tensorSheafMap_zero_left` does the same.
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.sheafTensor
  PresheafOfModules.tensorObj TopCat.Presheaf.IsSheaf

variable (X : RingedSpace.{u, u})

/-- **The induced morphism of tensor products of modules on a ringed space is additive in its
right variable.** On a local pure tensor it is `m ⊗ n ↦ φ(m) ⊗ ψ(n) + φ(m) ⊗ ψ'(n)`. -/
theorem tensorSheafMap_add_right {A B C D : SheafOfModules.{u} (structureSheafRing X)}
    (φ : A ⟶ C) (ψ ψ' : B ⟶ D) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
          ((φ, ψ + ψ') : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
            ((φ, ψ) : (_, _) ⟶ (_, _))) +
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
              ((φ, ψ') : (_, _) ⟶ (_, _))) := by
  refine (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) φ (ψ + ψ')).trans
    (Eq.trans ?_ (congrArg₂ (· + ·)
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) φ ψ).symm
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) φ ψ').symm))
  rw [show (ψ + ψ').val = ψ.val + ψ'.val from rfl, PresheafOfModules.tensorHom_add_right]
  apply CategoryTheory.Functor.map_add

/-- **The induced morphism of tensor products of modules on a ringed space is additive in its
left variable.** On a local pure tensor it is `m ⊗ n ↦ φ(m) ⊗ ψ(n) + φ'(m) ⊗ ψ(n)`. -/
theorem tensorSheafMap_add_left {A B C D : SheafOfModules.{u} (structureSheafRing X)}
    (φ φ' : A ⟶ C) (ψ : B ⟶ D) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
          ((φ + φ', ψ) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
            ((φ, ψ) : (_, _) ⟶ (_, _))) +
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
              ((φ', ψ) : (_, _) ⟶ (_, _))) := by
  refine (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) (φ + φ') ψ).trans
    (Eq.trans ?_ (congrArg₂ (· + ·)
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) φ ψ).symm
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) φ' ψ).symm))
  rw [show (φ + φ').val = φ.val + φ'.val from rfl, PresheafOfModules.tensorHom_add_left]
  apply CategoryTheory.Functor.map_add

/-- **The induced morphism of tensor products vanishes when the right factor does.** -/
theorem tensorSheafMap_zero_right {A B C D : SheafOfModules.{u} (structureSheafRing X)}
    (φ : A ⟶ C) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
        ((φ, (0 : B ⟶ D)) : (_, _) ⟶ (_, _))) = 0 := by
  refine (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) φ (0 : B ⟶ D)).trans ?_
  rw [show (0 : B ⟶ D).val = 0 from rfl, PresheafOfModules.tensorHom_zero_right]
  exact CategoryTheory.Functor.map_zero _ _ _

attribute [local instance] monoidal

/-- The monoidal product of two morphisms for `Stacks.SheafOfModules.OnSpace.monoidal` is the
canonical induced morphism of tensor product sheaves. This is
`Stacks.SheafOfModules.OnSpace.monoidal_tensorHom` with the two identifications of the objects
discharged, which is the form the biadditivity proof consumes. -/
theorem tensorHom_eq_tensorSheafMap {A B C D : SheafOfModules.{u} (structureSheafRing X)}
    (φ : A ⟶ C) (ψ : B ⟶ D) :
    (φ ⊗ₘ ψ) = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
        ((φ, ψ) : (_, _) ⟶ (_, _))) := by
  have h := monoidal_tensorHom X φ ψ
  change (𝟙 _ ≫ (φ ⊗ₘ ψ) ≫ 𝟙 _) = _ at h
  rwa [Category.id_comp, Category.comp_id] at h

/-- **The tensor product of modules on a ringed space is biadditive**: both whiskerings are
additive, so tensoring by a fixed module is an additive functor. This is the distributive law
that lets an additive statement be transported across a bijection of hom-groups built from the
unitors, the associators and the two whiskerings — in particular across the hom-group form of
the duality of a finite locally free module. -/
theorem monoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (structureSheafRing X)) where
  whiskerLeft_zero {A B C} := by
    rw [← id_tensorHom, tensorHom_eq_tensorSheafMap, tensorSheafMap_zero_right]
    rfl
  zero_whiskerRight {A B C} := by
    rw [← tensorHom_id, tensorHom_eq_tensorSheafMap,
      AlgebraicGeometry.SheafOfModules.tensorSheafMap_zero_left]
    rfl
  whiskerLeft_add {A B C} f g := by
    rw [← id_tensorHom, ← id_tensorHom, ← id_tensorHom, tensorHom_eq_tensorSheafMap,
      tensorHom_eq_tensorSheafMap, tensorHom_eq_tensorSheafMap, tensorSheafMap_add_right]
    rfl
  add_whiskerRight {A B C} f g := by
    rw [← tensorHom_id, ← tensorHom_id, ← tensorHom_id, tensorHom_eq_tensorSheafMap,
      tensorHom_eq_tensorSheafMap, tensorHom_eq_tensorSheafMap, tensorSheafMap_add_left]
    rfl

end Stacks.SheafOfModules.OnSpace

end

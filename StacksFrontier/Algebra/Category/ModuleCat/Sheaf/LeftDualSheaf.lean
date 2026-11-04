module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor product of sheaves of modules as a strict monoidal product

In the strict monoidal structure `Stacks.SheafOfModules.Strict.monoidalCategory` on sheaves of
`𝒪`-modules, whose tensor product is the tensor product sheaf and whose unit is
`SheafOfModules.unit`, the tensor product of two morphisms is the sheafification of the
objectwise tensor product of their underlying morphisms of presheaves of modules.

The objectwise tensor products `PresheafOfModules.tensorObj`,
`PresheafOfModules.Monoidal.tensorObj` and
`Stacks.SheafOfModules.TensorSheafification.tensorPresheaf` are definitionally equal once the
module universes equal the ring universe, by structure eta and proof irrelevance.

## Main results

* `Stacks.tensorObj_eq_monoidalTensorObj`: `PresheafOfModules.tensorObj` is Mathlib's monoidal
  product of presheaves of modules, by `rfl`.
* `Stacks.SheafOfModules.comp_sheafifyValIso_inv`: naturality of the identification of a sheaf
  of modules with its sheafification.
* `Stacks.SheafOfModules.sheafifyTensorIso_naturality`: the comparison isomorphism
  `𝒫^# ⊗ 𝒬^# ≅ (𝒫 ⊗ 𝒬)^#` is natural in both variables.
* `Stacks.SheafOfModules.tensorHom_comp_tensorObjIso_hom`: a tensor product of morphisms
  corresponding to morphisms of presheaves of modules under comparison isomorphisms with
  sheafifications corresponds to the sheafified tensor product of those morphisms.
* `Stacks.SheafOfModules.Strict.tensorHom_eq_sheafifyMap`: the tensor product of two morphisms
  in the strict monoidal structure is the sheafification of the objectwise tensor product.
* `Stacks.SheafOfModules.Strict.exists_monoidalCategory_tensorSheaf`: there is a monoidal
  structure on sheaves of `𝒪`-modules whose unit is `SheafOfModules.unit`, whose tensor product
  is the tensor product sheaf, and whose tensor product of morphisms is the sheafified objectwise
  one.

## References

* [The Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks

section Dedup

variable {C : Type u} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F G : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

/-- The objectwise tensor product `PresheafOfModules.tensorObj F G` is Mathlib's monoidal
product `F ⊗ G` of presheaves of modules. -/
theorem tensorObj_eq_monoidalTensorObj :
    PresheafOfModules.tensorObj (O := 𝒪) F G = F ⊗ G := rfl

end Dedup

namespace SheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

section Counit

variable {A A' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪)}

/-- Naturality of the identification `sheafifyValIso` of a sheaf of modules with its
sheafification. -/
theorem sheafifyFunctor_map_comp_sheafifyValIso_hom (f : A ⟶ A') :
    (sheafifyFunctor 𝒪 h𝒪).map f.val ≫ (sheafifyValIso 𝒪 h𝒪 A').hom =
      (sheafifyValIso 𝒪 h𝒪 A).hom ≫ f :=
  (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit.naturality f

/-- Naturality of the identification `sheafifyValIso` of a sheaf of modules with its
sheafification, stated with its inverse. -/
theorem comp_sheafifyValIso_inv (f : A ⟶ A') :
    f ≫ (sheafifyValIso 𝒪 h𝒪 A').inv =
      (sheafifyValIso 𝒪 h𝒪 A).inv ≫ (sheafifyFunctor 𝒪 h𝒪).map f.val := by
  rw [Iso.comp_inv_eq, Category.assoc,
    sheafifyFunctor_map_comp_sheafifyValIso_hom 𝒪 h𝒪 f, Iso.inv_hom_id_assoc]

end Counit

section Tensorator

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

variable {P P' Q Q' : PresheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}

/-- The comparison isomorphism `sheafifyTensorIso` of the sheafification of a tensor product with
the tensor product of sheafifications is natural in both variables. -/
theorem sheafifyTensorIso_naturality (φ : P ⟶ P') (ψ : Q ⟶ Q') :
    ((sheafifyFunctor 𝒪 h𝒪).map φ ⊗ₘ (sheafifyFunctor 𝒪 h𝒪).map ψ) ≫
        (sheafifyTensorIso 𝒪 h𝒪 P' Q').hom =
      (sheafifyTensorIso 𝒪 h𝒪 P Q).hom ≫ (sheafifyFunctor 𝒪 h𝒪).map (φ ⊗ₘ ψ) :=
  Functor.LaxMonoidal.μ_natural (CategoryTheory.Localization.Monoidal.toMonoidalCategory
    (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪)) φ ψ

variable {A A' B B' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
  𝒪 h𝒪)}

/-- If `f` and `g` correspond to `φ` and `ψ` under comparison isomorphisms with sheafified
presheaves of modules, then `f ⊗ g` corresponds to the sheafification of `φ ⊗ ψ`. -/
theorem tensorHom_comp_tensorObjIso_hom
    (cA : (sheafifyFunctor 𝒪 h𝒪).obj P ≅ A) (cA' : (sheafifyFunctor 𝒪 h𝒪).obj P' ≅ A')
    (cB : (sheafifyFunctor 𝒪 h𝒪).obj Q ≅ B) (cB' : (sheafifyFunctor 𝒪 h𝒪).obj Q' ≅ B')
    (φ : P ⟶ P') (ψ : Q ⟶ Q') (f : A ⟶ A') (g : B ⟶ B')
    (hf : f ≫ cA'.inv = cA.inv ≫ (sheafifyFunctor 𝒪 h𝒪).map φ)
    (hg : g ≫ cB'.inv = cB.inv ≫ (sheafifyFunctor 𝒪 h𝒪).map ψ) :
    (f ⊗ₘ g) ≫ ((cA'.inv ⊗ₘ cB'.inv) ≫ (sheafifyTensorIso 𝒪 h𝒪 P' Q').hom) =
      ((cA.inv ⊗ₘ cB.inv) ≫ (sheafifyTensorIso 𝒪 h𝒪 P Q).hom) ≫
        (sheafifyFunctor 𝒪 h𝒪).map (φ ⊗ₘ ψ) := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg, ← tensorHom_comp_tensorHom,
    Category.assoc, Category.assoc, sheafifyTensorIso_naturality]

/-- Naturality of the identification `tensorObjIso` of the monoidal product of sheaves of
modules with the sheafified objectwise tensor product. -/
theorem tensorHom_comp_tensorObjIso (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g) ≫ (tensorObjIso 𝒪 h𝒪 A' B').hom =
      (tensorObjIso 𝒪 h𝒪 A B).hom ≫ (sheafifyFunctor 𝒪 h𝒪).map (f.val ⊗ₘ g.val) :=
  tensorHom_comp_tensorObjIso_hom 𝒪 h𝒪 (sheafifyValIso 𝒪 h𝒪 A) (sheafifyValIso 𝒪 h𝒪 A')
    (sheafifyValIso 𝒪 h𝒪 B) (sheafifyValIso 𝒪 h𝒪 B') f.val g.val f g
    (comp_sheafifyValIso_inv 𝒪 h𝒪 f) (comp_sheafifyValIso_inv 𝒪 h𝒪 g)

end Tensorator

namespace Strict

variable {A A' B B' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
  𝒪 h𝒪)}

/-- In the strict monoidal structure, the tensor product of two morphisms is the sheafification
of the objectwise tensor product of their underlying morphisms of presheaves of modules. -/
theorem tensorHom_eq_sheafifyMap (f : A ⟶ A') (g : B ⟶ B') :
    MonoidalCategoryStruct.tensorHom (self := monoidalCategoryStruct 𝒪 h𝒪) f g =
      (sheafifyFunctor 𝒪 h𝒪).map (f.val ⊗ₘ g.val) :=
  (tensorHom_eq 𝒪 h𝒪 f g).trans
    ((Iso.inv_comp_eq _).2 (tensorHom_comp_tensorObjIso 𝒪 h𝒪 f g))

/-- There is a monoidal structure on sheaves of `𝒪`-modules whose unit is `SheafOfModules.unit`,
whose tensor product is the tensor product sheaf, and whose tensor product of two morphisms is
the sheafification of the objectwise tensor product of the underlying morphisms. -/
theorem exists_monoidalCategory_tensorSheaf :
    ∃ M : MonoidalCategory (SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)),
      letI := M
      ∃ (_hunit : 𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        𝒪 h𝒪)) =
            SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
        (htensor : ∀ A B : SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪),
            A ⊗ B = (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
              (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (A)).obj (B))),
        ∀ {A A' B B' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          𝒪 h𝒪)}
          (f : A ⟶ A') (g : B ⟶ B'),
          eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
            (sheafifyFunctor 𝒪 h𝒪).map (f.val ⊗ₘ g.val) :=
  ⟨monoidalCategory 𝒪 h𝒪, rfl, fun _ _ ↦ rfl, fun f g ↦ by
    let := monoidalCategory 𝒪 h𝒪
    show 𝟙 _ ≫ (f ⊗ₘ g) ≫ 𝟙 _ = _
    exact (Category.id_comp _).trans
      ((Category.comp_id _).trans (tensorHom_eq_sheafifyMap 𝒪 h𝒪 f g))⟩

end Strict

end SheafOfModules

end Stacks

end

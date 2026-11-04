module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits

/-!
# The tensor product of sheaves is additive in each variable

Let `A` be a preadditive monoidal category whose tensor product is additive in each variable
(`MonoidalPreadditive A`). Then so is the pointwise tensor product of presheaves with values in `A`
(`CategoryTheory.Monoidal.functorCategoryMonoidalPreadditive`), and so is the tensor product of
sheaves obtained from it by localization along sheafification
(`CategoryTheory.Sheaf.monoidalCategory`), as soon as sheafification is additive.

## Main results

* `CategoryTheory.Sheaf.tensorLeftIso`, `CategoryTheory.Sheaf.tensorRightIso`: tensoring a sheaf
  by a fixed sheaf `F` is the sheafification of the pointwise tensor product with the underlying
  presheaf of `F`.
* `CategoryTheory.Sheaf.monoidalPreadditive`: the tensor product of sheaves is additive in each
  variable.

## Implementation notes

`Sheaf.monoidalCategory` is not an instance, so `Sheaf.monoidalPreadditive` is a theorem about
it rather than an instance; a file that activates the monoidal structure on a particular site
registers the corresponding instance there.

The additivity of `F ⊗ -` is read off the isomorphism `F ⊗ - ≅ sheafify (F ⊗ (-))`
(`Sheaf.tensorLeftIso`): the right-hand side is a composite of additive functors, sheafification
being monoidal (`CategoryTheory.Functor.Monoidal.commTensorLeft`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]
  [Preadditive A] [MonoidalCategory A] [MonoidalPreadditive A]

namespace Sheaf

variable (J : GrothendieckTopology C) [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory

/-- Tensoring by a fixed sheaf `F` on the left is the sheafification of the pointwise tensor
product of presheaves by the underlying presheaf of `F`. -/
noncomputable def tensorLeftIso (F : Sheaf J A) :
    tensorLeft F ≅ sheafToPresheaf J A ⋙ tensorLeft F.obj ⋙ presheafToSheaf J A :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
          ((tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J A).counit.app F)).symm) ≪≫
        Functor.Monoidal.commTensorLeft (presheafToSheaf J A) F.obj)

/-- Tensoring by a fixed sheaf `F` on the right is the sheafification of the pointwise tensor
product of presheaves by the underlying presheaf of `F`. -/
noncomputable def tensorRightIso (F : Sheaf J A) :
    tensorRight F ≅ sheafToPresheaf J A ⋙ tensorRight F.obj ⋙ presheafToSheaf J A :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
          ((tensoringRight _).mapIso (asIso ((sheafificationAdjunction J A).counit.app F)).symm) ≪≫
        Functor.Monoidal.commTensorRight (presheafToSheaf J A) F.obj)

variable [(presheafToSheaf J A).Additive]

/-- **The tensor product of sheaves is additive in each variable**, for the monoidal structure
`Sheaf.monoidalCategory` obtained by localizing the pointwise tensor product of presheaves. -/
theorem monoidalPreadditive : MonoidalPreadditive (Sheaf J A) := by
  have hl (F : Sheaf J A) : (tensorLeft F).Additive :=
    Functor.additive_of_iso (tensorLeftIso J F).symm
  have hr (F : Sheaf J A) : (tensorRight F).Additive :=
    Functor.additive_of_iso (tensorRightIso J F).symm
  exact
    { whiskerLeft_zero := fun {X _ _} ↦ (tensorLeft X).map_zero _ _
      zero_whiskerRight := fun {X _ _} ↦ (tensorRight X).map_zero _ _
      whiskerLeft_add := fun {X _ _} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X _ _} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

end Sheaf

end CategoryTheory

end

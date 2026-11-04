module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# Biadditivity of the tensor product of sheaves of modules

The tensor product of sheaves of `𝒪`-modules is biadditive: the monoidal structure
`Stacks.SheafOfModules.monoidalCategory` is `CategoryTheory.MonoidalPreadditive`.

## Main results

* `CategoryTheory.monoidalPreadditive_of_additiveSection`: if `L : C ⥤ D` is an additive monoidal
  functor out of a monoidal preadditive category and `L` has an additive section `ι : D ⥤ C`, that
  is, an additive functor with `ι ⋙ L ≅ 𝟭 D`, then `D` is monoidal preadditive.
* `PresheafOfModules.monoidalPreadditive`: presheaves of modules are monoidal preadditive.
* `Stacks.SheafOfModules.monoidalPreadditive`: sheaves of modules are monoidal preadditive for
  `Stacks.SheafOfModules.monoidalCategory`.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

section AdditiveSection

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [MonoidalCategory C] [MonoidalCategory D]
  (L : C ⥤ D) [L.Monoidal] [L.Additive] (ι : D ⥤ C) (hι : ι.Additive) (c : ι ⋙ L ≅ 𝟭 D)

/-- Tensoring on the left with `X : D`, computed in `C` and transported back: if `ι` is a section
of a monoidal functor `L`, then `- ↦ X ⊗ -` is isomorphic to `- ↦ L (ι X ⊗ ι -)`. -/
noncomputable def tensorLeftIsoOfAdditiveSection (X : D) :
    tensorLeft X ≅ ι ⋙ tensorLeft (ι.obj X) ⋙ L :=
  (curriedTensor D).mapIso (c.app X).symm ≪≫
    (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight c.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ι (Functor.Monoidal.commTensorLeft L (ι.obj X))

/-- Tensoring on the right with `X : D`, computed in `C` and transported back: if `ι` is a section
of a monoidal functor `L`, then `- ↦ - ⊗ X` is isomorphic to `- ↦ L (ι - ⊗ ι X)`. -/
noncomputable def tensorRightIsoOfAdditiveSection (X : D) :
    tensorRight X ≅ ι ⋙ tensorRight (ι.obj X) ⋙ L :=
  (curriedTensor D).flip.mapIso (c.app X).symm ≪≫
    (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight c.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ι (Functor.Monoidal.commTensorRight L (ι.obj X))

variable [MonoidalPreadditive C]

include L hι c in
/-- If `L` is an additive monoidal functor out of a monoidal preadditive category with an additive
section `ι`, then tensoring on the left with any `X : D` is additive. -/
lemma tensorLeft_additive_of_additiveSection (X : D) : (tensorLeft X).Additive :=
  let := hι
  Functor.additive_of_iso (tensorLeftIsoOfAdditiveSection L ι c X).symm

include L hι c in
/-- If `L` is an additive monoidal functor out of a monoidal preadditive category with an additive
section `ι`, then tensoring on the right with any `X : D` is additive. -/
lemma tensorRight_additive_of_additiveSection (X : D) : (tensorRight X).Additive :=
  let := hι
  Functor.additive_of_iso (tensorRightIsoOfAdditiveSection L ι c X).symm

include L hι c in
/-- **Transport of biadditivity along an additive monoidal functor with an additive section.**
If `L : C ⥤ D` is an additive monoidal functor from a monoidal preadditive category, and `L` has an
additive section `ι` (an additive functor with `ι ⋙ L ≅ 𝟭 D`), then the monoidal structure of `D`
is biadditive as well. -/
theorem monoidalPreadditive_of_additiveSection : MonoidalPreadditive D := by
  have := tensorLeft_additive_of_additiveSection L ι hι c
  have := tensorRight_additive_of_additiveSection L ι hι c
  exact
    { whiskerLeft_zero := (tensorLeft _).map_zero _ _
      zero_whiskerRight := (tensorRight _).map_zero _ _
      whiskerLeft_add := fun _ _ => (tensorLeft _).map_add
      add_whiskerRight := fun _ _ => (tensorRight _).map_add }

end AdditiveSection

end CategoryTheory

namespace PresheafOfModules

universe u

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The tensor product of presheaves of modules is biadditive. -/
noncomputable instance monoidalPreadditive :
    MonoidalPreadditive (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) where
  whiskerLeft_zero := by
    intros; ext1 U; exact MonoidalPreadditive.whiskerLeft_zero (C := ModuleCat (R.obj U))
  zero_whiskerRight := by
    intros; ext1 U; exact MonoidalPreadditive.zero_whiskerRight (C := ModuleCat (R.obj U))
  whiskerLeft_add := by
    intros; ext1 U; exact MonoidalPreadditive.whiskerLeft_add (C := ModuleCat (R.obj U)) _ _
  add_whiskerRight := by
    intros; ext1 U; exact MonoidalPreadditive.add_whiskerRight (C := ModuleCat (R.obj U)) _ _

end PresheafOfModules

namespace Stacks.SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategory

/-- Sheafification of presheaves of modules is a monoidal functor for `monoidalCategory`. -/
noncomputable instance sheafifyFunctor_monoidal : (sheafifyFunctor 𝒪 h𝒪).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪)).Monoidal)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Sheafification of presheaves of modules is an additive functor. -/
instance sheafifyFunctor_additive : (sheafifyFunctor 𝒪 h𝒪).Additive :=
  (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).left_adjoint_additive

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The right adjoint of the sheafification adjunction is a section of sheafification: the counit
of the adjunction, as an isomorphism from the composite to the identity functor. -/
noncomputable def sheafifySection :
    (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⋙
        PresheafOfModules.restrictScalars (𝟙
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)) ⋙
      sheafifyFunctor 𝒪 h𝒪 ≅ 𝟭 _ :=
  asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit

/-- **The tensor product of sheaves of modules is biadditive**: the monoidal structure
`monoidalCategory` on sheaves of modules is `CategoryTheory.MonoidalPreadditive`. -/
theorem monoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :=
  monoidalPreadditive_of_additiveSection (sheafifyFunctor 𝒪 h𝒪)
    (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⋙
      PresheafOfModules.restrictScalars (𝟙
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj))
    (inferInstanceAs (SheafOfModules.forget
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⋙
      PresheafOfModules.restrictScalars (𝟙
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).Additive)
    (sheafifySection 𝒪 h𝒪)

end Stacks.SheafOfModules

end

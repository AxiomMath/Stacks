module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Symmetric monoidal complexes of modules on a ringed site

For a ringed site, complexes of modules form a symmetric monoidal category.  Its tensor
bifunctor is the total complex of the sheafified tensor product, and its unit is the structure
sheaf concentrated in degree zero.

## Main definitions

* `Stacks.Cohomology.MonoidalComplexesOfModules.SymmetricMonoidalComplexes`: a symmetric
  monoidal structure on complexes of modules with prescribed tensor bifunctor and unit.

## Main results

* `Stacks.Cohomology.MonoidalComplexesOfModules.symmetricMonoidalComplexes`: such a structure
  exists for every ringed site.

## References

* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace Stacks.Cohomology.MonoidalComplexesOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

/-- `Mod(O)`, the category of `O`-modules on the ringed site `(C, O)`. -/
abbrev Mod := SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)

/-- `Comp(Mod(O))`, the category of cochain complexes of `O`-modules. -/
abbrev Complexes := CochainComplex (Mod R) ℤ

/-! ### The field types of `SymmetricMonoidalComplexes` -/

/-- Presheaves of abelian groups on the site have a sheafification. -/
abbrev WeakSheafify : Prop := HasWeakSheafify J AddCommGrpCat.{max u v}

/-- A morphism of presheaves of abelian groups becomes an isomorphism after sheafification
exactly when it is locally bijective. -/
abbrev LocallyBijective : Prop := J.WEqualsLocallyBijective AddCommGrpCat.{max u v}

/-- `Mod(O)` has binary biproducts. -/
abbrev BinaryBiproducts : Prop := HasBinaryBiproducts (Mod R)

/-- `Mod(O)` has a zero object. -/
abbrev ZeroObject : Prop := HasZeroObject (Mod R)

/-- `⊗_O` is additive, i.e. bilinear on morphisms, in its first variable. -/
abbrev SheafTensorAdditive [WeakSheafify.{v, u} (J := J)] [LocallyBijective.{v, u} (J := J)]
    [BinaryBiproducts R] : Prop :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R).Additive

/-- For every `O`-module `ℱ`, the functor `ℱ ⊗_O -` is additive. -/
abbrev SheafTensorObjAdditive [WeakSheafify.{v, u} (J := J)] [LocallyBijective.{v, u} (J := J)]
    [BinaryBiproducts R] : Prop :=
  ∀ M, Functor.Additive
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R).obj M)

/-- The total complexes of the tensor double complexes of two complexes of `O`-modules
exist. -/
abbrev HasTensorComplex [WeakSheafify.{v, u} (J := J)] [LocallyBijective.{v, u} (J := J)]
    [BinaryBiproducts R] (_ : SheafTensorAdditive R) (_ : SheafTensorObjAdditive R) : Prop :=
  ∀ (K L : Complexes R), K.HasMapBifunctor L (Stacks.SheafOfModules.Tensor.sheafTensor R)

/-- A monoidal category structure on `Comp(Mod(O))`. -/
abbrev Monoidal := MonoidalCategory (Complexes R)

/-- A symmetry for a monoidal structure on `Comp(Mod(O))`. -/
abbrev Symmetric [Monoidal R] := SymmetricCategory (Complexes R)

/-- The tensor product of `Comp(Mod(O))` is `Tot(- ⊗_O -)`. -/
abbrev TensorEqTotal [WeakSheafify.{v, u} (J := J)] [LocallyBijective.{v, u} (J := J)]
    [BinaryBiproducts R] [Monoidal R] (h₁ : SheafTensorAdditive R)
    (h₂ : SheafTensorObjAdditive R) (h₃ : HasTensorComplex R h₁ h₂) : Prop :=
  letI := h₁
  letI := h₂
  letI := h₃
  curriedTensor (Complexes R) = Stacks.SheafOfModules.Tensor.tensorComplex R

/-- The unit of `Comp(Mod(O))` is the structure sheaf in degree zero. -/
abbrev UnitEqStructureSheaf [Monoidal R] (h : ZeroObject R) : Prop :=
  letI := h
  𝟙_ (Complexes R) = (CochainComplex.singleFunctor (Mod R) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-! ### The statement -/

/-- A symmetric monoidal structure on complexes of sheaves of modules, with tensor bifunctor
given by totalized sheaf tensor and unit the structure sheaf in degree zero, together with the
categorical constructions on `Mod(O)` required to form that tensor. -/
public structure SymmetricMonoidalComplexes where
  weakSheafify : WeakSheafify.{v, u} (J := J)
  locallyBijective : LocallyBijective.{v, u} (J := J)
  binaryBiproducts : BinaryBiproducts R
  zeroObject : ZeroObject R
  sheafTensorAdditive : SheafTensorAdditive R
  sheafTensorObjAdditive : SheafTensorObjAdditive R
  hasTensorComplex : HasTensorComplex R sheafTensorAdditive sheafTensorObjAdditive
  monoidal : Monoidal R
  symmetric : Symmetric R
  tensor_eq_total :
    TensorEqTotal R sheafTensorAdditive sheafTensorObjAdditive hasTensorComplex
  unit_eq_structureSheaf : UnitEqStructureSheaf R zeroObject

/-! ### The construction -/

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

/-- Complexes of modules on any ringed site form a symmetric monoidal category; its tensor
bifunctor is totalized sheaf tensor. -/
@[stacks 0FPQ, sga "4 XVII 4.1.6" "⊗ on complexes"]
public def symmetricMonoidalComplexes : SymmetricMonoidalComplexes R :=
  letI : HasWeakSheafify J AddCommGrpCat.{max u v} := inferInstance
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} := inferInstance
  letI : MonoidalCategory (Mod R) := SheafOfModules.monoidalCategorySheafTensor R
  { weakSheafify := inferInstance
    locallyBijective := inferInstance
    binaryBiproducts := inferInstance
    zeroObject := inferInstance
    sheafTensorAdditive := inferInstance
    sheafTensorObjAdditive := inferInstance
    hasTensorComplex K L := Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor R K L
    monoidal := inferInstance
    symmetric := CochainComplex.symmetricCategory (Mod R)
    tensor_eq_total := by
      dsimp only [TensorEqTotal, Stacks.SheafOfModules.Tensor.tensorComplex]
      change curriedTensor (Complexes R) =
        (curriedTensor (Mod R)).map₂HomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      rfl
    unit_eq_structureSheaf := rfl }

/-- The monoidal structure on complexes of modules on a ringed site. -/
@[instance_reducible]
public def cochainComplexMonoidalCategory : MonoidalCategory (Complexes R) :=
  (symmetricMonoidalComplexes R).monoidal

/-- The symmetry on complexes of modules on a ringed site. -/
@[instance_reducible]
public def cochainComplexSymmetricCategory :
    letI := cochainComplexMonoidalCategory R
    SymmetricCategory (Complexes R) :=
  (symmetricMonoidalComplexes R).symmetric

end Stacks.Cohomology.MonoidalComplexesOfModules

end

end

module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectDirectImageChart
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectComplexes
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor maps against the left unit constraint of the sheaf tensor product

Compatibilities of the left unit constraint `Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft`
of the sheaf tensor product with maps tensored in the left factor.

## Main results

* `Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft_unit`: at the structure sheaf `O` the left
  and right unit constraints agree.
* `Stacks.SheafOfModules.Tensor.sheafTensorMap_app_unit_comp_sheafTensorUnitIsoLeft`: for an
  endomorphism `e` of `O`, `(e ⊗ 1) ≫ λ_O = λ_O ≫ e`.
* `Stacks.SheafOfModules.Tensor.sheafTensorMap_app_comp_sheafTensorUnitIsoLeft_of_iso`: the same
  for an endomorphism of a module isomorphic to `O`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

section LeftUnitor

/-- At the structure sheaf `O`, the left unit constraint `O ⊗ O ≅ O` of the sheaf tensor product
is the right unit constraint. -/
theorem sheafTensorUnitIsoLeft_unit :
    sheafTensorUnitIsoLeft R (SheafOfModules.unit (ringSheaf R)) =
      sheafTensorUnitIsoRight R (SheafOfModules.unit (ringSheaf R)) := by
  have h : (λ_ (SheafOfModules.unit (ringSheaf R)).val).hom =
      (ρ_ (SheafOfModules.unit (ringSheaf R)).val).hom :=
    MonoidalCategory.unitors_equal
  apply Iso.ext
  change (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
      (λ_ (SheafOfModules.unit (ringSheaf R)).val).hom ≫ _ =
    (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
      (ρ_ (SheafOfModules.unit (ringSheaf R)).val).hom ≫ _
  rw [h]
  rfl

/-- **An endomorphism of the structure sheaf commutes with the left unit constraint at the
structure sheaf**, tensored in the left factor: `(e ⊗ 1) ≫ λ_O = λ_O ≫ e`. -/
theorem sheafTensorMap_app_unit_comp_sheafTensorUnitIsoLeft
    (e : SheafOfModules.unit (ringSheaf R) ⟶ SheafOfModules.unit (ringSheaf R)) :
    ((sheafTensor R).map e).app (SheafOfModules.unit (ringSheaf R)) ≫
        (sheafTensorUnitIsoLeft R (SheafOfModules.unit (ringSheaf R))).hom =
      (sheafTensorUnitIsoLeft R (SheafOfModules.unit (ringSheaf R))).hom ≫ e := by
  rw [sheafTensorUnitIsoLeft_unit]
  exact sheafTensorUnitIsoRight_naturality R e

/-- **An endomorphism of a copy of the structure sheaf commutes with multiplication**: for
`u : X ≅ O` and `f : X ⟶ X`, tensoring `f` in the left factor of `X ⊗ X ≅ O ⊗ X` and then
applying the left unit constraint is the unit constraint followed by `f`. -/
theorem sheafTensorMap_app_comp_sheafTensorUnitIsoLeft_of_iso
    {X : SheafOfModules.{w} (ringSheaf R)} (u : X ≅ SheafOfModules.unit (ringSheaf R))
    (f : X ⟶ X) :
    ((sheafTensor R).map f).app X ≫ ((sheafTensor R).map u.hom).app X ≫
        (sheafTensorUnitIsoLeft R X).hom =
      ((sheafTensor R).map u.hom).app X ≫ (sheafTensorUnitIsoLeft R X).hom ≫ f := by
  set e := u.inv ≫ f ≫ u.hom with he
  have heu : f ≫ u.hom = u.hom ≫ e := by simp [he]
  have h1 : ((sheafTensor R).map f).app X ≫ ((sheafTensor R).map u.hom).app X =
      ((sheafTensor R).map u.hom).app X ≫ ((sheafTensor R).map e).app X := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, heu]
  have hlu := sheafTensorUnitIsoLeft_naturality R u.hom
  have h2 : ((sheafTensor R).map e).app X ≫ (sheafTensorUnitIsoLeft R X).hom =
      (sheafTensorUnitIsoLeft R X).hom ≫ f := by
    rw [← cancel_mono u.hom, Category.assoc, Category.assoc, heu, ← hlu, ← Category.assoc,
      ← ((sheafTensor R).map e).naturality u.hom, Category.assoc,
      sheafTensorMap_app_unit_comp_sheafTensorUnitIsoLeft, ← Category.assoc, hlu, Category.assoc]
  rw [← Category.assoc, h1, Category.assoc, h2]

end LeftUnitor

end Stacks.SheafOfModules.Tensor

end

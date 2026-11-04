module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso

/-!
# The comparison of Stacks 01CD at an identity morphism of ringed spaces

Let `X` be a ringed space and let `A`, `B` be sheaves of `𝒪_X`-modules. The comparison of
[Stacks, Tag 01CD] at `f = 𝟙 X` is a morphism `(𝟙 X)^*(A ⊗ B) ⟶ (𝟙 X)^*A ⊗ (𝟙 X)^*B`; it is not
an identity, since `(𝟙 X)^*` is an abstract left adjoint and is not equal to `𝟭`. This file
proves that the comparison composed with the unit of the adjunction `(𝟙 X)^* ⊣ (𝟙 X)_*` is the
tensor product of the two units.

## Main results

* `Stacks.RingedSpace.comparisonTranspose_id` — the adjoint transpose of the comparison at
  `𝟙 X` is `A ⊗ B ⟶ (𝟙 X)^*A ⊗ (𝟙 X)^*B` applied to the pair of units.
* `Stacks.RingedSpace.unit_comp_comparison_id` — the comparison at an identity, composed with
  the unit: `η_{A ⊗ B} ≫ comparison (𝟙 X) A B = (A ⊗ B)(η_A, η_B)`.
* `Stacks.RingedSpace.unit_comp_comparisonIso_id` — the same for the isomorphism
  `Stacks.RingedSpace.comparisonIso`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction _root_.Stacks.PresheafOfModules CategoryTheory.Sheaf

variable (X : RingedSpace.{u, u}) (A B : SheafOfModules.{u} (structureRingSheaf X))

/-- The pair of units of the adjunction `(𝟙 X)^* ⊣ (𝟙 X)_*`, as a morphism
`(A, B) ⟶ ((𝟙 X)^*A, (𝟙 X)^*B)` in the product category; the pushforward along an identity is the
identity functor on the nose. -/
abbrev unitPairId :
    ((A, B) : SheafOfModules.{u} (structureRingSheaf X) ×
        SheafOfModules.{u} (structureRingSheaf X)) ⟶
      ((pullbackFunctor (𝟙 X)).obj A, (pullbackFunctor (𝟙 X)).obj B) :=
  ((pullbackAdjunction (𝟙 X)).unit.app A, (pullbackAdjunction (𝟙 X)).unit.app B)

/-- **The adjoint transpose of the comparison of Stacks 01CD at an identity morphism is the
tensor product of the two units.** -/
theorem comparisonTranspose_id :
    comparisonTranspose (𝟙 X) A B = (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).map
        (unitPairId X A B) := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun U x y => ?_)
  exact (comparisonTranspose_unit_tmul (𝟙 X) A B U x y).trans
    (tensorSheaf_map_unit_tmul X (unitPairId X A B).1 (unitPairId X A B).2 U x y).symm

/-- **The comparison of Stacks 01CD at an identity morphism, composed with the unit of the
pullback–pushforward adjunction, is the tensor product of the two units.** -/
theorem unit_comp_comparison_id :
    (pullbackAdjunction (𝟙 X)).unit.app ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).obj
          (A, B)) ≫
        comparison (𝟙 X) A B =
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).map
          (unitPairId X A B) :=
  ((pullbackAdjunction (𝟙 X)).homEquiv_unit (f := comparison (𝟙 X) A B)).symm.trans
    ((homEquiv_comparison (𝟙 X) A B).trans (comparisonTranspose_id X A B))

/-- The component at `(A, B)` of the comparison isomorphism `comparisonIso (𝟙 X)`, composed with
the unit of the pullback–pushforward adjunction, is the tensor product of the two units. -/
theorem unit_comp_comparisonIso_id :
    (pullbackAdjunction (𝟙 X)).unit.app ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).obj
          (A, B)) ≫
        ((comparisonIso (𝟙 X)).app (A, B)).hom =
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.presheaf, X.IsSheaf⟩)).map
          (unitPairId X A B) :=
  unit_comp_comparison_id X A B

end Stacks.RingedSpace

end

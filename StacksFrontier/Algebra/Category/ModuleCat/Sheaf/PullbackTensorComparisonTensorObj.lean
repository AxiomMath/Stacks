module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence

/-!
# The pullback tensor comparison in the monoidal spelling of the tensor product

For a morphism of ringed spaces `f : X ⟶ Y` and sheaves of modules `A`, `B` on `Y`, this file
states the comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of pullback with the tensor product, and its
uniqueness, with both tensor products written as the monoidal product `⊗`.

## Main definitions

* `Stacks.RingedSpace.tensorComparisonIso`: the comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`.

## Main results

* `Stacks.RingedSpace.tensorComparisonIso_hom`: the forward map of
  `Stacks.RingedSpace.tensorComparisonIso` is
  `Stacks.PullbackTensorCoherence.pullbackTensorComparison`.
* `Stacks.RingedSpace.tensorComparison_unique`: the comparison is determined by its effect on
  the sheafification-unit images of local pure tensors.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
open RingedSpaceModuleAdjunction PresheafOfModules
open Stacks.PullbackTensorCoherence (pullbackTensorComparison)

noncomputable section

namespace Stacks.RingedSpace

universe u

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y))

/-- The comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of pullback with the tensor product, as an
isomorphism. -/
def tensorComparisonIso : (pullbackFunctor f).obj (A ⊗ B) ≅
    (pullbackFunctor f).obj A ⊗ (pullbackFunctor f).obj B :=
  (comparisonIso f).app (A, B)

/-- The forward map of `Stacks.RingedSpace.tensorComparisonIso` is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison`. -/
@[simp]
lemma tensorComparisonIso_hom :
    (tensorComparisonIso f A B).hom = pullbackTensorComparison f A B := by
  rw [tensorComparisonIso, Iso.app_hom, comparisonIso_hom, comparisonNatTrans_app]
  rfl

/-- A morphism `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` whose adjunct sends the sheafification-unit image of
every local pure tensor `x ⊗ₜ y` to that of `pullbackUnit f A U x ⊗ₜ pullbackUnit f B U y` is the
comparison `Stacks.PullbackTensorCoherence.pullbackTensorComparison`. -/
lemma tensorComparison_unique
    (θ : (pullbackFunctor f).obj (A ⊗ B) ⟶
      (pullbackFunctor f).obj A ⊗ (pullbackFunctor f).obj B)
    (hθ : ∀ (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U),
      Hom.app ((pullbackAdjunction f).homEquiv _ _ θ).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (Y))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Y).presheaf) (A).val (B).val)) U (x ⊗ₜ y)) =
        Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (X))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (X).presheaf) (((pullbackFunctor f).obj A)).val
                (((pullbackFunctor f).obj B)).val))
          ((opensMap f).op.obj U) (pullbackUnit f A U x ⊗ₜ pullbackUnit f B U y)) :
    θ = pullbackTensorComparison f A B :=
  comparison_unique f A B θ hθ

end Stacks.RingedSpace

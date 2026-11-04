module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductRightOperator

/-!
# The comparison of Tag 01CD intertwines the symmetry of the tensor product sheaf

For a morphism of schemes `g : X ⟶ Y` and `𝒪_Y`-modules `A` and `B`, the comparison
`g^*(A ⊗ B) ≅ g^*A ⊗ g^*B` of [Stacks, Tag 01CD] intertwines the symmetry constraint of
[Stacks, Tag 01CA], stated with `AlgebraicGeometry.Scheme.Modules.pullback` for the inverse image,
`Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso` for the comparison and
`Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap` for the symmetry.

## Main results

* `AlgebraicGeometry.tensorSheafSwap_hom_eq_braiding`: on a ringed space,
  `Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap` agrees with the braiding `β_` of
  `Stacks.PullbackTensorCoherence.braidedCategory`.
* `AlgebraicGeometry.schemePullbackTensorIso_tensorSheafSwap`: the comparison of Tag 01CD
  intertwines the symmetry constraint.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.SheafOfModules.TensorPresentations (tensorSheafSwap
  tensorSheafSwap_app_toTensorSheafSection)
open Stacks.Tag01VSPullbackTensor (schemePullbackTensorIso)
open Stacks.RingedSpace (structureRingSheaf)

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory

/-! ### The two spellings of the symmetry constraint -/

/-- The symmetry constraint of [Stacks, Tag 01CA] on a tensor product sheaf, in its two
spellings: `Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap`, the sheafification of the
braiding of the underlying presheaves of modules, equals the braiding `β_` of
`Stacks.PullbackTensorCoherence.braidedCategory`. -/
public theorem tensorSheafSwap_hom_eq_braiding (Z : RingedSpace.{u, u})
    (A B : SheafOfModules.{u} (structureRingSheaf Z)) :
    (tensorSheafSwap Z A B).hom = (β_ A B).hom :=
  Stacks.PullbackTensorCoherence.tensor_hom_ext fun U a b =>
    (tensorSheafSwap_app_toTensorSheafSection Z A B U.unop a b).trans
      (Stacks.PullbackTensorCoherence.braiding_tmul Z A B U a b).symm

/-! ### The coherence, at the spelling of the adic development -/

/-- The comparison of [Stacks, Tag 01CD] intertwines the symmetry constraint of
[Stacks, Tag 01CA]: splitting the inverse image of a tensor product and then exchanging the two
factors is exchanging them first and then splitting,

  `g^*(A ⊗ B) ⟶ g^*(B ⊗ A) ⟶ g^*B ⊗ g^*A`  equals  `g^*(A ⊗ B) ⟶ g^*A ⊗ g^*B ⟶ g^*B ⊗ g^*A`. -/
public theorem schemePullbackTensorIso_tensorSheafSwap {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A B : Y.Modules) :
    (Scheme.Modules.pullback g).map (tensorSheafSwap Y.toRingedSpace A B).hom ≫
        (schemePullbackTensorIso g B A).hom =
      (schemePullbackTensorIso g A B).hom ≫
        (tensorSheafSwap X.toRingedSpace ((Scheme.Modules.pullback g).obj A)
          ((Scheme.Modules.pullback g).obj B)).hom :=
  (congrArg (fun z => (Scheme.Modules.pullback g).map z ≫ (schemePullbackTensorIso g B A).hom)
        (tensorSheafSwap_hom_eq_braiding Y.toRingedSpace A B)).trans
    ((Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding
          g.toLRSHom.toShHom A B).trans
      (congrArg (fun z => (schemePullbackTensorIso g A B).hom ≫ z)
        (tensorSheafSwap_hom_eq_braiding X.toRingedSpace ((Scheme.Modules.pullback g).obj A)
          ((Scheme.Modules.pullback g).obj B)).symm))

end AlgebraicGeometry

end

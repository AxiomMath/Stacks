module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedPushforwardCompShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftComplexBifunctors
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetChase

/-!
# The naive cup product composed with a pairing, through the relative cup product

For a morphism of ringed spaces `f : X ⟶ Y`, complexes `A`, `B` of `𝒪_X`-modules and a pairing
`h : Tot(A ⊗ B) ⟶ W`, [Stacks, Tag 0FP3] identifies the naive cup product of `f_*A` and `f_*B`
with the relative cup product of `Rf_*QA` and `Rf_*QB` up to the comparisons
`Q(f_*K) ⟶ Rf_*(QK)`. The same identification holds after composing both sides with the direct
image of `h`.

## Main results

* `toTensor_naiveCupProduct_map_comp_pushforwardComparisonQ`: the naive cup product followed by
  the direct image of a pairing, transported along the comparisons `Q(f_*K) ⟶ Rf_*(QK)`, is the
  relative cup product followed by `Rf_*(toTensor)` and `Rf_*(Qh)`.

## References

* [Stacks, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel CategoryTheory.Prod
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex naiveCupProduct)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)

universe u

namespace Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- For a morphism of ringed spaces `f` and a pairing `h : Tot(A ⊗ B) ⟶ W`, the derived tensor of
the comparisons `Q(f_*K) ⟶ Rf_*(QK)` transports `toTensor ≫ Q(naive cup product ≫ f_*h)` to the
relative cup product followed by `Rf_*(toTensor)` and `Rf_*(Qh)`. -/
theorem toTensor_naiveCupProduct_map_comp_pushforwardComparisonQ
    {A B W : CochainComplex (ModulesOn X) ℤ}
    (h : ((tensorComplexBifunctorOn X).obj A).obj B ⟶ W) :
    (canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A)
        ((pushforwardComplex f).obj B) ≫
      DerivedCategory.Q.map (naiveCupProduct f A B ≫ (pushforwardComplex f).map h) ≫
      pushforwardComparisonQ f W =
    (((derivedTensorProductFunctor Y.sheaf).map (pushforwardComparisonQ f A)).app _ ≫
        ((derivedTensorProductFunctor Y.sheaf).obj _).map (pushforwardComparisonQ f B)) ≫
      Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f
        (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) ≫
      (derivedPushforward f).map ((canonicalDerivedTensorProduct X.sheaf).toTensor A B) ≫
        (derivedPushforward f).map (DerivedCategory.Q.map h) := by
  have h3 : (canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A)
        ((pushforwardComplex f).obj B) ≫
      DerivedCategory.Q.map (naiveCupProduct f A B) ≫
      pushforwardComparisonQ f (((tensorComplexBifunctorOn X).obj A).obj B) =
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
          (pushforwardComparisonQ f A ×ₘ pushforwardComparisonQ f B) ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f
          (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) ≫
        (derivedPushforward f).map ((canonicalDerivedTensorProduct X.sheaf).toTensor A B) :=
    naiveCupProduct_relativeCupProduct f A B
  have hn := pushforwardComparisonQ_naturality f h
  have e1 : DerivedCategory.Q.map (naiveCupProduct f A B ≫ (pushforwardComplex f).map h) ≫
      pushforwardComparisonQ f W = DerivedCategory.Q.map (naiveCupProduct f A B) ≫
        pushforwardComparisonQ f (((tensorComplexBifunctorOn X).obj A).obj B) ≫
        (derivedPushforward f).map (DerivedCategory.Q.map h) := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (DerivedCategory.Q.map (naiveCupProduct f A B) ≫ ·) hn
  exact Stacks.GradedTargetChase.naiveCup_chase h3 e1 (Functor.uncurry_obj_map _ _)

end Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces

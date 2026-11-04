module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DirectSummands

/-!
# Finite Tor dimension passes to a retract

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)`. If `K` is a
retract of `L` in `D(O)` and `L` has finite Tor dimension, then so has `K`, with the same
interval: Tor amplitude passes to retracts
(`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_retract`).

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_of_retract`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, w, d} X)

/-- **Finite Tor dimension passes to a retract**, with the same interval. -/
theorem hasFiniteTorDimension_of_retract {K L : RingedSite.DerivedModules.{u, v, w, d} X}
    (i : K ⟶ L) (r : L ⟶ K) (hir : i ≫ r = 𝟙 K) (h : HasFiniteTorDimension T L) :
    HasFiniteTorDimension T K :=
  let ⟨a, b, hab⟩ := h
  ⟨a, b, hasTorAmplitude_of_retract T i r hir a b hab⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end

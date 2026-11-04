module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Transporting derived tensor product data on a ringed site

A derived tensor product datum `Stacks.SheafOfModules.DerivedTensorProduct Y` on a ringed site `Y`
has the same fields as a datum `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Y.O` for its
structure sheaf, so it can be read as one with the same bifunctor. As a consequence, on a ringed
space the derived tensor product `Stacks.SheafOfModules.derivedTensor` of two perfect objects is
perfect.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDatum`: a derived tensor product
  datum on a ringed site `Y`, read as one for the structure sheaf `Y.O`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDatum_tensor`: the transported datum
  has the same bifunctor.
* `AlgebraicGeometry.RingedSpace.isPerfect_derivedTensor`: on a ringed space the derived tensor
  product `Stacks.SheafOfModules.derivedTensor` of two perfect objects is perfect.

## References

* [Stacks Project, Lemma 20.46.6 (Tag 09J5)](https://stacks.math.columbia.edu/tag/09J5)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable (Y : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules Y)]
  [(Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u} Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (AlgebraicGeometry.RingedSite.Modules Y) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)]

/-- A derived tensor product datum on a ringed site `Y`, read as a derived tensor product datum
for its structure sheaf `Y.O`, with the same fields. -/
def toRingedSiteDatum (T : Stacks.SheafOfModules.DerivedTensorProduct Y) :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Y.O where
  tensor := T.tensor
  comparison := T.comparison
  comparison_naturality := T.comparison_naturality
  comparisonRight := T.comparisonRight
  comparisonRight_naturality := T.comparisonRight_naturality
  comparisonRight_eq_comparison := T.comparisonRight_eq_comparison
  comparisonLeft := T.comparisonLeft
  comparisonLeft_naturality := T.comparisonLeft_naturality
  comparisonLeft_eq_comparison := T.comparisonLeft_eq_comparison
  toTensor := T.toTensor
  toTensor_naturality := T.toTensor_naturality
  toTensor_eq_comparisonRight := T.toTensor_eq_comparisonRight
  toTensor_eq_comparisonLeft := T.toTensor_eq_comparisonLeft
  commShift₂ := T.commShift₂
  exact_left := T.exact_left
  exact_right := T.exact_right

/-- The transport leaves the derived tensor bifunctor unchanged. -/
theorem toRingedSiteDatum_tensor (T : Stacks.SheafOfModules.DerivedTensorProduct Y) :
    (toRingedSiteDatum Y T).tensor = T.tensor :=
  rfl

end Stacks.SheafOfModules.DerivedTensorProduct

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u} X.sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)]

/-- On a ringed space the derived tensor product `Stacks.SheafOfModules.derivedTensor` takes a
pair of perfect objects of `D(O_X)` to a perfect object. -/
@[stacks 09J5 "at the derived tensor product of the internal Hom development"]
theorem isPerfect_derivedTensor
    (K L : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : IsPerfect (X := X) K)
    (hL : IsPerfect (X := X) L) :
    IsPerfect (X := X)
      (((derivedTensor X.sheaf).obj K).obj L) :=
  isPerfect_derivedTensorProduct X
    (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDatum (ringedSite X.sheaf)
      (canonicalDerivedTensorProduct (ringedSite X.sheaf))) K L hK hL

end AlgebraicGeometry.RingedSpace

end

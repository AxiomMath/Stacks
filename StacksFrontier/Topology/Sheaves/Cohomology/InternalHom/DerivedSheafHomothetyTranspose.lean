module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomCounitTransport
import StacksCore.Tactic.StacksAttribute

/-!
# The transpose of the homothety

For a complex `K` in the derived category of sheaves of modules over a sheaf of commutative rings
`R` on a topological space, the morphism `R ⊗ K → K` corresponding to the homothety
`R → R Hom(K, K)` under the tensor–hom bijection is invertible.

## Main results

* `isIso_derivedSheafHomTensorEquiv_derivedSheafHomothety`: the transpose of the homothety under
  `derivedSheafHomTensorEquiv` is an isomorphism.
* `isIso_derivedCurryHomEquiv_derivedSheafHomothety`: the transpose of the homothety under
  `RingedSite.derivedCurryHomEquiv` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The transpose of the homothety under the tensor–hom bijection `derivedSheafHomTensorEquiv` is
invertible. -/
theorem isIso_derivedSheafHomTensorEquiv_derivedSheafHomothety
    (K : DerivedCategory (StructureSheafModules Rc)) :
    IsIso (derivedSheafHomTensorEquiv Rc _ K K (derivedSheafHomothety Rc K)) := by
  let := derivedMonoidalStructure Rc
  rw [← whiskerRight_comp_derivedSheafHomCounit, whiskerRight_derivedSheafHomothety_comp]
  infer_instance

/-- The transpose of the homothety under the derived currying bijection
`RingedSite.derivedCurryHomEquiv` of the ringed site is invertible. -/
theorem isIso_derivedCurryHomEquiv_derivedSheafHomothety
    (K : DerivedCategory (StructureSheafModules Rc)) :
    IsIso (RingedSite.derivedCurryHomEquiv (ringedSite Rc) _ K K (derivedSheafHomothety Rc K)) :=
  isIso_derivedSheafHomTensorEquiv_derivedSheafHomothety Rc K

end Stacks.SheafOfModules

end

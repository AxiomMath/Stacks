module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical map from an object of `D(O)` to its double derived dual

Let `(C, O)` be a ringed site and `K` an object of `D(O)`, and write `K^∨ = RSheafHom(K, O)` for
the derived dual. This file constructs the canonical morphism

`K ⟶ (K^∨)^∨`

in `D(O)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedBidual`: the canonical map `K ⟶ (K^∨)^∨`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedBidual_eq`: the map, unfolded.

## Implementation notes

The map is the composite

`K ≅ O ⊗^L_O K ⟶ RSheafHom(O, O) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, O), O)`

of the inverse of the left unit constraint
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso`, the inverse of the
identification `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` of `RSheafHom(O, O)`
with `O`, and the evaluation morphism `AlgebraicGeometry.RingedSite.derivedSheafHomEvaluation` of
Stacks 0A97 at intermediate and target object the structure sheaf, taken at the datum
`AlgebraicGeometry.RingedSite.derivedInternalHomOfBifunctor`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The canonical map from an object of `D(O)` to its double derived dual**,
`K ⟶ (K^∨)^∨`. It is the unit constraint `K ≅ O ⊗^L_O K`, followed by the identification
`O ≅ RSheafHom(O, O)` of the tensor factor, followed by the evaluation morphism of derived
internal Homs of Stacks 0A97 at intermediate and target object the structure sheaf. -/
@[sga "6 I 7.2" "partial"]
def derivedBidual
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    K ⟶ derivedDual X (derivedDual X K) :=
  (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
      (derivedTensorProductDatumOfSite X T) K).inv ≫
    (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).app K ≫
    derivedSheafHomEvaluation X T (derivedInternalHomOfBifunctor X) K
      (derivedStructureSheaf X) (derivedStructureSheaf X)

/-- The canonical map to the double derived dual, unfolded. -/
theorem derivedBidual_eq
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedBidual X T K =
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
          (derivedTensorProductDatumOfSite X T) K).inv ≫
        (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).app K ≫
        derivedSheafHomEvaluation X T (derivedInternalHomOfBifunctor X) K
          (derivedStructureSheaf X) (derivedStructureSheaf X) :=
  rfl

end AlgebraicGeometry.RingedSite

end

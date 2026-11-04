module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DegreewiseComparison

/-!
# The derived comparison of flat base change is compatible with the shift

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes and let `G` be an `𝒪_{S'}`-module flat over `S`. The derived
comparison `RΦ ∘ Rf_* ⟶ Rf'_* ∘ RΨ`
(`Stacks.AlgebraicGeometry.ModuleBaseChange.derivedComparison`) is a natural transformation
between two composites of right derived functors, each of which is a triangulated functor on the
bounded below derived category. This file proves that the transformation is compatible with the
shift; consequently the objects at which the comparison is invertible form a triangulated
subcategory of `D⁺(X)`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.natTransCommShift_comparisonOnHomotopy`: the
  comparison on bounded below homotopy categories is compatible with the shift.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.natTransCommShift_derivedComparison`: **the derived
  comparison of [Stacks, Tag 0GN5] is compatible with the shift.**
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isTriangulated_isIso_derivedComparison_app`: **the
  objects of `D⁺(X)` at which the derived comparison is invertible form a triangulated
  subcategory**, and `isIso_derivedComparison_app_of_distTriang`: two out of three for a
  distinguished triangle.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **The comparison on bounded below homotopy categories is compatible with the shift.** -/
theorem natTransCommShift_comparisonOnHomotopy (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    NatTrans.CommShift (comparisonOnHomotopy G w hG) ℤ :=
  Stacks.Cohomology.BaseChange.natTransCommShift_onHomotopy
    (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
    (baseCoefficients g G) (totalCoefficients g' f' G) (underivedComparison w G)
    (baseCoefficientsDerivedIso g G hG)
    (Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit (baseCoefficients g G))
    (Stacks.Cohomology.BaseChange.natTransCommShift_mapPlus (underivedComparison w G))
    (Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso
      (Iso.refl (modulePushforward f.toLRSHom.toShHom ⋙ baseCoefficients g G)))
    (Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso
      (Iso.refl (totalCoefficients g' f' G ⋙ modulePushforward f'.toLRSHom.toShHom)))

/-- **The derived comparison of [Stacks, Tag 0GN5] is compatible with the shift.** -/
theorem natTransCommShift_derivedComparison (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    NatTrans.CommShift (derivedComparison G w hG) ℤ :=
  Stacks.Cohomology.BaseChange.natTransCommShift_derived
    (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
    (baseCoefficients g G) (totalCoefficients g' f' G) (underivedComparison w G)
    (baseCoefficientsDerivedIso g G hG) (natTransCommShift_comparisonOnHomotopy w G hG)

/-- **The objects of `D⁺(X)` at which the derived comparison of [Stacks, Tag 0GN5] is invertible
form a triangulated subcategory.** -/
theorem isTriangulated_isIso_derivedComparison_app (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    ObjectProperty.IsTriangulated
      (fun E : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) =>
        IsIso ((derivedComparison G w hG).app E)) :=
  let := natTransCommShift_derivedComparison w G hG
  Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated _ _ (derivedComparison G w hG)

/-- The invertibility locus of the derived comparison is closed under isomorphisms. -/
theorem isClosedUnderIsomorphisms_isIso_derivedComparison_app (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun E : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) =>
        IsIso ((derivedComparison G w hG).app E)) :=
  Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms
    (derivedComparison G w hG)

/-- **Two out of three for the derived comparison of [Stacks, Tag 0GN5].** If the comparison is
invertible at the second and third vertices of a distinguished triangle of `D⁺(X)`, it is
invertible at the first. -/
theorem isIso_derivedComparison_app_of_distTriang (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (T : Triangle (DerivedCategory.Plus
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))))
    (hT : T ∈ distTriang (DerivedCategory.Plus
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))))
    (h₂ : IsIso ((derivedComparison G w hG).app T.obj₂))
    (h₃ : IsIso ((derivedComparison G w hG).app T.obj₃)) :
    IsIso ((derivedComparison G w hG).app T.obj₁) :=
  have := isTriangulated_isIso_derivedComparison_app w G hG
  have := isClosedUnderIsomorphisms_isIso_derivedComparison_app w G hG
  ObjectProperty.ext_of_isTriangulatedClosed₁
    (fun E : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) =>
      IsIso ((derivedComparison G w hG).app E)) T hT h₂ h₃

end Stacks.AlgebraicGeometry.ModuleBaseChange

end

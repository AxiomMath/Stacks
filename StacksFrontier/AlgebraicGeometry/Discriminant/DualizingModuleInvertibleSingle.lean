module

import StacksFrontier.RingTheory.Dualizing.Complex
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.DedekindComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleCompleteIntersection
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.RingTheory.Artinian.FiniteType
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.FieldGlobalToRingMap
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinCriteria
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalCompleteIntersection
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext

/-!
# Invertibility of a free rank one module in degree zero

A module isomorphic to the ring `R`, placed in degree zero, is an invertible object of the
derived category of `R`-modules.

## Main results

* `isInvertible_single_of_linearEquiv`: if `M ≃ₗ[R] R`, then `M` placed in degree zero is an
  invertible object of the derived category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- A module isomorphic to the ring, placed in degree zero, is an invertible object of the
derived category: it is isomorphic to the monoidal unit. -/
theorem isInvertible_single_of_linearEquiv {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (e : M ≃ₗ[R] R) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
    MonoidalCategory.IsInvertible
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
  let j : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ≅ 𝟙_ _ :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso e.toModuleIso ≪≫
      (CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj R).symm
  exact ⟨{ inv := 𝟙_ _, isoLeft := ρ_ _ ≪≫ j, isoRight := λ_ _ ≪≫ j }⟩

end Stacks.Discriminant

end

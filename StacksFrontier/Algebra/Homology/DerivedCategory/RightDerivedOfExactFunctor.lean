module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-!
# A total right derived functor of an exact functor is the functor it induces on derived
categories

Let `F : A ⥤ B` be an exact functor between abelian categories with derived categories, and let
`RF : D(A) ⥤ D(B)` be a total right derived functor of `K(F) ⋙ Q_h` with respect to the
quasi-isomorphisms, with comparison `α : K(F) ⋙ Q_h ⟶ Q_h ⋙ RF`. Then no derivation happened:
`RF` is `F.mapDerivedCategory`, the functor that `F` induces degreewise.

For an exact `F` the comparison `CategoryTheory.Functor.mapDerivedCategoryFactorsh` is an
isomorphism, so `F.mapDerivedCategory` is itself a right derived functor of `K(F) ⋙ Q_h`
(`CategoryTheory.Functor.isRightDerivedFunctor_of_inverts`), and right derived functors are
unique up to unique isomorphism (`CategoryTheory.Functor.rightDerivedUnique`). This is the
right-handed counterpart of `Stacks.Homology.leftDerivedIsoMapDerivedCategory`.

## Main results

* `Stacks.Homology.rightDerivedIsoMapDerivedCategory`: a total right derived functor of an exact
  functor is the functor it induces on derived categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Stacks.Homology

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- **A total right derived functor of an exact functor is the functor it induces degreewise.**
If `RF` is a right derived functor of `K(F) ⋙ Q_h` with comparison `α` and `F` is exact, then
`RF ≅ F.mapDerivedCategory`. -/
def rightDerivedIsoMapDerivedCategory
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    RF ≅ F.mapDerivedCategory :=
  have := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh
  Functor.rightDerivedUnique RF F.mapDerivedCategory α F.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

end Stacks.Homology

end

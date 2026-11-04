module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# Right derived functors in non-positive degrees

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, where `𝒜` has enough
injectives, and let `R ⁱ F = H ⁱ ∘ RF ∘ (·[0])` be its higher right derived functors on bounded
below derived categories (`CategoryTheory.Functor.rightDerivedPlus`). This file records the two
facts about `R ⁱ F` in degrees `i ≤ 0` in the forms consumers need:

* `R ⁱ F (X) = 0` for `i < 0`, and
* `R ⁰ F ≅ F` when `F` is left exact.

Both come from
`CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`
(Stacks 05TD), whose first component is the vanishing in negative degrees and whose third
component says that the canonical map `F ⟶ R ⁰ F` is invertible exactly when `F` is left exact.
What is added here is the packaging: the vanishing at an object rather than as a functor, and the
isomorphism `R ⁰ F ≅ F` itself, which the source produces only inside the proof of that
equivalence.

## Main results

* `Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj`: `R ⁱ F (X) = 0` for `i < 0`.
* `Stacks.RightDerivedPlus.rightDerivedPlusZeroIso`: `R ⁰ F ≅ F` for left exact `F`.
* `Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso`: its value at an object.

## Implementation notes

`unitTargetIso` identifies the target of `H ⁰` of the unit of `F.rightDerivedFunctorPlus`,
evaluated at the complexes `X[0]`, with `R ⁰ F`; its source is identified with `F` by
`CategoryTheory.Functor.rightDerivedZeroSourceIso`. `unitTargetIso` exists only so that
`rightDerivedPlusZeroIso` can be written down and is not meant to be used elsewhere.

## References

* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory

namespace Stacks.RightDerivedPlus

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

variable [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
  [EnoughInjectives A]

/-- The target of `H ⁰(α)` at the complexes `X[0]`, where `α` is the unit of a right derived
functor `RF` of `F`, is `R ⁰ F`. -/
noncomputable def unitTargetIso (RF : Plus A ⥤ Plus B) :
    (HomotopyCategory.Plus.singleFunctor A 0 ⋙ Plus.Qh ⋙ RF) ⋙ Plus.homologyFunctor B 0 ≅
      Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0 :=
  Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.singleFunctorPlusIsoCompQh (A := A) 0).symm RF)
      (Plus.homologyFunctor B 0) ≪≫
    Functor.associator _ _ _

/-- **Right derived functors vanish in negative degrees**: `R ⁱ F (X) = 0` for `i < 0`.

This is the object-level form of part (1) of [Stacks, Tag 05TD]. -/
theorem isZero_rightDerivedPlus_obj (i : ℤ) (hi : i < 0) (X : A) :
    IsZero ((F.rightDerivedPlus i).obj X) :=
  (Functor.isZero_iff _).1
    ((Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
      F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit).1 i hi) X

/-- **A left exact functor is its own zeroth right derived functor**: `R ⁰ F ≅ F`.

The isomorphism is `H ⁰` of the unit of `F.rightDerivedFunctorPlus` at the complexes `X[0]`,
which is invertible by part (3) of [Stacks, Tag 05TD]. -/
noncomputable def rightDerivedPlusZeroIso [PreservesFiniteLimits F] :
    F.rightDerivedPlus 0 ≅ F :=
  have _happ : ∀ X : A, IsIso ((Functor.whiskerRight (Functor.whiskerLeft
      (HomotopyCategory.Plus.singleFunctor A 0) F.rightDerivedFunctorPlusUnit)
        (Plus.homologyFunctor B 0)).app X) := fun X =>
    (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
      F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit).2.2.2 inferInstance X
  have : IsIso (Functor.whiskerRight (Functor.whiskerLeft
      (HomotopyCategory.Plus.singleFunctor A 0) F.rightDerivedFunctorPlusUnit)
        (Plus.homologyFunctor B 0)) := NatIso.isIso_of_isIso_app _
  (unitTargetIso (A := A) F.rightDerivedFunctorPlus).symm ≪≫
    (asIso (Functor.whiskerRight (Functor.whiskerLeft
      (HomotopyCategory.Plus.singleFunctor A 0) F.rightDerivedFunctorPlusUnit)
        (Plus.homologyFunctor B 0))).symm ≪≫
    CategoryTheory.Functor.rightDerivedZeroSourceIso F

/-- The value of `rightDerivedPlusZeroIso` at an object: `R ⁰ F (X) ≅ F (X)` for left exact
`F`. -/
noncomputable def rightDerivedPlusZeroObjIso [PreservesFiniteLimits F] (X : A) :
    (F.rightDerivedPlus 0).obj X ≅ F.obj X :=
  (rightDerivedPlusZeroIso F).app X

end Stacks.RightDerivedPlus

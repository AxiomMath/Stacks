module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# The right derived functor of an exact functor on a complex concentrated in degree zero

Let `F : A ⥤ B` be an exact additive functor of abelian categories, with `A` having enough
injectives. Its bounded below right derived functor carries the complex `X[0]` to `F(X)[0]`:

`RF(X[0]) ≅ F(X)[0]`.

## Main definitions

* `CategoryTheory.Functor.mapHomotopyCategoryPlusObjSingleIso`: an additive functor carries
  `X[n]` to `F(X)[n]` on bounded below homotopy categories.
* `CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIso`: `RF(X[0]) ≅ F(X)[0]` for an
  exact `F`, at a single object.

## Implementation notes

Only the object-level comparison is constructed; no naturality in `X` is claimed. Exactness is
needed: for a merely additive `F` the left hand side has the derived functors `RⁱF(X)` as its
cohomology, and the two sides differ already at `i = 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vA uA vB uB wA wB

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive]

/-- An additive functor carries `X[n]` to `F(X)[n]` on bounded below homotopy categories. -/
def mapHomotopyCategoryPlusObjSingleIso (n : ℤ) (X : A) :
    F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A n).obj X) ≅
      (HomotopyCategory.Plus.singleFunctor B n).obj (F.obj X) :=
  (HomotopyCategory.Plus.ι B).preimageIso
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app X))

variable [EnoughInjectives A] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The bounded below right derived functor of an exact functor `F` carries `X[0]` to
`F(X)[0]`. -/
def rightDerivedFunctorPlusObjSingleIso (X : A) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X) :=
  haveI : IsIso F.rightDerivedFunctorPlusUnit :=
    isIso_rightDerivedFunctorPlusUnit_of_preservesHomology F
  haveI : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) :=
    NatIso.isIso_app_of_isIso F.rightDerivedFunctorPlusUnit _
  F.rightDerivedFunctorPlus.mapIso ((singleFunctorPlusIsoCompQh (A := A) 0).app X) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X))).symm ≪≫
    DerivedCategory.Plus.Qh.mapIso (F.mapHomotopyCategoryPlusObjSingleIso 0 X) ≪≫
    ((singleFunctorPlusIsoCompQh (A := B) 0).app (F.obj X)).symm

end CategoryTheory.Functor

end

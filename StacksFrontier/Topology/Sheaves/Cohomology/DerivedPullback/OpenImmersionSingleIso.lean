module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The derived pullback along an open immersion on classes of complexes and on single complexes

Pullback of sheaves of modules along an open immersion of ringed spaces is exact, so its left
derived functor is the functor it induces on derived categories
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`). This file reads that
identification on the class of a complex and on a module placed in a single degree, shifted or
not.

## Main results

* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionComplexIso`:
  `Li^*(Q A) ≅ Q(i^*A)`.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionSingleIso`:
  `Li^*(A[j]) ≅ (i^*A)[j]`, with no flatness asked of `A`.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionSingleShiftIso`:
  `Li^*(A[j]⟦n⟧) ≅ ((i^*A)[j])⟦n⟧`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.HigherDirectImage

namespace Stacks.Cohomology.DerivedOpenImmersion

universe u

attribute [local instance] HasDerivedCategory.standard

section OpenImmersion

variable {X Y : RingedSpace.{u, u}} (i : X ⟶ Y) [SheafedSpace.IsOpenImmersion i]

/-- **`Li^*(Q A) ≅ Q(i^*A)`**: the derived pullback along an open immersion of ringed spaces of
the class of a cochain complex is the class of its degreewise pullback.

`derivedPullbackOpenImmersionIso` says the derived pullback is the functor the degreewise pullback
induces on derived categories, and `CategoryTheory.Functor.mapDerivedCategoryFactors` says that
functor takes the class of a complex to the class of the degreewise image.

`Stacks.Cohomology.ProjectionFormulaPerfect.derivedPullbackRestrictComplexIso` is the same
statement for the particular open immersion `X.ofRestrict U.isOpenEmbedding`, written with
`AlgebraicGeometry.RingedSpace.restrictComplex`; this is the form for an arbitrary open immersion,
which is what a base change taken as a genuine fibre product produces. -/
def derivedPullbackOpenImmersionComplexIso
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (derivedPullback i).obj (DerivedCategory.Q.obj A) ≅
      DerivedCategory.Q.obj
        (((modulePullback i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) :=
  (derivedPullbackOpenImmersionIso i).app _ ≪≫
    (modulePullback i).mapDerivedCategoryFactors.app A

/-- **`Li^*(A[j]) ≅ (i^*A)[j]`**: the derived pullback along an open immersion of ringed spaces of
a module placed in the degree `j` is its degreewise pullback placed in the degree `j`.

No flatness is asked of `A`, and the degree is arbitrary: pullback along an open immersion is
exact, so `derivedPullbackOpenImmersionComplexIso` presents the derived pullback of the single
complex as the class of its degreewise pullback, and
`HomologicalComplex.singleMapHomologicalComplex` identifies that with the single complex of the
pullback.

`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso` and
`derivedPullbackSingleIsoOfFlat` of
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/PullbackPushforwardTensor.lean` are the
same statement for an arbitrary morphism of ringed spaces, respectively of schemes, at the cost
of flatness of `A` and only in degree zero: there the route is the K-flatness of `A[0]`, which
is what flatness buys, whereas here the exactness of `i^*` does the work and the module is
unconstrained. -/
def derivedPullbackOpenImmersionSingleIso (j : ℤ)
    (A : SheafOfModules.{u} (structureSheafRing Y)) :
    (derivedPullback i).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) j).obj A) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) j).obj
        ((modulePullback i).obj A) :=
  (derivedPullback i).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (structureSheafRing Y)) j).app A) ≪≫
    derivedPullbackOpenImmersionComplexIso i _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback i) (ComplexShape.up ℤ) j).app A) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (structureSheafRing X)) j).app ((modulePullback i).obj A)).symm

/-- **`Li^*(A[j]⟦n⟧) ≅ ((i^*A)[j])⟦n⟧`**: `derivedPullbackOpenImmersionSingleIso` shifted, the
derived pullback commuting with the shift by
`Stacks.Cohomology.DerivedPullbackTriangulated.derivedPullback_commShift`.

This is the shape in which the dévissage of the projection formula over an open of the base
consumes the terms of the source complex. -/
def derivedPullbackOpenImmersionSingleShiftIso (j n : ℤ)
    (A : SheafOfModules.{u} (structureSheafRing Y)) :
    (derivedPullback i).obj
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing Y)) j).obj A)⟦n⟧) ≅
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) j).obj
        ((modulePullback i).obj A))⟦n⟧ :=
  ((derivedPullback i).commShiftIso n).app _ ≪≫
    (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) n).mapIso
      (derivedPullbackOpenImmersionSingleIso i j A)

end OpenImmersion

end Stacks.Cohomology.DerivedOpenImmersion

end

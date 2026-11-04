module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistence
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.FibreDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingModule
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StalkVanishingCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedPushforwardSupplement
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDualitySupplement

/-!
# Further results on `NormalizedDualizingExistence`

Results about the objects of the module `NormalizedDualizingExistence` (in `RationalSingularities`)
that need imports beyond those of that module.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase (moduleGlobalSections)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry

/-! ### A quasi-coherent module in a single degree -/

namespace RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

/-- **The hypothesis of [Stacks, Tag 08D5] at the modification, discharged.** `Rf_*` carries an
object of `D_QCoh(𝒪_X)` to one with quasi-coherent cohomology: `f` is proper, hence quasi-compact
and quasi-separated, and `Spec(A)` is quasi-compact. -/
abbrev derivedPushforwardQcoh :
    ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory S.X) (i : ℤ),
      ((DerivedCategory.homologyFunctor S.base.Modules i).obj
        ((Stacks.Duality.derivedPushforward S.f).obj K.obj)).IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs S.f

end RationalSingularitySituation

end AlgebraicGeometry

end

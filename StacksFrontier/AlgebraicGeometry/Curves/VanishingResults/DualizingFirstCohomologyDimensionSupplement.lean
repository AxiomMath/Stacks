module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheafLinear
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.UnitDimension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDualitySupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistenceSupplement

/-!
# Further results on `DualizingFirstCohomologyDimension`

Results about the objects of the module
`StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimension` that
need imports beyond those of that module.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
  TopologicalSpace CategoryTheory.Triangulated

universe u

namespace AlgebraicGeometry.CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- **`𝒪_X` placed in degree zero, as an object of `D_QCoh(𝒪_X)`**, which is the shape in which
clause (4) of [Stacks, Tag 0BS2] consumes it. -/
def unitQuasiCoherent : Stacks.Duality.quasiCoherentDerivedCategory S.X :=
  Stacks.Duality.singleQuasiCoherent (Stacks.Ample.unitModule S.X)
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S.X) 0

/-- The underlying object of `unitQuasiCoherent` is `𝒪_X` placed in degree zero. -/
theorem unitQuasiCoherent_obj :
    (unitQuasiCoherent S).obj =
      (DerivedCategory.singleFunctor S.X.Modules 0).obj (Stacks.Ample.unitModule S.X) := rfl

/-- `𝒪_X[0]` lies in `D^{≤ 0}`. Stated because the instance for a module placed in degree zero
is not found through the definition of `unitQuasiCoherent`. -/
instance isLE_unitQuasiCoherent_obj :
    DerivedCategory.TStructure.t.IsLE (unitQuasiCoherent S).obj 0 :=
  inferInstanceAs (DerivedCategory.TStructure.t.IsLE
    ((DerivedCategory.singleFunctor S.X.Modules 0).obj (Stacks.Ample.unitModule S.X)) 0)

end AlgebraicGeometry.CohenMacaulayCurveSituation

end

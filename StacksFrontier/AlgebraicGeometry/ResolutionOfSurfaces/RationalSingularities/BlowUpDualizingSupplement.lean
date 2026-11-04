module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurveSupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpEventualVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealTwist

/-!
# Further results on `BlowUpDualizing`

Results about the objects of the module
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing` that
need imports beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple

/-- `tensorModules` in this file is `Stacks.RelativeVeryAmple.tensorModules`, the tensor product
of two modules on a scheme given explicitly. `AlgebraicGeometry.tensorModules`, which is in scope
through the imports and would otherwise be found first from inside `AlgebraicGeometry`, takes
the two modules only. -/
local notation "tensorModules" => Stacks.RelativeVeryAmple.tensorModules
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor)

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The conormal sheaf of the exceptional curve is `𝒪_E(1)`: the identification
`ℐ_E ≅ 𝒪_X(1)` of the ideal sheaf of the exceptional divisor with the first twist, restricted
to `E`. -/
def conormalSheafIso_unconditional : conormalSheaf A ≅ curveTwistSheaf A 1 :=
  (Scheme.Modules.pullback (exceptionalImmersion A)).mapIso
      (exceptionalIdealModuleIsoTwistSheaf A) ≪≫
    pullbackTwistSheafIso A 1

/-- `𝒪_E(-1)` is a tensor inverse of the conormal sheaf of the exceptional curve. -/
def conormalTensorTwistNegOneIso_unconditional :
    Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve A) (curveTwistSheaf A (-1))
        (conormalSheaf A) ≅
      unitModule (exceptionalCurve A) :=
  tensorModulesMapIso (exceptionalCurve A) (Iso.refl _) (conormalSheafIso_unconditional A) ≪≫
    curveTwistSheafAddIso A (-1) 1 ≪≫
    curveTwistSheafCongr A (show (-1 : ℤ) + 1 = 0 by ring) ≪≫ curveTwistSheafZeroIso A

/-- The conormal sheaf of the exceptional curve is invertible: it is `𝒪_E(1)`. -/
theorem isInvertibleModule_conormalSheaf_unconditional :
    IsInvertibleModule (exceptionalCurve A) (conormalSheaf A) :=
  Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    (conormalSheafIso_unconditional A).symm

variable {A}

variable (A)

end AlgebraicGeometry.BlowUpDualizing

end

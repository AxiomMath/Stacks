module

public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.DerivedLimitQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.InverseLimitAffineCohomology

/-!
# Additivity of sections over an open of a scheme

For a scheme `X` and an open `U` of `X`, the functor taking a sheaf of modules on the ringed site
of opens of `X` to its sections over `U` is additive.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
attribute [local instance] HasDerivedCategory.standard
namespace AlgebraicGeometry
universe u

private noncomputable instance sectionsOverObjectAdditive (X : Scheme.{u}) (U : X.Opens) :
    (Stacks.Cohomology.Localization.sectionsOverObject (schemeOpensRingedSite X) U).Additive := by
  dsimp [Stacks.Cohomology.Localization.sectionsOverObject, SheafOfModules.evaluation]
  infer_instance

end AlgebraicGeometry
end
